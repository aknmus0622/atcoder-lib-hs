{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | 文字列 (列) のアルゴリズム: ローリングハッシュ・Z-algorithm・Suffix Array・LCP 配列。
--
-- 文字列は 'G.Vector' (@U.fromList s@ で 'String' から作る) で渡す。要素は 'Char' でも 'Int' でもよい。
-- 添字は 0 始まり、区間は半開区間 @[l, r)@。
--
-- > let s = U.fromList "abracadabra"
-- > let h = buildRH s
-- > hashRH 0 4 h == hashRH 7 11 h       -- "abra" と "abra" が一致するか。O(1)
-- > lcpRH 0 7 h h                       -- 位置 0 と位置 7 から始まる部分の共通接頭辞の長さ
-- > zFunction s                         -- z_i = s と s[i..] の共通接頭辞の長さ
-- > let sa = suffixArray s              -- 接尾辞を辞書順に並べた開始位置
-- > lcpArray s sa                       -- 辞書順で隣り合う接尾辞の共通接頭辞の長さ
--
-- == ローリングハッシュ
--
-- 法 2^61 - 1 の多項式ハッシュ。値の一致は「ほぼ確実に」文字列の一致
-- (違う文字列がぶつかる確率は 1 組あたり 長さ / 2^61 程度)。比べる 2 つは同じ長さにする。
-- 2 つの文字列をまたいで比べるときは、それぞれ 'buildRH' して同じ関数で比べる (基数は共通)。
module Atc.String where

import Atc.Math (mulHiLo)
import Atc.Sequence (compressCoords)
import Control.Monad (forM_, when)
import Control.Monad.ST (ST, runST)
import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- ローリングハッシュ

-- | 接頭辞のハッシュ (長さ n + 1) と、基数の累乗 (長さ n + 1)。
data RollingHash = RollingHash !(U.Vector Int) !(U.Vector Int)

-- 法 2^61 - 1。
rhMod :: Int
rhMod = (1 `shiftL` 61) - 1

-- 基数。法より小さい適当な大きい数。
rhBase :: Int
rhBase = 1103515245 * 1000003 + 12345

-- 法 2^61 - 1 の積。2^61 ≡ 1 を使って割り算なしで余りを取る。
rhMul :: Int -> Int -> Int
rhMul a b = rhReduce (fromIntegral ((hi `shiftL` 3) .|. (lo `shiftR` 61)) + fromIntegral (lo .&. fromIntegral rhMod))
  where
    (hi, lo) = mulHiLo (fromIntegral a) (fromIntegral b)
{-# INLINE rhMul #-}

-- 2^62 未満の値を法の中に入れる。
rhReduce :: Int -> Int
rhReduce x = let y = (x .&. rhMod) + (x `shiftR` 61) in if y >= rhMod then y - rhMod else y
{-# INLINE rhReduce #-}

-- 要素を 1 以上 法 未満の値にする (0 を避ける)。
rhCode :: (Enum a) => a -> Int
rhCode x = fromEnum x `mod` (rhMod - 1) + 1
{-# INLINE rhCode #-}

-- | 列から作る。O(n)。
buildRH :: (G.Vector v a, Enum a) => v a -> RollingHash
buildRH xs = RollingHash pre pw
  where
    n = G.length xs
    pre = U.scanl' (\h c -> rhReduce (rhMul h rhBase + c)) 0 (U.generate n (rhCode . G.unsafeIndex xs))
    pw = U.iterateN (n + 1) (`rhMul` rhBase) 1
{-# INLINE buildRH #-}

-- | 長さ。
lengthRH :: RollingHash -> Int
lengthRH (RollingHash pre _) = U.length pre - 1

-- | @[l, r)@ のハッシュ。@0 <= l <= r <= n@。O(1)。
hashRH :: Int -> Int -> RollingHash -> Int
hashRH l r h@(RollingHash pre pw)
  | l < 0 || r < l || r > lengthRH h = error ("Atc.String.hashRH: 範囲外 [" ++ show l ++ ", " ++ show r ++ ")")
  | otherwise = rhReduce (U.unsafeIndex pre r + rhMod - rhMul (U.unsafeIndex pre l) (U.unsafeIndex pw (r - l)))
{-# INLINE hashRH #-}

-- | 列全体のハッシュ ('buildRH' して 'hashRH' 0 n したものと同じ)。O(n)。
hashOfRH :: (Enum a) => [a] -> Int
hashOfRH = foldl (\h c -> rhReduce (rhMul h rhBase + rhCode c)) 0

-- | 連結のハッシュ: @s@ のハッシュ、@t@ のハッシュ、@t@ の長さから @s ++ t@ のハッシュ。O(log 長さ)。
concatHashRH :: Int -> Int -> Int -> Int
concatHashRH hs ht lenT = rhReduce (rhMul hs (rhPow rhBase lenT) + ht)
  where
    rhPow _ 0 = 1
    rhPow b e = let x = rhPow (rhMul b b) (e `div` 2) in if odd e then rhMul x b else x

-- | @h1@ の位置 @i@ から始まる部分と、@h2@ の位置 @j@ から始まる部分の共通接頭辞の長さ。
-- 同じ文字列どうしなら @h1@ と @h2@ に同じものを渡す。O(log n)。
lcpRH :: Int -> Int -> RollingHash -> RollingHash -> Int
lcpRH i j h1 h2 = go 0 (min (lengthRH h1 - i) (lengthRH h2 - j) + 1)
  where
    -- 長さ ok は一致、ng は不一致 (か範囲外)。
    go ok ng
      | ng - ok <= 1 = ok
      | hashRH i (i + mid) h1 == hashRH j (j + mid) h2 = go mid ng
      | otherwise = go ok mid
      where
        mid = (ok + ng) `div` 2

-- ---------------------------------------------------------------------
-- Z-algorithm

-- | @z_i@ = 列と、位置 @i@ から始まる部分の共通接頭辞の長さ (@z_0 = n@)。O(n)。
--
-- パターン @p@ がテキスト @t@ のどこに現れるかは、@p ++ [区切り] ++ t@ の z が @length p@ 以上の位置。
zFunction :: (G.Vector v a, Eq a) => v a -> U.Vector Int
zFunction s
  | n == 0 = U.empty
  | otherwise = U.create $ do
      z <- UM.replicate n 0
      UM.write z 0 n
      -- [l, r) は今までで最も右まで届いた一致の区間。
      let go !i !l !r
            | i >= n = pure ()
            | otherwise = do
                zi0 <- if i < r then min (r - i) <$> UM.unsafeRead z (i - l) else pure 0
                let ext k = if i + k < n && G.unsafeIndex s k == G.unsafeIndex s (i + k) then ext (k + 1) else k
                    zi = ext zi0
                UM.unsafeWrite z i zi
                if i + zi > r then go (i + 1) i (i + zi) else go (i + 1) l r
      go 1 0 0
      pure z
  where
    n = G.length s
{-# INLINE zFunction #-}

-- ---------------------------------------------------------------------
-- Suffix Array / LCP

-- | 接尾辞配列: 接尾辞 @s[i..]@ を辞書順に並べたときの開始位置 @i@ の並び。
-- ダブリングと計数ソートで O(n log n)。
suffixArray :: (G.Vector v a, Ord a) => v a -> U.Vector Int
suffixArray s
  | n == 0 = U.empty
  | otherwise = runST $ do
      let (_, ids) = compressCoords s
      rank <- U.thaw ids
      sa <- UM.unsafeNew n
      cnt <- UM.unsafeNew (n + 1)
      newRank <- UM.unsafeNew n
      -- 初期: 1 文字で安定に並べる。
      countSort rank cnt (U.enumFromN 0 n) sa
      let loop !k = do
            r <- U.freeze rank
            -- 2 つ目の鍵 (rank[i + k]、なければ最小) の順: i + k >= n の i が先、続いて sa の順に i = sa[j] - k。
            saV <- U.freeze sa
            let second = U.enumFromN (n - k) k U.++ U.map (subtract k) (U.filter (>= k) saV)
            countSort rank cnt second sa
            -- 新しい順位を振る。
            sa' <- U.freeze sa
            let key i = (U.unsafeIndex r i, if i + k < n then U.unsafeIndex r (i + k) else -1)
            UM.unsafeWrite newRank (U.head sa') 0
            forM_ [1 .. n - 1] $ \j -> do
              let a = U.unsafeIndex sa' (j - 1)
                  b = U.unsafeIndex sa' j
              pr <- UM.unsafeRead newRank a
              UM.unsafeWrite newRank b (if key a == key b then pr else pr + 1)
            UM.unsafeCopy rank newRank
            top <- UM.unsafeRead rank (U.last sa')
            when (top < n - 1 && 2 * k < n) $ loop (2 * k)
      loop 1
      U.freeze sa
  where
    n = G.length s
    -- order の順を保ったまま、rank で安定に並べて out に書く。
    countSort :: UM.MVector s Int -> UM.MVector s Int -> U.Vector Int -> UM.MVector s Int -> ST s ()
    countSort rank cnt order out = do
      UM.set cnt 0
      U.forM_ order $ \i -> UM.unsafeRead rank i >>= UM.unsafeModify cnt (+ 1) . (+ 1)
      forM_ [1 .. n] $ \c -> UM.unsafeRead cnt (c - 1) >>= \x -> UM.unsafeModify cnt (+ x) c
      U.forM_ order $ \i -> do
        c <- UM.unsafeRead rank i
        p <- UM.unsafeRead cnt c
        UM.unsafeWrite cnt c (p + 1)
        UM.unsafeWrite out p i
{-# INLINE suffixArray #-}

-- | LCP 配列 (Kasai 法): 長さ @n - 1@ で、@i@ 番目は接尾辞 @sa_i@ と @sa_{i+1}@ の
-- 共通接頭辞の長さ。@sa@ は 'suffixArray' の結果。O(n)。
lcpArray :: (G.Vector v a, Eq a) => v a -> U.Vector Int -> U.Vector Int
lcpArray s sa
  | n <= 1 = U.empty
  | otherwise = U.create $ do
      out <- UM.replicate (n - 1) 0
      -- 元の位置の順に見る。i の次の位置 i + 1 では、共通部分は高々 1 減るだけ。
      let go !i !h
            | i >= n = pure ()
            | otherwise = do
                let r = U.unsafeIndex rnk i
                if r == 0
                  then go (i + 1) 0
                  else do
                    let j = U.unsafeIndex sa (r - 1)
                        ext k = if i + k < n && j + k < n && G.unsafeIndex s (i + k) == G.unsafeIndex s (j + k) then ext (k + 1) else k
                        h' = ext h
                    UM.unsafeWrite out (r - 1) h'
                    go (i + 1) (max 0 (h' - 1))
      go 0 0
      pure out
  where
    n = G.length s
    rnk = U.update (U.replicate n 0) (U.imap (flip (,)) sa)
{-# INLINE lcpArray #-}
