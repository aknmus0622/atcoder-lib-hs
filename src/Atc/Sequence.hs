{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | 列の定番の処理: 累積和・いもす法・座標圧縮・最長増加部分列・転倒数。
--
-- 添字は 0 始まり、区間は半開区間 @[l, r)@。
--
-- > let ps = prefixSums as          -- 長さ n + 1、ps U.! i = a_0 + .. + a_{i-1}
-- > sliceSum l r ps                 -- a_l + .. + a_{r-1}
-- > imos n [(l, r, x)]              -- 各区間 [l, r) に x を足した結果 (長さ n)
-- >
-- > let (vals, ids) = compressCoords as   -- vals は重複を除いて昇順、a_i = vals ! (ids ! i)
-- > lisLength (<) as                -- 狭義増加の最長部分列の長さ。(<=) なら広義、(>) なら減少
-- > lisIndices (<) as               -- その部分列の添字の 1 つ
-- > countInversions as              -- i < j かつ a_i > a_j の組の数
--
-- 2 次元の累積和は "Atc.Grid" の 'scanRow' と 'scanColumn' で作る。
module Atc.Sequence where

import Atc.BinarySearch (bisect)
import Atc.Fenwick (addFT, newFT, prefixSumFT)
import Control.Monad.ST (runST)
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 累積和

-- | 累積和。長さは @n + 1@ で、@i@ 番目は先頭 @i@ 個の和 (0 番目は 0)。O(n)。
prefixSums :: (G.Vector v a, Num a) => v a -> v a
prefixSums = G.scanl' (+) 0
{-# INLINE prefixSums #-}

-- | 'prefixSums' から @[l, r)@ の和。@0 <= l <= r <= n@。O(1)。
sliceSum :: (G.Vector v a, Num a) => Int -> Int -> v a -> a
sliceSum l r ps
  | l < 0 || r < l || r >= G.length ps = error ("Atc.Sequence.sliceSum: 範囲外 [" ++ show l ++ ", " ++ show r ++ ")")
  | otherwise = G.unsafeIndex ps r - G.unsafeIndex ps l
{-# INLINE sliceSum #-}

-- | いもす法: 長さ @n@ の 0 の列で、各 @(l, r, x)@ の区間 @[l, r)@ に @x@ を足した結果。
-- 区間は @0 <= l <= r <= n@ に切り詰める。O(n + 区間の数)。
imos :: (U.Unbox a, Num a) => Int -> [(Int, Int, a)] -> U.Vector a
imos n qs = U.init (U.scanl1' (+) diff)
  where
    diff =
      U.accum
        (+)
        (U.replicate (n + 1) 0)
        (concat [[(l', x), (r', negate x)] | (l, r, x) <- qs, let l' = clamp l; r' = clamp r, l' < r'])
    clamp = max 0 . min n
{-# INLINE imos #-}

-- ---------------------------------------------------------------------
-- 座標圧縮

-- | 座標圧縮。@(vals, ids)@ で、@vals@ は値を重複なく昇順に並べたもの、@ids@ は
-- 各要素が @vals@ の何番目か (@a_i = vals ! (ids ! i)@)。O(n log n)。
--
-- 圧縮前の値 @x@ の番号は @bisect (-1) (G.length vals) (\\i -> vals ! i <= x)@ などで引く
-- ('compressedIndex' は @x@ 以上の最初の番号)。
compressCoords :: (G.Vector v a, Ord a) => v a -> (v a, U.Vector Int)
compressCoords xs = (vals, ids)
  where
    vals = G.uniq (G.modify Intro.sort xs)
    ids = U.generate (G.length xs) (\i -> compressedIndex (G.unsafeIndex xs i) vals)
{-# INLINE compressCoords #-}

-- | 昇順の @vals@ で、@x@ 以上の最初の番号 (なければ長さ)。@x@ が @vals@ にあればその番号。O(log n)。
compressedIndex :: (G.Vector v a, Ord a) => a -> v a -> Int
compressedIndex x vals = bisect (-1) (G.length vals) (\i -> G.unsafeIndex vals i < x) + 1
{-# INLINE compressedIndex #-}

-- ---------------------------------------------------------------------
-- 最長増加部分列

-- | 最長の部分列の長さ。@rel@ は隣り合う要素の関係で、@(<)@ なら狭義増加、
-- @(<=)@ なら広義増加、@(>)@ なら狭義減少。O(n log n)。
lisLength :: (G.Vector v a) => (a -> a -> Bool) -> v a -> Int
lisLength rel xs = if G.null xs then 0 else U.maximum (lisEndingAt rel xs)
{-# INLINE lisLength #-}

-- | 各 @i@ について、@i@ 番目で終わる最長の部分列の長さ。O(n log n)。
--
-- 長さ k の部分列の末尾として最も「続けやすい」値を @tails[k - 1]@ に持つ
-- (@(<)@ なら最小の末尾)。@x@ は @rel (tails[j]) x@ が偽になる最初の @j@ に置く。
lisEndingAt :: (G.Vector v a) => (a -> a -> Bool) -> v a -> U.Vector Int
lisEndingAt rel xs = runST $ do
  let n = G.length xs
  tails <- G.thaw xs -- 型を合わせるため写す (中身は上書きする)
  out <- UM.unsafeNew n
  let go !i !len
        | i == n = pure ()
        | otherwise = do
            let x = G.unsafeIndex xs i
            -- rel (tails j) x が真になる最後の j (単調: 前ほど真)。
            j <- bisectM (-1) len (\k -> (`rel` x) <$> GM.unsafeRead tails k)
            let pos = j + 1
            GM.unsafeWrite tails pos x
            UM.unsafeWrite out i (pos + 1)
            go (i + 1) (max len (pos + 1))
  go 0 0
  U.unsafeFreeze out
  where
    bisectM ok ng p
      | abs (ng - ok) <= 1 = pure ok
      | otherwise = do
          let mid = ok + (ng - ok) `div` 2
          b <- p mid
          if b then bisectM mid ng p else bisectM ok mid p
{-# INLINE lisEndingAt #-}

-- | 最長の部分列の添字 (昇順) の 1 つ。O(n log n)。
lisIndices :: (G.Vector v a) => (a -> a -> Bool) -> v a -> [Int]
lisIndices rel xs
  | G.null xs = []
  | otherwise = go (U.maxIndex ends) (U.maximum ends) []
  where
    ends = lisEndingAt rel xs
    -- 長さ k で終わる i から、前にある長さ k - 1 で終わり rel が成り立つものへ戻る。
    go i k acc
      | k == 1 = i : acc
      | otherwise =
          let j = head [j' | j' <- [i - 1, i - 2 .. 0], U.unsafeIndex ends j' == k - 1, rel (G.unsafeIndex xs j') (G.unsafeIndex xs i)]
           in go j (k - 1) (i : acc)
{-# INLINE lisIndices #-}

-- ---------------------------------------------------------------------
-- 転倒数

-- | 転倒数: @i < j@ かつ @a_i > a_j@ の組の数。O(n log n)。
countInversions :: (G.Vector v a, Ord a) => v a -> Int
countInversions xs = runST $ do
  let (vals, ids) = compressCoords xs
      k = G.length vals
  t <- newFT k
  -- 左から入れて、自分より大きい値がいくつ入っているか数える。
  let go !i !acc
        | i == U.length ids = pure acc
        | otherwise = do
            let c = U.unsafeIndex ids i
            le <- prefixSumFT (c + 1) t
            addFT c (1 :: Int) t
            go (i + 1) (acc + i - le)
  go 0 0
{-# INLINE countInversions #-}
