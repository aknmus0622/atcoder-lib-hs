{-# LANGUAGE BangPatterns #-}

-- | 畳み込み (数論変換 NTT)。@c_k = Σ_{i + j = k} a_i b_j@ を O((n + m) log (n + m)) で。
--
-- > convolveMI as bs                 -- U.Vector Mint どうし (998244353 など NTT に向く法)
-- > convolveMod 998244353 xs ys      -- Int のまま、法を渡す
-- > convolveInt xs ys                -- 法なしの正確な値 (結果の絶対値が 2^63 未満のとき)
--
-- 結果の長さは @n + m - 1@ (どちらかが空なら空)。
--
-- 法は @c 2^k + 1@ の形の素数で、@2^k@ が結果の長さ以上であること (998244353 = 119 2^23 + 1
-- なら 2^23 = 8388608 まで)。10^9 + 7 は使えないので、'convolveInt' で正確な値を出してから割る
-- (値が大きいなら 3 つに分けて掛ける)。
module Atc.Convolution where

import Atc.Math (Mont, fromMont, montMul, montOf, powMod, primeFactorCounts, toMont)
import Atc.ModInt (ModInt (..), Modulus (..))
import Control.Monad (when)
import Control.Monad.ST (ST)
import Data.Bits (countTrailingZeros, shiftL, shiftR, xor, (.&.))
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- | 法 @p@ での畳み込み。
convolveMod ::
  -- | @p@: 法 (NTT に向く素数)
  Int ->
  -- | @a@ (負でもよい)
  U.Vector Int ->
  -- | @b@ (負でもよい)
  U.Vector Int ->
  -- | @c_k = Σ_{i + j = k} a_i b_j mod p@ (@0@ 以上 @p@ 未満)
  U.Vector Int
convolveMod p as0 bs0
  | U.null as0 || U.null bs0 = U.empty
  | min n m <= 40 = naive
  | sz > maxLen = error ("Atc.Convolution.convolveMod: 法 " ++ show p ++ " では長さ " ++ show (n + m - 1) ++ " を扱えない")
  | otherwise = U.map (\x -> fromIntegral (fromMont mo x)) $ U.take (n + m - 1) $ U.create $ do
      -- 値は Montgomery 表現の Word で持つ (掛け算の剰余に割り算を使わない)。
      fa <- U.thaw (pad as)
      fb <- U.thaw (pad bs)
      ntt mo pw g False fa
      ntt mo pw g False fb
      let mulLoop !i = when (i < sz) $ do
            y <- UM.unsafeRead fb i
            UM.unsafeModify fa (\x -> montMul mo x y) i
            mulLoop (i + 1)
      mulLoop 0
      ntt mo pw g True fa
      pure fa
  where
    as = U.map (`mod` p) as0
    bs = U.map (`mod` p) bs0
    n = U.length as
    m = U.length bs
    sz = head [s | s <- iterate (* 2) 1, s >= n + m - 1]
    pw = fromIntegral p :: Word
    mo = montOf pw
    pad v = U.map (toMont mo . fromIntegral) v U.++ U.replicate (sz - U.length v) 0
    maxLen = 1 `shiftL` countTrailingZeros (p - 1)
    g = primitiveRoot p
    naive = U.accumulate (\x y -> (x + y) `rem` p) (U.replicate (n + m - 1) 0) $
      U.concatMap (\(i, a) -> U.imap (\j b -> (i + j, a * b `rem` p)) bs) (U.indexed as)

-- | 'ModInt' どうしの畳み込み。法は NTT に向く素数 (998244353 など)。
convolveMI ::
  (Modulus m) =>
  -- | @a@
  U.Vector (ModInt m) ->
  -- | @b@
  U.Vector (ModInt m) ->
  -- | @c_k = Σ_{i + j = k} a_i b_j@
  U.Vector (ModInt m)
convolveMI as bs = U.map ModInt (convolveMod p (U.map (\(ModInt x) -> x) as) (U.map (\(ModInt x) -> x) bs))
  where
    p = modulusOf (proxyOf as)
    -- 法を型から取り出すための値 (中身は見ない)。
    proxyOf :: U.Vector (ModInt m) -> ModInt m
    proxyOf _ = ModInt 0

-- | 法なしの畳み込み。結果の各値の絶対値が 2^63 未満なら正確。
-- 3 つの法で計算して中国剰余定理で戻す。長さは 2^24 まで。
convolveInt ::
  -- | @a@ (負でもよい)
  U.Vector Int ->
  -- | @b@ (負でもよい)
  U.Vector Int ->
  -- | @c_k = Σ_{i + j = k} a_i b_j@
  U.Vector Int
convolveInt as bs
  | U.null as || U.null bs = U.empty
  | min (U.length as) (U.length bs) <= 40 =
      U.accumulate (+) (U.replicate (U.length as + U.length bs - 1) 0) $
        U.concatMap (\(i, a) -> U.imap (\j b -> (i + j, a * b)) bs) (U.indexed as)
  | otherwise = U.zipWith3 combine c1 c2 c3
  where
    (p1, p2, p3) = (754974721, 167772161, 469762049)
    c1 = convolveMod p1 as bs
    c2 = convolveMod p2 as bs
    c3 = convolveMod p3 as bs
    inv a m = powMod a (m - 2) m
    i12 = inv (p1 `mod` p2) p2
    i123 = inv (p1 * p2 `mod` p3) p3
    -- Garner: x = x1 + p1 x2 + p1 p2 x3 (0 <= x < p1 p2 p3)。真の値は x か x - p1 p2 p3。
    -- 'Int' の掛け算は 2^64 で折り返すので、そのまま足せば 2^64 を法とした値になる。
    combine r1 r2 r3 =
      let x1 = r1
          x2 = (r2 - x1) `mod` p2 * i12 `mod` p2
          x3 = ((r3 - x1 - p1 `mod` p3 * x2) `mod` p3 * i123) `mod` p3
          big = p1 * p2 * p3 -- 2^64 で折り返した値
          x = x1 + p1 * x2 + p1 * p2 * x3
       in if x3 >= p3 `div` 2 then x - big else x

-- | 法 @p@ (素数) の原始根。O(√p) より速い (p - 1 を素因数分解する)。
primitiveRoot :: Int -> Int
primitiveRoot p
  | p == 2 = 1
  | otherwise = head [g | g <- [2 ..], all (\(q, _) -> powMod g ((p - 1) `div` q) p /= 1) qs]
  where
    qs = primeFactorCounts (p - 1)

-- | 長さが 2 冪の配列を、その場で数論変換する (inv なら逆変換して長さで割る)。
-- 値は法 p の Montgomery 表現。g は原始根 (普通の表現)。
ntt :: Mont -> Word -> Int -> Bool -> UM.MVector s Word -> ST s ()
ntt mo p g inv a = do
  -- ビット反転の順に並べ替える。
  let rev !i = when (i < sz) $ do
        let j = bitReverse i
        when (i < j) $ UM.unsafeSwap a i j
        rev (i + 1)
  rev 0
  let stage !len = when (len <= sz) $ do
        let pi' = fromIntegral p :: Int
            w0 = powMod g ((pi' - 1) `div` len) pi'
            w = toMont mo (fromIntegral (if inv then powMod w0 (pi' - 2) pi' else w0))
            half = len `shiftR` 1
            -- この段で使う 1 の累乗根の累乗を先に作る。
            ws = U.iterateN half (\x -> montMul mo x w) (toMont mo 1)
            butterfly !i !j = when (j < half) $ do
              u <- UM.unsafeRead a (i + j)
              v0 <- UM.unsafeRead a (i + j + half)
              let v = montMul mo v0 (U.unsafeIndex ws j)
                  s' = u + v
              UM.unsafeWrite a (i + j) (if s' >= p then s' - p else s')
              UM.unsafeWrite a (i + j + half) (if u >= v then u - v else u + p - v)
              butterfly i (j + 1)
            block !i = when (i < sz) $ butterfly i 0 >> block (i + len)
        block 0
        stage (len `shiftL` 1)
  stage 2
  when inv $ do
    let pi' = fromIntegral p :: Int
        r = toMont mo (fromIntegral (powMod sz (pi' - 2) pi'))
        scale !i = when (i < sz) $ UM.unsafeModify a (\x -> montMul mo x r) i >> scale (i + 1)
    scale 0
  where
    sz = UM.length a
    lg = countTrailingZeros sz
    bitReverse x = go lg x 0
      where
        go :: Int -> Int -> Int -> Int
        go 0 _ !acc = acc
        go k y acc = go (k - 1) (y `shiftR` 1) ((acc `shiftL` 1) `xor` (y .&. 1))
{-# INLINE ntt #-}
