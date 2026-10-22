{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}

module Atc.Math where

import Control.Monad.ST (runST)
import Data.Kind (Type)
import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import GHC.Exts (Word (W#), quotRemWord2#, timesWord2#)

gcdAll :: [Int] -> Int
gcdAll = foldr gcd 0

lcmAll :: [Int] -> Int
lcmAll = foldr lcm 1

-- ---------------------------------------------------------------------
-- 素数判定・素因数分解
--
-- 'Int' と 'Integer' のどちらでも同じ名前で使える ('PrimeNum')。
--
-- > isPrime (998244353 :: Int)              -- True
-- > primeFactors (360 :: Int)               -- [2,2,2,3,3,5]        (U.Vector Int)
-- > primeFactorCounts (360 :: Int)          -- [(2,3),(3,2),(5,1)]  (U.Vector (Int, Int))
-- > primeFactors (2 ^ 70 * 3 :: Integer)    -- [2,2,…,2,3]          (V.Vector Integer)
-- > powMod (2 :: Integer) (10 ^ 30) (10 ^ 20 + 39)
--
-- 結果の Vector は、'Int' なら @U.Vector@、'Integer' なら @V.Vector@
-- ('Integer' は Unboxed にできないため)。個数は どちらも 'Int'。
--
-- 数値リテラルを直接渡すときは型を書く (@isPrime 7@ だけだと型が決まらない)。
-- 入力から読んだ値なら型は決まっているので不要。
--
-- 素因数分解は Pollard の ρ 法 (Brent の改良版)。途中で「もう素数か」を見るのに
-- Miller–Rabin 法を使う ('isPrime' もこれ)。ρ 法は約数を見つける方法で、
-- 素数かどうかは判定できないので、この 2 つで 1 組になっている。
--
-- 2^63 未満は 'Integer' でも 'Int' と同じ高速な計算 (128 bit 積と Montgomery 乗算) に回す。
-- それより大きい 'Integer' は多倍長のまま計算する。
--
-- * 'isPrime' は 3.3 × 10^24 未満なら必ず正しい。それ以上は 20 個の基底で調べる
--   (誤判定は事実上起きないが、理論上は確率的)。
-- * 'primeFactors' は、2 番目に大きい素因数が 10^12 程度までなら現実的な時間で終わる
--   (ρ 法は 最小の素因数 p に対して √p 回程度かかる)。

-- | 素数判定・素因数分解ができる整数型。
class (Integral a) => PrimeNum a where
  -- | 結果を並べる Vector。'Int' は @U.Vector@、'Integer' は @V.Vector@。
  type PrimeVec a :: Type -> Type

  -- | 素数か。
  isPrime :: a -> Bool

  -- | 素因数を小さい順に、重複も含めて並べる。@n <= 1@ は空。
  --
  -- > primeFactors (360 :: Int)   -- [2,2,2,3,3,5]
  primeFactors :: a -> PrimeVec a a

  -- | @(素因数, 個数)@ を素因数の小さい順に並べる。@n <= 1@ は空。
  --
  -- > primeFactorCounts (360 :: Int)   -- [(2,3),(3,2),(5,1)]
  primeFactorCounts :: a -> PrimeVec a (a, Int)

  -- | @a * b mod m@ (@0@ 以上 @m@ 未満)。@m >= 1@。'Int' でも桁あふれしない。
  mulMod :: a -> a -> a -> a

  -- | @a ^ e mod m@ (@0@ 以上 @m@ 未満)。@e >= 0@、@m >= 1@。'Int' でも桁あふれしない。
  powMod :: a -> a -> a -> a

instance PrimeNum Int where
  type PrimeVec Int = U.Vector

  isPrime n = n >= 2 && isPrimeW (fromIntegral n)

  primeFactors n
    | n <= 1 = U.empty
    | otherwise = U.map fromIntegral (primeFactorsW (fromIntegral n))

  primeFactorCounts = countRuns . primeFactors

  mulMod a b m = fromIntegral (mulModW (toWordMod a m) (toWordMod b m) (fromIntegral m))

  powMod a e m = fromIntegral (powModW (toWordMod a m) (fromIntegral e) (fromIntegral m))

instance PrimeNum Integer where
  type PrimeVec Integer = V.Vector

  isPrime n
    | n < 2 = False
    | otherwise = isPrimeI n

  primeFactors n
    | n <= 1 = V.empty
    | n < wordLimit = V.map toInteger (V.convert (primeFactorsW (fromInteger n)))
    | otherwise = primeFactorsI n

  primeFactorCounts = countRuns . primeFactors

  mulMod a b m = (a * b) `mod` m

  powMod a0 e0 m = go (a0 `mod` m) e0 (1 `mod` m)
    where
      go !_ 0 !acc = acc
      go a e acc = go (a * a `mod` m) (e `div` 2) (if odd e then acc * a `mod` m else acc)

-- ---------------------------------------------------------------------
-- 型によらない部分

-- 並べ替え済みの素因数を (素因数, 個数) にまとめる。
countRuns :: (G.Vector v a, G.Vector v (a, Int), Eq a) => v a -> v (a, Int)
countRuns fs = runST $ do
  let len = G.length fs
  buf <- GM.unsafeNew len
  let go !i !k
        | i >= len = pure k
        | otherwise = do
            let p = G.unsafeIndex fs i
                j = maybe len (+ i) (G.findIndex (/= p) (G.unsafeDrop i fs))
            GM.unsafeWrite buf k (p, j - i)
            go j (k + 1)
  k <- go 0 0
  G.unsafeFreeze (GM.unsafeSlice 0 k buf)
{-# INLINE countRuns #-}

-- 小さい素因数は割り算で先に取る (ρ 法は 2 や小さい素数が苦手)。
smallPrimes :: [Int]
smallPrimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

-- 素因数を最大 @size@ 個分の領域に書いて、最後に並べ替える。
-- 小さい素数で割ったあとの残りを、素数になるまで @divisorOf@ で割っていく。
factorsWith ::
  (G.Vector v t, Integral t) => Int -> (t -> Bool) -> (t -> t) -> t -> v t
factorsWith size prime divisorOf n0 = runST $ do
  buf <- GM.unsafeNew size
  let trial !k !m [] = pure (k, m)
      trial k m (p : ps)
        | m `mod` p' == 0 = GM.unsafeWrite buf k p' >> trial (k + 1) (m `div` p') (p : ps)
        | otherwise = trial k m ps
        where
          p' = fromIntegral p
      split !k 1 = pure k
      split k m
        | prime m = GM.unsafeWrite buf k m >> pure (k + 1)
        | otherwise = do
            let d = divisorOf m
            k' <- split k d
            split k' (m `div` d)
  (k, rest) <- trial 0 n0 smallPrimes
  k' <- split k rest
  let v = GM.unsafeSlice 0 k' buf
  Intro.sort v
  G.unsafeFreeze v
{-# INLINE factorsWith #-}

-- Miller–Rabin 法。n は 5 以上の奇数。
-- @mul@ は法 n の掛け算、@lift@ は普通の値を @mul@ 用の表現に直す関数、@one@ は 1 の表現。
millerRabinWith :: (Integral t) => (t -> t -> t) -> (t -> t) -> t -> t -> [t] -> Bool
millerRabinWith mul lift one n = all witness
  where
    minusOne = n - one
    -- n - 1 = d * 2^s (d は奇数)
    (s, d) = split2 (0 :: Int) (n - 1)
    split2 !k x
      | even x = split2 (k + 1) (x `div` 2)
      | otherwise = (k, x)
    pow a0 e0 = go a0 e0 one
      where
        go !_ 0 !acc = acc
        go a e acc = go (mul a a) (e `div` 2) (if odd e then mul acc a else acc)
    witness base
      | base `mod` n == 0 = True
      | otherwise = x0 == one || x0 == minusOne || squares (s - 1) x0
      where
        x0 = pow (lift (base `mod` n)) d
    squares 0 _ = False
    squares k x =
      let x' = mul x x
       in x' == minusOne || (x' /= one && squares (k - 1) x')
{-# INLINE millerRabinWith #-}

-- Pollard の ρ 法 (Brent の改良版)。合成数 m の 1 より大きい約数を 1 つ返す。m 自身が返ったら失敗。
-- f(x) = x^2 + c を回し、128 回分の |x - y| の積をまとめて gcd を取る。
-- @mul@ は法 m の掛け算 (Montgomery 表現のままでもよい。表現が変わっても gcd は変わらない)。
rhoWith :: forall t. (Integral t) => (t -> t -> t) -> t -> t -> t
rhoWith mul m c = outer 2 1 (1 :: Int)
  where
    batch = 128 :: Int
    f x = let v = mul x x + c in if v >= m then v - m else v
    diff a b = if a > b then a - b else b - a
    -- 今の点を x として固定し、y を r 歩進めてから、さらに r 歩ぶんを batch 個ずつ調べる。
    outer !y !q !r = inner y r 0 (iterateN r y) q
    inner !x !r !k !y !q
      | k >= r = outer y q (2 * r)
      | g == 1 = inner x r (k + batch) y' q'
      | g /= m = g
      | otherwise = backtrack x y
      where
        (y', q') = steps (min batch (r - k)) y q
        g = gcd q' m
        steps :: Int -> t -> t -> (t, t)
        steps 0 !yy !qq = (yy, qq)
        steps i yy qq = let yy' = f yy in steps (i - 1) yy' (mul qq (diff x yy'))
    -- まとめた積が m の倍数になったら、1 歩ずつ戻って調べ直す。
    backtrack x ys =
      let ys' = f ys
          g = gcd (diff x ys') m
       in if g > 1 then g else backtrack x ys'
    iterateN :: Int -> t -> t
    iterateN 0 !y = y
    iterateN i y = iterateN (i - 1) (f y)
{-# INLINE rhoWith #-}

-- 失敗したら定数 c を変えてやり直す。
findDivisorWith :: (Integral t) => (t -> t -> t) -> t -> t
findDivisorWith mul m = go 1
  where
    go c = let d = rhoWith mul m c in if d /= m then d else go (c + 1)
{-# INLINE findDivisorWith #-}

-- ---------------------------------------------------------------------
-- 2^63 未満: Word で計算する

wordLimit :: Integer
wordLimit = 2 ^ (63 :: Int)

-- 負の数も法 m の中に入れてから Word にする。
toWordMod :: Int -> Int -> Word
toWordMod a m = fromIntegral (a `mod` m)

-- | 128 bit の積を (上位, 下位) で返す。
mulHiLo :: Word -> Word -> (Word, Word)
mulHiLo (W# a) (W# b) = case timesWord2# a b of (# h, l #) -> (W# h, W# l)
{-# INLINE mulHiLo #-}

-- 128 bit の積を作って割る。a, b < m なので上位 64 bit は m 未満になり、割り算があふれない。
mulModW :: Word -> Word -> Word -> Word
mulModW (W# a) (W# b) (W# m) = case timesWord2# a b of
  (# hi, lo #) -> case quotRemWord2# hi lo m of
    (# _, r #) -> W# r
{-# INLINE mulModW #-}

-- 法が奇数なら Montgomery 乗算、偶数なら割り算で。a < m。
powModW :: Word -> Word -> Word -> Word
powModW a e m
  | m == 1 = 0
  | odd m = let mo = montOf m in fromMont mo (montPow mo (toMont mo a) e)
  | otherwise = go a e 1
  where
    go !_ 0 !acc = acc
    go x k acc = go (mulModW x x m) (k `div` 2) (if odd k then mulModW acc x m else acc)

-- Montgomery 乗算: x を x * 2^64 mod n で表すと、掛け算の剰余が割り算なしで求まる。
-- n は 2^63 未満の奇数。
--
-- 法 n、-n^(-1) mod 2^64、2^128 mod n。
data Mont = Mont !Word !Word !Word

montOf :: Word -> Mont
montOf n = Mont n (negate inv) r2
  where
    -- ニュートン法で n^(-1) mod 2^64。正しい桁数が 3 → 6 → 12 → 24 → 48 → 96 と倍になる。
    inv = iterate (\x -> x * (2 - n * x)) n !! 5
    r1 = negate n `mod` n
    r2 = mulModW r1 r1 n

-- (hi * 2^64 + lo) / 2^64 mod n。hi < n のとき。
montReduce :: Mont -> Word -> Word -> Word
montReduce (Mont n ni _) hi lo =
  let (mh, _) = mulHiLo (lo * ni) n
      -- lo + (lo * ni * n の下位) は 2^64 の倍数なので、繰り上がりは lo /= 0 のときだけ。
      t = hi + mh + (if lo /= 0 then 1 else 0)
   in if t >= n then t - n else t
{-# INLINE montReduce #-}

montMul :: Mont -> Word -> Word -> Word
montMul mo a b = let (hi, lo) = mulHiLo a b in montReduce mo hi lo
{-# INLINE montMul #-}

toMont :: Mont -> Word -> Word
toMont mo@(Mont n _ r2) x = montMul mo (x `mod` n) r2
{-# INLINE toMont #-}

fromMont :: Mont -> Word -> Word
fromMont mo = montReduce mo 0
{-# INLINE fromMont #-}

montPow :: Mont -> Word -> Word -> Word
montPow mo a0 e0 = go a0 e0 (toMont mo 1)
  where
    go !_ 0 !acc = acc
    go a e acc = go (montMul mo a a) (e `div` 2) (if odd e then montMul mo acc a else acc)

-- この 7 つの基底で調べれば 2^64 未満は必ず正しく判定できる。
isPrimeW :: Word -> Bool
isPrimeW n
  | n < 2 = False
  | n < 4 = True
  | even n = False
  | otherwise =
      let mo = montOf n
       in millerRabinWith (montMul mo) (toMont mo) (toMont mo 1) n [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

-- 素因数は 64 個未満。
primeFactorsW :: Word -> U.Vector Word
primeFactorsW = factorsWith 64 isPrimeW findDivisorW

-- 奇数で、47 以下の素因数を持たない合成数の約数。
findDivisorW :: Word -> Word
findDivisorW m = let mo = montOf m in findDivisorWith (montMul mo) m

-- ---------------------------------------------------------------------
-- 2^63 以上の Integer: 多倍長で計算する。途中で 2^63 未満になったら Word に回す。

isPrimeI :: Integer -> Bool
isPrimeI n
  | n < wordLimit = isPrimeW (fromInteger n)
  | even n = False
  -- 41 までの 13 個で 3.3 × 10^24 未満は必ず正しい。残りは念のため。
  | otherwise =
      millerRabinWith (\a b -> a * b `mod` n) id 1 n [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

primeFactorsI :: Integer -> V.Vector Integer
primeFactorsI n = factorsWith (bitLength n) isPrimeI findDivisorI n
  where
    bitLength x = length (takeWhile (> 0) (iterate (`div` 2) x))

findDivisorI :: Integer -> Integer
findDivisorI m
  | m < wordLimit = toInteger (findDivisorW (fromInteger m))
  | otherwise = findDivisorWith (\a b -> a * b `mod` m) m
