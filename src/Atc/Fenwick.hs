{-# LANGUAGE BangPatterns #-}

-- | Fenwick Tree (Binary Indexed Tree)。1 点加算と区間和を O(log n) で。
--
-- 値は和を取れる型 ('Num' かつ 'U.Unbox': 'Int'、'Double'、'Atc.ModInt.Mint' など)。
-- 添字は 0 始まり、区間は半開区間 @[l, r)@。可変で、@m@ は使うモナド (@IO@ か @ST s@)。
--
-- > t <- buildFT (U.fromList [3, 1, 4, 1, 5])
-- > addFT 2 10 t                  -- a_2 += 10
-- > sumFT 1 4 t                   -- a_1 + a_2 + a_3 = 1 + 14 + 1 = 16
-- > prefixSumFT 3 t               -- a_0 + a_1 + a_2 = 18
-- > maxRightFT (<= 5) t           -- 先頭からの和が 5 以下になる最長の長さ (値が非負のとき)
--
-- セグメント木 ("Atc.SegTree") でも同じことができるが、こちらは和専用で軽い。
-- 区間の最小・最大や、区間への作用が要るならセグメント木を使う。
--
-- 転倒数は "Atc.Sequence" の 'countInversions' (中でこれを使う)。
module Atc.Fenwick where

import Control.Monad.Primitive (PrimMonad, PrimState)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Data.Bits (countLeadingZeros, finiteBitSize, shiftL, shiftR, (.&.))

-- | 長さ n の Fenwick Tree。
newtype Fenwick m a
  = Fenwick
      -- | 1 始まりの配列 (長さ n + 1。@i@ 番目は @(i - lowbit i, i]@ の和)
      (UM.MVector (PrimState m) a)

-- | 長さ @n@ で、全て 0 の Fenwick Tree。O(n)。
newFT :: (PrimMonad m, U.Unbox a, Num a) => Int -> m (Fenwick m a)
newFT n = Fenwick <$> UM.replicate (n + 1) 0
{-# INLINE newFT #-}

-- | 列から作る。O(n)。
buildFT :: (PrimMonad m, U.Unbox a, Num a) => U.Vector a -> m (Fenwick m a)
buildFT xs = do
  let n = U.length xs
  t <- UM.replicate (n + 1) 0
  -- 各位置の値を、自分を含む 1 つ上の節点へ足していく。
  let go !i = if i > n
        then pure ()
        else do
          v <- UM.unsafeRead t i
          let x = v + U.unsafeIndex xs (i - 1)
          UM.unsafeWrite t i x
          let j = i + (i .&. negate i)
          if j <= n then UM.unsafeModify t (+ x) j else pure ()
          go (i + 1)
  go 1
  pure (Fenwick t)
{-# INLINE buildFT #-}

-- | 長さ。O(1)。
lengthFT :: (U.Unbox a) => Fenwick m a -> Int
lengthFT (Fenwick t) = UM.length t - 1
{-# INLINE lengthFT #-}

-- | @a_i += x@。範囲外は 'error'。O(log n)。
addFT ::
  (PrimMonad m, U.Unbox a, Num a) =>
  -- | @i@: 添字
  Int ->
  -- | @x@: 足す値
  a ->
  -- | 書き換える Fenwick Tree
  Fenwick m a ->
  -- | なし
  m ()
addFT i0 x f@(Fenwick t)
  | i0 < 0 || i0 >= n = error ("Atc.Fenwick.addFT: 範囲外の添字 " ++ show i0)
  | otherwise = go (i0 + 1)
  where
    n = lengthFT f
    go !i = if i > n then pure () else UM.unsafeModify t (+ x) i >> go (i + (i .&. negate i))
{-# INLINE addFT #-}

-- | @a_0 + .. + a_{r-1}@。@0 <= r <= n@。O(log n)。
prefixSumFT ::
  (PrimMonad m, U.Unbox a, Num a) =>
  -- | @r@: 先頭から何個の和か (@0 <= r <= n@)
  Int ->
  -- | Fenwick Tree
  Fenwick m a ->
  -- | @a_0 + .. + a_{r-1}@
  m a
prefixSumFT r0 f@(Fenwick t)
  | r0 < 0 || r0 > lengthFT f = error ("Atc.Fenwick.prefixSumFT: 範囲外 " ++ show r0)
  | otherwise = go r0 0
  where
    go !i !acc = if i == 0 then pure acc else UM.unsafeRead t i >>= \v -> go (i .&. (i - 1)) (acc + v)
{-# INLINE prefixSumFT #-}

-- | @[l, r)@ の和。@0 <= l <= r <= n@。O(log n)。
sumFT ::
  (PrimMonad m, U.Unbox a, Num a) =>
  -- | @l@: 左端 (含む)
  Int ->
  -- | @r@: 右端 (含まない)
  Int ->
  -- | Fenwick Tree
  Fenwick m a ->
  -- | @a_l + .. + a_{r-1}@
  m a
sumFT l r f
  | l > r = error ("Atc.Fenwick.sumFT: l > r (" ++ show l ++ ", " ++ show r ++ ")")
  | otherwise = (-) <$> prefixSumFT r f <*> prefixSumFT l f
{-# INLINE sumFT #-}

-- | 1 点の値 @a_i@。O(log n)。
getFT ::
  (PrimMonad m, U.Unbox a, Num a) =>
  -- | @i@: 添字
  Int ->
  -- | Fenwick Tree
  Fenwick m a ->
  -- | @a_i@
  m a
getFT i = sumFT i (i + 1)
{-# INLINE getFT #-}

-- | 先頭からの和が条件を満たす最長の長さ。O(log n)。
--
-- > maxRightFT (< k) t   -- 先頭からの和が初めて k 以上になる位置 (k 番目の要素を探す)
maxRightFT ::
  (PrimMonad m, U.Unbox a, Num a) =>
  -- | @p s@: 先頭からの和 @s@ が条件を満たすか。@p 0@ が真で、@r@ を増やすと
  -- @p (a_0 + .. + a_{r-1})@ が真から偽に 1 回だけ変わること (値が非負で @p = (<= k)@ など)
  (a -> Bool) ->
  -- | Fenwick Tree
  Fenwick m a ->
  -- | @p (a_0 + .. + a_{r-1})@ が真になる最大の @r@
  m Int
maxRightFT p f@(Fenwick t) = go top 0 0
  where
    n = lengthFT f
    -- n 以下で最大の 2 冪から降りていく。
    top = if n == 0 then 0 else 1 `shiftL` (finiteBitSize n - 1 - countLeadingZeros n)
    go !step !pos !acc
      | step == 0 = pure pos
      | pos + step <= n = do
          v <- UM.unsafeRead t (pos + step)
          if p (acc + v) then go (step `shiftR` 1) (pos + step) (acc + v) else go (step `shiftR` 1) pos acc
      | otherwise = go (step `shiftR` 1) pos acc
{-# INLINE maxRightFT #-}

-- | 全ての値 (@a_0 .. a_{n-1}@)。O(n)。
toVecFT :: (PrimMonad m, U.Unbox a, Num a) => Fenwick m a -> m (U.Vector a)
toVecFT f@(Fenwick t) = do
  raw <- U.freeze t
  let n = lengthFT f
      -- 'buildFT' の逆: 後ろから、各節点の和を 1 つ上の節点から引く。
      vals = U.create $ do
        v <- U.thaw raw
        let go !i = if i < 1
              then pure ()
              else do
                let j = i + (i .&. negate i)
                if j <= n
                  then UM.unsafeRead v i >>= \x -> UM.unsafeModify v (subtract x) j
                  else pure ()
                go (i - 1)
        go n
        pure (UM.tail v)
  pure vals
{-# INLINE toVecFT #-}
