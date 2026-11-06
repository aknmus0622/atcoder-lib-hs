{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Sparse Table: 更新しない列の区間 @[l, r)@ の最小・最大などを O(1) で求める。
--
-- 演算は結合的で、同じ要素を 2 回使っても結果が変わらない (冪等: @op x x = x@) こと。
-- 'min' / 'max' / 'gcd' / @(.&.)@ / @(.|.)@ など。和は冪等でないので使えない
-- (和は "Atc.Sequence" の 'prefixSums'、更新があるなら "Atc.SegTree")。
--
-- > let t = buildSPT min as        -- 作るのは O(n log n)
-- > foldSPT l r t                  -- min a_l .. a_{r-1}。O(1)
--
-- @v@ は 'U.Vector' や 'V.Vector'。
module Atc.SparseTable where

import Data.Bits (countLeadingZeros, finiteBitSize, shiftL)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G

-- | Sparse Table ('buildSPT' で作る)。
data SparseTable v a
  = SparseTable
      -- | 演算
      (a -> a -> a)
      -- | 段ごとの表。@k@ 段目の @i@ 番目は @[i, i + 2^k)@ の結果
      !(V.Vector (v a))

-- | 表を作る。O(n log n)。
buildSPT ::
  forall v a.
  (G.Vector v a) =>
  -- | @op x y@: 結合的で冪等 (@op x x = x@) な演算
  (a -> a -> a) ->
  -- | @xs@: 元の列
  v a ->
  -- | Sparse Table
  SparseTable v a
buildSPT op xs = SparseTable op (V.fromList (go 0 xs))
  where
    n = G.length xs
    -- k 段目 (長さ n - 2^k + 1) から k + 1 段目: [i, i + 2^k) と [i + 2^k, i + 2^(k+1)) を合わせる。
    go :: Int -> v a -> [v a]
    go k row
      | 2 `shiftL` k > n = [row]
      | otherwise = row : go (k + 1) (G.zipWith op row (G.drop (1 `shiftL` k) row))

-- | 区間 @[l, r)@ を演算で畳む。@0 <= l < r <= n@ (空の区間は 'error')。O(1)。
foldSPT ::
  (G.Vector v a) =>
  -- | @l@: 区間の左端 (含む)
  Int ->
  -- | @r@: 区間の右端 (含まない)
  Int ->
  -- | Sparse Table
  SparseTable v a ->
  -- | @op a_l .. a_{r-1}@ の結果
  a
foldSPT l r (SparseTable op tbl)
  | l < 0 || r <= l || r > G.length (V.head tbl) = error ("Atc.SparseTable.foldSPT: 範囲外か空 [" ++ show l ++ ", " ++ show r ++ ")")
  | otherwise = op (G.unsafeIndex row l) (G.unsafeIndex row (r - 1 `shiftL` k))
  where
    k = finiteBitSize (r - l) - 1 - countLeadingZeros (r - l)
    row = V.unsafeIndex tbl k
{-# INLINE foldSPT #-}

-- | 元の列の長さ。
lengthSPT :: (G.Vector v a) => SparseTable v a -> Int
lengthSPT (SparseTable _ tbl) = G.length (V.head tbl)
