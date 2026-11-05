-- | "Atc.Fenwick" を使った 1 点加算・区間和。
module Fenwick where

import Atc
import Control.Monad (forM_)
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | @0 i x@ で a_i に x を足し、@1 l r@ で [l, r) の和を出力する。
pointAddRangeSum :: IO ()
pointAddRangeSum = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildFT as
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, i, x] -> addFT i x t
      [_, l, r] -> sumFT l r t >>= print
      _ -> error "query"

-- | k 番目に小さい値を答える多重集合 (値は 0 以上 n 未満)。
-- @0 x@ で x を入れ、@1 x@ で x を 1 つ消し、@2 k@ で k 番目 (1 始まり) に小さい値を出力する。
-- 値ごとの個数を持ち、先頭からの個数が k 未満の最長の長さが答え ('maxRightFT')。
kthSmallest :: IO ()
kthSmallest = do
  [n, q] <- ints
  t <- newFT n
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, x] -> addFT x (1 :: Int) t -- x を入れる
      [1, x] -> addFT x (-1) t -- x を 1 つ消す
      [2, k] -> maxRightFT (< k) t >>= print -- 個数の和が k 未満の最長 = k 番目の値 (k 個なければ n)
      _ -> error "query"
