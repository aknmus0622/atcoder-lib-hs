-- | "Atc.SparseTable" を使った、更新のない列の区間最小・最大。
module SparseTable where

import Atc
import Control.Monad (replicateM_)
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 各問い合わせ @l r@ に [l, r) の最小と最大を出力する。表は 1 回作れば O(1) で引ける。
rangeMinMax :: IO ()
rangeMinMax = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  let lo = buildSPT min as
      hi = buildSPT max as
  replicateM_ q $ do
    qu <- ints
    case qu of
      [l, r] -> print (foldSPT l r lo, foldSPT l r hi)
      _ -> error "query"

-- | 冪等な演算なら何でもよい: 区間の最大公約数。
rangeGcd :: IO ()
rangeGcd = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  let t = buildSPT gcd as
  replicateM_ q $ do
    qu <- ints
    case qu of
      [l, r] -> print (foldSPT l r t)
      _ -> error "query"
