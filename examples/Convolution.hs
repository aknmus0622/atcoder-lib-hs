-- | "Atc.Convolution" を使った畳み込み。
module Convolution where

import Atc
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 2 つの多項式の積の係数 (mod 998244353)。
polyProduct :: IO ()
polyProduct = do
  as <- U.fromList . map mkMI <$> ints
  bs <- U.fromList . map mkMI <$> ints
  print (U.toList (convolveMI as bs :: U.Vector Mint))

-- | 法なしの正確な値: 2 つの列から 1 つずつ選んだ和ごとの組の数。
-- 値 x の個数を係数にした多項式どうしを掛ける。
pairSums :: IO ()
pairSums = do
  as <- ints
  bs <- ints
  let hist xs = U.accum (+) (U.replicate (maximum xs + 1) 0) [(x, 1) | x <- xs]
      c = convolveInt (hist as) (hist bs)
  print [(s, k) | (s, k) <- zip [0 :: Int ..] (U.toList c), k > 0]
