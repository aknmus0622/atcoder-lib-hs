-- | "Atc.Sequence" を使った列の定番の処理。
--
-- 添字は 0 始まり、区間は半開区間 @[l, r)@。
module Sequence where

import Atc
import Control.Monad (replicateM)
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 区間和のクエリ: 'prefixSums' を 1 回作って 'sliceSum'。
-- 入力の @l r@ は 1 始まりの閉区間なので @[l - 1, r)@ にする。
rangeSums :: IO ()
rangeSums = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  let ps = prefixSums as
  qs <- replicateM q ints
  mapM_ (\(l, r) -> print (sliceSum (l - 1) r ps)) (map pair qs)

-- | いもす法: 区間 @[l, r)@ に x を足すのをまとめて行う。
-- ここでは時刻ごとの人数 (各人は [s, t) にいる)。
peopleCount :: IO ()
peopleCount = do
  [n, t] <- ints
  qs <- replicateM n ((\(s, e) -> (s, e, 1 :: Int)) . pair <$> ints)
  print (U.maximum (imos t qs))

-- | 座標圧縮: 値を 0 から順の番号に置きかえる。番号は値の小さい順。
compress :: IO ()
compress = do
  as <- U.fromList <$> ints
  let (vals, ids) = compressCoords as
  print (U.length vals) -- 値の種類数
  print (U.toList ids)
  print (compressedIndex 10 vals) -- 10 以上で最小の値の番号

-- | 最長増加部分列: 'lisLength' に隣どうしの関係を渡す。
-- @(<)@ で狭義増加、@(<=)@ で広義増加、@(>)@ で狭義減少。O(n log n)。
longestIncreasing :: IO ()
longestIncreasing = do
  as <- U.fromList <$> ints
  print (lisLength (<) as)
  print (lisLength (<=) as)
  print (map (as U.!) (lisIndices (<) as)) -- その列の 1 つ

-- | 「i 番目で終わる最長の長さ」を両側から使う: 山型 (増えてから減る) の最長。
mountain :: IO ()
mountain = do
  as <- U.fromList <$> ints
  let up = lisEndingAt (<) as
      down = U.reverse (lisEndingAt (<) (U.reverse as)) -- i から始まる狭義減少
  print (U.maximum (U.zipWith (\a b -> a + b - 1) up down))

-- | 転倒数: バブルソートの交換回数。
bubbleSwaps :: IO ()
bubbleSwaps = do
  as <- U.fromList <$> ints
  print (countInversions as)

-- 2 つの整数の行。
pair :: [Int] -> (Int, Int)
pair [a, b] = (a, b)
pair _ = error "2 つの整数"
