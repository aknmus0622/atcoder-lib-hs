-- | "Atc.Graph.Functional" を使った問題。
--
-- 行き先の並び @a_1 .. a_N@ は 'functionalGraph' で 'AtcGraph' にする。
-- 結果の頂点番号は 0 始まりなので、出力するときは 1 を足す。
module Graph.Functional where

import Atc
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | K 回先の頂点 (ABC167 D)。始点が 1 つなので 'walkFG'。
teleporter :: IO ()
teleporter = do
  [_, k] <- ints
  g <- functionalGraph . U.fromList <$> ints
  print (walkFG g 0 k + 1)

-- | 始点ごとの K 回先: 'jumpTableFG' の表を引く。
teleporterQueries :: IO ()
teleporterQueries = do
  [_, q] <- ints
  g <- functionalGraph . U.fromList <$> ints
  qs <- mapM (const ints) [1 .. q]
  let table = jumpTableFG g (maximum (0 : map (!! 1) qs))
  mapM_ (\[v, k] -> print (jumpFG table (v - 1) k + 1)) qs

-- | 経路上の和 (ABC241 E)。
--
-- 辺の重みに足す量を持たせ、'rhoFG' の経路の累積和を取る。閉路の分は周回数を掛ける。
puttingCandies :: IO ()
puttingCandies = do
  [n, k] <- ints
  a <- ints
  let g = graphFromList n [(i, (i + x) `mod` n, x) | (i, x) <- zip [0 ..] a]
      (path, t, c) = rhoFG g 0
      pre = U.scanl' (+) 0 (U.map (U.head . adjacentWeights g) path)
      (q, r) = (k - t) `divMod` c
  print $
    if k <= t
      then pre U.! k
      else pre U.! t + q * (pre U.! (t + c) - pre U.! t) + (pre U.! (t + r) - pre U.! t)

-- | 同じ問題を辺の重みの表で: 'weightedJumpTableFG' と 'foldJT'。
puttingCandiesTable :: IO ()
puttingCandiesTable = do
  [n, k] <- ints
  a <- ints
  let g = graphFromList n [(i, (i + x) `mod` n, x) | (i, x) <- zip [0 ..] a]
  print (snd (foldJT (+) 0 (weightedJumpTableFG (+) g k) 0 k))

-- | 閉路の長さと頂点を出す (ABC311 C)。
oneCycle :: IO ()
oneCycle = do
  _ <- ints
  g <- functionalGraph . U.fromList <$> ints
  let c = V.head (cyclesFG g)
  print (U.length c)
  putStrLn (unwords (map (show . (+ 1)) (U.toList c)))

-- | 到達できる頂点の組の数 (ABC357 E)。
reachablePairs :: IO ()
reachablePairs = do
  _ <- ints
  g <- functionalGraph . U.fromList <$> ints
  print (U.sum (reachFG g))

-- | 連結成分の個数: 各成分に閉路は 1 つなので、閉路の個数と等しい。
componentsOfFunctional :: IO ()
componentsOfFunctional = do
  _ <- ints
  g <- functionalGraph . U.fromList <$> ints
  print (countCyclesFG g)

-- | 成分ごとの DP: 各閉路について、流れ込む木の頂点数の最大を求める。
--
-- 'foldTreesFG' で閉路の頂点まで畳み込み、'cyclesFG' で閉路ごとにまとめる。
largestTree :: IO ()
largestTree = do
  _ <- ints
  g <- functionalGraph . U.fromList <$> ints
  let size = foldTreesFG g (const (1 :: Int)) (+)
  mapM_ (print . U.maximum . U.map (size U.!)) (cyclesFG g)
