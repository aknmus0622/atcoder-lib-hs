-- | "Atc.Graph.Cycle" を使った問題。
--
-- 有向か無向かは作るときに決まるので、関数は同じものを呼ぶ。
-- 結果の頂点番号は 0 始まりなので、出力するときは 1 を足す。
module Graph.Cycle where

import Atc
import qualified Data.Vector.Unboxed as U
import Input (ints)

showCycle :: U.Vector Int -> String
showCycle = unwords . map (show . (+ 1)) . U.toList

-- | 閉路を 1 つ出力する。なければ @-1@。
anyCycle :: IO ()
anyCycle = do
  [n, m] <- ints
  es <- getIntGrid 2 m :: IO (Grid U.Vector Int)
  let g = graphFromList n [(u - 1, v - 1, 1) | [u, v] <- toRows es]
  putStrLn (maybe "-1" showCycle (findCycle g))

-- | なもりグラフ (連結で n 頂点 n 辺) の閉路。閉路は 1 つだけなので 'findCycle' で取れる。
namori :: IO ()
namori = do
  n <- head <$> ints
  es <- getIntGrid 2 n :: IO (Grid U.Vector Int)
  mapM_ (putStrLn . showCycle) (findCycle (undirectedGraph es))

-- | 頂点 1 を通る最短閉路 (ABC376 D)。なければ @-1@。
shortestThroughFirst :: IO ()
shortestThroughFirst = do
  [n, m] <- ints
  es <- getIntGrid 2 m :: IO (Grid U.Vector Int)
  let g = graphFromList n [(u - 1, v - 1, 1) | [u, v] <- toRows es]
  print (maybe (-1) fst (shortestCycleFrom g 0))

-- | 重み付きの最短閉路 (内周)。
girth :: IO ()
girth = do
  [n, m] <- ints
  es <- getIntGrid 3 m :: IO (Grid U.Vector Int)
  let g = undirectedGraphFromList n [(u - 1, v - 1, w) | [u, v, w] <- toRows es]
  print (maybe (-1) fst (shortestCycle g))

-- | 小さいグラフの最長閉路と、単純閉路の個数。
longestAndCount :: IO ()
longestAndCount = do
  [n, m] <- ints
  es <- getIntGrid 3 m :: IO (Grid U.Vector Int)
  let g = undirectedGraphFromList n [(u - 1, v - 1, w) | [u, v, w] <- toRows es]
  print (maybe (-1) fst (longestCycle g))
  print (countCycles g)
