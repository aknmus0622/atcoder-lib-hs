-- | "Atc.Graph.Flow" を使った最大流・最小費用流・二部マッチング。
module Graph.Flow where

import Atc
import Control.Monad (forM, forM_, replicateM)
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 最大流: 辺 @u v c@ (0 始まり) を足して、0 から n - 1 へ流す。
-- 流した後は 'edgeMF' で辺ごとの流量が見られる。
maxFlowExample :: IO ()
maxFlowExample = do
  [n, m] <- ints
  g <- newMF n
  ids <- forM [1 .. m] $ \_ -> do
    qu <- ints
    case qu of
      [u, v, c] -> addEdgeMF u v c g
      _ -> error "edge"
  f <- flowMF 0 (n - 1) g
  print f
  forM_ ids $ \i -> edgeMF i g >>= print -- (出発点, 行き先, 容量, 流量)

-- | 最小カット: 最大流の値が最小カットの容量。s 側の頂点は 'minCutMF'。
-- ここでは「どの頂点を s 側に残すか」を出力する。
minCutExample :: IO ()
minCutExample = do
  [n, m] <- ints
  g <- newMF n
  forM_ [1 .. m] $ \_ -> do
    qu <- ints
    case qu of
      [u, v, c] -> () <$ addEdgeMF u v c g
      _ -> error "edge"
  _ <- flowMF 0 (n - 1) g
  cut <- minCutMF 0 g
  print [v | v <- [0 .. n - 1], cut U.! v]

-- | 二部マッチング: 左 l 人と右 r 個の組み合わせ (@a b@、0 始まり) から最大マッチング。
matching :: IO ()
matching = do
  [l, r, m] <- ints
  es <- replicateM m ((\qu -> case qu of [a, b] -> (a, b); _ -> error "edge") <$> ints)
  let ms = maxBipartiteMatching l r es
  print (length ms)
  print ms

-- | 最小費用流: 辺 @u v cap cost@ を足して、0 から n - 1 へ k まで流す。
-- 'slopeMCF' は流量と最小費用の折れ線 (流量 0 から始まる)。
minCostFlowExample :: IO ()
minCostFlowExample = do
  [n, m, k] <- ints
  g <- newMCF n
  forM_ [1 .. m] $ \_ -> do
    qu <- ints
    case qu of
      [u, v, cap, cost] -> () <$ addEdgeMCF u v cap cost g
      _ -> error "edge"
  (f, c) <- flowLimitMCF 0 (n - 1) k g
  print (f, c)

-- | 割り当て問題: n 人に n 個の仕事を 1 つずつ。費用 @c_ij@ の合計の最小。
-- 始点 → 人 → 仕事 → 終点 に容量 1 の辺を張って n 流す。
assignment :: IO ()
assignment = do
  [n] <- ints
  cs <- replicateM n ints
  g <- newMCF (2 * n + 2)
  let s = 2 * n
      t = 2 * n + 1
  forM_ (zip [0 ..] cs) $ \(i, row) -> forM_ (zip [0 ..] row) $ \(j, c) -> addEdgeMCF i (n + j) 1 c g
  forM_ [0 .. n - 1] $ \i -> addEdgeMCF s i 1 0 g >> addEdgeMCF (n + i) t 1 0 g
  (_, c) <- flowMCF s t g
  print c
