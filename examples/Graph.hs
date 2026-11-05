-- | "Atc.Graph" を使ったグラフのアルゴリズム。
--
-- 頂点は 0 始まり。入力の始まりは 'fromOneBased' / 'fromZeroBased' で示す。距離は
-- 届かない頂点を @-1@ (負の重みを扱う関数は 'Nothing') で表す。
module Graph where

import Atc
import qualified Data.Graph as DG
import Data.Maybe (fromMaybe)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 無向グラフを読む (重みなし)。
--
-- 幅 2 のグリッドで @u v@ を読み、1 始まりなので 'fromOneBased' で包む。
-- 頂点数は辺に出てくる最大の番号になるので、
-- 孤立した頂点がありうるなら 'graphFromList' に頂点数を渡す。
readUndirected :: IO AtcGraph
readUndirected = do
  [_, m] <- ints
  es <- getIntGrid 2 m :: IO (Grid U.Vector Int)
  pure (undirectedGraph (fromOneBased es))

-- | 有向グラフを読む (重み付き)。
--
-- 幅 3 で @u v w@。有向なので @u@ から @v@ への辺だけが入る。
readDirected :: IO AtcGraph
readDirected = do
  [_, m] <- ints
  es <- getIntGrid 3 m :: IO (Grid U.Vector Int)
  pure (directedGraph (fromOneBased es))

-- | 頂点番号が 0 始まりの入力 (@0 .. n - 1@) は 'fromZeroBased' で包む。
readZeroBased :: IO AtcGraph
readZeroBased = do
  [_, m] <- ints
  es <- getIntGrid 2 m :: IO (Grid U.Vector Int)
  pure (undirectedGraph (fromZeroBased es))

-- | 0 始まりの辺を自分で組み立てる: 'graphFromList'。
--
-- 頂点数を渡せるので、孤立した頂点があっても困らない。無向にしたいなら
-- 'undirectedGraphFromList' に片方の向きだけ渡す。
buildByHand :: IO ()
buildByHand = do
  [n, m] <- ints
  es <- mapM (const ((\[a, b, w] -> (a - 1, b - 1, w)) <$> ints)) [1 .. m]
  let g = undirectedGraphFromList n es
  print (numVertices g)

-- | グラフを覗く: 次数と隣接。
--
-- 'adjacent' は @(行き先, 重み)@ を O(1) で切り出す。重みが要らなければ
-- 'adjacentVertices'、重みだけなら 'adjacentWeights'。
inspect :: IO ()
inspect = do
  g <- readUndirected
  print (numVertices g)
  print (outDegree g 0)
  print (adjacent g 0)
  print (adjacentVertices g 0)
  print (adjacentWeights g 0)
  print (take 5 (graphEdges g)) -- 無向なら両向きが入る

-- | 辺の向きを逆にする: 'reverseGraph'。
--
-- 「全頂点から 1 点への距離」を知りたいときは、逆向きのグラフで 1 点から
-- BFS すればよい。
reversed :: IO ()
reversed = do
  g <- readDirected
  let back = reverseGraph g
  print (bfsDist back [0])

-- | "Data.Graph" に渡す: 'toDataGraph' (重みは捨てる)。
--
-- 標準ライブラリ側の関数を使いたいときの橋渡し。
toStdlib :: IO ()
toStdlib = do
  g <- readUndirected
  print (DG.topSort (toDataGraph g))

-- | 重みなしの最短路: 'bfsDist'。始点は複数でもよい。
--
-- 届かない頂点は @-1@。多始点 BFS は「どの始点からでもよい最短距離」になる。
bfs :: IO ()
bfs = do
  g <- readUndirected
  let dist = bfsDist g [0]
  print (U.toList dist)
  print (U.toList (bfsDist g [0, 1, 2])) -- 多始点

-- | 経路も欲しいとき: 'bfsDistPrev' と 'pathTo'。
--
-- @prev@ は各頂点の直前の頂点 (始点と届かない頂点は @-1@)。出力するときは
-- 1 を足す。
bfsWithPath :: IO ()
bfsWithPath = do
  g <- readUndirected
  let n = numVertices g
      (dist, prev) = bfsDistPrev g [0]
  if dist U.! (n - 1) == -1
    then putStrLn "No"
    else putStrLn (unwords (map (show . (+ 1)) (pathTo prev (n - 1))))

-- | グラフを作らずに BFS する: 'bfsDistBy'。
--
-- 隣接関係が式で書けるとき (格子・ビット全探索の状態遷移など) に、
-- 頂点数と隣接関数だけで済ませられる。
bfsWithoutGraph :: IO ()
bfsWithoutGraph = do
  [h, w] <- ints
  g <- getCharGrid w h :: IO (Grid U.Vector Char)
  let next i =
        let (r, c) = indexToPos w i
         in [posToIndex w q | (q, x) <- neighbors4 (r, c) g, x /= '#']
      dist = bfsDistBy (w * h) next [0]
  print (dist U.! (w * h - 1))

-- | 重み付きの最短路 (非負): 'dijkstraDist'。
--
-- O(m log m)。届かない頂点は @-1@。経路が要れば 'dijkstraDistPrev'。
dijkstra :: IO ()
dijkstra = do
  g <- readDirected
  let n = numVertices g
      (dist, prev) = dijkstraDistPrev g [0]
  print (U.toList (dijkstraDist g [0]))
  print (dist U.! (n - 1))
  print (map (+ 1) (pathTo prev (n - 1)))

-- | 負の重みがあるとき: 'bellmanFord'。
--
-- 届かない頂点は 'Nothing'、負の閉路があれば全体が 'Nothing'。
-- @-1@ が本当の距離になりうるので、ここだけ表し方が違う。
negativeWeights :: IO ()
negativeWeights = do
  g <- readDirected
  case bellmanFord g 0 of
    Nothing -> putStrLn "負の閉路があります"
    Just dist -> print (V.toList dist)

-- | 全頂点間の距離: 'floydWarshall'。
--
-- 結果はグリッドなので @elemAt (u, v)@ で引く。O(n^3)。
allPairs :: IO ()
allPairs = do
  g <- readDirected
  case floydWarshall g of
    Nothing -> putStrLn "負の閉路があります"
    Just d -> do
      print (elemAt (0, 1) d)
      print (fromMaybe (-1) (elemAt (0, 1) d))

-- | 最小全域木: 'minimumSpanningTree' (Kruskal)。
--
-- @(重みの合計, 使った辺)@ を返す。連結でなければ森になるので、辺の本数で
-- 連結かどうかが分かる。
mst :: IO ()
mst = do
  g <- readDirected
  let (total, used) = minimumSpanningTree g
  print total
  print (length used == numVertices g - 1) -- 連結か
  print used

-- | 二部グラフか: 'isBipartite' と 'bipartiteColoring'。
--
-- 塗り分けが要るなら 'bipartiteColoring' (塗れなければ 'Nothing')。
bipartite :: IO ()
bipartite = do
  g <- readUndirected
  print (isBipartite g)
  case bipartiteColoring g of
    Nothing -> putStrLn "No"
    Just colors -> print (U.toList colors)

-- | トポロジカル順: 'topologicalOrder' (閉路があれば 'Nothing')。
--
-- 並び順に DP すれば、DAG 上の最長路などがそのまま書ける。
topological :: IO ()
topological = do
  g <- readDirected
  case topologicalOrder g of
    Nothing -> putStrLn "閉路があります"
    Just order -> print (map (+ 1) (U.toList order))

-- | 連結成分の番号: 'componentIds'。
--
-- @(成分の数, 頂点ごとの成分番号)@ を返す。部分グラフは作らないので軽い。
-- 「同じ成分か」「成分がいくつか」だけならこれで足りる。
-- 有向グラフに使うと、向きを無視した成分 (弱連結成分) になる。
componentNumbers :: IO ()
componentNumbers = do
  g <- readUndirected
  let (k, cid) = componentIds g
  print k -- 成分の数
  print (cid U.! 0 == cid U.! 1) -- 頂点 0 と 1 が同じ成分か
  d <- readDirected
  print (fst (componentIds d)) -- 弱連結成分の数

-- | 連結成分ごとの部分グラフ: 'splitComponents'。
--
-- 成分ごとの @(部分グラフ, 元の頂点番号)@ と、頂点ごとの
-- @(成分番号, 成分の中での番号)@ を返す。成分は小さい頂点を含むものから。
components :: IO ()
components = do
  g <- readUndirected
  let (comps, loc) = splitComponents g
  print (V.length comps) -- 成分の数
  V.forM_ comps $ \(sub, vertices) ->
    print (numVertices sub, U.toList (U.map (+ 1) vertices))
  print (loc U.! 0) -- 頂点 0 の (成分番号, 成分内の番号)

-- | 強連結成分: 'strongComponentIds'。
--
-- 成分はトポロジカル順に並ぶ (辺 @u -> v@ なら @u@ の成分番号 <= @v@ の成分番号)。
-- 部分グラフも要るなら 'splitStrongComponents'。
stronglyConnected :: IO ()
stronglyConnected = do
  g <- readDirected
  let (k, scc) = strongComponentIds g
  print k
  print (scc U.! 0 == scc U.! 1) -- 同じ強連結成分か

-- | 成分を 1 頂点に縮める: 'condense'。
--
-- 成分番号を渡すと、成分をまたぐ辺だけを残したグラフになる。強連結成分なら
-- DAG なので、'topologicalOrder' の順に DP できる (縮めた頂点の番号は成分番号)。
-- ここでは各成分の頂点数を重みにして、通る頂点数が最大の道を求める。
condensed :: IO ()
condensed = do
  g <- readDirected
  let ids@(k, scc) = strongComponentIds g
      dag = condense ids g
      size = U.accumulate (+) (U.replicate k 0) (U.map (\c -> (c, 1 :: Int)) scc)
      -- 成分の番号がトポロジカル順なので、後ろから DP すればよい。
      best = V.constructrN k $ \done ->
        let c = k - 1 - V.length done
            next = [V.unsafeIndex done (k - 1 - d) | d <- U.toList (adjacentVertices dag c)]
         in size U.! c + maximum (0 : next)
  print (numVertices dag)
  print (V.maximum (V.cons 0 best))

-- | 多重辺を除く: 'simplifyGraph'。
--
-- 'condense' は成分をまたぐ辺を全部残すので、縮めた後の次数を数えるときは
-- 先に単純グラフにする。同じ向きの辺は重みが最小の 1 本だけ残り、自己ループも消える。
condensedDegrees :: IO ()
condensedDegrees = do
  g <- readDirected
  let ids = strongComponentIds g
      dag = simplifyGraph (condense ids g)
  print [outDegree dag c | c <- [0 .. numVertices dag - 1]]

-- | 橋と関節点: 'bridgeEdges' / 'articulationPoints'。
--
-- どちらも昇順、O(n + m)。橋は @(u, v)@ で @u < v@。無向グラフ用 (有向グラフは 'error')。
bridgesAndPoints :: IO ()
bridgesAndPoints = do
  g <- readUndirected
  print (bridgeEdges g)
  print (articulationPoints g)

-- | 橋を除いた連結成分 (二重辺連結成分): 'bridgeComponentIds'。
--
-- 同じ成分の 2 頂点は、どの 1 本の辺を切っても繋がったままでいられる。
-- 'condense' すると、橋を辺とする木 (非連結なら森) になる。
twoEdgeConnected :: IO ()
twoEdgeConnected = do
  g <- readUndirected
  let ids@(k, cid) = bridgeComponentIds g
      tree = condense ids g
  print k
  print (cid U.! 0)
  print (numVertices tree, length (graphEdges tree) `div` 2) -- 頂点数と、橋の本数

-- | 二重頂点連結成分: 'splitBiconnectedComponents'。
--
-- 関節点は複数の成分に入るので、2 つ目の返り値は「元の頂点 → 入っている
-- @(成分番号, 成分内の番号)@ のリスト」。
twoVertexConnected :: IO ()
twoVertexConnected = do
  g <- readUndirected
  let (comps, places) = splitBiconnectedComponents g
  print (V.length comps)
  print (places V.! 0)

-- | ブロックカット木: 'blockCutTree'。
--
-- 頂点 @0 .. n - 1@ は元の頂点、@n + b@ は @b@ 番目の二重頂点連結成分。
-- 元のグラフで u から v へのどの道も通る頂点は、この木の u - v の道にある元の頂点。
-- ここでは頂点 0 から各頂点へ、必ず通る頂点 (両端を含む) の数を出す。
blockCut :: IO ()
blockCut = do
  g <- readUndirected
  let n = numVertices g
      t = blockCutTree g
      -- 木の上の道は、元の頂点と成分の頂点が交互に並ぶ。
      d = bfsDist t [0]
  print (numVertices t - n) -- 成分の数
  print [if d U.! v < 0 then -1 else d U.! v `div` 2 + 1 | v <- [0 .. n - 1]]

-- | 木の親と深さ: 'treeParentDepth'。
--
-- 根からの親 (根は @-1@) と深さ (辺の本数)。O(n)。
treeShape :: IO ()
treeShape = do
  g <- readUndirected
  let (parent, depth) = treeParentDepth g 0
  print (U.toList parent)
  print (U.toList depth)

-- | 木の重み付きの距離: 'treeDist'。
--
-- 木なので 'dijkstraDist' より速い O(n)。
treeDistances :: IO ()
treeDistances = do
  g <- readDirected
  print (U.toList (treeDist g 0))

-- | 木の直径: 'treeDiameter'。
--
-- @(長さ, 端点, 端点)@。重みは非負であること。
diameter :: IO ()
diameter = do
  g <- readDirected
  let (len, u, v) = treeDiameter g
  print (len, u + 1, v + 1)

-- | 条件を満たす辺だけの連結成分: 'componentIdsWith'。
--
-- 条件は @u v 重み@ を受け取る。「重みが K 以下の辺だけで繋がっているか」のような
-- 条件付きの連結性に使う。番号を 'splitByIds' に渡せば部分グラフも作れる。
conditionalComponents :: IO ()
conditionalComponents = do
  g <- readWeightedUndirected
  [k] <- ints
  let ids@(c, cid) = componentIdsWith (\_ _ w -> w <= k) g
      (comps, _) = splitByIds ids g
  print c
  print (cid U.! 0 == cid U.! 1) -- 重み k 以下の辺だけで 0 から 1 へ行けるか
  print (V.length comps)

-- | 重み付きの無向グラフを読む。幅 3 で @u v w@。
readWeightedUndirected :: IO AtcGraph
readWeightedUndirected = do
  [_, m] <- ints
  es <- getIntGrid 3 m :: IO (Grid U.Vector Int)
  pure (undirectedGraph (fromOneBased es))

-- | 入力のグリッドを辺のリストに直す: 'edgesOfGrid' と 'vertexCountOf'。
--
-- 'undirectedGraph' / 'directedGraph' はこの 2 つを使っている。頂点数を
-- 自分で決めたいが辺の読み方は任せたい、というときに直に呼ぶ。
-- 第 1 引数はエラーに出す名前。
edgeList :: IO ()
edgeList = do
  [n, m] <- ints
  es <- getIntGrid 2 m :: IO (Grid U.Vector Int)
  let arcs' = edgesOfGrid "edgeList" (fromOneBased es)
  print (U.toList arcs')
  print (vertexCountOf arcs') -- 辺に出てくる最大の番号 + 1
  print (numVertices (graphFromList n (U.toList arcs')))

-- | DFS 木を自分で見る: 'dfsLowlink' と 'isBridgeArc'。
--
-- 'bridgeEdges' / 'articulationPoints' / 'bridgeComponentIds' はこの
-- 'Lowlink' を使っている。独自の条件で橋を数えたいときに直に呼ぶ。
-- 中身はフィールド 'llOrder' (訪問順) / 'llLow' / 'llParent' (DFS 木の親) などで取り出す。
lowlinkByHand :: IO ()
lowlinkByHand = do
  g <- readWeightedUndirected
  let link = dfsLowlink g
      -- 重みが 10 以上の橋だけ。条件を付けないなら 'bridgeEdges' と同じ結果。
      heavy = [(u, v) | (u, v, w) <- graphEdges g, u < v, w >= 10, isBridgeArc link u v]
  print heavy
  print (bridgeEdges g)
  print (U.toList (llParent link)) -- DFS 木の親

-- | 'Lowlink' を受け取る関数を書く。
--
-- 型を書いておけば、1 回の DFS の結果を何度も使い回せる。
countBridgeArcs :: AtcGraph -> Lowlink -> Int
countBridgeArcs g link =
  length [() | (u, v, _) <- graphEdges g, u < v, isBridgeArc link u v]

-- | 既存のグラフに足す: 'addGraphVertices' と 'addGraphEdges'。
--
-- 超頂点 @n@ を足して全ての始点とつなぐ。無向なら辺は片方の向きだけ渡す。
-- 元のグラフは変わらない。O(n + m) かかるので、足す辺はまとめて渡す。
superSource :: IO ()
superSource = do
  g <- readUndirected
  starts <- map (subtract 1) <$> ints
  let n = numVertices g
      g' = addGraphEdges (addGraphVertices g 1) [(n, s, 1) | s <- starts]
  print (U.toList (bfsDist g' [n]))

-- | 辺が増えていくグラフ: 'MGraph'。
--
-- 関数は 'AtcGraph' と同じで、返り値が @IO@ に入る。辺を足すのは 1 本 O(1)。
-- 'bfsDist' のようなアルゴリズムは呼ぶたびに CSR へ写す。
growing :: IO ()
growing = do
  [n, q] <- ints
  g <- newMGraph Undirected n
  mapM_ (const (query g)) [1 .. q]
  where
    query g = do
      [t, u, v] <- ints
      if t == 1
        then addGraphEdges g [(u - 1, v - 1, 1)]
        else do
          d <- bfsDist g [u - 1]
          print (d U.! (v - 1))

-- | ST の中で作って不変にする: 'createGraph'。
buildInST :: Int -> [(Int, Int)] -> AtcGraph
buildInST n es = createGraph $ do
  g <- newMGraph Directed n
  addGraphEdges g [(u, v, 1) | (u, v) <- es]
  pure g
