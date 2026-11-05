{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | 隣接リスト (CSR) のグラフと、その上の基本的なアルゴリズム。
--
-- 頂点は 0 始まりの @0 .. n - 1@。辺はすべて重み付き (@Int@) で、
-- 重みのない辺は重み 1 として持つ。無向グラフは両向きの有向辺として持つ。
--
-- == 作る
--
-- 入力の @u v@ (重み付きなら @u v w@) が M 行並んだものを 'getIntGridU' で読み、
-- 頂点番号の始まりを 'fromOneBased' / 'fromZeroBased' で示して渡す。
--
-- > [n, m] <- getInts
-- > es <- getIntGridU 2 m                           -- 重み付きなら getIntGridU 3 m
-- > let g = undirectedGraph (fromOneBased es)       -- 有向なら directedGraph。0 始まりなら fromZeroBased
--
-- 頂点数は辺に出てくる最大の頂点番号 (0 始まりに直した後) + 1 になる。番号の大きい頂点が
-- 孤立しうる (辺が 1 本もない頂点がある) ときは、頂点数を渡せる 'graphFromList' (有向) や
-- 'undirectedGraphFromList' (無向) を使う。自分で組み立てた辺もこれらに渡す。
--
-- グラフは有向か無向かを覚えている ('graphDirection')。"Atc.Graph.Cycle" はこれを見て動く。
--
-- ほかのグラフのモジュール:
--
-- * "Atc.Graph.Tree": LCA (2 点の距離・祖先) と全方位木 DP。
-- * "Atc.Graph.Flow": 最大流・最小カット・最小費用流・二部マッチング。
-- * "Atc.Graph.Cycle": 単純閉路。"Atc.Graph.Functional": Functional Graph。
-- * 2-SAT はこのモジュールの 'solveTwoSat' (強連結成分分解で解く)。
--
-- == 結果の読み方
--
-- 距離は届かない頂点を @-1@ にする ('bfsDist' / 'dijkstraDist')。
-- 負の重みを扱う 'bellmanFord' / 'floydWarshall' は @-1@ が本当の距離になりうるので、
-- 届かない頂点を 'Nothing' にする。負の閉路があれば全体が 'Nothing'。
--
-- 結果の頂点番号も 0 始まり。出力するときは 1 を足す。
--
-- > let (dist, prev) = dijkstraDistPrev g [0]
-- > dist U.! (n - 1)                 -- 届かなければ -1
-- > map (+ 1) (pathTo prev (n - 1))  -- 0 から n - 1 への経路 (届くときだけ)
--
-- > let (k, cid) = componentIds g          -- 連結成分の数と、頂点ごとの成分番号
-- > let (comps, loc) = splitComponents g   -- 連結成分ごとの部分グラフと番号の対応
--
-- == 不変版と可変版で同じ関数
--
-- 下の関数は不変の 'AtcGraph' にも可変の 'MGraph' にも使える。返り値の形が
-- グラフの型で決まる (@a@ か @m a@)。
--
-- > 関数                     AtcGraph       MGraph m
-- > numVertices g            Int            m Int          O(1)
-- > outDegree g v            Int            m Int          O(1)
-- > adjacent g v             Vector         m Vector       O(次数)    (adjacentVertices / adjacentWeights も同じ)
-- > addGraphEdges g es       AtcGraph       m ()           足す辺の数
-- > addGraphVertices g k     AtcGraph       m ()           O(k)
-- > reverseGraph g           AtcGraph       m (MGraph m)   O(n + m)   (condense / blockCutTree / simplifyGraph も同じ)
-- > bfsDist g s など         a              m a            変換 O(n + m) + 本体
--
-- 'graphDirection' は両方とも純粋な関数。残りの関数 (探索・分解・木など) も共通で、
-- 可変版は呼ぶたびに CSR へ写してから実行する。辺を変えずに何度も呼ぶなら、
-- 'freezeGraph' で 1 回写して 'AtcGraph' に対して呼ぶ。
--
-- > g <- newMGraph Undirected n
-- > addGraphEdges g [(0, 1, 1), (1, 2, 1)]    -- 書き換える
-- > d <- bfsDist g [0]                        -- 同じ関数名
-- >
-- > let g' = addGraphEdges (undirectedGraph (fromOneBased es)) [(0, 1, 1)]   -- 不変版は新しいグラフ
--
-- 'MGraph' の隣接は足した順に並ぶ。'undirectedGraph' は全辺の順向きのあとに逆向きを
-- 並べるので、同じ辺でも隣接の順は違うことがある。
--
-- 'newMGraph' / 'thawGraph' / 'freezeGraph' / 'createGraph' は "Atc.Grid" の同名の関数と同じ役割。
-- "Atc.BFS" の本体の外で作った 'MGraph' は本体から触れないので、'AtcGraph' にして渡す。
--
-- == 仕組みと、関数の足し方
--
-- アルゴリズムの本体は名前に @C@ を付けた 'AtcGraph' の関数に 1 回だけ書き、共通の関数は
-- 'primGraph' (値を返す) か 'primGraphNew' (グラフを返す) に渡す薄い包みにする。
--
-- > foo :: (GraphKind g) => g -> GraphRet g Int
-- > foo g = primGraph g fooC
--
-- == 名前
--
-- @atc bundle@ は解答と 1 ファイルにまとめるので、解答側で自前定義しがちな名前
-- (@bfs@, @dijkstra@, @bridges@, @lowlink@ …) や "Data.Graph" の名前 (@graphFromEdges@,
-- @components@, @scc@, @topSort@ …) は避けている。
module Atc.Graph where

import Atc.Grid (Grid (..), ZeroBased (..))
import Atc.UnionFind (newUF, rootUF, uniteUF)
import Control.Monad (foldM, forM_, when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST, runST)
import qualified Data.Graph as DG
import Data.Primitive.MutVar (MutVar, newMutVar, readMutVar, writeMutVar)
import Data.Ord (comparing)
import Data.STRef (newSTRef, readSTRef, writeSTRef)
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 型

-- | 作るときに決まるグラフの向き。
data Direction = Directed | Undirected deriving (Eq, Show)

-- | 頂点数・各頂点の辺の開始位置 (長さ n + 1)・行き先・重み・向き。
-- 頂点 @v@ の辺は @[off ! v, off ! (v + 1))@ の範囲。
data AtcGraph = AtcGraph !Int !(U.Vector Int) !(U.Vector Int) !(U.Vector Int) !Direction

instance Show AtcGraph where
  show g = "AtcGraph {vertices = " ++ show (numVertices g) ++ ", edges = " ++ show (graphEdges g) ++ "}"

-- ---------------------------------------------------------------------
-- 作る

-- | @u v@ / @u v w@ の並びから無向グラフを作る。幅が 2 なら重み 1。
-- 頂点番号の始まりは 'fromOneBased' / 'fromZeroBased' で示す。
-- 幅が 2 でも 3 でもなければ 'error'。
--
-- 頂点数は辺に出てくる最大の頂点番号 (0 始まり) + 1。それより大きい番号の頂点は (辺がないので) 入らない。
undirectedGraph :: (G.Vector v Int) => ZeroBased (Grid v Int) -> AtcGraph
undirectedGraph g = buildCSR Undirected (vertexCountOf es) (bothWays es)
  where
    es = edgesOfGrid "undirectedGraph" g

-- | @u v@ / @u v w@ の並びから、@u@ から @v@ への有向グラフを作る。
-- 頂点番号の始まりと頂点数は 'undirectedGraph' と同じ。
directedGraph :: (G.Vector v Int) => ZeroBased (Grid v Int) -> AtcGraph
directedGraph g = buildCSR Directed (vertexCountOf es) es
  where
    es = edgesOfGrid "directedGraph" g

-- | 0 始まりの @(u, v, 重み)@ のリストから有向グラフを作る。
-- 無向にしたいときは 'undirectedGraphFromList'。
graphFromList :: Int -> [(Int, Int, Int)] -> AtcGraph
graphFromList n es = buildCSR Directed n (U.fromList es)

-- | 0 始まりの @(u, v, 重み)@ のリストから無向グラフを作る。各辺は片方の向きだけ渡す。
undirectedGraphFromList :: Int -> [(Int, Int, Int)] -> AtcGraph
undirectedGraphFromList n es = buildCSR Undirected n (bothWays (U.fromList es))

bothWays :: U.Vector (Int, Int, Int) -> U.Vector (Int, Int, Int)
bothWays es = es U.++ U.map (\(u, v, c) -> (v, u, c)) es

-- | @u v@ / @u v w@ の並びを、0 始まりの @(u, v, 重み)@ の辺に直す。幅が 2 なら重み 1。
-- 第 1 引数はエラーに出す名前。
edgesOfGrid :: (G.Vector v Int) => String -> ZeroBased (Grid v Int) -> U.Vector (Int, Int, Int)
edgesOfGrid name (ZeroBased (Grid w h d))
  | w == 2 = U.generate h (\i -> (at (2 * i), at (2 * i + 1), 1))
  | w == 3 = U.generate h (\i -> (at (3 * i), at (3 * i + 1), at (3 * i + 2)))
  | otherwise = error ("Atc.Graph." ++ name ++ ": 幅は 2 (u v) か 3 (u v w)")
  where
    at = G.unsafeIndex d

-- | 0 始まりの辺に出てくる最大の頂点番号 + 1。辺がなければ 0。
vertexCountOf :: U.Vector (Int, Int, Int) -> Int
vertexCountOf = U.foldl' (\k (u, v, _) -> max k (max u v + 1)) 0

-- | 次数を数えて累積和を取り、そこへ書き込む。O(n + m)。同じ頂点の辺は入力順に並ぶ。
buildCSR :: Direction -> Int -> U.Vector (Int, Int, Int) -> AtcGraph
buildCSR dir n es
  | U.any (\(u, v, _) -> u < 0 || n <= u || v < 0 || n <= v) es =
      error "Atc.Graph: 頂点番号が範囲外です"
  | otherwise = AtcGraph n off tgt wt dir
  where
    m = U.length es
    off = U.scanl' (+) 0 (U.accumulate (+) (U.replicate n 0) (U.map (\(u, _, _) -> (u, 1)) es))
    (tgt, wt) = runST $ do
      pos <- U.thaw off
      t <- UM.unsafeNew m
      w <- UM.unsafeNew m
      U.forM_ es $ \(u, v, c) -> do
        p <- UM.unsafeRead pos u
        UM.unsafeWrite pos u (p + 1)
        UM.unsafeWrite t p v
        UM.unsafeWrite w p c
      (,) <$> U.unsafeFreeze t <*> U.unsafeFreeze w

-- ---------------------------------------------------------------------
-- 不変版と可変版で共通の操作

-- | 'AtcGraph' と 'MGraph' で共通の操作。返り値の形はグラフの型で決まる。
class GraphKind g where
  -- | 不変版は @a@、可変版は @m a@。
  type GraphRet g a

  -- | 不変版は新しいグラフ、可変版は @m ()@。
  type GraphUpdated g

  -- | CSR の上の処理を実行する。可変版は 'freezeGraph' してから実行する。
  primGraph :: g -> (AtcGraph -> a) -> GraphRet g a

  -- | グラフを返す処理を実行する。可変版は新しい 'MGraph' を作り、元は変えない。
  primGraphNew :: g -> (AtcGraph -> AtcGraph) -> GraphRet g g

  -- | 有向か無向か。
  graphDirection :: g -> Direction

  numVertices :: g -> GraphRet g Int

  -- | 出ていく辺の数。無向グラフなら次数。
  outDegree :: g -> Int -> GraphRet g Int

  -- | @v@ から出る辺の @(行き先, 重み)@。
  adjacent :: g -> Int -> GraphRet g (U.Vector (Int, Int))

  -- | @v@ から出る辺の行き先。
  adjacentVertices :: g -> Int -> GraphRet g (U.Vector Int)

  -- | @v@ から出る辺の重み。'adjacentVertices' と同じ順。
  adjacentWeights :: g -> Int -> GraphRet g (U.Vector Int)

  -- | 0 始まりの @(u, v, 重み)@ の辺を足す。無向グラフは片方の向きだけ渡す。
  -- 範囲外の頂点は 'error'。不変版は O(n + m + 足す辺の数)、可変版は O(足す辺の数)。
  addGraphEdges :: g -> [(Int, Int, Int)] -> GraphUpdated g

  -- | 頂点を @k@ 個増やす。新しい番号は @n, n + 1 ..@。
  -- 不変版は O(n + k)、可変版は O(k)。
  addGraphVertices :: g -> Int -> GraphUpdated g

instance GraphKind AtcGraph where
  type GraphRet AtcGraph a = a
  type GraphUpdated AtcGraph = AtcGraph
  primGraph g f = f g
  {-# INLINE primGraph #-}
  primGraphNew g f = f g
  {-# INLINE primGraphNew #-}
  graphDirection (AtcGraph _ _ _ _ dir) = dir
  {-# INLINE graphDirection #-}
  numVertices (AtcGraph n _ _ _ _) = n
  {-# INLINE numVertices #-}
  outDegree (AtcGraph _ off _ _ _) v = off U.! (v + 1) - off U.! v
  {-# INLINE outDegree #-}
  adjacent g v = U.zip (adjacentVertices g v) (adjacentWeights g v)
  {-# INLINE adjacent #-}
  adjacentVertices (AtcGraph _ off t _ _) v = U.slice (off U.! v) (off U.! (v + 1) - off U.! v) t
  {-# INLINE adjacentVertices #-}
  adjacentWeights (AtcGraph _ off _ w _) v = U.slice (off U.! v) (off U.! (v + 1) - off U.! v) w
  {-# INLINE adjacentWeights #-}
  addGraphEdges g@(AtcGraph n _ tgt wt dir) es = buildCSR dir n (U.zip3 (grArcSources g) tgt wt U.++ new)
    where
      new = (if dir == Undirected then bothWays else id) (U.fromList es)
  addGraphVertices (AtcGraph n off tgt wt dir) k
    | k < 0 = error "Atc.Graph.addGraphVertices: 負の個数"
    | otherwise = AtcGraph (n + k) (off U.++ U.replicate k (U.last off)) tgt wt dir

instance (PrimMonad m) => GraphKind (MGraph m) where
  type GraphRet (MGraph m) a = m a
  type GraphUpdated (MGraph m) = m ()
  primGraph g f = f <$> freezeGraph g
  {-# INLINE primGraph #-}
  primGraphNew g f = freezeGraph g >>= thawGraph . f
  graphDirection (MGraph dir _) = dir
  {-# INLINE graphDirection #-}
  numVertices (MGraph _ r) = do
    GraphBody reg _ _ _ _ _ _ <- readMutVar r
    UM.unsafeRead reg 0
  {-# INLINE numVertices #-}
  outDegree g@(MGraph _ r) v = do
    checkVertex g v
    GraphBody _ _ _ deg _ _ _ <- readMutVar r
    UM.unsafeRead deg v
  {-# INLINE outDegree #-}
  adjacent g v = U.zip <$> adjacentVertices g v <*> adjacentWeights g v
  adjacentVertices g v = arcFieldM (\(GraphBody _ _ _ _ t _ _) -> t) g v
  adjacentWeights g v = arcFieldM (\(GraphBody _ _ _ _ _ w _) -> w) g v
  addGraphEdges g es = forM_ es $ \(u, v, c) -> do
    addArcM g u v c
    when (graphDirection g == Undirected) $ addArcM g v u c
  addGraphVertices (MGraph _ r) k
    | k < 0 = error "Atc.Graph.addGraphVertices: 負の個数"
    | otherwise = do
        GraphBody reg hd tl deg tgt wt nxt <- readMutVar r
        n <- UM.unsafeRead reg 0
        let cap = UM.length hd
            extra = max 0 (max (n + k) (2 * cap) - cap)
        when (n + k > cap) $ do
          hd' <- UM.grow hd extra
          tl' <- UM.grow tl extra
          deg' <- UM.grow deg extra
          UM.set (UM.slice cap extra hd') (-1)
          UM.set (UM.slice cap extra tl') (-1)
          UM.set (UM.slice cap extra deg') 0
          writeMutVar r (GraphBody reg hd' tl' deg' tgt wt nxt)
        UM.unsafeWrite reg 0 (n + k)

-- ---------------------------------------------------------------------
-- 可変版

-- | 辺と頂点を足せるグラフ。@m@ は使うモナド (@IO@ か @ST s@)。
data MGraph m = MGraph !Direction !(MutVar (PrimState m) (GraphBody (PrimState m)))

-- 頂点数と辺数・頂点ごとの先頭の辺・末尾の辺・次数、辺ごとの行き先・重み・次の辺。
-- 辺は足した順につながる。領域が足りなくなると 2 倍に広げるので、全体を MutVar に入れる。
data GraphBody s
  = GraphBody
      !(UM.MVector s Int)
      !(UM.MVector s Int)
      !(UM.MVector s Int)
      !(UM.MVector s Int)
      !(UM.MVector s Int)
      !(UM.MVector s Int)
      !(UM.MVector s Int)

-- | 頂点数 @n@ で辺のない可変グラフ。
newMGraph :: (PrimMonad m) => Direction -> Int -> m (MGraph m)
newMGraph dir n = thawGraph (buildCSR dir n U.empty)

-- | 'AtcGraph' から可変グラフを作る。O(n + m)。
thawGraph :: (PrimMonad m) => AtcGraph -> m (MGraph m)
thawGraph (AtcGraph n off tgt wt dir) = do
  reg <- U.thaw (U.fromList [n, a])
  hd <- U.thaw (U.generate n (\v -> if has v then off U.! v else -1))
  tl <- U.thaw (U.generate n (\v -> if has v then off U.! (v + 1) - 1 else -1))
  deg <- U.thaw (U.generate n (\v -> off U.! (v + 1) - off U.! v))
  t <- U.thaw tgt
  w <- U.thaw wt
  nx <- U.thaw (U.update (U.enumFromN 1 a) (U.map (\v -> (off U.! (v + 1) - 1, -1)) (U.filter has (U.enumFromN 0 n))))
  MGraph dir <$> newMutVar (GraphBody reg hd tl deg t w nx)
  where
    a = U.length tgt
    has v = off U.! v < off U.! (v + 1)

-- | 今の中身を 'AtcGraph' に写す。辺は足した順。元とは独立。O(n + m)。
freezeGraph :: (PrimMonad m) => MGraph m -> m AtcGraph
freezeGraph (MGraph dir r) = do
  GraphBody reg hd _ deg tgt wt nxt <- readMutVar r
  n <- UM.unsafeRead reg 0
  a <- UM.unsafeRead reg 1
  degs <- U.freeze (UM.take n deg)
  let off = U.scanl' (+) 0 degs
  t <- UM.unsafeNew a
  w <- UM.unsafeNew a
  rep n $ \u -> do
    let go !p !e = when (e >= 0) $ do
          UM.unsafeRead tgt e >>= UM.unsafeWrite t p
          UM.unsafeRead wt e >>= UM.unsafeWrite w p
          UM.unsafeRead nxt e >>= go (p + 1)
    UM.unsafeRead hd u >>= go (U.unsafeIndex off u)
  t' <- U.unsafeFreeze t
  w' <- U.unsafeFreeze w
  pure (AtcGraph n off t' w' dir)

-- | ST の中で作って 'AtcGraph' として取り出す。
createGraph :: (forall s. ST s (MGraph (ST s))) -> AtcGraph
createGraph m = runST (m >>= freezeGraph)

checkVertex :: (PrimMonad m) => MGraph m -> Int -> m ()
checkVertex (MGraph _ r) v = do
  GraphBody reg _ _ _ _ _ _ <- readMutVar r
  n <- UM.unsafeRead reg 0
  when (v < 0 || n <= v) $ error "Atc.Graph: 頂点番号が範囲外です"

-- 有向辺を 1 本、u の辺の末尾につなぐ。
addArcM :: (PrimMonad m) => MGraph m -> Int -> Int -> Int -> m ()
addArcM g@(MGraph _ r) u v c = do
  checkVertex g u
  checkVertex g v
  body0@(GraphBody reg _ _ _ tgt0 _ _) <- readMutVar r
  a <- UM.unsafeRead reg 1
  GraphBody _ hd tl deg tgt wt nxt <- if a < UM.length tgt0 then pure body0 else growArcsM r body0
  UM.unsafeWrite tgt a v
  UM.unsafeWrite wt a c
  UM.unsafeWrite nxt a (-1)
  t <- UM.unsafeRead tl u
  if t < 0 then UM.unsafeWrite hd u a else UM.unsafeWrite nxt t a
  UM.unsafeWrite tl u a
  UM.unsafeModify deg (+ 1) u
  UM.unsafeWrite reg 1 (a + 1)

growArcsM :: (PrimMonad m) => MutVar (PrimState m) (GraphBody (PrimState m)) -> GraphBody (PrimState m) -> m (GraphBody (PrimState m))
growArcsM r (GraphBody reg hd tl deg tgt wt nxt) = do
  let extra = max 16 (UM.length tgt)
  body <- GraphBody reg hd tl deg <$> UM.grow tgt extra <*> UM.grow wt extra <*> UM.grow nxt extra
  writeMutVar r body
  pure body

-- v の辺について、辺ごとの配列の値を足した順に並べる。
arcFieldM :: (PrimMonad m) => (GraphBody (PrimState m) -> UM.MVector (PrimState m) Int) -> MGraph m -> Int -> m (U.Vector Int)
arcFieldM field g@(MGraph _ r) v = do
  checkVertex g v
  body@(GraphBody _ hd _ deg _ _ nxt) <- readMutVar r
  d <- UM.unsafeRead deg v
  out <- UM.unsafeNew d
  let xs = field body
      go !i !e = when (e >= 0) $ do
        UM.unsafeRead xs e >>= UM.unsafeWrite out i
        UM.unsafeRead nxt e >>= go (i + 1)
  UM.unsafeRead hd v >>= go (0 :: Int)
  U.unsafeFreeze out

-- ---------------------------------------------------------------------
-- 基本

-- | 全ての有向辺 @(u, v, 重み)@。無向グラフは両向きが入る。
{-# INLINE graphEdges #-}
graphEdges :: (GraphKind g) => g -> GraphRet g ([(Int, Int, Int)])
graphEdges g = primGraph g graphEdgesC

graphEdgesC :: AtcGraph -> [(Int, Int, Int)]
graphEdgesC g = [(u, v, c) | u <- [0 .. numVertices g - 1], (v, c) <- U.toList (arcs g u)]

-- | 辺の向きを全て逆にする。
{-# INLINE reverseGraph #-}
reverseGraph :: (GraphKind g) => g -> GraphRet g g
reverseGraph g = primGraphNew g reverseGraphC

reverseGraphC :: AtcGraph -> AtcGraph
reverseGraphC g = buildCSR (graphDirection g) (numVertices g) (U.fromList [(v, u, c) | (u, v, c) <- graphEdges g])

-- | "Data.Graph" の 'DG.Graph' に直す (重みは捨てる)。O(n + m)。
{-# INLINE toDataGraph #-}
toDataGraph :: (GraphKind g) => g -> GraphRet g (DG.Graph)
toDataGraph g = primGraph g toDataGraphC

toDataGraphC :: AtcGraph -> DG.Graph
toDataGraphC g = DG.buildG (0, numVertices g - 1) [(u, v) | (u, v, _) <- graphEdges g]

-- 範囲を見ない版 (中で使う)。
targetsOf :: AtcGraph -> Int -> U.Vector Int
targetsOf (AtcGraph _ off t _ _) v =
  let i = U.unsafeIndex off v in U.unsafeSlice i (U.unsafeIndex off (v + 1) - i) t
{-# INLINE targetsOf #-}

arcs :: AtcGraph -> Int -> U.Vector (Int, Int)
arcs (AtcGraph _ off t w _) v =
  let i = U.unsafeIndex off v
      k = U.unsafeIndex off (v + 1) - i
   in U.zip (U.unsafeSlice i k t) (U.unsafeSlice i k w)
{-# INLINE arcs #-}

-- ---------------------------------------------------------------------
-- 最短路

-- | 重みを見ない (辺 1 本を 1 とする) 距離。始点は複数でもよい。届かない頂点は @-1@。O(n + m)。
{-# INLINE bfsDist #-}
bfsDist :: (GraphKind g) => g -> [Int] -> GraphRet g (U.Vector Int)
bfsDist g x = primGraph g (\c -> bfsDistC c x)

bfsDistC :: AtcGraph -> [Int] -> U.Vector Int
bfsDistC g = fst . bfsDistPrevC g

-- | 'bfsDist' と、各頂点の直前の頂点 (始点と届かない頂点は @-1@)。経路は 'pathTo' で。
{-# INLINE bfsDistPrev #-}
bfsDistPrev :: (GraphKind g) => g -> [Int] -> GraphRet g (U.Vector Int, U.Vector Int)
bfsDistPrev g x = primGraph g (\c -> bfsDistPrevC c x)

{-# INLINE bfsDistPrevC #-}
bfsDistPrevC :: AtcGraph -> [Int] -> (U.Vector Int, U.Vector Int)
bfsDistPrevC g = bfsCore (numVertices g) (\v f z -> U.foldM' f z (targetsOf g v))

-- | 頂点数と隣接関数から BFS する。グラフを作らずに済ませたいとき用。
--
-- > -- 迷路: '#' 以外を 4 方向に進む
-- > let nbr i = [posToIndex w q | (q, x) <- neighbors4 (indexToPos w i) maze, x /= '#']
-- > bfsDistBy (w * h) nbr [0]
bfsDistBy :: Int -> (Int -> [Int]) -> [Int] -> U.Vector Int
bfsDistBy n nbr = fst . bfsCore n (\v f z -> foldM f z (nbr v))

-- 隣接は「v の行き先で畳む」関数として受け取る。
bfsCore ::
  Int -> (forall s b. Int -> (b -> Int -> ST s b) -> b -> ST s b) -> [Int] -> (U.Vector Int, U.Vector Int)
bfsCore n foldNbr srcs = runST $ do
  dist <- UM.replicate n (-1)
  prev <- UM.replicate n (-1)
  que <- UM.unsafeNew n
  let visit !v !d !p !tl = do
        x <- UM.read dist v
        if x /= -1
          then pure tl
          else do
            UM.unsafeWrite dist v d
            UM.unsafeWrite prev v p
            UM.unsafeWrite que tl v
            pure (tl + 1)
      go !hd !tl
        | hd == tl = pure ()
        | otherwise = do
            v <- UM.unsafeRead que hd
            dv <- UM.unsafeRead dist v
            foldNbr v (\t u -> visit u (dv + 1) v t) tl >>= go (hd + 1)
  foldM (\t s -> visit s 0 (-1) t) 0 srcs >>= go 0
  (,) <$> U.unsafeFreeze dist <*> U.unsafeFreeze prev
{-# INLINE bfsCore #-}

-- | 重みが非負のときの距離。始点は複数でもよい。届かない頂点は @-1@。O(m log m)。
{-# INLINE dijkstraDist #-}
dijkstraDist :: (GraphKind g) => g -> [Int] -> GraphRet g (U.Vector Int)
dijkstraDist g x = primGraph g (\c -> dijkstraDistC c x)

dijkstraDistC :: AtcGraph -> [Int] -> U.Vector Int
dijkstraDistC g = fst . dijkstraDistPrev g

-- | 'dijkstraDist' と、各頂点の直前の頂点 (始点と届かない頂点は @-1@)。経路は 'pathTo' で。
{-# INLINE dijkstraDistPrev #-}
dijkstraDistPrev :: (GraphKind g) => g -> [Int] -> GraphRet g (U.Vector Int, U.Vector Int)
dijkstraDistPrev g x = primGraph g (\c -> dijkstraDistPrevC c x)

dijkstraDistPrevC :: AtcGraph -> [Int] -> (U.Vector Int, U.Vector Int)
dijkstraDistPrevC g@(AtcGraph n _ tgt _ _) srcs = runST $ do
  dist <- UM.replicate n (-1)
  prev <- UM.replicate n (-1)
  -- (距離, 頂点) の二分ヒープ。積むのは辺ごとに高々 1 回と始点なので、大きさは m + 始点数。
  -- 同じ頂点が古い距離で残っていてもよい。取り出したときに捨てる。
  heap <- UM.unsafeNew (U.length tgt + length srcs)
  let push !sz x = do
        let up i
              | i == 0 = UM.unsafeWrite heap 0 x
              | otherwise = do
                  let p = (i - 1) `div` 2
                  y <- UM.unsafeRead heap p
                  if fst y <= fst x then UM.unsafeWrite heap i x else UM.unsafeWrite heap i y >> up p
        up sz
        pure (sz + 1)
      -- 先頭を取り除き、末尾を根から沈める。
      pop !sz = do
        top <- UM.unsafeRead heap 0
        x <- UM.unsafeRead heap (sz - 1)
        let sz' = sz - 1
            down i = do
              let l = 2 * i + 1
              if l >= sz'
                then UM.unsafeWrite heap i x
                else do
                  yl <- UM.unsafeRead heap l
                  (c, y) <-
                    if l + 1 < sz'
                      then do
                        yr <- UM.unsafeRead heap (l + 1)
                        pure (if fst yr < fst yl then (l + 1, yr) else (l, yl))
                      else pure (l, yl)
                  if fst x <= fst y then UM.unsafeWrite heap i x else UM.unsafeWrite heap i y >> down c
        when (sz' > 0) (down 0)
        pure (top, sz')
      go !sz = when (sz > 0) $ do
        ((d, v), sz') <- pop sz
        dv <- UM.unsafeRead dist v
        if dv /= d then go sz' else U.foldM' (relax d v) sz' (arcs g v) >>= go
      relax d v !sz (u, c) = do
        du <- UM.unsafeRead dist u
        let nd = d + c
        if du /= -1 && du <= nd
          then pure sz
          else do
            UM.unsafeWrite dist u nd
            UM.unsafeWrite prev u v
            push sz (nd, u)
  foldM (\sz s -> UM.write dist s 0 >> push sz (0, s)) 0 srcs >>= go
  (,) <$> U.unsafeFreeze dist <*> U.unsafeFreeze prev

-- | 'bfsDistPrev' / 'dijkstraDistPrev' の直前の頂点から、始点から @t@ までの経路。
-- @t@ に届くときだけ使う (届かなければ @[t]@ になる)。
pathTo :: (G.Vector v Int) => v Int -> Int -> [Int]
pathTo prev = go []
  where
    go acc v
      | v == -1 = acc
      | otherwise = go (v : acc) (prev G.! v)

-- | 負の重みがあってもよい距離。届かない頂点は 'Nothing'。
-- @s@ から届く負の閉路があれば 'Nothing'。O(nm)。
{-# INLINE bellmanFord #-}
bellmanFord :: (GraphKind g) => g -> Int -> GraphRet g (Maybe (V.Vector (Maybe Int)))
bellmanFord g x = primGraph g (\c -> bellmanFordC c x)

bellmanFordC :: AtcGraph -> Int -> Maybe (V.Vector (Maybe Int))
bellmanFordC g s = runST $ do
  dist <- UM.replicate n inf
  UM.write dist s 0
  let relaxAll = foldM relaxFrom False [0 .. n - 1]
      relaxFrom ch u = do
        du <- UM.unsafeRead dist u
        if du == inf
          then pure ch
          else
            U.foldM'
              ( \ch' (v, c) -> do
                  dv <- UM.unsafeRead dist v
                  if du + c < dv then UM.unsafeWrite dist v (du + c) >> pure True else pure ch'
              )
              ch
              (arcs g u)
      -- 負の閉路がなければ n - 1 回までで更新が止まる。n 回目も更新されたら負の閉路。
      loop i
        | i == n = pure False
        | otherwise = do
            ch <- relaxAll
            if ch then loop (i + 1) else pure True
  ok <- loop (0 :: Int)
  if ok then Just . V.map fromInf . V.convert <$> U.unsafeFreeze dist else pure Nothing
  where
    n = numVertices g

-- | 全頂点間の距離。@elemAt (u, v) d@ が @u@ から @v@ への距離 (届かなければ 'Nothing')。
-- 負の重みがあってもよく、負の閉路があれば 'Nothing'。O(n^3)。
{-# INLINE floydWarshall #-}
floydWarshall :: (GraphKind g) => g -> GraphRet g (Maybe (Grid V.Vector (Maybe Int)))
floydWarshall g = primGraph g floydWarshallC

floydWarshallC :: AtcGraph -> Maybe (Grid V.Vector (Maybe Int))
floydWarshallC g = runST $ do
  d <- UM.replicate (n * n) inf
  rep n $ \i -> UM.unsafeWrite d (i * n + i) 0
  rep n $ \u -> U.forM_ (arcs g u) $ \(v, c) -> do
    x <- UM.unsafeRead d (u * n + v)
    when (c < x) $ UM.unsafeWrite d (u * n + v) c
  rep n $ \k -> rep n $ \i -> do
    dik <- UM.unsafeRead d (i * n + k)
    when (dik /= inf) $ rep n $ \j -> do
      dkj <- UM.unsafeRead d (k * n + j)
      when (dkj /= inf) $ do
        dij <- UM.unsafeRead d (i * n + j)
        when (dik + dkj < dij) $ UM.unsafeWrite d (i * n + j) (dik + dkj)
  res <- U.unsafeFreeze d
  pure $
    if U.any (\i -> U.unsafeIndex res (i * n + i) < 0) (U.enumFromN 0 n)
      then Nothing
      else Just (Grid n n (V.map fromInf (V.convert res)))
  where
    n = numVertices g

-- 'bellmanFord' / 'floydWarshall' の中で、届かないことを表す値。
inf :: Int
inf = maxBound

fromInf :: Int -> Maybe Int
fromInf x = if x == inf then Nothing else Just x

rep :: (Monad m) => Int -> (Int -> m ()) -> m ()
rep n f = go 0
  where
    go !i = when (i < n) $ f i >> go (i + 1)
{-# INLINE rep #-}

-- ---------------------------------------------------------------------
-- 最小全域木

-- | 最小全域木 (Kruskal)。@(重みの合計, 使った辺 (u, v, 重み))@。O(m log m)。
-- 辺は無向として扱う (有向グラフでも向きを無視する)。連結でなければ各成分の
-- 最小全域木を合わせたもの (最小全域森) になるので、連結か調べるには
-- 使った辺が @n - 1@ 本か見る。
{-# INLINE minimumSpanningTree #-}
minimumSpanningTree :: (GraphKind g) => g -> GraphRet g (Int, [(Int, Int, Int)])
minimumSpanningTree g = primGraph g minimumSpanningTreeC

minimumSpanningTreeC :: AtcGraph -> (Int, [(Int, Int, Int)])
minimumSpanningTreeC g = runST $ do
  es <- U.thaw (U.fromList [e | e@(u, v, _) <- graphEdges g, u /= v])
  Intro.sortBy (comparing (\(_, _, c) -> c)) es
  sorted <- U.unsafeFreeze es
  uf <- newUF (numVertices g)
  used <- U.filterM (\(u, v, _) -> uniteUF u v uf) sorted
  pure (U.sum (U.map (\(_, _, c) -> c) used), U.toList used)

-- ---------------------------------------------------------------------
-- 二部グラフ

-- | 無向グラフを 2 色 (0 / 1) に塗る。塗れなければ 'Nothing'。O(n + m)。
{-# INLINE bipartiteColoring #-}
bipartiteColoring :: (GraphKind g) => g -> GraphRet g (Maybe (U.Vector Int))
bipartiteColoring g = primGraph g bipartiteColoringC

bipartiteColoringC :: AtcGraph -> Maybe (U.Vector Int)
bipartiteColoringC g = runST $ do
  col <- UM.replicate n (-1)
  que <- UM.unsafeNew n
  let paint s = do
        UM.unsafeWrite col s 0
        UM.unsafeWrite que 0 s
        let go !hd !tl
              | hd == tl = pure True
              | otherwise = do
                  v <- UM.unsafeRead que hd
                  cv <- UM.unsafeRead col v
                  r <- U.foldM' (visit cv) (Just tl) (targetsOf g v)
                  maybe (pure False) (go (hd + 1)) r
        go 0 (1 :: Int)
      visit _ Nothing _ = pure Nothing
      visit cv (Just tl) u = do
        cu <- UM.unsafeRead col u
        case () of
          _
            | cu == -1 -> UM.unsafeWrite col u (1 - cv) >> UM.unsafeWrite que tl u >> pure (Just (tl + 1))
            | cu == cv -> pure Nothing
            | otherwise -> pure (Just tl)
      loop s
        | s == n = Just <$> U.unsafeFreeze col
        | otherwise = do
            c <- UM.unsafeRead col s
            if c /= -1
              then loop (s + 1)
              else do
                ok <- paint s
                if ok then loop (s + 1) else pure Nothing
  loop 0
  where
    n = numVertices g

-- | 2 色に塗れるか。
{-# INLINE isBipartite #-}
isBipartite :: (GraphKind g) => g -> GraphRet g Bool
isBipartite g = primGraph g isBipartiteC

isBipartiteC :: AtcGraph -> Bool
isBipartiteC = maybe False (const True) . bipartiteColoring

-- ---------------------------------------------------------------------
-- 有向グラフ

-- | トポロジカル順 (どの辺も前から後ろへ向かう並び)。閉路があれば 'Nothing'。O(n + m)。
{-# INLINE topologicalOrder #-}
topologicalOrder :: (GraphKind g) => g -> GraphRet g (Maybe (U.Vector Int))
topologicalOrder g = primGraph g topologicalOrderC

topologicalOrderC :: AtcGraph -> Maybe (U.Vector Int)
topologicalOrderC g@(AtcGraph n _ tgt _ _) = runST $ do
  indeg <- U.thaw (U.accumulate (+) (U.replicate n 0) (U.map (\v -> (v, 1 :: Int)) tgt))
  que <- UM.unsafeNew n
  let push !tl v = do
        d <- UM.unsafeRead indeg v
        if d == 0 then UM.unsafeWrite que tl v >> pure (tl + 1) else pure tl
      decr !tl u = do
        d <- UM.unsafeRead indeg u
        UM.unsafeWrite indeg u (d - 1)
        if d == 1 then UM.unsafeWrite que tl u >> pure (tl + 1) else pure tl
      go !hd !tl
        | hd == tl = pure tl
        | otherwise = do
            v <- UM.unsafeRead que hd
            U.foldM' decr tl (targetsOf g v) >>= go (hd + 1)
  cnt <- foldM push 0 [0 .. n - 1] >>= go 0
  if cnt < n then pure Nothing else Just <$> U.unsafeFreeze que

-- ---------------------------------------------------------------------
-- 分解
--
-- 成分への分け方は、まず頂点ごとの成分番号 @(成分の数, 元の番号 → 成分の番号)@ として求める
-- ('componentIds' / 'strongComponentIds' / 'bridgeComponentIds' / 'componentIdsWith')。
-- 番号だけなら O(n + m) で、部分グラフは作らない。部分グラフが要るときは 'splitByIds'、
-- 成分を 1 頂点に縮めるときは 'condense' に渡す。
--
-- > let ids@(k, cid) = strongComponentIds g
-- > k                                    -- 成分の数
-- > cid U.! u == cid U.! v               -- u と v が同じ成分か
-- > let dag = condense ids g             -- 縮めたグラフ (強連結成分なら DAG)
-- > let (comps, loc) = splitByIds ids g  -- 成分ごとの部分グラフ
--
-- 'splitComponents' / 'splitStrongComponents' / 'splitBridgeComponents' は、番号を振って
-- 'splitByIds' に渡すまでを 1 回で行う。返り値は次の 2 つ。
--
-- * 1 つ目: 成分ごとの @(部分グラフ, 部分の番号 → 元の番号)@。
--   成分の中の番号は元の番号の小さい順に振る (なので 2 つ目の Vector は昇順)。
--   部分グラフの辺は元のグラフの順のまま。成分をまたぐ辺は落ちる ('condense' で取り出す)。
-- * 2 つ目: 元の番号 → @(成分の番号, 部分の番号)@。
--
-- > let (comps, loc) = splitComponents g
-- > V.length comps                                -- 成分の数
-- > fst (loc U.! u) == fst (loc U.! v)            -- u と v が同じ成分か
-- > V.forM_ comps $ \(sub, orig) -> ...           -- 部分の頂点 i は元の orig U.! i
--
-- 'bridgeComponentIds' / 'splitBridgeComponents' / 'splitBiconnectedComponents' /
-- 'blockCutTree' / 'bridgeEdges' / 'articulationPoints' / 'dfsLowlink' は無向グラフ用で、
-- 有向グラフを渡すと 'error'。'undirectedGraph' などで無向グラフとして作る
-- (有向グラフに両向きの辺を入れたものは有向グラフのまま)。

-- | 連結成分の番号 @(成分の数, 元の番号 → 成分の番号)@。成分は小さい頂点を含むものから。
-- 有向グラフでは向きを無視して数える (弱連結成分)。O(n + m)。
{-# INLINE componentIds #-}
componentIds :: (GraphKind g) => g -> GraphRet g (Int, U.Vector Int)
componentIds g = primGraph g componentIdsC

componentIdsC :: AtcGraph -> (Int, U.Vector Int)
componentIdsC = componentIdsWithC (\_ _ _ -> True)

-- | @componentIdsWith ok g@: @ok u v 重み@ が真の辺だけを使った連結成分の番号。
-- 「重みが K 以下の辺だけで繋がっているか」のような条件付きの連結性に使う。
-- 番号の振り方は 'componentIds' と同じ。有向グラフでも向きを無視する。
-- 無向グラフでは各辺が両向き (@ok u v w@ と @ok v u w@) で呼ばれ、どちらかが真なら使う。
-- O(n + m α(n))。
{-# INLINE componentIdsWith #-}
componentIdsWith :: (GraphKind g) => (Int -> Int -> Int -> Bool) -> g -> GraphRet g (Int, U.Vector Int)
componentIdsWith ok g = primGraph g (componentIdsWithC ok)

componentIdsWithC :: (Int -> Int -> Int -> Bool) -> AtcGraph -> (Int, U.Vector Int)
componentIdsWithC ok g@(AtcGraph n _ tgt wt _) = runST $ do
  uf <- newUF n
  U.forM_ (U.zip3 (grArcSources g) tgt wt) $ \(u, v, c) ->
    when (ok u v c) $ do
      _ <- uniteUF u v uf
      pure ()
  roots <- U.generateM n (\v -> rootUF v uf)
  pure (grNumberRoots roots)

-- | 強連結成分の番号。成分はトポロジカル順 (辺 @u -> v@ なら @u@ の番号 <= @v@ の番号) で、
-- 'condense' すると DAG になる。無向グラフでは連結成分になる。O(n + m)。
{-# INLINE strongComponentIds #-}
strongComponentIds :: (GraphKind g) => g -> GraphRet g (Int, U.Vector Int)
strongComponentIds g = primGraph g strongComponentIdsC

-- Tarjan 法。再帰の代わりに、呼び出しのスタック cs と頂点ごとの次に見る辺 it を持つ。
-- 成分は吸い込む側 (逆トポロジカル順) から決まるので、最後に番号を反転する。
strongComponentIdsC :: AtcGraph -> (Int, U.Vector Int)
strongComponentIdsC (AtcGraph n off tgt _ _) = runST $ do
  ordM <- UM.replicate n (-1 :: Int)
  lowM <- UM.unsafeNew n
  compM <- UM.replicate n (-1)
  itM <- UM.unsafeNew n
  stk <- UM.unsafeNew n -- 成分が決まっていない頂点
  cs <- UM.unsafeNew n
  let enter !t !sp !csp !k v = do
        UM.unsafeWrite ordM v t
        UM.unsafeWrite lowM v t
        UM.unsafeWrite stk sp v
        UM.unsafeWrite cs csp v
        UM.unsafeWrite itM v (U.unsafeIndex off v)
        go (t + 1) (sp + 1) (csp + 1) k
      go !t !sp !csp !k
        | csp == 0 = pure (t, k)
        | otherwise = do
            v <- UM.unsafeRead cs (csp - 1)
            i <- UM.unsafeRead itM v
            if i < U.unsafeIndex off (v + 1)
              then do
                UM.unsafeWrite itM v (i + 1)
                let w = U.unsafeIndex tgt i
                o <- UM.unsafeRead ordM w
                if o == -1
                  then enter t sp csp k w
                  else do
                    c <- UM.unsafeRead compM w
                    when (c == -1) $ UM.unsafeModify lowM (min o) v
                    go t sp csp k
              else do
                lv <- UM.unsafeRead lowM v
                ov <- UM.unsafeRead ordM v
                when (csp >= 2) $ do
                  p <- UM.unsafeRead cs (csp - 2)
                  UM.unsafeModify lowM (min lv) p
                if lv == ov
                  then do
                    sp' <- popTo k v sp
                    go t sp' (csp - 1) (k + 1)
                  else go t sp (csp - 1) k
      popTo k v sp = do
        x <- UM.unsafeRead stk (sp - 1)
        UM.unsafeWrite compM x k
        if x == v then pure (sp - 1) else popTo k v (sp - 1)
      outer (!t, !k) r = do
        o <- UM.unsafeRead ordM r
        if o /= -1 then pure (t, k) else enter t 0 0 k r
  (_, k) <- foldM outer (0, 0) [0 .. n - 1]
  comp <- U.unsafeFreeze compM
  pure (k, U.map (\c -> k - 1 - c) comp)

-- | 2-SAT。変数 @x_0 .. x_{n-1}@ と節 @(i, f, j, g)@ (「@x_i == f@ または @x_j == g@」) の並びから、
-- 全ての節を満たす割り当てを 1 つ返す。なければ 'Nothing'。O(n + 節の数)。
--
-- > solveTwoSat 2 [(0, True, 1, True), (0, False, 1, False)]   -- x_0 xor x_1: Just [True,False] など
-- > solveTwoSat 1 [(0, True, 0, True)]                         -- x_0 を真に固定: Just [True]
--
-- 「@x_i@ なら @x_j@」は @(i, False, j, True)@。リテラル @x_i == f@ を頂点にして、節 @a ∨ b@ を
-- 辺 @¬a → b@ と @¬b → a@ にし、'strongComponentIds' で解く。
solveTwoSat :: Int -> [(Int, Bool, Int, Bool)] -> Maybe (U.Vector Bool)
solveTwoSat n clauses
  | any (\(i, _, j, _) -> i < 0 || i >= n || j < 0 || j >= n) clauses = error "Atc.Graph.solveTwoSat: 範囲外の変数"
  | U.any (\i -> cid U.! lit i True == cid U.! lit i False) (U.enumFromN 0 n) = Nothing
  -- トポロジカル順で後ろにあるリテラルを真にする。
  | otherwise = Just (U.generate n (\i -> cid U.! lit i True > cid U.! lit i False))
  where
    -- リテラル x_i == f の頂点。
    lit i f = 2 * i + (if f then 0 else 1)
    g = graphFromList (2 * n) (concat [[(lit i (not f), lit j g', 1), (lit j (not g'), lit i f, 1)] | (i, f, j, g') <- clauses])
    (_, cid) = strongComponentIdsC g

-- | 二重辺連結成分 (橋を除いた後の連結成分) の番号。成分は小さい頂点を含むものから。
-- 'condense' すると橋の木 (非連結なら森) になる。無向グラフ用。O(n + m)。
{-# INLINE bridgeComponentIds #-}
bridgeComponentIds :: (GraphKind g) => g -> GraphRet g (Int, U.Vector Int)
bridgeComponentIds g = primGraph g bridgeComponentIdsC

bridgeComponentIdsC :: AtcGraph -> (Int, U.Vector Int)
bridgeComponentIdsC g0 = componentIdsWithC (\u v _ -> not (isBridgeArc ll u v)) g
  where
    g = grRequireUndirected "bridgeComponentIds" g0
    ll = grLowlink g

-- | 成分番号 @(成分の数, 元の番号 → 成分の番号)@ から、成分ごとの部分グラフを作る。
-- 返り値は 'splitComponents' と同じ形。番号は 0 以上・成分の数未満で、
-- 頂点数と長さが違えば 'error'。番号は自分で振ったものでもよい。O(n + m)。
{-# INLINE splitByIds #-}
splitByIds :: (GraphKind g) => (Int, U.Vector Int) -> g -> GraphRet g (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitByIds ids g = primGraph g (splitByIdsC ids)

splitByIdsC :: (Int, U.Vector Int) -> AtcGraph -> (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitByIdsC ids g0 = (grBuildParts g verts arcComp, loc)
  where
    g@(AtcGraph n _ tgt _ _) = grCheckIds "splitByIds" ids g0
    (k, cid) = ids
    cnt = U.accumulate (+) (U.replicate k 0) (U.map (\c -> (c, 1)) cid)
    voff = U.scanl' (+) 0 cnt
    -- 頂点を成分ごとに、番号の小さい順に並べる。
    grouped = U.create $ do
      pos <- U.thaw voff
      out <- UM.unsafeNew n
      U.iforM_ cid $ \v c -> do
        p <- UM.unsafeRead pos c
        UM.unsafeWrite pos c (p + 1)
        UM.unsafeWrite out p v
      pure out
    verts = V.generate k (\c -> U.slice (voff U.! c) (cnt U.! c) grouped)
    posOf = U.update (U.replicate n 0) (U.imap (flip (,)) grouped)
    loc = U.imap (\v c -> (c, posOf U.! v - voff U.! c)) cid
    arcComp = U.zipWith (\u w -> let c = cid U.! u in if c == cid U.! w then c else -1) (grArcSources g) tgt

-- | 連結成分 ('componentIds') ごとの部分グラフ。返り値は節の説明を参照。O(n + m)。
{-# INLINE splitComponents #-}
splitComponents :: (GraphKind g) => g -> GraphRet g (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitComponents g = primGraph g splitComponentsC

splitComponentsC :: AtcGraph -> (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitComponentsC g = splitByIdsC (componentIdsC g) g

-- | 強連結成分 ('strongComponentIds') ごとの部分グラフ。成分はトポロジカル順。O(n + m)。
{-# INLINE splitStrongComponents #-}
splitStrongComponents :: (GraphKind g) => g -> GraphRet g (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitStrongComponents g = primGraph g splitStrongComponentsC

splitStrongComponentsC :: AtcGraph -> (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitStrongComponentsC g = splitByIdsC (strongComponentIdsC g) g

-- | 二重辺連結成分 ('bridgeComponentIds') ごとの部分グラフ。無向グラフ用。O(n + m)。
{-# INLINE splitBridgeComponents #-}
splitBridgeComponents :: (GraphKind g) => g -> GraphRet g (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitBridgeComponents g = primGraph g splitBridgeComponentsC

splitBridgeComponentsC :: AtcGraph -> (V.Vector (AtcGraph, U.Vector Int), U.Vector (Int, Int))
splitBridgeComponentsC g0 = splitByIdsC (bridgeComponentIdsC g) g
  where
    g = grRequireUndirected "splitBridgeComponents" g0

-- | 二重頂点連結成分。関節点は複数の成分に入るので、2 つ目は元の番号 → 入っている
-- @(成分の番号, 部分の番号)@ 全部 (成分の番号の昇順)。関節点でなければ長さ 1。
--
-- どの辺もちょうど 1 つの成分に入る。辺のない頂点はそれだけで 1 つの成分になり、
-- 自己ループはその頂点を含む成分のどれかに入る。
-- 成分は、頂点 (昇順) の並びの辞書順。縮めるときは 'blockCutTree'。
-- 無向グラフ用。O((n + m) log n)。
{-# INLINE splitBiconnectedComponents #-}
splitBiconnectedComponents :: (GraphKind g) => g -> GraphRet g (V.Vector (AtcGraph, U.Vector Int), V.Vector [(Int, Int)])
splitBiconnectedComponents g = primGraph g splitBiconnectedComponentsC

splitBiconnectedComponentsC :: AtcGraph -> (V.Vector (AtcGraph, U.Vector Int), V.Vector [(Int, Int)])
splitBiconnectedComponentsC g0 = (grBuildParts g verts arcComp, loc)
  where
    g = grRequireUndirected "splitBiconnectedComponents" g0
    (verts, arcComp) = grBiconnected g
    k = V.length verts
    loc =
      V.accum
        (flip (:))
        (V.replicate (numVertices g) [])
        [(v, (c, i)) | c <- [k - 1, k - 2 .. 0], (i, v) <- U.toList (U.indexed (verts V.! c))]

-- | ブロックカット木。二重頂点連結成分を頂点にして、元の頂点とそれを含む成分を結ぶ。
-- 頂点 @0 .. n - 1@ は元の頂点、@n + b@ は 'splitBiconnectedComponents' の @b@ 番目の成分
-- (成分の数は @numVertices t - n@)。辺は重み 1 の無向。
--
-- 関節点は 2 つ以上の成分と結ばれ、それ以外の頂点は 1 つの成分とだけ結ばれる (葉になる)。
-- 元が連結なら木、そうでなければ森。「u から v へのどの道も通る頂点」は、
-- この木の u - v の道にある元の頂点。無向グラフ用。O((n + m) log n)。
{-# INLINE blockCutTree #-}
blockCutTree :: (GraphKind g) => g -> GraphRet g g
blockCutTree g = primGraphNew g blockCutTreeC

blockCutTreeC :: AtcGraph -> AtcGraph
blockCutTreeC g0 = buildCSR Undirected (n + V.length verts) (bothWays es)
  where
    g = grRequireUndirected "blockCutTree" g0
    n = numVertices g
    (verts, _) = grBiconnected g
    es = U.create $ do
      out <- UM.unsafeNew (V.sum (V.map U.length verts))
      let go !i b = when (b < V.length verts) $ do
            let vs = V.unsafeIndex verts b
            rep (U.length vs) $ \j -> UM.unsafeWrite out (i + j) (U.unsafeIndex vs j, n + b, 1)
            go (i + U.length vs) (b + 1)
      go 0 0
      pure out

-- | 橋 @(u, v)@ (@u < v@)。昇順。無向グラフ用。O(n + m)。
{-# INLINE bridgeEdges #-}
bridgeEdges :: (GraphKind g) => g -> GraphRet g ([(Int, Int)])
bridgeEdges g = primGraph g bridgeEdgesC

bridgeEdgesC :: AtcGraph -> [(Int, Int)]
bridgeEdgesC g0 = U.toList (U.modify Intro.sort (U.map edge (U.filter isBridge (U.enumFromN 0 (numVertices g)))))
  where
    -- 橋は DFS 木の辺 (親 p - 子 v) で、v の下から p 以上へ戻れないもの。
    isBridge v = let p = par U.! v in p /= -1 && low U.! v > ordv U.! p
    edge v = let p = par U.! v in (min p v, max p v)
    g = grRequireUndirected "bridgeEdges" g0
    Lowlink {llOrder = ordv, llLow = low, llParent = par} = grLowlink g

-- | 関節点 (取り除くと連結成分が増える頂点)。昇順。無向グラフ用。O(n + m)。
{-# INLINE articulationPoints #-}
articulationPoints :: (GraphKind g) => g -> GraphRet g ([Int])
articulationPoints g = primGraph g articulationPointsC

articulationPointsC :: AtcGraph -> [Int]
articulationPointsC g0 = U.toList (U.findIndices (>= 2) score)
  where
    g = grRequireUndirected "articulationPoints" g0
    n = numVertices g
    Lowlink {llOrder = ordv, llLow = low, llParent = par} = grLowlink g
    -- 根でない頂点は、子の low が自分の訪問順以上なら関節点 (2 点にする)。
    -- 根は子 1 つにつき 1 点で、子が 2 つ以上なら関節点。
    score = U.create $ do
      sc <- UM.replicate n (0 :: Int)
      rep n $ \c -> do
        let p = U.unsafeIndex par c
        when (p /= -1) $
          if U.unsafeIndex par p == -1
            then UM.unsafeModify sc (+ 1) p
            else when (U.unsafeIndex low c >= U.unsafeIndex ordv p) $ UM.unsafeWrite sc p 2
      pure sc

-- | 成分を 1 頂点に縮める。@ids@ は成分番号 @(成分の数, 元の番号 → 成分の番号)@
-- ('componentIds' / 'strongComponentIds' / 'bridgeComponentIds' など)。
-- 成分をまたぐ辺だけを (重み付きのまま、多重辺もそのまま) 残す。多重辺は 'simplifyGraph' で除ける。
-- 頂点数と長さが違えば 'error'。O(n + m)。
{-# INLINE condense #-}
condense :: (GraphKind g) => (Int, U.Vector Int) -> g -> GraphRet g g
condense ids g = primGraphNew g (condenseC ids)

condenseC :: (Int, U.Vector Int) -> AtcGraph -> AtcGraph
condenseC ids g0 = buildCSR (graphDirection g) k (U.filter (\(a, b, _) -> a /= b) es)
  where
    g@(AtcGraph _ _ tgt wt _) = grCheckIds "condense" ids g0
    (k, cid) = ids
    es = U.zipWith3 (\u v c -> (cid U.! u, cid U.! v, c)) (grArcSources g) tgt wt

-- | 単純グラフにする。自己ループを除き、同じ向きの多重辺は重みが最小の 1 本だけ残す。
-- 無向グラフでも、各辺が 1 本ずつになる。隣接は行き先の昇順になる。O(n + m log m)。
{-# INLINE simplifyGraph #-}
simplifyGraph :: (GraphKind g) => g -> GraphRet g g
simplifyGraph g = primGraphNew g simplifyGraphC

simplifyGraphC :: AtcGraph -> AtcGraph
simplifyGraphC g@(AtcGraph n _ tgt wt dir) = buildCSR dir n (U.ifilter keep sorted)
  where
    sorted = U.modify Intro.sort (U.filter (\(u, v, _) -> u /= v) (U.zip3 (grArcSources g) tgt wt))
    keep i (u, v, _) = i == 0 || let (u', v', _) = U.unsafeIndex sorted (i - 1) in (u', v') /= (u, v)

-- | 無向グラフの DFS の結果 ('dfsLowlink')。
data Lowlink = Lowlink
  { -- | 訪問順 (0 から)。
    llOrder :: !(U.Vector Int)
  , -- | low: 子孫から後退辺 1 本で戻れる最小の訪問順。
    llLow :: !(U.Vector Int)
  , -- | DFS 木の親。根は @-1@。
    llParent :: !(U.Vector Int)
  , -- | 二重頂点連結成分の頂点 (作った順。成分の中は、切れ目の頂点の後に積んだ順)。
    llBlocks :: !(V.Vector (U.Vector Int))
  , -- | 頂点ごとに、それを含む 'llBlocks' の成分の 1 つ。根でなければ、親から入る木の辺の成分。
    llHome :: !(U.Vector Int)
  }

-- | 無向グラフを DFS して、訪問順・low・親を求める。'bridgeEdges' / 'articulationPoints' /
-- 'bridgeComponentIds' などの元になる。独自の条件で橋を調べたいときは、これと 'isBridgeArc' を使う。
-- 無向グラフ用。O(n + m)。
{-# INLINE dfsLowlink #-}
dfsLowlink :: (GraphKind g) => g -> GraphRet g Lowlink
dfsLowlink g = primGraph g dfsLowlinkC

dfsLowlinkC :: AtcGraph -> Lowlink
dfsLowlinkC = grLowlink . grRequireUndirected "dfsLowlink"

-- | 辺 @u - v@ が橋か。O(1)。
--
-- DFS 木で深い方 d と浅い方 a について、木の辺 a - d で、d の下から a 以上へ戻れないとき
-- (このとき a - d の辺は 1 本だけ)。
isBridgeArc :: Lowlink -> Int -> Int -> Bool
isBridgeArc (Lowlink ordv low par _ _) u v = u /= v && par U.! d == a && low U.! d > ordv U.! a
  where
    (d, a) = if ordv U.! u > ordv U.! v then (u, v) else (v, u)

-- 以下は内部用。

-- 各辺の出発点。
grArcSources :: AtcGraph -> U.Vector Int
grArcSources (AtcGraph n off _ _ _) = U.create $ do
  out <- UM.unsafeNew (U.last off)
  rep n $ \u -> do
    let s = U.unsafeIndex off u
    UM.set (UM.unsafeSlice s (U.unsafeIndex off (u + 1) - s) out) u
  pure out

-- 無向グラフでなければ止める。第 1 引数はエラーに出す名前。
grRequireUndirected :: String -> AtcGraph -> AtcGraph
grRequireUndirected name g
  | graphDirection g == Undirected = g
  | otherwise = error ("Atc.Graph." ++ name ++ ": 無向グラフ用です (undirectedGraph などで作る)")

-- 成分番号の形を確かめる。
grCheckIds :: String -> (Int, U.Vector Int) -> AtcGraph -> AtcGraph
grCheckIds name (k, cid) g
  | U.length cid /= numVertices g = error ("Atc.Graph." ++ name ++ ": 成分番号の長さが頂点数と違います")
  | U.any (\c -> c < 0 || k <= c) cid = error ("Atc.Graph." ++ name ++ ": 成分番号が 0 以上・成分の数未満ではありません")
  | otherwise = g

-- 頂点ごとの代表から、代表を初めて見た順に 0, 1 .. と番号を振る。代表は 0 以上 n 未満。
grNumberRoots :: U.Vector Int -> (Int, U.Vector Int)
grNumberRoots rs = runST $ do
  idOf <- UM.replicate n (-1)
  out <- UM.unsafeNew n
  let step !k v = do
        let r = U.unsafeIndex rs v
        x <- UM.unsafeRead idOf r
        if x /= -1
          then UM.unsafeWrite out v x >> pure k
          else UM.unsafeWrite idOf r k >> UM.unsafeWrite out v k >> pure (k + 1)
  k <- foldM step 0 [0 .. n - 1]
  (,) k <$> U.unsafeFreeze out
  where
    n = U.length rs

-- 二重頂点連結成分の、成分ごとの頂点 (昇順。成分は辞書順) と、辺ごとの成分。
--
-- 2 つの成分が共有する頂点は高々 1 つなので、昇順に並べた頂点の先頭 2 つ (1 頂点の成分は
-- 先頭と -1) で辞書順が決まる。1 頂点の成分の頂点は、ほかのどの成分にも入らない。
grBiconnected :: AtcGraph -> (V.Vector (U.Vector Int), U.Vector Int)
grBiconnected g@(AtcGraph _ _ tgt _ _) = (verts, arcComp)
  where
    Lowlink {llOrder = ordv, llBlocks = blocks, llHome = home} = grLowlink g
    k = V.length blocks
    sorted = V.map (U.modify Intro.sort) blocks
    key b = let vs = V.unsafeIndex sorted b in (U.unsafeIndex vs 0, if U.length vs > 1 then U.unsafeIndex vs 1 else -1, b)
    -- 新しい順に並べた、作った順の番号
    perm = U.map (\(_, _, b) -> b) (U.modify Intro.sort (U.generate k key))
    newId = U.update (U.replicate k 0) (U.imap (flip (,)) perm)
    verts = V.map (V.unsafeIndex sorted) (V.convert perm)
    -- 辺 u - w は、DFS 木で深い方の頂点の home の成分に入る
    -- (木の辺も後退辺も、深い方へ入る木の辺と同じ成分)。
    arcComp =
      U.zipWith
        (\u w -> newId U.! (home U.! (if ordv U.! w > ordv U.! u then w else u)))
        (grArcSources g)
        tgt

-- 成分ごとの頂点 (昇順) と、辺ごとの成分 (-1 なら落とす) から部分グラフを作る。
--
-- 全ての成分の CSR を 1 本ずつの大きな配列に書き、成分ごとに切り出す。成分の中の辺は
-- 元の順 (出発点の昇順) に並べるので、そのまま CSR になる。元の番号 → 部分の番号は、
-- 成分を 1 つずつ処理しながら同じ配列に書き直す (二重頂点連結成分では頂点が複数の成分に入る)。
grBuildParts :: AtcGraph -> V.Vector (U.Vector Int) -> U.Vector Int -> V.Vector (AtcGraph, U.Vector Int)
grBuildParts g@(AtcGraph n _ tgt wt _) verts arcComp = runST $ do
  -- 辺を成分ごとに (成分の中は元の順で) 並べる。
  pos <- U.thaw aoff
  order <- UM.unsafeNew total
  U.iforM_ arcComp $ \i c -> when (c >= 0) $ do
    p <- UM.unsafeRead pos c
    UM.unsafeWrite pos c (p + 1)
    UM.unsafeWrite order p i
  ordered <- U.unsafeFreeze order
  local <- UM.unsafeNew n
  offM <- UM.replicate (U.last voff) 0 -- 成分 c の off は [voff c, voff (c + 1))
  tgtM <- UM.unsafeNew total
  wtM <- UM.unsafeNew total
  rep k $ \c -> do
    let vs = V.unsafeIndex verts c
        base = U.unsafeIndex voff c
        s0 = U.unsafeIndex aoff c
    rep (U.length vs) $ \i -> UM.unsafeWrite local (U.unsafeIndex vs i) i
    rep (U.unsafeIndex cnt c) $ \j0 -> do
      let j = s0 + j0
          a = U.unsafeIndex ordered j
      lu <- UM.unsafeRead local (U.unsafeIndex src a)
      lw <- UM.unsafeRead local (U.unsafeIndex tgt a)
      UM.unsafeModify offM (+ 1) (base + lu + 1)
      UM.unsafeWrite tgtM j lw
      UM.unsafeWrite wtM j (U.unsafeIndex wt a)
    -- 次数の累積和にする。
    rep (U.length vs) $ \i0 -> do
      let i = base + i0 + 1
      x <- UM.unsafeRead offM (i - 1)
      UM.unsafeModify offM (+ x) i
  offs <- U.unsafeFreeze offM
  tgts <- U.unsafeFreeze tgtM
  wts <- U.unsafeFreeze wtM
  pure $ V.generate k $ \c ->
    let vs = V.unsafeIndex verts c
        s = U.unsafeIndex aoff c
        e = U.unsafeIndex cnt c
     in ( AtcGraph
            (U.length vs)
            (U.slice (U.unsafeIndex voff c) (U.length vs + 1) offs)
            (U.slice s e tgts)
            (U.slice s e wts)
            (graphDirection g)
        , vs
        )
  where
    k = V.length verts
    src = grArcSources g
    cnt = U.accumulate (+) (U.replicate k 0) (U.map (\c -> (c, 1)) (U.filter (>= 0) arcComp))
    aoff = U.scanl' (+) 0 cnt
    total = U.last aoff
    -- 成分 c の off は長さ (頂点数 + 1)。
    voff = U.scanl' (+) 0 (U.convert (V.map (\vs -> U.length vs + 1) verts))

-- 'dfsLowlink' の本体 (向きは確かめない)。
--
-- 再帰の代わりに、呼び出しのスタック cs と頂点ごとの次に見る辺 it を持つ。
-- 親へ戻る辺は 1 本だけ飛ばす (残りの多重辺は後退辺として数える)。
-- 二重頂点連結成分は、頂点を積んでおいて、子 v の low が親 p の訪問順以上になったら
-- v から上を下ろし、p と合わせて 1 つの成分にする。成分は 1 本の配列 blk に続けて書く
-- (どの頂点も下ろされるのは 1 回なので、長さは 2n で足りる)。
grLowlink :: AtcGraph -> Lowlink
grLowlink (AtcGraph n off tgt _ _) = runST $ do
  ordM <- UM.replicate n (-1)
  lowM <- UM.unsafeNew n
  parM <- UM.replicate n (-1)
  homeM <- UM.replicate n (-1)
  itM <- UM.unsafeNew n
  skipM <- UM.unsafeNew n -- 親へ戻る辺を 1 本飛ばしたか
  stk <- UM.unsafeNew n -- 成分が決まっていない頂点
  atM <- UM.unsafeNew n -- 頂点を積んだ位置
  cs <- UM.unsafeNew n
  blk <- UM.unsafeNew (2 * n)
  bof <- UM.unsafeNew (n + 1) -- 成分 b は blk の [bof b, bof (b + 1))
  UM.write bof 0 0
  nbR <- newSTRef (0 :: Int)
  let -- p と、stk の [from, sp) を 1 つの成分にする。
      newBlock p from sp = do
        b <- readSTRef nbR
        s <- UM.unsafeRead bof b
        UM.unsafeWrite blk s p
        let len = sp - from
        UM.unsafeCopy (UM.unsafeSlice (s + 1) len blk) (UM.unsafeSlice from len stk)
        rep len $ \i -> UM.unsafeRead stk (from + i) >>= \x -> UM.unsafeWrite homeM x b
        UM.unsafeWrite bof (b + 1) (s + 1 + len)
        writeSTRef nbR (b + 1)
        pure b
      enter !t !sp !csp v p = do
        UM.unsafeWrite ordM v t
        UM.unsafeWrite lowM v t
        UM.unsafeWrite parM v p
        UM.unsafeWrite itM v (U.unsafeIndex off v)
        UM.unsafeWrite skipM v False
        UM.unsafeWrite stk sp v
        UM.unsafeWrite atM v sp
        UM.unsafeWrite cs csp v
        go (t + 1) (sp + 1) (csp + 1)
      go !t !sp !csp
        | csp == 0 = pure t
        | otherwise = do
            v <- UM.unsafeRead cs (csp - 1)
            i <- UM.unsafeRead itM v
            p <- UM.unsafeRead parM v
            if i < U.unsafeIndex off (v + 1)
              then do
                UM.unsafeWrite itM v (i + 1)
                let w = U.unsafeIndex tgt i
                skipped <- UM.unsafeRead skipM v
                if w == v
                  then go t sp csp
                  else
                    if w == p && not skipped
                      then UM.unsafeWrite skipM v True >> go t sp csp
                      else do
                        o <- UM.unsafeRead ordM w
                        if o /= -1
                          then UM.unsafeModify lowM (min o) v >> go t sp csp
                          else enter t sp csp w v
              else
                if p == -1
                  then go t sp (csp - 1)
                  else do
                    -- v から戻る。親 p の low を直し、p で切れるなら成分を下ろす。
                    lv <- UM.unsafeRead lowM v
                    UM.unsafeModify lowM (min lv) p
                    op <- UM.unsafeRead ordM p
                    if lv >= op
                      then do
                        from <- UM.unsafeRead atM v
                        b <- newBlock p from sp
                        pp <- UM.unsafeRead parM p
                        when (pp == -1) $ do
                          h <- UM.unsafeRead homeM p
                          when (h == -1) $ UM.unsafeWrite homeM p b
                        go t from (csp - 1)
                      else go t sp (csp - 1)
      outer !t r = do
        o <- UM.unsafeRead ordM r
        if o /= -1
          then pure t
          else do
            -- 終わると根 r だけが積まれて残る (次の根は 0 から積む)。
            t' <- enter t 0 0 r (-1)
            h <- UM.unsafeRead homeM r
            when (h == -1) $ do
              b <- newBlock r 0 0
              UM.unsafeWrite homeM r b
            pure t'
  _ <- foldM outer 0 [0 .. n - 1]
  nb <- readSTRef nbR
  bofs <- U.unsafeFreeze bof
  blks <- U.unsafeFreeze blk
  Lowlink
    <$> U.unsafeFreeze ordM
    <*> U.unsafeFreeze lowM
    <*> U.unsafeFreeze parM
    <*> pure (V.generate nb (\b -> U.slice (bofs U.! b) (bofs U.! (b + 1) - bofs U.! b) blks))
    <*> U.unsafeFreeze homeM

-- ---------------------------------------------------------------------
-- 木
--
-- 連結な木 (無向で辺 n - 1 本) を前提にする。

-- | 根 @root@ からの親 (根は @-1@) と深さ (辺の本数)。O(n)。
{-# INLINE treeParentDepth #-}
treeParentDepth :: (GraphKind g) => g -> Int -> GraphRet g (U.Vector Int, U.Vector Int)
treeParentDepth g x = primGraph g (\c -> treeParentDepthC c x)

treeParentDepthC :: AtcGraph -> Int -> (U.Vector Int, U.Vector Int)
treeParentDepthC g root = let (d, p) = bfsDistPrev g [root] in (p, d)

-- | 根 @root@ からの重み付きの距離。O(n)。
{-# INLINE treeDist #-}
treeDist :: (GraphKind g) => g -> Int -> GraphRet g (U.Vector Int)
treeDist g x = primGraph g (\c -> treeDistC c x)

treeDistC :: AtcGraph -> Int -> U.Vector Int
treeDistC g root = runST $ do
  dist <- UM.replicate n 0
  seen <- UM.replicate n False
  que <- UM.unsafeNew n
  UM.write seen root True
  UM.unsafeWrite que 0 root
  let visit dv !tl (u, c) = do
        s <- UM.unsafeRead seen u
        if s
          then pure tl
          else do
            UM.unsafeWrite seen u True
            UM.unsafeWrite dist u (dv + c)
            UM.unsafeWrite que tl u
            pure (tl + 1)
      go !hd !tl = when (hd < tl) $ do
        v <- UM.unsafeRead que hd
        dv <- UM.unsafeRead dist v
        U.foldM' (visit dv) tl (arcs g v) >>= go (hd + 1)
  go 0 (1 :: Int)
  U.unsafeFreeze dist
  where
    n = numVertices g

-- | 直径 (重み付き)。@(長さ, 端点, 端点)@。重みは非負。O(n)。
{-# INLINE treeDiameter #-}
treeDiameter :: (GraphKind g) => g -> GraphRet g (Int, Int, Int)
treeDiameter g = primGraph g treeDiameterC

treeDiameterC :: AtcGraph -> (Int, Int, Int)
treeDiameterC g = (dv U.! v, u, v)
  where
    u = U.maxIndex (treeDist g 0)
    dv = treeDist g u
    v = U.maxIndex dv
