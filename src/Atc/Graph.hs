{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}

-- | 隣接リスト (CSR) のグラフと、その上の基本的なアルゴリズム。
--
-- 頂点は 0 始まりの @0 .. n - 1@。辺はすべて重み付き (@Int@) で、
-- 重みのない辺は重み 1 として持つ。無向グラフは両向きの有向辺として持つ。
--
-- == 作る
--
-- 入力の @u v@ (重み付きなら @u v w@) が M 行並んだものを 'getIntGrid' で読んで渡す。
-- 入力の頂点番号は 1 始まりとして、1 を引いて取り込む。
--
-- > [n, m] <- getInts
-- > es <- getIntGrid 2 m            -- 重み付きなら getIntGrid 3 m
-- > let g = undirectedGraph n es    -- 有向なら directedGraph
--
-- 0 始まりの頂点番号や、自分で組み立てた辺は 'graphFromList' に (有向で) 渡す。
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
-- > let (k, ids) = connectedComponents g   -- 成分数と、頂点ごとの成分番号
-- > componentGroups (k, ids)               -- 成分ごとの頂点 (stronglyConnected にも使える)
--
-- == 名前
--
-- @atc bundle@ は解答と 1 ファイルにまとめるので、解答側で自前定義しがちな名前
-- (@bfs@, @dijkstra@ …) や "Data.Graph" の名前 (@graphFromEdges@, @components@,
-- @scc@, @topSort@ …) は避けている。
module Atc.Graph where

import Atc.Grid (Grid (..))
import Control.Monad (foldM, when)
import Control.Monad.ST (ST, runST)
import qualified Data.Foldable as F
import qualified Data.Graph as DG
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 型

-- | 頂点数・各頂点の辺の開始位置 (長さ n + 1)・行き先・重み。
-- 頂点 @v@ の辺は @[off ! v, off ! (v + 1))@ の範囲。
data AtcGraph = AtcGraph !Int !(U.Vector Int) !(U.Vector Int) !(U.Vector Int)

instance Show AtcGraph where
  show g = "AtcGraph {vertices = " ++ show (numVertices g) ++ ", edges = " ++ show (graphEdges g) ++ "}"

-- ---------------------------------------------------------------------
-- 作る

-- | 1 始まりの @u v@ / @u v w@ の並びから無向グラフを作る。幅が 2 なら重み 1。
-- 幅が 2 でも 3 でもなければ 'error'。
undirectedGraph :: Int -> Grid U.Vector Int -> AtcGraph
undirectedGraph n g = buildCSR n (es U.++ U.map (\(u, v, c) -> (v, u, c)) es)
  where
    es = edgesOfGrid "undirectedGraph" g

-- | 1 始まりの @u v@ / @u v w@ の並びから、@u@ から @v@ への有向グラフを作る。
directedGraph :: Int -> Grid U.Vector Int -> AtcGraph
directedGraph n g = buildCSR n (edgesOfGrid "directedGraph" g)

-- | 0 始まりの @(u, v, 重み)@ のリストから有向グラフを作る。
-- 無向にしたいときは両向きを入れる。
graphFromList :: Int -> [(Int, Int, Int)] -> AtcGraph
graphFromList n es = buildCSR n (U.fromList es)

edgesOfGrid :: String -> Grid U.Vector Int -> U.Vector (Int, Int, Int)
edgesOfGrid name (Grid w h d)
  | w == 2 = U.generate h (\i -> (at (2 * i) - 1, at (2 * i + 1) - 1, 1))
  | w == 3 = U.generate h (\i -> (at (3 * i) - 1, at (3 * i + 1) - 1, at (3 * i + 2)))
  | otherwise = error ("Atc.Graph." ++ name ++ ": 幅は 2 (u v) か 3 (u v w)")
  where
    at = U.unsafeIndex d

-- | 次数を数えて累積和を取り、そこへ書き込む。O(n + m)。同じ頂点の辺は入力順に並ぶ。
buildCSR :: Int -> U.Vector (Int, Int, Int) -> AtcGraph
buildCSR n es
  | U.any (\(u, v, _) -> u < 0 || n <= u || v < 0 || n <= v) es =
      error "Atc.Graph: 頂点番号が範囲外です"
  | otherwise = AtcGraph n off tgt wt
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
-- 基本

numVertices :: AtcGraph -> Int
numVertices (AtcGraph n _ _ _) = n

-- | 出ていく辺の数。無向グラフなら次数。
outDegree :: AtcGraph -> Int -> Int
outDegree (AtcGraph _ off _ _) v = off U.! (v + 1) - off U.! v

-- | @v@ から出る辺の @(行き先, 重み)@。O(1) で切り出す。
adjacent :: AtcGraph -> Int -> U.Vector (Int, Int)
adjacent g v = U.zip (adjacentVertices g v) (adjacentWeights g v)

-- | @v@ から出る辺の行き先。
adjacentVertices :: AtcGraph -> Int -> U.Vector Int
adjacentVertices (AtcGraph _ off t _) v = U.slice (off U.! v) (off U.! (v + 1) - off U.! v) t

-- | @v@ から出る辺の重み。'adjacentVertices' と同じ順。
adjacentWeights :: AtcGraph -> Int -> U.Vector Int
adjacentWeights (AtcGraph _ off _ w) v = U.slice (off U.! v) (off U.! (v + 1) - off U.! v) w

-- | 全ての有向辺 @(u, v, 重み)@。無向グラフは両向きが入る。
graphEdges :: AtcGraph -> [(Int, Int, Int)]
graphEdges g = [(u, v, c) | u <- [0 .. numVertices g - 1], (v, c) <- U.toList (arcs g u)]

-- | 辺の向きを全て逆にする。
reverseGraph :: AtcGraph -> AtcGraph
reverseGraph g = buildCSR (numVertices g) (U.fromList [(v, u, c) | (u, v, c) <- graphEdges g])

-- | "Data.Graph" の 'DG.Graph' に直す (重みは捨てる)。O(n + m)。
toDataGraph :: AtcGraph -> DG.Graph
toDataGraph g = DG.buildG (0, numVertices g - 1) [(u, v) | (u, v, _) <- graphEdges g]

-- 範囲を見ない版 (中で使う)。
targetsOf :: AtcGraph -> Int -> U.Vector Int
targetsOf (AtcGraph _ off t _) v =
  let i = U.unsafeIndex off v in U.unsafeSlice i (U.unsafeIndex off (v + 1) - i) t
{-# INLINE targetsOf #-}

arcs :: AtcGraph -> Int -> U.Vector (Int, Int)
arcs (AtcGraph _ off t w) v =
  let i = U.unsafeIndex off v
      k = U.unsafeIndex off (v + 1) - i
   in U.zip (U.unsafeSlice i k t) (U.unsafeSlice i k w)
{-# INLINE arcs #-}

-- ---------------------------------------------------------------------
-- 最短路

-- | 重みを見ない (辺 1 本を 1 とする) 距離。始点は複数でもよい。届かない頂点は @-1@。O(n + m)。
bfsDist :: AtcGraph -> [Int] -> U.Vector Int
bfsDist g = fst . bfsDistPrev g

-- | 'bfsDist' と、各頂点の直前の頂点 (始点と届かない頂点は @-1@)。経路は 'pathTo' で。
bfsDistPrev :: AtcGraph -> [Int] -> (U.Vector Int, U.Vector Int)
bfsDistPrev g = bfsCore (numVertices g) (\v f z -> U.foldM' f z (targetsOf g v))

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
dijkstraDist :: AtcGraph -> [Int] -> U.Vector Int
dijkstraDist g = fst . dijkstraDistPrev g

-- | 'dijkstraDist' と、各頂点の直前の頂点 (始点と届かない頂点は @-1@)。経路は 'pathTo' で。
dijkstraDistPrev :: AtcGraph -> [Int] -> (U.Vector Int, U.Vector Int)
dijkstraDistPrev g@(AtcGraph n _ tgt _) srcs = runST $ do
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
pathTo :: U.Vector Int -> Int -> [Int]
pathTo prev = go []
  where
    go acc v
      | v == -1 = acc
      | otherwise = go (v : acc) (prev U.! v)

-- | 負の重みがあってもよい距離。届かない頂点は 'Nothing'。
-- @s@ から届く負の閉路があれば 'Nothing'。O(nm)。
bellmanFord :: AtcGraph -> Int -> Maybe (V.Vector (Maybe Int))
bellmanFord g s = runST $ do
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
floydWarshall :: AtcGraph -> Maybe (Grid V.Vector (Maybe Int))
floydWarshall g = runST $ do
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
-- 連結

-- | 無向グラフの連結成分。成分数と、頂点ごとの成分番号 (@0 .. 成分数 - 1@)。
-- 番号は小さい頂点を含む成分ほど小さい。O(n + m)。
connectedComponents :: AtcGraph -> (Int, U.Vector Int)
connectedComponents g = runST $ do
  ids <- UM.replicate n (-1)
  que <- UM.unsafeNew n
  let paint c s = do
        UM.unsafeWrite ids s c
        UM.unsafeWrite que 0 s
        let go !hd !tl = when (hd < tl) $ do
              v <- UM.unsafeRead que hd
              U.foldM' (visit c) tl (targetsOf g v) >>= go (hd + 1)
        go 0 (1 :: Int)
      visit c !tl u = do
        x <- UM.unsafeRead ids u
        if x /= -1
          then pure tl
          else UM.unsafeWrite ids u c >> UM.unsafeWrite que tl u >> pure (tl + 1)
      step !c s = do
        x <- UM.unsafeRead ids s
        if x /= -1 then pure c else paint c s >> pure (c + 1)
  k <- foldM step 0 [0 .. n - 1]
  (,) k <$> U.unsafeFreeze ids
  where
    n = numVertices g

-- | 成分番号から、成分ごとの頂点 (昇順) に直す。
-- 'connectedComponents' / 'stronglyConnected' の結果をそのまま渡す。
componentGroups :: (Int, U.Vector Int) -> V.Vector [Int]
componentGroups (k, ids) =
  V.accum (flip (:)) (V.replicate k []) [(c, v) | (v, c) <- reverse (U.toList (U.indexed ids))]

-- | 無向グラフを 2 色 (0 / 1) に塗る。塗れなければ 'Nothing'。O(n + m)。
bipartiteColoring :: AtcGraph -> Maybe (U.Vector Int)
bipartiteColoring g = runST $ do
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
isBipartite :: AtcGraph -> Bool
isBipartite = maybe False (const True) . bipartiteColoring

-- ---------------------------------------------------------------------
-- 有向グラフ

-- | トポロジカル順 (どの辺も前から後ろへ向かう並び)。閉路があれば 'Nothing'。O(n + m)。
topologicalOrder :: AtcGraph -> Maybe (U.Vector Int)
topologicalOrder g@(AtcGraph n _ tgt _) = runST $ do
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

-- | 強連結成分。成分数と、頂点ごとの成分番号。
-- 番号はトポロジカル順 (辺 @u -> v@ なら @u@ の番号 <= @v@ の番号)。O(n + m)。
stronglyConnected :: AtcGraph -> (Int, U.Vector Int)
stronglyConnected g = (length comps, ids)
  where
    -- DG.scc は逆トポロジカル順に返す。
    comps = reverse (DG.scc (toDataGraph g))
    ids =
      U.update
        (U.replicate (numVertices g) 0)
        (U.fromList [(v, c) | (c, t) <- zip [0 ..] comps, v <- F.toList t])

-- ---------------------------------------------------------------------
-- 木
--
-- 連結な木 (無向で辺 n - 1 本) を前提にする。

-- | 根 @root@ からの親 (根は @-1@) と深さ (辺の本数)。O(n)。
treeParentDepth :: AtcGraph -> Int -> (U.Vector Int, U.Vector Int)
treeParentDepth g root = let (d, p) = bfsDistPrev g [root] in (p, d)

-- | 根 @root@ からの重み付きの距離。O(n)。
treeDist :: AtcGraph -> Int -> U.Vector Int
treeDist g root = runST $ do
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
treeDiameter :: AtcGraph -> (Int, Int, Int)
treeDiameter g = (dv U.! v, u, v)
  where
    u = U.maxIndex (treeDist g 0)
    dv = treeDist g u
    v = U.maxIndex dv
