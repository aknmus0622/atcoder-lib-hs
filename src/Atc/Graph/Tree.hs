{-# LANGUAGE BangPatterns #-}

-- | 木の上の問い合わせ: 最小共通祖先 (LCA) と全方位木 DP。
--
-- グラフは "Atc.Graph" の無向グラフ ('undirectedGraph' などで作ったもの) で、森でもよい
-- (成分ごとに、番号が最小の頂点か指定した根を根にする)。重みはそのまま距離に使う。
--
-- == LCA
--
-- > let t = buildLCA g 0             -- 頂点 0 を根にする。O(n log n)
-- > lcaOf u v t                      -- u と v の最小共通祖先。O(log n)
-- > distanceLCA u v t                -- u と v の間の辺の本数
-- > weightedDistanceLCA u v t        -- u と v の間の重みの和
-- > ancestorLCA k v t                -- v から k 回親に上った頂点 (根を越えれば -1)
-- > depthLCA v t / parentLCA v t     -- 深さ (辺の本数) / 親 (根は -1)
--
-- == 全方位木 DP
--
-- 「各頂点を根にしたときの木 DP の値」を全頂点まとめて O(n) で求める ('rerootDP')。
-- 部分木の値を @b@、子から集めた値を @a@ とし、@merge@ / @e@ / @up@ / @finish@ の 4 つを渡す
-- (それぞれの意味は 'rerootDP' の引数の説明)。
--
-- > -- 各頂点から最も遠い頂点までの距離 (重み付き)
-- > rerootDP max 0 (\_ _ w d -> d + w) (\_ a -> a) g
-- >
-- > -- 各頂点から全頂点への距離の和 (b = (距離の和, 頂点数))
-- > rerootDP (\(s1, c1) (s2, c2) -> (s1 + s2, c1 + c2)) (0, 0)
-- >          (\_ _ w (s, c) -> (s + w * c, c)) (\_ (s, c) -> (s, c + 1)) g
--
-- 演算は可換でなくてもよい (子は隣接の順に、親から来る値は最後にまとめる)。
-- 値は表に書くときに WHNF まで評価する。タプルの中身までは評価しないので、
-- 大きな木では @(s, c)@ のような値は正格なデータ型にするか、@seq@ で評価してから返す。
module Atc.Graph.Tree where

import Atc.Graph
import Control.Monad.ST (runST)
import Data.Bits (shiftR, testBit)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 根付き木の形

-- | 根付きの森の形。各配列は頂点番号で引く (長さ n)。
data RootedTree = RootedTree
  { -- | 訪れた順 (BFS 順。親は子より前)
    rtOrder :: !(U.Vector Int)
  , -- | 親 (根は -1)
    rtParent :: !(U.Vector Int)
  , -- | 深さ (根からの辺の本数)
    rtDepth :: !(U.Vector Int)
  , -- | 根からの重みの和
    rtDist :: !(U.Vector Int)
  , -- | 親へ向かう辺の重み (根は 0)
    rtParentWeight :: !(U.Vector Int)
  }

-- | @root@ を最初の根にして、残りの成分は番号が最小の頂点を根にした BFS。O(n + m)。
-- 無向グラフ用。閉路があっても 'error' にはしない (BFS 木を使う)。
rootTree ::
  (GraphKind g) =>
  -- | 無向グラフ (森でもよい)
  g ->
  -- | @root@: 最初の根
  Int ->
  -- | 根付きの形
  GraphRet g RootedTree
rootTree g root = primGraph g (\c -> rootTreeC c root)

-- | 'rootTree' の本体。
rootTreeC :: AtcGraph -> Int -> RootedTree
rootTreeC g root
  | graphDirection g /= Undirected = error "Atc.Graph.Tree: 無向グラフ用です (undirectedGraph などで作る)"
  | n > 0 && (root < 0 || root >= n) = error ("Atc.Graph.Tree: 根 " ++ show root ++ " が範囲外")
  | otherwise = runST $ do
      parM <- UM.replicate n (-2) -- -2 は未訪問
      depM <- UM.replicate n 0
      distM <- UM.replicate n 0
      pwM <- UM.replicate n 0
      que <- UM.unsafeNew n
      let bfs !hd !tl
            | hd == tl = pure tl
            | otherwise = do
                v <- UM.unsafeRead que hd
                dv <- UM.unsafeRead depM v
                sv <- UM.unsafeRead distM v
                let visit !t (u, w) = do
                      p <- UM.unsafeRead parM u
                      if p /= -2
                        then pure t
                        else do
                          UM.unsafeWrite parM u v
                          UM.unsafeWrite depM u (dv + 1)
                          UM.unsafeWrite distM u (sv + w)
                          UM.unsafeWrite pwM u w
                          UM.unsafeWrite que t u
                          pure (t + 1)
                U.foldM' visit tl (adjacent g v) >>= bfs (hd + 1)
          start !tl r = do
            p <- UM.unsafeRead parM r
            if p /= -2
              then pure tl
              else do
                UM.unsafeWrite parM r (-1)
                UM.unsafeWrite que tl r
                bfs tl (tl + 1)
      t0 <- if n > 0 then start 0 root else pure 0
      _ <- U.foldM' start t0 (U.enumFromN 0 n)
      RootedTree
        <$> U.unsafeFreeze que
        <*> U.unsafeFreeze parM
        <*> U.unsafeFreeze depM
        <*> U.unsafeFreeze distM
        <*> U.unsafeFreeze pwM
  where
    n = numVertices g

-- ---------------------------------------------------------------------
-- LCA

-- | LCA の表 ('buildLCA' で作る)。
data LCA
  = LCA
      -- | 根付きの形
      !RootedTree
      -- | 第 k 段は各頂点の 2^k 個上の祖先 (越えれば -1)
      !(V.Vector (U.Vector Int))

-- | 頂点 @root@ を根にして LCA の表を作る (森なら他の成分は最小の頂点が根)。
-- 無向グラフ用。O(n log n)。
buildLCA ::
  (GraphKind g) =>
  -- | 無向グラフ (森でもよい)
  g ->
  -- | @root@: 根
  Int ->
  -- | LCA の表
  GraphRet g LCA
buildLCA g root = primGraph g (\c -> buildLCAC c root)

-- | 'buildLCA' の本体。
buildLCAC :: AtcGraph -> Int -> LCA
buildLCAC g root = LCA rt (V.fromList (take levels (iterate double par)))
  where
    rt = rootTreeC g root
    par = rtParent rt
    n = numVertices g
    levels = max 1 (bitLen n)
    double up = U.map (\v -> if v == -1 then -1 else U.unsafeIndex up v) up
    bitLen x = if x <= 1 then 1 else 1 + bitLen (x `shiftR` 1)

-- | 頂点が範囲内か確かめる (範囲外なら関数名付きで 'error')。
lcaCheck :: String -> Int -> LCA -> ()
lcaCheck name v (LCA rt _)
  | v < 0 || v >= U.length (rtParent rt) = error ("Atc.Graph.Tree." ++ name ++ ": 頂点 " ++ show v ++ " が範囲外")
  | otherwise = ()
{-# INLINE lcaCheck #-}

-- | 深さ (根からの辺の本数)。O(1)。
depthLCA ::
  -- | @v@: 頂点
  Int ->
  -- | LCA の表
  LCA ->
  -- | @v@ の深さ
  Int
depthLCA v t@(LCA rt _) = lcaCheck "depthLCA" v t `seq` U.unsafeIndex (rtDepth rt) v

-- | 親。根なら -1。O(1)。
parentLCA ::
  -- | @v@: 頂点
  Int ->
  -- | LCA の表
  LCA ->
  -- | @v@ の親 (根なら -1)
  Int
parentLCA v t@(LCA rt _) = lcaCheck "parentLCA" v t `seq` U.unsafeIndex (rtParent rt) v

-- | 根付きの形 ('rtOrder' などで中身を見る)。
rootedLCA :: LCA -> RootedTree
rootedLCA (LCA rt _) = rt

-- | @v@ から @k@ 回親に上った頂点。根を越えれば -1。@k = 0@ なら @v@。O(log n)。
ancestorLCA ::
  -- | @k@: 上る回数 (0 以上)
  Int ->
  -- | @v@: 始める頂点
  Int ->
  -- | LCA の表
  LCA ->
  -- | @k@ 個上の祖先 (根を越えれば -1)
  Int
ancestorLCA k v0 t@(LCA _ ups)
  | k < 0 = error "Atc.Graph.Tree.ancestorLCA: 負の回数"
  | k >= 2 ^ V.length ups = lcaCheck "ancestorLCA" v0 t `seq` (-1)
  | otherwise = lcaCheck "ancestorLCA" v0 t `seq` go 0 v0
  where
    go !i !v
      | v == -1 || i >= V.length ups = v
      | testBit k i = go (i + 1) (U.unsafeIndex (V.unsafeIndex ups i) v)
      | otherwise = go (i + 1) v

-- | 最小共通祖先。違う成分 (森) なら -1。O(log n)。
lcaOf ::
  -- | @u@: 頂点
  Int ->
  -- | @v@: 頂点
  Int ->
  -- | LCA の表
  LCA ->
  -- | @u@ と @v@ の最小共通祖先 (違う成分なら -1)
  Int
lcaOf u0 v0 t@(LCA rt ups) = lcaCheck "lcaOf" u0 t `seq` lcaCheck "lcaOf" v0 t `seq` result
  where
    dep = rtDepth rt
    (du, dv) = (U.unsafeIndex dep u0, U.unsafeIndex dep v0)
    -- 深い方を同じ深さまで上げてから、祖先が分かれる直前まで一緒に上る。
    (a, b) = if du >= dv then (ancestorLCA (du - dv) u0 t, v0) else (u0, ancestorLCA (dv - du) v0 t)
    climb i x y
      | i < 0 = (x, y)
      | otherwise =
          let row = V.unsafeIndex ups i
              x' = U.unsafeIndex row x
              y' = U.unsafeIndex row y
           in if x' /= y' then climb (i - 1) x' y' else climb (i - 1) x y
    result
      | a == b = a
      | otherwise =
          let (x, y) = climb (V.length ups - 1) a b
              px = U.unsafeIndex (rtParent rt) x
           in if px == U.unsafeIndex (rtParent rt) y then px else -1

-- | @u@ と @v@ の間の辺の本数。違う成分なら -1。O(log n)。
distanceLCA ::
  -- | @u@: 頂点
  Int ->
  -- | @v@: 頂点
  Int ->
  -- | LCA の表
  LCA ->
  -- | 辺の本数 (違う成分なら -1)
  Int
distanceLCA u v t@(LCA rt _) = case lcaOf u v t of
  -1 -> -1
  w -> U.unsafeIndex dep u + U.unsafeIndex dep v - 2 * U.unsafeIndex dep w
  where
    dep = rtDepth rt

-- | @u@ と @v@ の間の重みの和。違う成分なら 'Nothing'。O(log n)。
weightedDistanceLCA ::
  -- | @u@: 頂点
  Int ->
  -- | @v@: 頂点
  Int ->
  -- | LCA の表
  LCA ->
  -- | 重みの和 (違う成分なら 'Nothing')
  Maybe Int
weightedDistanceLCA u v t@(LCA rt _) = case lcaOf u v t of
  -1 -> Nothing
  w -> Just (U.unsafeIndex d u + U.unsafeIndex d v - 2 * U.unsafeIndex d w)
  where
    d = rtDist rt

-- | @u@ から @v@ への道の頂点 (両端を含む)。違う成分なら空。O(道の長さ + log n)。
pathLCA ::
  -- | @u@: 始点
  Int ->
  -- | @v@: 終点
  Int ->
  -- | LCA の表
  LCA ->
  -- | @u@ から @v@ への道の頂点 (両端を含む。違う成分なら空)
  [Int]
pathLCA u v t@(LCA rt _) = case lcaOf u v t of
  -1 -> []
  w -> upTo u w ++ reverse (init' (upTo v w))
  where
    par = rtParent rt
    upTo x w = if x == w then [w] else x : upTo (U.unsafeIndex par x) w
    init' xs = take (length xs - 1) xs

-- ---------------------------------------------------------------------
-- 全方位木 DP

-- | 各頂点を根にしたときの木 DP の値。森なら成分ごとに計算する。無向グラフ用。
-- O(n) 回 @merge@ / @up@ / @finish@ を呼ぶ。
rerootDP ::
  (GraphKind g) =>
  -- | @merge a1 a2@: 子から集めた値 @a@ どうしをまとめる結合的な演算 (可換でなくてよい)
  (a -> a -> a) ->
  -- | @e@: @merge@ の単位元 (子がないときの値)
  a ->
  -- | @up v c w b@: 隣の頂点 @c@ 側の部分木の値 @b@ を、辺 @v - c@ (重み @w@) を通して
  -- @v@ から見た値 @a@ にする。@v@ は見ている側 (今の根に近い側) で、元の木の親とは限らない
  (Int -> Int -> Int -> b -> a) ->
  -- | @finish v a@: 子から集めた値 @a@ から、頂点 @v@ の部分木の値 @b@ を作る
  (Int -> a -> b) ->
  -- | 無向グラフ (木または森)
  g ->
  -- | 頂点 @v@ を根にしたときの値 (頂点番号で引く)
  GraphRet g (V.Vector b)
rerootDP merge e up finish g = primGraph g (rerootDPC merge e up finish)

-- | 'rerootDP' の本体。
rerootDPC :: (a -> a -> a) -> a -> (Int -> Int -> Int -> b -> a) -> (Int -> a -> b) -> AtcGraph -> V.Vector b
rerootDPC merge e up finish g = runST $ do
  -- 1. 葉から: down v = v を根とする部分木の値。
  down <- VM.new n
  U.forM_ (U.reverse order) $ \v -> do
    let p = U.unsafeIndex par v
        go !acc [] = pure acc
        go acc ((c, w) : rest)
          | c == p = go acc rest
          | otherwise = VM.read down c >>= \x -> go (merge acc $! up v c w x) rest
    acc <- go e (U.toList (adjacent g v))
    VM.write down v $! finish v acc
  -- 2. 根から: fromParent v = 親の側 (v を除いた残り) を v から見た値。
  fromParent <- VM.replicate n e
  res <- VM.new n
  U.forM_ order $ \v -> do
    let p = U.unsafeIndex par v
    pv <- if p == -1 then pure Nothing else Just <$> VM.read fromParent v
    -- 子 (隣接の順) から来る値と、親から来る値。
    kids <- V.forM (V.fromList [(c, w) | (c, w) <- U.toList (adjacent g v), c /= p]) $ \(c, w) -> do
      dc <- VM.read down c
      pure (c, w, up v c w $! dc)
    let vals = V.map (\(_, _, x) -> x) kids
        -- i より前の累積と、i より後ろの累積 (親の値は最後に付ける)。
        pre = V.prescanl' merge e vals
        suf = V.prescanr' merge e vals
        tailVal = maybe e id pv
    VM.write res v $! finish v (merge (V.foldl' merge e vals) tailVal)
    V.iforM_ kids $ \i (c, _, _) -> do
      -- c を除いた v の値を、c から見た値にする。
      let without = merge (merge (V.unsafeIndex pre i) (V.unsafeIndex suf i)) tailVal
          wc = U.unsafeIndex pw c
      VM.write fromParent c $! up c v wc $! finish v $! without
  V.freeze res
  where
    n = numVertices g
    rt = rootTreeC g 0
    order = rtOrder rt
    par = rtParent rt
    pw = rtParentWeight rt
