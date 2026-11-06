{-# LANGUAGE BangPatterns #-}

-- | 最大流 (Dinic 法)・最小費用流 (主双対法)・二部マッチング。
--
-- どちらも可変で、@m@ は使うモナド (@IO@ か @ST s@)。頂点は @0 .. n - 1@。
-- 辺を足すと辺の番号 (足した順に 0, 1, ..) が返り、流した後に 'edgeMF' などで流量を見られる。
-- 流した後に辺を足して、続きを流してもよい (流量は積み上がる)。
--
-- > g <- newMF 4
-- > _ <- addEdgeMF 0 1 10 g          -- 0 -> 1 に容量 10
-- > ...
-- > f <- flowMF 0 3 g                -- 0 から 3 への最大流
-- > cut <- minCutMF 0 g              -- 最小カットの s 側 (残余グラフで 0 から行ける頂点)
-- >
-- > h <- newMCF 4
-- > _ <- addEdgeMCF 0 1 5 3 h        -- 容量 5、1 単位あたりの費用 3
-- > (f, c) <- flowLimitMCF 0 3 k h   -- k まで流したときの (流量, 最小費用)
-- > ps <- slopeMCF 0 3 maxBound h    -- 流量と最小費用の折れ線の頂点
--
-- 二部マッチングは 'maxBipartiteMatching' (中で最大流を使う)。
--
-- 計算量の目安: 最大流は O(n^2 m) だが実際はずっと速い (二部マッチングなら O(m √n))。
-- 最小費用流は O(流量 × m log n)。費用は非負であること。
module Atc.Graph.Flow where

import Control.Monad (forM_, when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST, runST)
import Data.Primitive.MutVar (MutVar, newMutVar, readMutVar, writeMutVar)
import qualified Data.Set as Set
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 辺の置き場 (最大流と最小費用流で共通)

-- | 辺の置き場。辺ごとの配列は足りなくなると 2 倍に広げる。
data FlowEdges s
  = FlowEdges
      -- | 辺の数 (長さ 1)
      !(UM.MVector s Int)
      -- | 辺ごとの出発点
      !(UM.MVector s Int)
      -- | 辺ごとの行き先
      !(UM.MVector s Int)
      -- | 辺ごとの容量
      !(UM.MVector s Int)
      -- | 辺ごとの流量
      !(UM.MVector s Int)
      -- | 辺ごとの費用
      !(UM.MVector s Int)

-- | 辺のない置き場を作る。
{-# INLINE flNew #-}
flNew :: (PrimMonad m) => m (MutVar (PrimState m) (FlowEdges (PrimState m)))
flNew = do
  c <- UM.replicate 1 0
  es <- FlowEdges c <$> UM.unsafeNew 4 <*> UM.unsafeNew 4 <*> UM.unsafeNew 4 <*> UM.unsafeNew 4 <*> UM.unsafeNew 4
  newMutVar es

-- | 辺の数。
{-# INLINE flCount #-}
flCount :: (PrimMonad m) => MutVar (PrimState m) (FlowEdges (PrimState m)) -> m Int
flCount r = do
  FlowEdges c _ _ _ _ _ <- readMutVar r
  UM.unsafeRead c 0

-- | 辺を足して辺の番号を返す ('addEdgeMF' / 'addEdgeMCF' の本体)。範囲外の頂点や負の容量は関数名付きで 'error'。
{-# INLINABLE flAdd #-}
{-# SPECIALIZE flAdd :: String -> Int -> MutVar (PrimState IO) (FlowEdges (PrimState IO)) -> Int -> Int -> Int -> Int -> IO Int #-}
{-# SPECIALIZE flAdd :: String -> Int -> MutVar (PrimState (ST s)) (FlowEdges (PrimState (ST s))) -> Int -> Int -> Int -> Int -> (ST s) Int #-}
flAdd :: (PrimMonad m) => String -> Int -> MutVar (PrimState m) (FlowEdges (PrimState m)) -> Int -> Int -> Int -> Int -> m Int
flAdd name n r u v cap cost = do
  when (u < 0 || u >= n || v < 0 || v >= n) $ error ("Atc.Graph.Flow." ++ name ++ ": 頂点が範囲外 " ++ show (u, v))
  when (cap < 0) $ error ("Atc.Graph.Flow." ++ name ++ ": 負の容量")
  FlowEdges c fr to cp fl co <- readMutVar r
  k <- UM.unsafeRead c 0
  FlowEdges _ fr' to' cp' fl' co' <-
    if k < UM.length fr
      then pure (FlowEdges c fr to cp fl co)
      else do
        let extra = UM.length fr
        es' <- FlowEdges c <$> UM.grow fr extra <*> UM.grow to extra <*> UM.grow cp extra <*> UM.grow fl extra <*> UM.grow co extra
        writeMutVar r es'
        pure es'
  UM.unsafeWrite fr' k u
  UM.unsafeWrite to' k v
  UM.unsafeWrite cp' k cap
  UM.unsafeWrite fl' k 0
  UM.unsafeWrite co' k cost
  UM.unsafeWrite c 0 (k + 1)
  pure k

-- | 辺の @(出発点, 行き先, 容量, 流量)@ ('edgeMF' / 'edgeMCF' の本体)。範囲外の番号は関数名付きで 'error'。
{-# INLINE flEdge #-}
flEdge :: (PrimMonad m) => String -> MutVar (PrimState m) (FlowEdges (PrimState m)) -> Int -> m (Int, Int, Int, Int)
flEdge name r i = do
  FlowEdges c fr to cp fl _ <- readMutVar r
  k <- UM.unsafeRead c 0
  when (i < 0 || i >= k) $ error ("Atc.Graph.Flow." ++ name ++ ": 辺の番号が範囲外 " ++ show i)
  (,,,) <$> UM.unsafeRead fr i <*> UM.unsafeRead to i <*> UM.unsafeRead cp i <*> UM.unsafeRead fl i

-- | 残余グラフ: 辺 k の順向きの弧と逆向きの弧を、出発点ごとに並べる (CSR)。
data Residual s
  = Residual
      -- | 出発点ごとの開始位置 (長さ n + 1)
      !(U.Vector Int)
      -- | 弧の行き先
      !(U.Vector Int)
      -- | 弧の残り容量 (可変)
      !(UM.MVector s Int)
      -- | 対になる弧の位置
      !(U.Vector Int)
      -- | 弧の費用
      !(U.Vector Int)
      -- | 辺 k の順向きの弧の位置
      !(U.Vector Int)

-- | 辺の置き場と今の流量から残余グラフを作る。
{-# INLINABLE flResidual #-}
{-# SPECIALIZE flResidual :: Int -> MutVar (PrimState IO) (FlowEdges (PrimState IO)) -> IO (Residual (PrimState IO)) #-}
{-# SPECIALIZE flResidual :: Int -> MutVar (PrimState (ST s)) (FlowEdges (PrimState (ST s))) -> (ST s) (Residual (PrimState (ST s))) #-}
flResidual :: (PrimMonad m) => Int -> MutVar (PrimState m) (FlowEdges (PrimState m)) -> m (Residual (PrimState m))
flResidual n r = do
  FlowEdges c fr to cp fl co <- readMutVar r
  k <- UM.unsafeRead c 0
  frs <- U.freeze (UM.slice 0 k fr)
  tos <- U.freeze (UM.slice 0 k to)
  cps <- U.freeze (UM.slice 0 k cp)
  fls <- U.freeze (UM.slice 0 k fl)
  cos' <- U.freeze (UM.slice 0 k co)
  let deg = U.accumulate (+) (U.replicate n 0) (U.map (\u -> (u, 1)) (frs U.++ tos))
      start = U.scanl' (+) 0 deg
      -- 弧 2k は順向き (出発点 from)、2k + 1 は逆向き (出発点 to)。出発点ごとに番号順に置く。
      srcOf a = if even a then frs U.! (a `div` 2) else tos U.! (a `div` 2)
      posOf = U.create $ do
        p <- U.thaw start
        out <- UM.unsafeNew (2 * k)
        forM_ [0 .. 2 * k - 1] $ \a -> do
          let u = srcOf a
          q <- UM.unsafeRead p u
          UM.unsafeWrite p u (q + 1)
          UM.unsafeWrite out a q
        pure out
      place f = U.update (U.replicate (2 * k) 0) (U.generate (2 * k) (\a -> (posOf U.! a, f a)))
      arcTo = place (\a -> if even a then tos U.! (a `div` 2) else frs U.! (a `div` 2))
      arcRev = place (\a -> posOf U.! (if even a then a + 1 else a - 1))
      arcCost = place (\a -> let e = cos' U.! (a `div` 2) in if even a then e else negate e)
      res0 = place (\a -> let e = a `div` 2 in if even a then cps U.! e - fls U.! e else fls U.! e)
      fwd = U.generate k (\e -> posOf U.! (2 * e))
  res <- U.thaw res0
  pure (Residual start arcTo res arcRev arcCost fwd)

-- | 流した結果を辺の流量に書き戻す。
{-# INLINE flWriteBack #-}
flWriteBack :: (PrimMonad m) => MutVar (PrimState m) (FlowEdges (PrimState m)) -> Residual (PrimState m) -> m ()
flWriteBack r (Residual _ _ res _ _ fwd) = do
  FlowEdges _ _ _ cp fl _ <- readMutVar r
  U.iforM_ fwd $ \e a -> do
    c <- UM.unsafeRead cp e
    left <- UM.unsafeRead res a
    UM.unsafeWrite fl e (c - left)

-- ---------------------------------------------------------------------
-- 最大流

-- | 最大流のグラフ。
data MaxFlow m
  = MaxFlow
      -- | 頂点数
      !Int
      -- | 辺の置き場
      !(MutVar (PrimState m) (FlowEdges (PrimState m)))

-- | 頂点数 @n@ で辺のないグラフ。
{-# INLINE newMF #-}
newMF :: (PrimMonad m) => Int -> m (MaxFlow m)
newMF n = MaxFlow n <$> flNew

-- | 辺を足す。O(1) (ならし)。
{-# INLINE addEdgeMF #-}
addEdgeMF ::
  (PrimMonad m) =>
  -- | @u@: 出発点
  Int ->
  -- | @v@: 行き先
  Int ->
  -- | @cap@: 容量 (非負)
  Int ->
  -- | グラフ
  MaxFlow m ->
  -- | 足した辺の番号 (足した順に 0, 1, ..)
  m Int
addEdgeMF u v cap (MaxFlow n r) = flAdd "addEdgeMF" n r u v cap 0

-- | 流せるだけ流す。
{-# INLINE flowMF #-}
flowMF ::
  (PrimMonad m) =>
  -- | @s@: 流し始める頂点
  Int ->
  -- | @t@: 流し込む頂点 (@s@ とは別)
  Int ->
  -- | グラフ
  MaxFlow m ->
  -- | 新しく流した量
  m Int
flowMF s t = flowLimitMF s t maxBound

-- | 上限を決めて流す。
{-# INLINABLE flowLimitMF #-}
{-# SPECIALIZE flowLimitMF :: Int -> Int -> Int -> MaxFlow IO -> IO Int #-}
{-# SPECIALIZE flowLimitMF :: Int -> Int -> Int -> MaxFlow (ST s) -> (ST s) Int #-}
flowLimitMF ::
  (PrimMonad m) =>
  -- | @s@: 流し始める頂点
  Int ->
  -- | @t@: 流し込む頂点 (@s@ とは別)
  Int ->
  -- | @limit@: 今回合わせて流す量の上限
  Int ->
  -- | グラフ
  MaxFlow m ->
  -- | 新しく流した量
  m Int
flowLimitMF s t limit (MaxFlow n r) = do
  when (s < 0 || s >= n || t < 0 || t >= n || s == t) $ error "Atc.Graph.Flow.flowLimitMF: s と t は範囲内で別の頂点"
  rg@(Residual start arcTo res arcRev _ _) <- flResidual n r
  level <- UM.replicate n (-1 :: Int)
  iter <- UM.unsafeNew n
  que <- UM.unsafeNew n
  let bfs = do
        UM.set level (-1)
        UM.unsafeWrite level s 0
        UM.unsafeWrite que 0 s
        -- t に届いたら止める (t より深い頂点は使わない)。
        let go !hd !tl = when (hd < tl) $ do
              reached <- UM.unsafeRead level t
              when (reached == -1) $ go1 hd tl
            go1 !hd !tl = do
              v <- UM.unsafeRead que hd
              lv <- UM.unsafeRead level v
              let visit !tl' a = do
                    c <- UM.unsafeRead res a
                    let w = U.unsafeIndex arcTo a
                    lw <- UM.unsafeRead level w
                    if c > 0 && lw == -1
                      then UM.unsafeWrite level w (lv + 1) >> UM.unsafeWrite que tl' w >> pure (tl' + 1)
                      else pure tl'
              tl2 <- U.foldM' visit tl (U.enumFromN (U.unsafeIndex start v) (U.unsafeIndex start (v + 1) - U.unsafeIndex start v))
              go (hd + 1) tl2
        go 0 1
        (/= -1) <$> UM.unsafeRead level t
      -- v から t へ、f まで流す。流した量を返す。t より浅い頂点 (と t) だけを通る。
      dfs lt v f
        | v == t = pure f
        | otherwise = do
            lv <- UM.unsafeRead level v
            let loop !pushed
                  | pushed == f = pure pushed
                  | otherwise = do
                      i <- UM.unsafeRead iter v
                      if i == U.unsafeIndex start (v + 1)
                        then pure pushed
                        else do
                          c <- UM.unsafeRead res i
                          let w = U.unsafeIndex arcTo i
                          lw <- UM.unsafeRead level w
                          if c > 0 && lw == lv + 1 && (w == t || lw < lt)
                            then do
                              let req = min (f - pushed) c
                              d <- dfs lt w req
                              when (d > 0) $ do
                                UM.unsafeModify res (subtract d) i
                                UM.unsafeModify res (+ d) (U.unsafeIndex arcRev i)
                              -- 行き止まりか、辺を使い切ったら次の辺へ。
                              when (d < req || d == c) $ UM.unsafeWrite iter v (i + 1)
                              loop (pushed + d)
                            else UM.unsafeWrite iter v (i + 1) >> loop pushed
            loop 0
      phases !total
        | total >= limit = pure total
        | otherwise = do
            ok <- bfs
            if not ok
              then pure total
              else do
                forM_ [0 .. n - 1] $ \v -> UM.unsafeWrite iter v (U.unsafeIndex start v)
                lt <- UM.unsafeRead level t
                let push !acc = do
                      f <- dfs lt s (limit - acc)
                      if f == 0 then pure acc else push (acc + f)
                total' <- push total
                if total' == total then pure total else phases total'
  total <- phases 0
  flWriteBack r rg
  pure total

-- | 最小カット。流した後に呼ぶ。O(n + m)。
{-# INLINABLE minCutMF #-}
{-# SPECIALIZE minCutMF :: Int -> MaxFlow IO -> IO (U.Vector Bool) #-}
{-# SPECIALIZE minCutMF :: Int -> MaxFlow (ST s) -> (ST s) (U.Vector Bool) #-}
minCutMF ::
  (PrimMonad m) =>
  -- | @s@: 流し始めた頂点
  Int ->
  -- | グラフ
  MaxFlow m ->
  -- | 残余グラフで @s@ から行ける頂点が 'True' (最小カットの @s@ 側。頂点番号で引く)
  m (U.Vector Bool)
minCutMF s (MaxFlow n r) = do
  Residual start arcTo res _ _ _ <- flResidual n r
  resV <- U.freeze res
  pure $ U.create $ do
    seen <- UM.replicate n False
    UM.write seen s True
    let go [] = pure ()
        go (v : rest) = do
          new <- fmap concat $ mapM (\a -> do
              let w = U.unsafeIndex arcTo a
              sw <- UM.unsafeRead seen w
              if U.unsafeIndex resV a > 0 && not sw then UM.unsafeWrite seen w True >> pure [w] else pure []) [U.unsafeIndex start v .. U.unsafeIndex start (v + 1) - 1]
          go (new ++ rest)
    go [s]
    pure seen

-- | 1 本の辺の今の様子。
{-# INLINE edgeMF #-}
edgeMF ::
  (PrimMonad m) =>
  -- | @i@: 辺の番号 ('addEdgeMF' が返したもの)
  Int ->
  -- | グラフ
  MaxFlow m ->
  -- | 辺 @i@ の @(出発点, 行き先, 容量, 流量)@
  m (Int, Int, Int, Int)
edgeMF i (MaxFlow _ r) = flEdge "edgeMF" r i

-- | 全ての辺の @(出発点, 行き先, 容量, 流量)@ (足した順)。
{-# INLINE edgesMF #-}
edgesMF :: (PrimMonad m) => MaxFlow m -> m (U.Vector (Int, Int, Int, Int))
edgesMF (MaxFlow _ r) = do
  k <- flCount r
  U.generateM k (flEdge "edgesMF" r)

-- | 二部マッチング: 最大マッチングを 1 つ求める。O(m √(l + r))。
maxBipartiteMatching ::
  -- | @l@: 左の頂点数 (左は @0 .. l - 1@)
  Int ->
  -- | @r@: 右の頂点数 (右は @0 .. r - 1@)
  Int ->
  -- | @es@: 左と右の間の辺 @(左, 右)@
  [(Int, Int)] ->
  -- | 最大マッチングの組 @(左, 右)@ (@es@ の中の順)
  [(Int, Int)]
maxBipartiteMatching l r es = runST $ do
  g <- newMF (l + r + 2)
  let s = l + r
      t = l + r + 1
  forM_ es $ \(a, b) -> do
    when (a < 0 || a >= l || b < 0 || b >= r) $ error "Atc.Graph.Flow.maxBipartiteMatching: 頂点が範囲外"
  ids <- mapM (\(a, b) -> addEdgeMF a (l + b) 1 g) es
  forM_ [0 .. l - 1] $ \a -> addEdgeMF s a 1 g
  forM_ [0 .. r - 1] $ \b -> addEdgeMF (l + b) t 1 g
  _ <- flowMF s t g
  used <- mapM (\i -> (\(_, _, _, f) -> f > 0) <$> edgeMF i g) ids
  pure [e | (e, True) <- zip es used]

-- ---------------------------------------------------------------------
-- 最小費用流

-- | 最小費用流のグラフ。
data MinCostFlow m
  = MinCostFlow
      -- | 頂点数
      !Int
      -- | 辺の置き場
      !(MutVar (PrimState m) (FlowEdges (PrimState m)))

-- | 頂点数 @n@ で辺のないグラフ。
{-# INLINE newMCF #-}
newMCF :: (PrimMonad m) => Int -> m (MinCostFlow m)
newMCF n = MinCostFlow n <$> flNew

-- | 辺を足す。
{-# INLINE addEdgeMCF #-}
addEdgeMCF ::
  (PrimMonad m) =>
  -- | @u@: 出発点
  Int ->
  -- | @v@: 行き先
  Int ->
  -- | @cap@: 容量 (非負)
  Int ->
  -- | @cost@: 1 単位あたりの費用 (非負)
  Int ->
  -- | グラフ
  MinCostFlow m ->
  -- | 足した辺の番号 (足した順に 0, 1, ..)
  m Int
addEdgeMCF u v cap cost (MinCostFlow n r) = do
  when (cost < 0) $ error "Atc.Graph.Flow.addEdgeMCF: 費用は非負"
  flAdd "addEdgeMCF" n r u v cap cost

-- | 流せるだけ流す。
{-# INLINE flowMCF #-}
flowMCF ::
  (PrimMonad m) =>
  -- | @s@: 流し始める頂点
  Int ->
  -- | @t@: 流し込む頂点 (@s@ とは別)
  Int ->
  -- | グラフ
  MinCostFlow m ->
  -- | 流せるだけ流したときの @(流量, 最小費用)@
  m (Int, Int)
flowMCF s t = flowLimitMCF s t maxBound

-- | 上限を決めて流す。
{-# INLINE flowLimitMCF #-}
flowLimitMCF ::
  (PrimMonad m) =>
  -- | @s@: 流し始める頂点
  Int ->
  -- | @t@: 流し込む頂点 (@s@ とは別)
  Int ->
  -- | @limit@: 流す量の上限
  Int ->
  -- | グラフ
  MinCostFlow m ->
  -- | @limit@ まで流したときの @(流量, 最小費用)@
  m (Int, Int)
flowLimitMCF s t limit g = last <$> slopeMCF s t limit g

-- | 流量と最小費用の関係の折れ線。何度か呼ぶと続きから流す (返る値は今回の分)。
{-# INLINABLE slopeMCF #-}
{-# SPECIALIZE slopeMCF :: Int -> Int -> Int -> MinCostFlow IO -> IO [(Int, Int)] #-}
{-# SPECIALIZE slopeMCF :: Int -> Int -> Int -> MinCostFlow (ST s) -> (ST s) [(Int, Int)] #-}
slopeMCF ::
  (PrimMonad m) =>
  -- | @s@: 流し始める頂点
  Int ->
  -- | @t@: 流し込む頂点 (@s@ とは別)
  Int ->
  -- | @limit@: 流す量の上限 (@maxBound@ なら流せるだけ)
  Int ->
  -- | グラフ
  MinCostFlow m ->
  -- | 折れ線の頂点 @[(0, 0), (f_1, c_1), ..]@。流量 @f_i@ から @f_{i+1}@ の間は費用が直線で増える
  -- (傾きは増えていく)。最後の点が @limit@ まで (流せるだけ) 流したとき
  m [(Int, Int)]
slopeMCF s t limit (MinCostFlow n r) = do
  when (s < 0 || s >= n || t < 0 || t >= n || s == t) $ error "Atc.Graph.Flow.slopeMCF: s と t は範囲内で別の頂点"
  rg@(Residual start arcTo res arcRev arcCost _) <- flResidual n r
  dual <- UM.replicate n 0
  dist <- UM.replicate n (0 :: Int)
  prevArc <- UM.unsafeNew n
  vis <- UM.replicate n False
  let inf = maxBound :: Int
      -- 被約費用 (cost - dual[to] + dual[from]) で Dijkstra。t まで届いたら、確定した頂点の dual を直す。
      dualRef = do
        UM.set dist inf
        UM.set vis False
        UM.unsafeWrite dist s 0
        let go q
              | Set.null q = pure ()
              | otherwise = do
                  let ((d, v), q') = Set.deleteFindMin q
                  seen <- UM.unsafeRead vis v
                  dv <- UM.unsafeRead dist v
                  if seen || d > dv
                    then go q'
                    else do
                      UM.unsafeWrite vis v True
                      if v == t
                        then pure ()
                        else do
                          duv <- UM.unsafeRead dual v
                          let relax qq a = do
                                c <- UM.unsafeRead res a
                                if c == 0
                                  then pure qq
                                  else do
                                    let w = U.unsafeIndex arcTo a
                                    duw <- UM.unsafeRead dual w
                                    dw <- UM.unsafeRead dist w
                                    let nd = dv + U.unsafeIndex arcCost a - duw + duv
                                    if nd < dw
                                      then UM.unsafeWrite dist w nd >> UM.unsafeWrite prevArc w a >> pure (Set.insert (nd, w) qq)
                                      else pure qq
                          q'' <- U.foldM' relax q' (U.enumFromN (U.unsafeIndex start v) (U.unsafeIndex start (v + 1) - U.unsafeIndex start v))
                          go q''
        go (Set.singleton (0, s))
        vt <- UM.unsafeRead vis t
        if not vt
          then pure False
          else do
            dt <- UM.unsafeRead dist t
            forM_ [0 .. n - 1] $ \v -> do
              b <- UM.unsafeRead vis v
              when b $ do
                dv <- UM.unsafeRead dist v
                UM.unsafeModify dual (subtract (dt - dv)) v
            pure True
      -- t から prevArc を辿る。
      walk v f
        | v == s = pure f
        | otherwise = do
            a <- UM.unsafeRead prevArc v
            c <- UM.unsafeRead res a
            walk (U.unsafeIndex arcTo (U.unsafeIndex arcRev a)) (min f c)
      apply v c = when (v /= s) $ do
        a <- UM.unsafeRead prevArc v
        UM.unsafeModify res (subtract c) a
        UM.unsafeModify res (+ c) (U.unsafeIndex arcRev a)
        apply (U.unsafeIndex arcTo (U.unsafeIndex arcRev a)) c
      loop !flow !cost !prevD acc
        | flow >= limit = pure (reverse acc)
        | otherwise = do
            ok <- dualRef
            if not ok
              then pure (reverse acc)
              else do
                c <- walk t (limit - flow)
                apply t c
                ds <- UM.unsafeRead dual s
                let d = negate ds
                    flow' = flow + c
                    cost' = cost + c * d
                    acc' = (flow', cost') : (if prevD == Just d then drop 1 acc else acc)
                loop flow' cost' (Just d) acc'
  pts <- loop 0 0 Nothing [(0, 0)]
  flWriteBack r rg
  pure pts

-- | 1 本の辺の今の様子。
{-# INLINE edgeMCF #-}
edgeMCF ::
  (PrimMonad m) =>
  -- | @i@: 辺の番号 ('addEdgeMCF' が返したもの)
  Int ->
  -- | グラフ
  MinCostFlow m ->
  -- | 辺 @i@ の @(出発点, 行き先, 容量, 流量)@
  m (Int, Int, Int, Int)
edgeMCF i (MinCostFlow _ r) = flEdge "edgeMCF" r i

-- | 全ての辺の @(出発点, 行き先, 容量, 流量)@ (足した順)。
{-# INLINE edgesMCF #-}
edgesMCF :: (PrimMonad m) => MinCostFlow m -> m (U.Vector (Int, Int, Int, Int))
edgesMCF (MinCostFlow _ r) = do
  k <- flCount r
  U.generateM k (flEdge "edgesMCF" r)
