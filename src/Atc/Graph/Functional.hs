{-# LANGUAGE BangPatterns #-}

-- | Functional Graph: どの頂点からも辺がちょうど 1 本出ている有向グラフ。
--
-- グラフは "Atc.Graph" の 'AtcGraph' をそのまま使う。入力が行き先の並び
-- @a_1 .. a_N@ なら 'functionalGraph' で作る。辺の並びなら 'directedGraph'、
-- 0 始まりの行き先や重み付きなら 'graphFromList' で作ってよい。
-- 出次数が 1 でない頂点があれば、この節の関数は 'error' で止まる。
--
-- 各成分は閉路がちょうど 1 つで、そこへ木が流れ込む形をしている。
--
-- > a <- getInts
-- > let g = functionalGraph (U.fromList a)
-- > walkFG g 0 k      -- 頂点 0 から k 回進んだ頂点
-- > cyclesFG g        -- 閉路の一覧
-- > reachFG g         -- 各頂点から到達できる頂点数
--
-- 結果の頂点番号は "Atc.Graph" と同じく 0 始まり。出力するときは 1 を足す。
--
-- == K 回先の頂点
--
-- * 始点が 1 つなら 'walkFG'。1 回 O(n) で、@k@ がいくら大きくても変わらない。
-- * 始点が複数なら 'jumpTableFG' で表を作って 'jumpFG'。表は O(n log K)、1 回 O(log K)。
--
-- 経路上の和は、'weightedJumpTableFG' で辺の重みの表を作って 'foldJT' で求める。
-- 始点が 1 つなら、'rhoFG' の経路の累積和と周期からも求められる。
-- 表の中身は "Atc.JumpTable" で、'climbJT' などもそのまま使える。
--
-- == 閉路と木
--
-- * 'onCycleFG' / 'cyclesFG' / 'countCyclesFG': 閉路の判定・一覧・個数。
-- * 'peelOrderFG': 閉路にない頂点を葉から順に。
-- * 'foldTreesFG': 木の部分を葉から畳み込む。閉路は結果の値を使って 'cyclesFG' で処理する。
module Atc.Graph.Functional where

import Atc.Graph
import Atc.JumpTable
import Control.Monad (foldM)
import Control.Monad.ST (runST)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 作る

-- | 1 始まりの行き先の並び @a_1 .. a_N@ から作る。頂点 @i@ から @a_i@ への重み 1 の辺。
-- 行き先が範囲外なら 'error'。
functionalGraph :: U.Vector Int -> AtcGraph
functionalGraph a = graphFromList (U.length a) [(i, x - 1, 1) | (i, x) <- U.toList (U.indexed a)]

-- | 各頂点の行き先。出次数が 1 でない頂点があれば 'error'。O(n)。
nextVerticesFG :: AtcGraph -> U.Vector Int
nextVerticesFG g = case filter (\v -> outDegree g v /= 1) [0 .. n - 1] of
  v : _ -> error ("nextVerticesFG: 頂点 " ++ show v ++ " の出次数が 1 ではない")
  [] -> U.generate n (U.head . adjacentVertices g)
  where
    n = numVertices g

-- ---------------------------------------------------------------------
-- K 回先の頂点

-- | @k <= maxK@ の 'jumpFG' に使える表を作る。O(n log maxK)。
jumpTableFG :: AtcGraph -> Int -> JumpTable U.Vector ()
jumpTableFG g maxK = buildJT (\_ _ -> ()) maxK (nextVerticesFG g) (U.replicate (numVertices g) ())

-- | 辺の重みを @merge@ で合成する表を作る。'foldJT' / 'climbJT' で経路上の値を求める。
-- O(n log maxK)。
weightedJumpTableFG :: (Int -> Int -> Int) -> AtcGraph -> Int -> JumpTable U.Vector Int
weightedJumpTableFG merge g maxK =
  buildJT merge maxK (nextVerticesFG g) (U.generate (numVertices g) (U.head . adjacentWeights g))

-- | 頂点 @v@ から @k@ 回進んだ頂点。O(log k)。@k@ が表の範囲を超えると 'error'。
jumpFG :: JumpTable v w -> Int -> Int -> Int
jumpFG = jumpJT

-- | 頂点 @v@ からの経路 @(path, t, c)@。O(n)。
--
-- @path@ は同じ頂点に戻る直前までの頂点の列で、長さ @t + c@。
-- 先頭の @t@ 個が閉路に入るまでの部分、残りの @c@ 個が閉路。
rhoFG :: AtcGraph -> Int -> (U.Vector Int, Int, Int)
rhoFG g v0
  | v0 < 0 || v0 >= n = error ("rhoFG: 頂点が範囲外: " ++ show v0)
  | otherwise = runST $ do
      seen <- UM.replicate n (-1)
      buf <- UM.new n
      let go !i !v = do
            s <- UM.read seen v
            if s >= 0
              then do
                path <- U.freeze (UM.take i buf)
                pure (path, s, i - s)
              else do
                UM.write seen v i
                UM.write buf i v
                go (i + 1) (U.unsafeIndex f v)
      go (0 :: Int) v0
  where
    f = nextVerticesFG g
    n = U.length f

-- | 頂点 @v@ から @k@ 回進んだ頂点。O(n)。@k@ が負なら 'error'。
walkFG :: AtcGraph -> Int -> Int -> Int
walkFG g v k
  | k < 0 = error ("walkFG: k が負: " ++ show k)
  | k < t = path U.! k
  | otherwise = path U.! (t + (k - t) `mod` c)
  where
    (path, t, c) = rhoFG g v

-- ---------------------------------------------------------------------
-- 閉路と木

-- | 閉路にない頂点を、自分へ流れ込む頂点より後になる順に。O(n)。
peelOrderFG :: AtcGraph -> U.Vector Int
peelOrderFG g = U.create $ do
  deg <- UM.replicate n (0 :: Int)
  U.forM_ f (UM.modify deg (+ 1))
  que <- UM.new n
  let push !end v = do
        d <- UM.read deg v
        if d == 0 then UM.write que end v >> pure (end + 1) else pure end
      go !front !end
        | front >= end = pure end
        | otherwise = do
            v <- UM.read que front
            let u = U.unsafeIndex f v
            UM.modify deg (subtract 1) u
            push end u >>= go (front + 1)
  end <- U.foldM' push 0 (U.generate n id)
  size <- go 0 end
  pure (UM.take size que)
  where
    f = nextVerticesFG g
    n = U.length f

-- | 各頂点が閉路の上にあるか。O(n)。
onCycleFG :: AtcGraph -> U.Vector Bool
onCycleFG g = U.modify (\m -> U.forM_ (peelOrderFG g) $ \v -> UM.write m v False) (U.replicate (numVertices g) True)

-- | 閉路の一覧。各閉路は最小の頂点から @f@ の向きに並ぶ。O(n)。
cyclesFG :: AtcGraph -> V.Vector (U.Vector Int)
cyclesFG g = runST $ do
  let onCycle = onCycleFG g
      f = nextVerticesFG g
      n = numVertices g
  seen <- UM.replicate n False
  let collect acc s = do
        done <- UM.read seen s
        if not (onCycle U.! s) || done
          then pure acc
          else do
            let vs = s : takeWhile (/= s) (tail (iterate (f U.!) s))
            mapM_ (\v -> UM.write seen v True) vs
            pure (U.fromList vs : acc)
  V.fromList . reverse <$> foldM collect [] [0 .. n - 1]

-- | 閉路の個数。連結成分の個数と等しい。O(n)。
countCyclesFG :: AtcGraph -> Int
countCyclesFG = V.length . cyclesFG

-- | 各頂点から到達できる頂点数 (自分を含む)。O(n)。
--
-- 閉路の上なら周期、木の部分なら行き先の値 + 1。
reachFG :: AtcGraph -> U.Vector Int
reachFG g = U.create $ do
  let f = nextVerticesFG g
  r <- UM.replicate (numVertices g) 0
  V.forM_ (cyclesFG g) $ \c -> U.forM_ c $ \v -> UM.write r v (U.length c)
  U.forM_ (U.reverse (peelOrderFG g)) $ \v -> UM.read r (f U.! v) >>= UM.write r v . (+ 1)
  pure r

-- | 木の部分を葉から畳み込む。O(n)。
--
-- 頂点 @v@ の値は @initial v@ から始まり、閉路にない頂点 @u@ の値が確定すると
-- @u@ の行き先の値を @merge (行き先の値) (u の値)@ で更新する。閉路の上の頂点には
-- 流れ込む木の分までが入る。閉路の上の頂点どうしでは畳み込まない。
foldTreesFG :: (U.Unbox a) => AtcGraph -> (Int -> a) -> (a -> a -> a) -> U.Vector a
foldTreesFG g initial merge = U.create $ do
  let f = nextVerticesFG g
  dp <- U.thaw (U.generate (numVertices g) initial)
  U.forM_ (peelOrderFG g) $ \v -> do
    x <- UM.read dp v
    UM.modify dp (`merge` x) (f U.! v)
  pure dp
