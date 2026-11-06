{-# LANGUAGE BangPatterns #-}

-- | 一般のグラフの単純閉路。
--
-- 有向か無向かはグラフが覚えている ('graphDirection') ので、関数は向きによらず同じ。
-- 'AtcGraph' にも 'MGraph' にも使える ('MGraph' なら返り値は @m@ の中に入る)。
-- Functional Graph なら "Atc.Graph.Functional" の 'Atc.Graph.Functional.cyclesFG' のほうが速い。
--
-- > let g = undirectedGraph (fromOneBased es)
-- > findCycle g            -- 閉路を 1 つ
-- > shortestCycle g        -- 最短閉路の (長さ, 頂点列)
-- > longestCycle g         -- 最長閉路の (長さ, 頂点列)
-- > countCycles g          -- 単純閉路の個数
-- > shortestCycleFrom g 0  -- 頂点 0 を通るものに限る。他の関数も …From で同じ
--
-- == 結果
--
-- 頂点列 @[v0, v1 .. vk-1]@ は辺 @v_i -> v_i+1@ と @vk-1 -> v0@ からなる閉路で、
-- @v0@ が閉路の最小の頂点。無向で長さ 3 以上なら、さらに @v1 < vk-1@ の向きに揃える。
-- 長さは辺の重みの和。重みのない辺は重み 1 なので、辺の本数になる。
--
-- == 計算量と制約
--
-- * 'findCycle' / 'findCycleFrom': O(n + m)。
-- * 'shortestCycleFrom': O(m log m)。'shortestCycle': O(nm log m)。重みは非負。
--   どれも自己ループは長さ 1 (重み 1 のとき)、多重辺は 2 本で閉路になる。
-- * 'longestCycle' / 'countCycles' と、その …From: O(2^n n^2)、@n@ は 18 程度まで。
--   単純グラフが前提で、自己ループは無視し、多重辺は 1 本 (最長は最大の重み) とみなす。
--   無向は長さ 3 以上で、向きの違いは 1 回だけ数える。有向は長さ 2 以上。
module Atc.Graph.Cycle where

import Atc.Graph
import Control.Monad (when)
import Control.Monad.ST (runST)
import Data.Bits (clearBit, countTrailingZeros, popCount, setBit, shiftL, testBit)
import Data.Function (on)
import Data.List (foldl', groupBy, sort)
import Data.Maybe (mapMaybe)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 結果の形

-- | 閉路の並びを、最小の頂点から始まる形に揃える。
canonCycle :: AtcGraph -> [Int] -> U.Vector Int
canonCycle g vs = case break (== minimum vs) vs of
  (before, m : after) -> U.fromList (m : turn (after ++ before))
  _ -> U.empty
  where
    turn xs
      | graphDirection g == Undirected && length xs >= 2 && head xs > last xs = reverse xs
      | otherwise = xs

-- | 長さが最小の (長さ, 中身)。空なら 'Nothing'。
minCycle :: [(Int, a)] -> Maybe (Int, a)
minCycle = foldl' step Nothing
  where
    step Nothing x = Just x
    step r@(Just (a, _)) x = if fst x < a then Just x else r

-- ---------------------------------------------------------------------
-- 1 つ見つける

-- | 閉路を 1 つ。なければ 'Nothing'。無向の親へ戻る辺は 1 本だけ飛ばす。O(n + m)。
{-# INLINE findCycle #-}
findCycle :: (GraphKind g) => g -> GraphRet g (Maybe (U.Vector Int))
findCycle g = primGraph g findCycleC

-- | 'findCycle' の本体。
findCycleC :: AtcGraph -> Maybe (U.Vector Int)
findCycleC g = fmap (canonCycle g) $ runST $ do
  -- 0 = 未訪問, 1 = 潜っている途中, 2 = 抜けた
  col <- UM.replicate n (0 :: Int)
  par <- UM.replicate n (-1)
  let -- 潜っている経路を v から w まで遡る。
      walk w v acc
        | v == w = pure (w : acc)
        | otherwise = UM.unsafeRead par v >>= \p -> walk w p (v : acc)
      dfs v p = do
        UM.unsafeWrite col v 1
        let ts = targetsOf g v
            go !i skip
              | i == U.length ts = pure Nothing
              | skip && U.unsafeIndex ts i == p = go (i + 1) False
              | otherwise = do
                  let w = U.unsafeIndex ts i
                  c <- UM.unsafeRead col w
                  case c of
                    0 -> do
                      UM.unsafeWrite par w v
                      dfs w v >>= maybe (go (i + 1) skip) (pure . Just)
                    1 -> Just <$> walk w v []
                    _ -> go (i + 1) skip
        r <- go (0 :: Int) (graphDirection g == Undirected && p >= 0)
        UM.unsafeWrite col v 2
        pure r
      loop s
        | s == n = pure Nothing
        | otherwise = do
            c <- UM.unsafeRead col s
            if c /= 0 then loop (s + 1) else dfs s (-1) >>= maybe (loop (s + 1)) (pure . Just)
  loop (0 :: Int)
  where
    n = numVertices g

-- | @s@ を通る閉路を 1 つ (辺の本数が最小のもの)。なければ 'Nothing'。O(n + m)。
{-# INLINE findCycleFrom #-}
findCycleFrom ::
  (GraphKind g) =>
  -- | グラフ (有向でも無向でも)
  g ->
  -- | @s@: 通る頂点
  Int ->
  -- | @s@ を通る閉路の頂点列 (なければ 'Nothing')
  GraphRet g (Maybe (U.Vector Int))
findCycleFrom g x = primGraph g (\c -> findCycleFromC c x)

-- | 'findCycleFrom' の本体。
findCycleFromC :: AtcGraph -> Int -> Maybe (U.Vector Int)
findCycleFromC g s = canonCycle g . snd <$> closeTree g units s (bfsDistPrev g [s])
  where
    units = [(u, v, 1) | (u, v, _) <- graphEdges g]

-- ---------------------------------------------------------------------
-- 最短

-- | @s@ からの最短路の木を辺で閉じて、@s@ を通る最短の閉路を作る。
--
-- 有向は @s@ へ入る辺で閉じる。無向は @s@ の直後の頂点 (枝) ごとに木を分け、
-- 違う枝をつなぐ辺で閉じる。違う枝の経路は @s@ でしか交わらないので単純閉路になる。
-- @s@ から出る辺は、木の辺でなければ閉じられる。同じ子への多重辺は軽い 2 本で閉じる。
closeTree :: AtcGraph -> [(Int, Int, Int)] -> Int -> (U.Vector Int, U.Vector Int) -> Maybe (Int, [Int])
closeTree g es s (dist, prev)
  | graphDirection g == Directed =
      minCycle [(dist U.! u + c, path u) | (u, v, c) <- es, v == s, reached u]
  | otherwise =
      minCycle $
        [(c, [s]) | (u, v, c) <- es, u == s, v == s]
          ++ [(c + dist U.! v, path v) | (v, c) <- fromS, branch V.! v /= v]
          ++ [(c1 + c2, [s, v]) | (v, c1) : (_, c2) : _ <- groupBy ((==) `on` fst) (sort fromS)]
          ++ [ (dist U.! u + c + dist U.! v, path u ++ reverse (tail (path v)))
             | (u, v, c) <- es,
               u < v,
               u /= s,
               v /= s,
               reached u,
               reached v,
               branch V.! u /= branch V.! v
             ]
  where
    n = numVertices g
    reached u = dist U.! u >= 0
    path = pathTo prev
    fromS = [(v, c) | (u, v, c) <- es, u == s, v /= s]
    -- 遅延評価のメモ。s の子なら自分、それ以外は親の枝。
    branch = V.generate n $ \v ->
      let p = prev U.! v in if p == s || p < 0 then v else branch V.! p

-- | @s@ を通る最短閉路の (長さ, 頂点列)。なければ 'Nothing'。重みは非負。O(m log m)。
{-# INLINE shortestCycleFrom #-}
shortestCycleFrom ::
  (GraphKind g) =>
  -- | グラフ (有向でも無向でも)
  g ->
  -- | @s@: 通る頂点
  Int ->
  -- | @s@ を通る最短閉路の (長さ, 頂点列) (なければ 'Nothing')
  GraphRet g (Maybe (Int, U.Vector Int))
shortestCycleFrom g x = primGraph g (\c -> shortestCycleFromC c x)

-- | 'shortestCycleFrom' の本体。
shortestCycleFromC :: AtcGraph -> Int -> Maybe (Int, U.Vector Int)
shortestCycleFromC g s = fmap (canonCycle g) <$> closeTree g (graphEdges g) s (dijkstraDistPrev g [s])

-- | 最短閉路の (長さ, 頂点列)。なければ 'Nothing'。重みは非負。O(nm log m)。
{-# INLINE shortestCycle #-}
shortestCycle :: (GraphKind g) => g -> GraphRet g (Maybe (Int, U.Vector Int))
shortestCycle g = primGraph g shortestCycleC

-- | 'shortestCycle' の本体。
shortestCycleC :: AtcGraph -> Maybe (Int, U.Vector Int)
shortestCycleC g = fmap (canonCycle g) <$> minCycle (mapMaybe from [0 .. numVertices g - 1])
  where
    es = graphEdges g
    from s = closeTree g es s (dijkstraDistPrev g [s])

-- ---------------------------------------------------------------------
-- 最長と個数 (ビット DP)
--
-- 閉路を最小の頂点から始まる経路として数える。@dp ! (S * n + v)@ は、@S@ の最小の頂点から
-- 始まり @S@ を全部通って @v@ で終わる経路の値。…From は @s@ と頂点 0 を入れ替えて、
-- 頂点 0 から始まる経路だけを見る。

-- | 頂点 s と 0 を入れ替える。
swapFirst :: Int -> Int -> Int
swapFirst s v
  | v == 0 = s
  | v == s = 0
  | otherwise = v

-- | 頂点 s と 0 を入れ替えた辺の一覧。
swappedEdges :: Int -> AtcGraph -> [(Int, Int, Int)]
swappedEdges s g = [(swapFirst s u, swapFirst s v, c) | (u, v, c) <- graphEdges g]

-- | 辺がないことを表す重み。
noArc :: Int
noArc = minBound

-- | 辺の重みの行列。自己ループは入れない。
arcMatrix :: Int -> [(Int, Int, Int)] -> U.Vector Int
arcMatrix n es = U.accum max (U.replicate (n * n) noArc) [(u * n + v, c) | (u, v, c) <- es, u /= v]

-- | 経路の値を v -> w に伸ばす @extend x 重み@ と、合流の @merge@ で表を埋める。
-- @none@ は届かない値、@one@ は長さ 0 の経路の値。
pathTable :: (Int -> Int -> Int) -> (Int -> Int -> Int) -> Int -> Int -> Bool -> Int -> U.Vector Int -> U.Vector Int
pathTable merge extend none one fixFirst n wm = U.create $ do
  dp <- UM.replicate (shiftL 1 n * n) none
  rep (if fixFirst then min 1 n else n) $ \s -> UM.write dp (shiftL 1 s * n + s) one
  rep (shiftL 1 n) $ \mask -> when (mask /= 0 && (not fixFirst || odd mask)) $ do
    let s = countTrailingZeros mask
    rep n $ \v -> when (testBit mask v) $ do
      x <- UM.unsafeRead dp (mask * n + v)
      when (x /= none) $ rep (n - s - 1) $ \i -> do
        let w = s + 1 + i
            c = U.unsafeIndex wm (v * n + w)
        when (not (testBit mask w) && c /= noArc) $
          UM.unsafeModify dp (merge (extend x c)) (setBit mask w * n + w)
  pure dp
{-# INLINE pathTable #-}

-- | 閉じられる経路 (S, v, 値, 閉じる辺の重み)。
closings :: AtcGraph -> Int -> Int -> U.Vector Int -> U.Vector Int -> [(Int, Int, Int, Int)]
closings g none n wm dp =
  [ (mask, v, x, c)
  | mask <- [1 .. shiftL 1 n - 1],
    popCount mask >= minLen,
    let s = countTrailingZeros mask,
    v <- [s + 1 .. n - 1],
    testBit mask v,
    let x = dp U.! (mask * n + v),
    x /= none,
    let c = wm U.! (v * n + s),
    c /= noArc
  ]
  where
    minLen = if graphDirection g == Directed then 2 else 3 :: Int

-- | 'countCycles' / 'countCyclesFrom' の共通の本体。
countBy :: Bool -> AtcGraph -> [(Int, Int, Int)] -> Int
countBy fixFirst g es = if graphDirection g == Directed then total else total `div` 2
  where
    n = numVertices g
    wm = arcMatrix n es
    total = sum [x | (_, _, x, _) <- closings g 0 n wm (pathTable (+) const 0 1 fixFirst n wm)]

-- | 'longestCycle' / 'longestCycleFrom' の共通の本体。
longestBy :: Bool -> AtcGraph -> [(Int, Int, Int)] -> Maybe (Int, [Int])
longestBy fixFirst g es = case closings g noArc n wm dp of
  [] -> Nothing
  cs ->
    let (best, mask, v) = foldl' (\r@(b, _, _) (m, u, x, c) -> if x + c > b then (x + c, m, u) else r) (noArc, 0, 0) cs
     in Just (best, walk mask v [])
  where
    n = numVertices g
    wm = arcMatrix n es
    dp = pathTable max (+) noArc 0 fixFirst n wm
    -- 値が合う直前の頂点を探して遡る。
    walk mask v acc
      | popCount mask == 1 = v : acc
      | otherwise =
          let m = clearBit mask v
              x = dp U.! (mask * n + v)
              fits u =
                let a = dp U.! (m * n + u)
                    c = wm U.! (u * n + v)
                 in testBit m u && a /= noArc && c /= noArc && a + c == x
           in walk m (head (filter fits [0 .. n - 1])) (v : acc)

-- | 最長閉路の (長さ, 頂点列)。なければ 'Nothing'。O(2^n n^2)。
{-# INLINE longestCycle #-}
longestCycle :: (GraphKind g) => g -> GraphRet g (Maybe (Int, U.Vector Int))
longestCycle g = primGraph g longestCycleC

-- | 'longestCycle' の本体。
longestCycleC :: AtcGraph -> Maybe (Int, U.Vector Int)
longestCycleC g = fmap (canonCycle g) <$> longestBy False g (graphEdges g)

-- | @s@ を通る最長閉路の (長さ, 頂点列)。なければ 'Nothing'。O(2^n n^2)。
{-# INLINE longestCycleFrom #-}
longestCycleFrom ::
  (GraphKind g) =>
  -- | グラフ (有向でも無向でも)
  g ->
  -- | @s@: 通る頂点
  Int ->
  -- | @s@ を通る最長閉路の (長さ, 頂点列) (なければ 'Nothing')
  GraphRet g (Maybe (Int, U.Vector Int))
longestCycleFrom g x = primGraph g (\c -> longestCycleFromC c x)

-- | 'longestCycleFrom' の本体。
longestCycleFromC :: AtcGraph -> Int -> Maybe (Int, U.Vector Int)
longestCycleFromC g s = fmap (canonCycle g . map (swapFirst s)) <$> longestBy True g (swappedEdges s g)

-- | 単純閉路の個数。O(2^n n^2)。
{-# INLINE countCycles #-}
countCycles :: (GraphKind g) => g -> GraphRet g Int
countCycles g = primGraph g countCyclesC

-- | 'countCycles' の本体。
countCyclesC :: AtcGraph -> Int
countCyclesC g = countBy False g (graphEdges g)

-- | @s@ を通る単純閉路の個数。O(2^n n^2)。
{-# INLINE countCyclesFrom #-}
countCyclesFrom ::
  (GraphKind g) =>
  -- | グラフ (有向でも無向でも)
  g ->
  -- | @s@: 通る頂点
  Int ->
  -- | @s@ を通る単純閉路の個数
  GraphRet g Int
countCyclesFrom g x = primGraph g (\c -> countCyclesFromC c x)

-- | 'countCyclesFrom' の本体。
countCyclesFromC :: AtcGraph -> Int -> Int
countCyclesFromC g s = countBy True g (swappedEdges s g)
