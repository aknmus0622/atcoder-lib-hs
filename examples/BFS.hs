{-# LANGUAGE RankNTypes #-}

-- | "Atc.BFS" を使った BFS。入口は 'runBFS' ひとつ。
--
-- 第 1 引数で表の持ち方 ('dense' の配列か 'sparse' の Map) を選び、
-- 本体で使う操作で探索の仕方 (普通 / 0-1 / 数え上げ / 成分 …) が決まる。
-- 結果は @(本体の戻り値, k -> Maybe a)@。
module BFS where

import Atc
import Control.Monad (forM_, unless, void, when)
import Data.Bits (setBit, testBit)
import Data.Maybe (fromMaybe, isNothing)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Input (ints)

-- | グリッド迷路の最短距離 (ABC007 C)。
--
-- 範囲外のキーは 'visitQ' が無視するので、'around4' の結果をそのまま積める。
-- 値の型は始点で @0 :: Int@ と決める。
maze :: IO ()
maze = do
  [h, w] <- ints
  [sy, sx] <- map (subtract 1) <$> ints
  [gy, gx] <- map (subtract 1) <$> ints
  g <- getCharGrid w h
  let (_, dist) = runBFS (dense ((0, 0), (h - 1, w - 1))) $ do
        visitQ (sy, sx) (0 :: Int)
        whileQ $ \p d -> forM_ (around4 p) $ \q ->
          when (inGrid q g && elemAt q g /= '#') $ void (visitQ q (d + 1))
  print (fromMaybe (-1) (dist (gy, gx)))

-- | グラフの距離 (始点が複数でもよい)。
--
-- 'bfsDist' と同じ結果。グラフを作らずに隣接をその場で書きたいときにも同じ形。
graphDist :: IO ()
graphDist = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = undirectedGraph es
      (_, dist) = runBFS (dense (0, n - 1)) $ do
        visitQ 0 (0 :: Int)
        whileQ $ \v d -> U.forM_ (adjacentVertices g v) $ \u -> visitQ u (d + 1)
  mapM_ (print . fromMaybe (-1) . dist) [0 .. n - 1]

-- | 0-1 BFS: 壁を壊して進む (ABC213 E)。
--
-- 'updateQ' で、値が良くなったときだけ書く。コスト 0 なら先頭、1 なら末尾に積む。
-- 通路へはコスト 0、パンチ (2x2 を壊す = 周囲 5x5 の角以外) はコスト 1。
strongerTakahashi :: IO ()
strongerTakahashi = do
  [h, w] <- ints
  g <- getCharGrid w h
  let relax q x end = void $ updateQ q $ \old ->
        if maybe True (x <) old then Just (x, end) else Nothing
      (_, dist) = runBFS (dense ((0, 0), (h - 1, w - 1))) $ do
        visitQ (0, 0) (0 :: Int)
        whileQ $ \p@(i, j) d -> do
          forM_ (around4 p) $ \q -> when (inGrid q g && elemAt q g == '.') $ relax q d PushFront
          forM_ [(i + di, j + dj) | di <- [-2 .. 2], dj <- [-2 .. 2], abs di + abs dj < 4] $ \q ->
            relax q (d + 1) PushBack
  print (fromMaybe (-1) (dist (h - 1, w - 1)))

-- | 状態を足した BFS: 鍵を拾うと開く扉のある迷路。
--
-- キーを @(位置, 持っている鍵のビット集合)@ にする。'dense' の範囲もタプルで書く。
-- 鍵は @'a' .. 'e'@、扉は @'A' .. 'E'@。
keysAndDoors :: IO ()
keysAndDoors = do
  [h, w] <- ints
  g <- getCharGrid w h
  let canEnter c m = c /= '#' && (c < 'A' || c > 'E' || testBit m (fromEnum c - fromEnum 'A'))
      (_, dist) = runBFS (dense (((0, 0), 0), ((h - 1, w - 1), 31))) $ do
        visitQ ((0, 0), 0) (0 :: Int)
        whileQ $ \(p, m) d -> forM_ (around4 p) $ \q ->
          when (inGrid q g && canEnter (elemAt q g) m) $ do
            let c = elemAt q g
                m' = if c >= 'a' && c <= 'e' then setBit m (fromEnum c - fromEnum 'a') else m :: Int
            void (visitQ (q, m') (d + 1))
  print (minimum (maxBound : [d | m <- [0 .. 31], Just d <- [dist ((h - 1, w - 1), m)]]))

-- | 経路の復元: prev は自前の配列に書く ('liftST')。
--
-- 本体の戻り値に凍結した prev を返せば、表と一緒に受け取れる。
shortestPath :: IO ()
shortestPath = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = undirectedGraph es
      (prev, dist) = runBFS (dense (0, n - 1)) $ do
        pv <- liftST (UM.replicate n (-1))
        visitQ 0 (0 :: Int)
        whileQ $ \v d -> U.forM_ (adjacentVertices g v) $ \u -> do
          new <- visitQ u (d + 1)
          when new $ liftST (UM.write pv u v)
        liftST (U.freeze pv)
  when (dist (n - 1) /= Nothing) $ putStrLn (unwords (map (show . (+ 1)) (pathTo prev (n - 1))))

-- | 最短経路の数 (ABC211 D)。
--
-- 値を @(距離, 数)@ にする。'updateQ' で、未訪問なら末尾に積み、
-- 訪問済みで距離が @d + 1@ なら数を足すだけ ('NoPush')。
-- FIFO なので、取り出した時点で数は確定している。
countShortest :: IO ()
countShortest = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = undirectedGraph es
      md = 10 ^ (9 :: Int) + 7
      (_, tbl) = runBFS (dense (0, n - 1)) $ do
        visitQ 0 (0 :: Int, 1 :: Int)
        whileQ $ \v (d, c) -> U.forM_ (adjacentVertices g v) $ \u ->
          updateQ u $ \old -> case old of
            Nothing -> Just ((d + 1, c), PushBack)
            Just (d', c') | d' == d + 1 -> Just ((d', (c' + c) `mod` md), NoPush)
            _ -> Nothing
  print (maybe 0 snd (tbl (n - 1)))

-- | 連結成分: 値を成分番号にして、未訪問の頂点から何度でも始める。
--
-- 本体の戻り値に成分の数を返す。
components :: IO ()
components = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = graphFromList n (concat [[(u - 1, v - 1, 1), (v - 1, u - 1, 1)] | [u, v] <- toRows es])
      (cnt, comp) = runBFS (dense (0, n - 1)) $ do
        let go v i = do
              seen <- valueOf v
              if isNothing seen
                then do
                  _ <- visitQ v (i :: Int)
                  whileQ $ \x c -> U.forM_ (adjacentVertices g x) $ \u -> visitQ u c
                  pure (i + 1)
                else pure i
        foldlM' go 0 [0 .. n - 1]
  print cnt
  putStrLn (unwords [maybe "-" show (comp v) | v <- [0 .. n - 1]])
  where
    foldlM' f z xs = foldr (\v k i -> f v i >>= k) pure xs z

-- | 二部グラフ判定: 訪問済みに当たったら色を比べる。
--
-- 値は色 (距離の偶奇でもよい)。矛盾があれば本体の戻り値を 'False' にする。
bipartite :: IO ()
bipartite = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = undirectedGraph es
      (ok, _) = runBFS (dense (0, n - 1)) $ do
        bad <- liftST (UM.replicate 1 False)
        forM_ [0 .. n - 1] $ \s -> do
          seen <- valueOf s
          when (isNothing seen) $ do
            _ <- visitQ s (0 :: Int)
            whileQ $ \v c -> U.forM_ (adjacentVertices g v) $ \u -> do
              new <- visitQ u (1 - c)
              unless new $ do
                Just c' <- valueOf u
                when (c' == c) $ liftST (UM.write bad 0 True)
        not <$> liftST (UM.read bad 0)
  putStrLn (if ok then "Yes" else "No")

-- | 早期終了: ゴールに着いたら答えを返して止める。
--
-- 'whileQ' の代わりに 'pullQ' で自分で回す。答えは本体の戻り値で受け取る。
untilGoal :: IO ()
untilGoal = do
  [h, w] <- ints
  g <- getCharGrid w h
  let goal = (h - 1, w - 1)
      (ans, _) = runBFS (dense ((0, 0), goal)) $ do
        visitQ (0, 0) (0 :: Int)
        let loop = do
              next <- pullQ
              case next of
                Nothing -> pure Nothing
                Just (p, d)
                  | p == goal -> pure (Just d)
                  | otherwise -> do
                      forM_ (around4 p) $ \q -> when (inGrid q g && elemAt q g /= '#') $ void (visitQ q (d + 1))
                      loop
        loop
  print (fromMaybe (-1) ans)

-- | 疎な状態空間: 'sparse' (ABC235 D Multiply and Rotate)。
--
-- 状態は @N@ 未満の整数だが、使う状態はわずか。'Int' キーなので IntMap になる。
-- 範囲がないので、範囲外の打ち切りは自分で書く。
multiplyAndRotate :: IO ()
multiplyAndRotate = do
  [a, n] <- ints
  let lim = 10 ^ length (show n)
      rot x = let s = show x in read (last s : init s) :: Int
      (_, dist) = runBFS sparse $ do
        visitQ 1 (0 :: Int)
        whileQ $ \x d -> do
          when (x * a < lim) $ void (visitQ (x * a) (d + 1))
          when (x >= 10 && x `mod` 10 /= 0) $ void (visitQ (rot x) (d + 1))
  print (fromMaybe (-1) (dist n))

-- | 木を BFS 順に並べ、葉から逆順に部分木の大きさを求める ('orderQ')。
--
-- 値は親。根の親は @-1@。'orderQ' は取り出した順なので、逆にすれば子が親より先に来る。
subtreeSizes :: IO ()
subtreeSizes = do
  n <- head <$> ints
  es <- getIntGrid 2 (n - 1)
  let g = undirectedGraph es
      (order, parent) = runBFS (dense (0, n - 1)) $ do
        visitQ 0 (-1 :: Int)
        whileQ $ \v _ -> U.forM_ (adjacentVertices g v) $ \u -> visitQ u v
        orderQ
      size = U.create $ do
        sz <- UM.replicate n (1 :: Int)
        forM_ (reverse order) $ \v -> do
          let p = fromMaybe (-1) (parent v)
          when (p >= 0) $ UM.read sz v >>= \s -> UM.modify sz (+ s) p
        pure sz
  putStrLn (unwords (map show (U.toList size)))
