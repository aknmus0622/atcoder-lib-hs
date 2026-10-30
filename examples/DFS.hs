{-# LANGUAGE RankNTypes #-}

-- | "Atc.DFS" を使った DFS。入口は 'runDFS' ひとつ。
--
-- 表の持ち方と値の読み書きは "Atc.BFS" と同じ。ループは @go@ を再帰で書き、
-- 'visitS' の本体の中で子へ潜る。結果は @(本体の戻り値, k -> Maybe a)@。
module DFS where

import Atc
import Control.Monad (forM_, unless, void, when)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Input (ints)

-- | グリッドの塗りつぶし (ATC001 A)。
--
-- 値は要らないので @()@。範囲外のキーは 'visitS' が無視する。
floodFill :: IO ()
floodFill = do
  [h, w] <- ints
  g <- getCharGrid w h
  let s = head [p | p <- range2 h w, elemAt p g == 's']
      t = head [p | p <- range2 h w, elemAt p g == 'g']
      (_, seen) = runDFS (dense ((0, 0), (h - 1, w - 1))) $ do
        let go p = visitS p () $ forM_ (around4 p) $ \q ->
              when (inGrid q g && elemAt q g /= '#') $ void (go q)
        go s
  putStrLn (if isJust (seen t) then "Yes" else "No")
  where
    range2 h w = [(i, j) | i <- [0 .. h - 1], j <- [0 .. w - 1]]

-- | 木 DP: 部分木の大きさ。
--
-- 子の 'visitS' が 'True' を返した時点で子の部分木は終わっているので、子の値を足す。
subtreeSizes :: IO ()
subtreeSizes = do
  n <- head <$> ints
  es <- getIntGrid 2 (n - 1)
  let g = undirectedGraph es
      (_, size) = runDFS (dense (0, n - 1)) $ do
        let go v = visitS v (1 :: Int) $ U.forM_ (adjacentVertices g v) $ \u -> do
              new <- go u
              when new $ valueOf u >>= mapM_ (\s -> modifyValue v (+ s))
        go 0
  putStrLn (unwords [maybe "-" show (size v) | v <- [0 .. n - 1]])

-- | 有向グラフの閉路の有無と、閉路がなければトポロジカル順。
--
-- 訪問済みでも 'onStackS' なら後退辺 (閉路)。抜けた順の逆がトポロジカル順。
topoOrCycle :: IO ()
topoOrCycle = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = directedGraph es
      ((cyc, post), _) = runDFS (dense (0, n - 1)) $ do
        bad <- liftST (UM.replicate 1 False)
        let go v = visitS v () $ U.forM_ (adjacentVertices g v) $ \u -> do
              new <- go u
              unless new $ do
                b <- onStackS u
                when b $ liftST (UM.write bad 0 True)
        forM_ [0 .. n - 1] go
        (,) <$> liftST (UM.read bad 0) <*> postorderS
  if cyc then putStrLn "cycle" else putStrLn (unwords (map (show . (+ 1)) (reverse post)))

-- | オイラーツアー: 入った時刻と抜けた時刻。
--
-- 値を入った時刻にして、抜けた時刻は自前の配列に書く。
-- @u@ が @v@ の部分木にある ⇔ @tin v <= tin u && tout u <= tout v@。
eulerTour :: IO ()
eulerTour = do
  n <- head <$> ints
  es <- getIntGrid 2 (n - 1)
  let g = undirectedGraph es
      (tout, tin) = runDFS (dense (0, n - 1)) $ do
        clock <- liftST (UM.replicate 1 (0 :: Int))
        out <- liftST (UM.replicate n 0)
        let tick = liftST $ do t <- UM.read clock 0; UM.write clock 0 (t + 1); pure t
            go v = do
              t <- liftST (UM.read clock 0)
              visitS v t $ do
                _ <- tick
                U.forM_ (adjacentVertices g v) go
                tick >>= liftST . UM.write out v
        _ <- go 0
        liftST (U.freeze out)
  forM_ [0 .. n - 1] $ \v -> putStrLn (show (fromMaybe (-1) (tin v)) ++ " " ++ show (tout U.! v))

-- | 単純パスの数え上げ (ABC284 E)。上限に達したら潜らない。
--
-- 'backtrackS' は抜けるときに未訪問へ戻すので、別の経路から同じ頂点に入れる。
countPaths :: IO ()
countPaths = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let g = undirectedGraph es
      lim = 10 ^ (6 :: Int) :: Int
      (ans, _) = runDFS (dense (0, n - 1)) $ do
        cnt <- liftST (UM.replicate 1 (0 :: Int))
        let go v = do
              c <- liftST (UM.read cnt 0)
              when (c < lim) $ void $ backtrackS v () $ do
                liftST (UM.write cnt 0 (c + 1))
                U.forM_ (adjacentVertices g v) go
        go 0
        liftST (UM.read cnt 0)
  print ans
