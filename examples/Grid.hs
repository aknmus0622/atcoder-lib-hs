-- | "Atc.Grid" を使った 2 次元グリッド。
--
-- 座標は @(r, c)@ = @(行, 列)@、大きさは @幅 高さ@ の順。不変版 'Grid' と
-- 可変版 'MGrid' で同じ関数が使える (可変版は返り値が @m@ に包まれる)。
module Grid where

import Atc
import Control.Monad (filterM, forM_)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Input (ints)

-- | 座標と 1 次元添字を行き来する。
--
-- Vector を自分で持つときや、訪問済みフラグを 1 本の配列で持つときに使う。
coordinates :: IO ()
coordinates = do
  [h, w] <- ints
  let i = posToIndex w (2, 3)
  print i
  print (indexToPos w i)
  print (inRange2D w h (2, 3))
  print (around4 (2, 3)) -- 上・下・左・右。範囲は見ない

-- | 行のリストから作って、形を聞く。
--
-- 'fromRows' は行の長さが揃っていなければ error。中身の Vector は
-- 型注釈で選ぶ ('U.Vector' は要素に @Unbox@ が要る、'V.Vector' は何でも入る)。
build :: IO ()
build = do
  let g = fromRows [[1, 2, 3], [4, 5, 6]] :: Grid U.Vector Int
  print (gridWidth g, gridHeight g)
  print (elemAt (1, 2) g) -- 6
  print (getElem (9, 9) g) -- Nothing (範囲外)
  print g

-- | 1 列に並んだリストから作る: 'unflattenRow' / 'unflattenColumn'。
--
-- 行優先 (上の行から、各行は左から) か列優先 (左の列から、各列は上から)。
fromFlat :: IO ()
fromFlat = do
  [h, w] <- ints
  xs <- ints
  print (unflattenRow w h xs :: Grid U.Vector Int)
  print (unflattenColumn w h xs :: Grid U.Vector Int)

-- | 範囲の見方: 'inGrid' と 'neighborPos4' / 'neighbors4'。
--
-- 'around4' は範囲を見ないが、こちらはグリッドの大きさで切ってくれる。
-- 'neighbors4' は値も一緒に返す。
neighborhood :: IO ()
neighborhood = do
  [h, w] <- ints
  g <- getCharGrid w h
  print (inGrid (0, 0) g)
  print (neighborPos4 (0, 0) g) -- 範囲内の座標だけ
  print (neighbors4 (0, 0) g) -- 座標と値の組

-- | 書き換える: 不変版は新しいグリッドが返る (O(HW))。
--
-- 'setElem' / 'adjustElem' は範囲外なら何もしない。@'@ 付きは値を評価してから
-- 書く strict 版で、数値を積むときはこちらを使う。
write :: IO ()
write = do
  let g = fromRows [[1, 2], [3, 4]] :: Grid U.Vector Int
  print (setElem (0, 0) 9 g)
  print (setElem' (0, 0) 9 g)
  print (adjustElem (1, 1) (* 10) g)
  print (adjustElem' (1, 1) (* 10) g)

-- | 全マスを変換する: 'mapGrid' と座標付きの 'imapGrid'。
--
-- 要素の型が変わってもよい。@'@ 付きは strict 版。
transform :: IO ()
transform = do
  [h, w] <- ints
  g <- getCharGrid w h
  print (mapGrid (== '#') g) -- Grid U.Vector Bool
  print (mapGrid' (== '#') g)
  print (imapGrid (\(r, c) x -> if even (r + c) then x else '.') g)
  print (imapGrid' (\(r, c) _ -> r * w + c) g)
  print (transposeGrid g) -- 幅と高さが入れ替わる

-- | 行・列を丸ごと変換する: 'mapRow' / 'mapColumn' とその i 付き。
--
-- 行 (列) をリストとして受け取るので、累積や並べ替えがそのまま書ける。
-- 返すリストの長さは元と同じでなければならない。
rowsAndColumns :: IO ()
rowsAndColumns = do
  let g = fromRows [[1, 2, 3], [4, 5, 6]] :: Grid U.Vector Int
  print (mapRow reverse g)
  print (mapRow' (map (* 2)) g)
  print (imapRow (\r xs -> map (+ r) xs) g)
  print (imapRow' (\r xs -> map (+ r) xs) g)
  print (mapColumn reverse g)
  print (mapColumn' (map negate) g)
  print (imapColumn (\c xs -> map (+ c) xs) g)
  print (imapColumn' (\c xs -> map (+ c) xs) g)

-- | 2 次元累積和: 'scanRow' のあと 'scanColumn'。
--
-- 'scanRow' は各行に左から @scanl@ をかけて幅を 1 増やし、'scanColumn' は
-- 各列に上から同じことをして高さを 1 増やす。続けてかければ累積和の表。
cumulativeSum :: IO ()
cumulativeSum = do
  [h, w] <- ints
  g <- getIntGrid w h
  let s = scanColumn' (+) 0 (scanRow' (+) 0 g)
  -- 長方形 [(r1, c1), (r2, c2)) の和
  let area (r1, c1) (r2, c2) =
        elemAt (r2, c2) s - elemAt (r1, c2) s - elemAt (r2, c1) s + elemAt (r1, c1) s
  print (area (0, 0) (h, w))
  print (scanRow (+) 0 g) -- 遅延版
  print (scanColumn (+) 0 g)

-- | 行ごと・列ごとにまとめる: 'foldRow' / 'foldColumn'。
--
-- 並べる先 (リスト / 'V.Vector' / 'U.Vector') は使い方から決まるので、
-- 受け取る側で型を書く。@'@ 付きは途中結果を評価しながら畳む。
foldLines :: IO ()
foldLines = do
  [h, w] <- ints
  g <- getIntGrid w h
  print (foldRow' (+) 0 g :: [Int]) -- 各行の和
  print (foldRow (+) 0 g :: U.Vector Int)
  print (foldColumn' (+) 0 g :: [Int]) -- 各列の和
  print (foldColumn (+) 0 g :: V.Vector Int)

-- | 全マスをまとめる: 'foldGrid'。
--
-- @U.Vector@ のグリッドは 'Foldable' にできないので、@sum@ ではなくこちら。
-- @V.Vector@ のグリッドなら @sum@ / @maximum@ / @length@ がそのまま使える。
foldAll :: IO ()
foldAll = do
  [h, w] <- ints
  g <- getCharGrid w h
  print (foldGrid' (\acc c -> if c == '#' then acc + 1 else acc) (0 :: Int) g)
  print (foldGrid (flip (:)) [] g)
  let v = fromRows [[1, 2], [3, 4]] :: Grid V.Vector Int
  print (sum v, maximum v, length v)

-- | 並べ直す: 'toRows' / 'flattenRow' / 'flattenColumn'。
--
-- 出力するときや、行単位で比べるときに使う。並べる先は受け取る側の型で決まる。
reshape :: IO ()
reshape = do
  [h, w] <- ints
  g <- getCharGrid w h
  print (toRows g :: [String])
  print (toRows g :: V.Vector (U.Vector Char))
  print (flattenRow g :: [Char]) -- 行優先
  print (flattenColumn g :: [Char]) -- 列優先

-- | 可変版の基本形: 'createGrid' の中で作って不変版として取り出す。
--
-- 壁 @#@ を避けた @(0, 0)@ からの BFS 距離。届かないマスは -1。
-- 'createGrid' は写さずに取り出すので、途中のコピーが無い。
bfsOnGrid :: Grid U.Vector Char -> Grid U.Vector Int
bfsOnGrid g = createGrid $ do
  dist <- newMGrid (gridWidth g) (gridHeight g) (-1)
  setElem (0, 0) 0 dist
  let go [] = pure ()
      go (p : ps) = do
        d <- elemAt p dist
        next <-
          filterM
            (\q -> (== -1) <$> elemAt q dist)
            [q | (q, x) <- neighbors4 p g, x /= '#']
        forM_ next $ \q -> setElem q (d + 1) dist
        go (ps ++ next)
  go [(0, 0)]
  pure dist

-- | 'IO' で直接使うなら型を書いて決める。
--
-- 可変版は読み書きが O(1)。同じ名前の関数が @m@ に包まれて返る。
mutableInIO :: IO ()
mutableInIO = do
  [h, w] <- ints
  g <- newMGrid w h 0 :: IO (MGrid UM.MVector IO Int)
  adjustElem (1, 2) (+ 1) g
  setElem' (0, 0) 5 g
  elemAt (1, 2) g >>= print
  getElem (99, 99) g >>= print
  rows <- toRows g
  print (rows :: [[Int]])
  frozen <- freezeGrid g
  print (frozen :: Grid U.Vector Int)

-- | 既にあるグリッドから可変版を作る: 'thawGrid'。
--
-- 'freezeGrid' は写すので、元の可変版はその後も使ってよい。
thawAndFreeze :: IO ()
thawAndFreeze = do
  [h, w] <- ints
  g <- getIntGrid w h
  m <- thawGrid g
  forM_ [0 .. h - 1] $ \r -> adjustElem' (r, 0) (* 2) m
  back <- freezeGrid m
  putIntGrid (back :: Grid U.Vector Int)

-- | 可変版でも共通関数が使える (返り値が @m@ に包まれるだけ)。
commonOnMutable :: IO ()
commonOnMutable = do
  [h, w] <- ints
  g <- newMGrid w h (1 :: Int) :: IO (MGrid UM.MVector IO Int)
  foldGrid' (+) 0 g >>= print
  (foldRow' (+) 0 g :: IO [Int]) >>= print
  mapped <- mapGrid' (* 3) g
  freezeGrid mapped >>= \f -> print (f :: Grid U.Vector Int)
  t <- transposeGrid g
  print (gridWidth t, gridHeight t)

-- | 'GridShape' だけで足りる関数: 大きさしか見ないなら不変版でも可変版でも。
--
-- 制約を 'GridShape' に留めておくと、'Grid' と 'MGrid' の両方に使える。
area :: (GridShape g) => g -> Int
area g = gridWidth g * gridHeight g

-- | 'GridOf' を制約にして、中身を読む関数を自分で書く。
--
-- 返り値は @Ret k x@ なので、不変版は値そのまま、可変版は @m x@ になる。
cornerSum :: (GridOf k Int) => k Int -> Ret k Int
cornerSum g = foldGrid' (+) 0 g

-- | 'Collect' を制約にして、並べる先を呼ぶ側に決めさせる。
--
-- 'foldRow' / 'toRows' / 'flattenRow' がこの形。リスト・'V.Vector'・
-- 'U.Vector' のどれでも返せる。
rowSums :: (Collect t Int) => Grid U.Vector Int -> t Int
rowSums = foldRow' (+) 0
