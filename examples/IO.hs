-- | "Atc.IO" を使った入出力。
--
-- グリッドの読み書きと、'readBS' による型に合わせた変換。
module IO where

import Atc
import qualified Data.ByteString.Char8 as C
import qualified Data.Vector.Unboxed as U

-- | 'readBS' は読む先の型で決まる。
--
-- 'Int' / 'Integer' / 'String' のどれにもなるので、受け取る側の型が答え。
-- 入力から読んだ値は型が決まっているので、注釈は普通は要らない。
parse :: IO ()
parse = do
  line <- C.getLine
  let n = readBS line :: Int
      big = readBS line :: Integer
      raw = readBS line :: String
  print (n, big, raw)

-- | @H W@ を読んでから整数のグリッドを読む。
--
-- 'getIntGrid' は @幅 高さ@ の順に取る。入力の @H W@ とは逆なので注意。
readIntGrid :: IO ()
readIntGrid = do
  [h, w] <- map readBS . C.words <$> C.getLine
  g <- getIntGrid w h
  putIntGrid (mapGrid (* 2) g)

-- | @#.#@ のような区切りなしのマス目を読んで、そのまま書き戻す。
readCharGrid :: IO ()
readCharGrid = do
  [h, w] <- map readBS . C.words <$> C.getLine
  g <- getCharGrid w h
  putCharGrid (mapGrid (\c -> if c == '#' then '.' else '#') g)

-- | 読んだグリッドを数えあげる。
--
-- 'foldGrid'' は全マスを畳む。壁の数を数えるだけならこれで足りる。
countWalls :: IO ()
countWalls = do
  [h, w] <- map readBS . C.words <$> C.getLine
  g <- getCharGrid w h
  print (foldGrid' (\acc c -> if c == '#' then acc + 1 else acc) (0 :: Int) g)

-- | 出力は 'putIntGrid' に任せる。
--
-- 自分で組み立てると行ごとの @unwords@ と @putStrLn@ になり、大きい出力では
-- 遅い。'putIntGrid' は Builder でまとめて書く。
writeGrid :: IO ()
writeGrid = do
  [h, w] <- map readBS . C.words <$> C.getLine
  putIntGrid (unflattenRow w h [1 .. w * h] :: Grid U.Vector Int)

-- | 'Parsable' を自分の関数の制約にする。
--
-- 'readBS' は返す型で決まるので、そのまま引き回せば 'Int' でも 'Integer' でも
-- 'String' でも使える関数になる。
readMany :: (Parsable a) => C.ByteString -> [a]
readMany = map readBS . C.words
