-- | "Atc.Debug" で WA を睨む。
--
-- 'dbg' と 'dbgIO' の出力は stderr に出るので、@atc test@ の
-- @stderr:@ の欄に出る (AC のときも出る)。判定とは混ざらない。
module Debug where

import Atc
import Control.Monad (forM_)
import Data.Function ((&))
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 式の途中を覗く: 'dbg' は値をそのまま返すので、どこにでも挟める。
inTheMiddle :: [Int] -> Int
inTheMiddle xs = sum (dbg "偶数" (filter even xs))

-- | @where@ の各段に付ける。
--
-- 計算を名前で切ってから 1 つずつ包むのが、一番読みやすい使い方。
inWhere :: [Int] -> Int
inWhere xs = total
  where
    evens = dbg "偶数" (filter even xs)
    total = dbg "合計" (sum evens)

-- | @&@ のパイプラインに差し込む。
--
-- @dbg \"ラベル\"@ は @a -> a@ なので、関数を並べる中に置ける。
inPipeline :: [Int] -> Int
inPipeline xs = xs & dbg "元" & map (* 2) & dbg "2倍" & sum

-- | @do@ の中では 'dbgIO'。
--
-- 'dbg' を文として裸で置くと「値を使っていない」ので型が合わない。
-- 'dbgIO' は値を返さず、その場で強制して覗く。
inDo :: IO ()
inDo = do
  xs <- ints
  dbgIO "入力" xs
  let evens = filter even xs
  dbgIO "偶数" evens
  print (sum evens)

-- | ループの各回を覗く。
--
-- 回数が多いときは条件を付ける ('dbg' は 1 回 4 μs ほど、20 万回で 0.9 秒)。
inLoop :: IO ()
inLoop = do
  xs <- ints
  forM_ (zip [0 :: Int ..] xs) $ \(i, x) -> do
    if i < 5 then dbgIO ("x[" ++ show i ++ "]") x else pure ()
    print x

-- | 大きい構造は切ってから渡す。
--
-- 無限リストをそのまま渡すと @show@ が終わらず、1 文字も出ないまま TLE になる
-- (@atc test@ からは stderr の欄すら出ない)。'take' は 'dbg' の内側で。
cutItDown :: IO ()
cutItDown = do
  xs <- ints
  print (sum (dbg "先頭5件" (take 5 xs)))
  print (take 3 (dbg "有限に切る" (take 10 [1 :: Int ..])))

-- | 'interact' に挟む。
--
-- @interact $ dbg \"入力\"@ と書く。@dbg \"入力\" id@ は 'id' そのものを
-- 表示しようとして @No instance for Show (String -> String)@ になる。
inInteract :: IO ()
inInteract = interact (dbg "入力" . map succ)

-- | Vector も 'Show' があるのでそのまま覗ける。
vectors :: IO ()
vectors = do
  xs <- U.fromList <$> ints
  dbgIO "vector" xs
  print (U.sum (dbg "2倍" (U.map (* 2) xs)))
