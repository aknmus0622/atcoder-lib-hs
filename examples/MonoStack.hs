-- | "Atc.MonoStack" を使った単調スタック。
--
-- 左から順に push し、push の前に @pop top x@ が成り立つ間 pop する。
-- pop は合計で予算 @b@ 回まで (予算が要らなければ 'maxBound')。
module MonoStack where

import Atc
import qualified Data.ByteString.Char8 as C
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 長さ K の部分列で辞書順最小 (典型 006)。
--
-- 捨ててよいのは N - K 個なので予算は @n - k@。残ったスタックの長さは
-- K 以上になり、その先頭の K 個が答え。
smallestSubsequence :: IO ()
smallestSubsequence = do
  [n, k] <- ints
  s <- U.fromList . C.unpack <$> C.getLine
  putStrLn (U.toList (U.take k (monoStack (n - k) (>) s)))

-- | 各要素について、左で最も近い「より小さい」要素の添字 (無ければ -1)。
--
-- 上が @x@ 以上なら pop するので、残る上は @x@ より小さい。
prevSmaller :: IO ()
prevSmaller = do
  _ <- ints
  as <- U.fromList <$> ints
  print (U.toList (monoStackTops maxBound (>=) as))

-- | 右で最も近い「より小さい」要素の添字 (無ければ N)。
--
-- 反転して左側の問題にし、添字を @n - 1 - i@ で戻す。
nextSmaller :: IO ()
nextSmaller = do
  [n] <- ints
  as <- U.fromList <$> ints
  let tops = monoStackTops maxBound (>=) (U.reverse as)
  print (U.toList (U.reverse (U.map (\j -> n - 1 - j) tops)))
