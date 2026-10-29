-- | 例の中で使う入力の読み取り。
--
-- ライブラリの API ではなく、examples/ の中だけの道具。実際の解答でも
-- この 3 行くらいは自分で書くことになる ('readBS' がその材料)。
module Input where

import Atc
import qualified Data.ByteString.Char8 as C

-- | 空白区切りの整数を 1 行。
--
-- @[n, m] <- ints@ のように受け取る。
ints :: IO [Int]
ints = map readBS . C.words <$> C.getLine

-- | 整数ひとつだけの行。
int :: IO Int
int = head <$> ints

-- | 整数が並んだ行を @h@ 行。
intRows :: Int -> IO [[Int]]
intRows h = mapM (const ints) [1 .. h]

-- | 文字列ひとつだけの行。
word :: IO String
word = C.unpack . C.takeWhile (/= ' ') <$> C.getLine
