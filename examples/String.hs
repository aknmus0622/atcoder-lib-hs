-- | "Atc.String" を使った文字列のアルゴリズム。
--
-- 文字列は @U.fromList s@ で 'U.Vector' 'Char' にして渡す。
module String where

import Atc
import Control.Monad (replicateM_)
import qualified Data.Vector.Unboxed as U
import Input (ints, word)

-- | 部分文字列の一致のクエリ: 'buildRH' のハッシュを比べる (O(1))。
-- 各問い合わせ @a b len@ に、位置 a と b から長さ len の部分が一致するかを出力する。
sameSubstrings :: IO ()
sameSubstrings = do
  s <- U.fromList <$> word
  let h = buildRH s
  [q] <- ints
  replicateM_ q $ do
    qu <- ints
    case qu of
      [a, b, len] -> putStrLn (if hashRH a (a + len) h == hashRH b (b + len) h then "Yes" else "No")
      _ -> error "query"

-- | 回文の判定: 反転した文字列のハッシュと比べる。
-- [l, r) が回文か = s の [l, r) と、反転の [n - r, n - l) が一致するか。
palindromes :: IO ()
palindromes = do
  s <- U.fromList <$> word
  let n = U.length s
      h = buildRH s
      hr = buildRH (U.reverse s)
      isPal l r = hashRH l r h == hashRH (n - r) (n - l) hr
  print [(l, r) | l <- [0 .. n - 1], r <- [l + 2 .. n], isPal l r]

-- | パターンの出現位置: 'zFunction' に「パターン ++ 区切り ++ テキスト」を渡す。
occurrences :: IO ()
occurrences = do
  t <- word
  p <- word
  let z = zFunction (U.fromList (p ++ "$" ++ t))
      m = length p
  print [i - m - 1 | i <- [m + 1 .. U.length z - 1], z U.! i >= m]

-- | 相異なる部分文字列の個数: 接尾辞の長さの和から、隣どうしの共通接頭辞を引く。
distinctSubstrings :: IO ()
distinctSubstrings = do
  s <- U.fromList <$> word
  let n = U.length s
      sa = suffixArray s
      lcp = lcpArray s sa
  print (n * (n + 1) `div` 2 - U.sum lcp)
