-- | "Atc.ModInt" を使った剰余の計算と数え上げ。
--
-- 法は型で決める ('Mint' は 998244353、'Mint107' は 10^9 + 7)。普通の数と同じく
-- @+@ / @-@ / @*@ / @/@ / @^@ が使え、'print' すると値だけが出る。
module ModInt where

import Atc
import qualified Data.Vector.Unboxed as U
import Input (int, ints)

-- | 列の積を 998244353 で割った余り。'mkMI' で 'Int' から変える (負の数でもよい)。
productMod :: IO ()
productMod = do
  as <- ints
  print (product (map mkMI as :: [Mint]))

-- | 割り算: 期待値の問題で「P / Q を mod で」と言われたら、そのまま @/@ で書く。
-- ここでは 1 から n の平均。
average :: IO ()
average = do
  n <- int
  let s = sum (map mkMI [1 .. n]) :: Mint
  print (s / mkMI n)

-- | 二項係数: 'buildBinomMI' で表を作って 'chooseMI'。
-- @h × w@ の格子を左上から右下へ、右か下に進む経路の数 (@(h + w - 2) C (h - 1)@)。
gridPaths :: IO ()
gridPaths = do
  [h, w] <- ints
  let t = buildBinomMI (h + w) :: BinomMI M998244353
  print (chooseMI (h + w - 2) (h - 1) t)

-- | 重複組合せ: n 種類から重複を許して k 個選ぶ ('multichooseMI')。
-- 順列: n 人から k 人選んで並べる ('permMI')。
selections :: IO ()
selections = do
  [n, k] <- ints
  let t = buildBinomMI (n + k) :: BinomMI M1000000007
  print (multichooseMI n k t)
  print (permMI n k t)

-- | 'U.Vector' にそのまま置ける。DP の表も 'Mint' で持てる。
-- ここでは階段を 1 段か 2 段ずつ上る方法の数。
stairs :: IO ()
stairs = do
  n <- int
  let dp = U.constructN (n + 1) $ \v -> case U.length v of
        0 -> 1
        1 -> 1
        i -> v U.! (i - 1) + v U.! (i - 2) :: Mint
  print (U.last dp)

-- | 自分の法: 空の型を作って 'Modulus' のインスタンスにする。
data M1000003

instance Modulus M1000003 where
  modulusOf _ = 1000003

-- | 2^n を 1000003 で割った余り。
powerOfTwo :: IO ()
powerOfTwo = do
  n <- int
  print (2 ^ n :: ModInt M1000003)
