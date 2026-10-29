-- | "Atc.Math" を使った整数の計算。
--
-- 素数判定・素因数分解・冪乗の剰余。'Int' でも 'Integer' でも同じ名前で書ける
-- ('PrimeNum')。
module Math where

import Atc
import Input (int, ints)

-- | 素数の個数を数える (ABC149 相当の素朴版)。
--
-- 'isPrime' は Miller–Rabin 法なので、10^18 の範囲の値でも 1 個あたり数 μs。
-- 1 個ずつ判定してよい。
countPrimes :: IO ()
countPrimes = do
  xs <- ints
  print (length (filter isPrime xs))

-- | 素因数分解して、重複を含めて並べる。
--
-- > primeFactors (360 :: Int)   -- [2,2,2,3,3,5]
factorize :: IO ()
factorize = do
  n <- int
  putStrLn (unwords (map show (primeFactors n)))

-- | 約数の個数 = 各素因数の指数 + 1 の積。
--
-- 'primeFactorCounts' が @(素因数, 個数)@ を返すので、そのまま掛ける。
divisorCount :: IO ()
divisorCount = do
  n <- int
  print (product [k + 1 | (_, k) <- primeFactorCounts n])

-- | 素因数の種類数 (個数は無視する)。
distinctFactors :: IO ()
distinctFactors = do
  n <- int
  print (length (primeFactorCounts n))

-- | @a^e mod m@ と @a*b mod m@。
--
-- 'powMod' / 'mulMod' は 'Int' でも桁あふれしない (128 bit の積を使う)。
-- 素数 @m@ の逆元はフェルマーの小定理から @a^(m-2)@。
modularArithmetic :: IO ()
modularArithmetic = do
  [a, b, e] <- ints
  let m = 1000000007 :: Int
  print (powMod a e m)
  print (mulMod a b m)
  print (mulMod a (powMod b (m - 2) m) m) -- a / b mod m

-- | 'Integer' でも同じ名前で書ける。
--
-- 2^63 未満なら中では 'Int' と同じ速い計算に回る。それより大きいと多倍長のまま。
bigIntegers :: IO ()
bigIntegers = do
  let n = 10 ^ (30 :: Int) + 57 :: Integer
  print (isPrime n)
  print (powMod (2 :: Integer) (10 ^ (30 :: Int)) (10 ^ (20 :: Int) + 39))

-- | 数列全体の最大公約数・最小公倍数。
--
-- 'lcmAll' は 'Int' であふれることがあるので、入力の範囲を確かめてから使う。
gcdAndLcm :: IO ()
gcdAndLcm = do
  xs <- ints
  print (gcdAll xs)
  print (lcmAll xs)

-- | 並べ替え済みのリストを @(値, 連続した個数)@ にまとめる。
--
-- 'primeFactorCounts' の中身と同じもので、素因数以外にも使える。
runLengths :: [Int] -> [(Int, Int)]
runLengths = countRuns

-- | 'PrimeNum' を制約にすれば 'Int' と 'Integer' の両方で使える。
--
-- 型を固定しないで書いておけば、@Int@ であふれそうなときに呼ぶ側で
-- @Integer@ に替えるだけで済む。
largestFactor :: (PrimeNum a) => a -> Maybe a
largestFactor n = case primeFactors n of
  [] -> Nothing
  fs -> Just (last fs)
