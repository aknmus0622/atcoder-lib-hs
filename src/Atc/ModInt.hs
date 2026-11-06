{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | 法を型で固定した剰余 'ModInt' と、二項係数の表。
--
-- 法は型で決める。よく使う 2 つは 'Mint' (998244353) と 'Mint107' (10^9 + 7)。
-- 'Num' / 'Fractional' のインスタンスがあるので、普通の数と同じように書ける。
--
-- > let x = 3 :: Mint
-- > x + 998244352                       -- 2
-- > x * x - 10                          -- 998244352 (= -1)
-- > x / 2                               -- 3 の 2 倍が 1 になる数 ('recip' は逆元)
-- > x ^ (10 ^ 18 :: Int)                -- 繰り返し二乗法
-- > sum (map fromIntegral as :: [Mint]) -- Int から変換して足す ('mkMI' も同じ)
-- > print (valMI x)                     -- Int に戻す ('print x' も値だけ出す)
--
-- 法が違う値は型が違うので、混ぜるとコンパイルエラーになる。
-- 'U.Unbox' のインスタンスもあるので @U.Vector Mint@ がそのまま使える。
--
-- == 自分の法
--
-- 空の型を作って 'Modulus' のインスタンスにする。
--
-- > data M1000003
-- > instance Modulus M1000003 where modulusOf _ = 1000003
-- > type Mod = ModInt M1000003
--
-- 法は 2 以上 2^31 未満 (積が 'Int' に収まるように)。入力から読んだ値を法にしたいときは、
-- "Atc.Math" の 'mulMod' / 'powMod' / 'modInverse' で 'Int' のまま計算する。
--
-- == 割り算と逆元
--
-- 'recip' (と @/@) は拡張ユークリッドの互除法で逆元を求める。法が素数でなくても、
-- 法と互いに素なら求まる。互いに素でなければ 'error'。
--
-- == 二項係数
--
-- 'buildBinomMI' で階乗とその逆元の表を作る。法は表の大きさより大きい素数であること。
--
-- > let t = buildBinomMI 200000 :: BinomMI M998244353
-- > chooseMI n k t        -- nCk (k < 0 や k > n なら 0)
-- > permMI n k t          -- nPk
-- > multichooseMI n k t   -- nHk (n 種類から重複を許して k 個)
module Atc.ModInt where

import Data.Ratio (denominator, numerator)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import Data.Vector.Unboxed (MVector, Vector)
import qualified Data.Vector.Unboxed as U

-- | 法を表す型のクラス。
class Modulus m where
  -- | 法の値。引数は見ない (型だけで決まる)。
  modulusOf :: proxy m -> Int

-- | 998244353。
data M998244353

-- | 10^9 + 7。
data M1000000007

instance Modulus M998244353 where
  modulusOf _ = 998244353
  {-# INLINE modulusOf #-}

instance Modulus M1000000007 where
  modulusOf _ = 1000000007
  {-# INLINE modulusOf #-}

-- | 法 @m@ の剰余。中身は @0@ 以上 法 未満の 'Int'。
newtype ModInt m = ModInt Int
  deriving (Eq, Ord)

-- | 998244353 で割った余り。
type Mint = ModInt M998244353

-- | 10^9 + 7 で割った余り。
type Mint107 = ModInt M1000000007

instance Show (ModInt m) where
  showsPrec d (ModInt a) = showsPrec d a

-- | 中身の 'Int' (@0@ 以上 法 未満)。
valMI :: ModInt m -> Int
valMI (ModInt a) = a
{-# INLINE valMI #-}

-- | この値の法。
modulusMI :: (Modulus m) => ModInt m -> Int
modulusMI = modulusOf
{-# INLINE modulusMI #-}

-- | 'Int' から作る。負の数でもよい。'fromIntegral' より速い ('Integer' を通らない)。
mkMI :: (Modulus m) => Int -> ModInt m
mkMI a = r
  where
    r = ModInt (a `mod` modulusMI r)
{-# INLINE mkMI #-}

-- | 累乗。O(log |e|)。
powMI ::
  (Modulus m) =>
  -- | @x@: 底
  ModInt m ->
  -- | @e@: 指数 (負なら逆元の累乗)
  Int ->
  -- | @x ^ e@
  ModInt m
powMI x e
  | e < 0 = powMI (recip x) (negate e)
  | otherwise = go x e 1
  where
    go !_ 0 !acc = acc
    go b k acc = go (b * b) (k `quot` 2) (if odd k then acc * b else acc)
{-# INLINE powMI #-}

instance (Modulus m) => Num (ModInt m) where
  x@(ModInt a) + ModInt b = let c = a + b; p = modulusMI x in ModInt (if c >= p then c - p else c)
  {-# INLINE (+) #-}
  x@(ModInt a) - ModInt b = let c = a - b in ModInt (if c < 0 then c + modulusMI x else c)
  {-# INLINE (-) #-}
  x@(ModInt a) * ModInt b = ModInt (a * b `rem` modulusMI x)
  {-# INLINE (*) #-}
  negate x@(ModInt a) = ModInt (if a == 0 then 0 else modulusMI x - a)
  {-# INLINE negate #-}
  abs = id
  signum (ModInt a) = ModInt (if a == 0 then 0 else 1)
  fromInteger n = r
    where
      r = ModInt (fromInteger (n `mod` toInteger (modulusMI r)))
  {-# INLINE fromInteger #-}

instance (Modulus m) => Fractional (ModInt m) where
  recip x@(ModInt a) = case miInverse a (modulusMI x) of
    Just b -> ModInt b
    Nothing -> error ("Atc.ModInt.recip: " ++ show a ++ " は法 " ++ show (modulusMI x) ++ " と互いに素でない")
  {-# INLINE recip #-}
  fromRational q = fromInteger (numerator q) / fromInteger (denominator q)

-- | 拡張ユークリッドで a の逆元 (法 m)。互いに素でなければ Nothing。
miInverse :: Int -> Int -> Maybe Int
miInverse a m = go a m 1 0
  where
    go !r0 !r1 !s0 !s1
      | r1 == 0 = if r0 == 1 then Just (s0 `mod` m) else Nothing
      | otherwise = let q = r0 `quot` r1 in go r1 (r0 - q * r1) s1 (s0 - q * s1)

-- U.Vector に置くためのインスタンス (中身の Int をそのまま並べる)。
-- MVector / Vector は修飾なしで書く (atc bundle が書き出す export に合わせるため)。
instance U.IsoUnbox (ModInt m) Int where
  toURepr (ModInt a) = a
  fromURepr = ModInt

newtype instance MVector s (ModInt m) = MV_ModInt (MVector s Int)

newtype instance Vector (ModInt m) = V_ModInt (Vector Int)

deriving via (U.As (ModInt m) Int) instance GM.MVector U.MVector (ModInt m)

deriving via (U.As (ModInt m) Int) instance G.Vector U.Vector (ModInt m)

instance U.Unbox (ModInt m)

-- ---------------------------------------------------------------------
-- 二項係数

-- | 階乗と、その逆元の表 (@0 .. n@)。
data BinomMI m
  = BinomMI
      -- | @0! .. n!@
      !(U.Vector (ModInt m))
      -- | @(0!)^-1 .. (n!)^-1@
      !(U.Vector (ModInt m))

-- | @0! .. n!@ とその逆元の表を作る。法は @n@ より大きい素数であること。O(n + log 法)。
buildBinomMI :: (Modulus m) => Int -> BinomMI m
buildBinomMI n
  | n < 0 = error "Atc.ModInt.buildBinomMI: 負の大きさ"
  | otherwise = BinomMI fact inv
  where
    fact = U.scanl' (*) 1 (U.generate n (mkMI . (+ 1)))
    -- (n!)^-1 から順に (k - 1)!^-1 = k!^-1 * k で戻る。
    inv = U.reverse (U.scanl' (*) (recip (U.last fact)) (U.generate n (\i -> mkMI (n - i))))

-- | 表の範囲を確かめる (超えれば関数名付きで 'error')。
binomCheck :: String -> Int -> BinomMI m -> ()
binomCheck name n (BinomMI fact _)
  | n >= U.length fact = error ("Atc.ModInt." ++ name ++ ": " ++ show n ++ " が表の大きさ " ++ show (U.length fact - 1) ++ " を超える")
  | otherwise = ()
{-# INLINE binomCheck #-}

-- | @n!@。
factMI ::
  -- | @n@: 0 以上、表の大きさ以下 (負なら 'error')
  Int ->
  -- | 表
  BinomMI m ->
  -- | @n!@
  ModInt m
factMI n t@(BinomMI fact _) = binomCheck "factMI" n t `seq` (fact U.! n)
{-# INLINE factMI #-}

-- | @(n!)^-1@。
invFactMI ::
  -- | @n@: 0 以上、表の大きさ以下
  Int ->
  -- | 表
  BinomMI m ->
  -- | @(n!)^-1@
  ModInt m
invFactMI n t@(BinomMI _ inv) = binomCheck "invFactMI" n t `seq` (inv U.! n)
{-# INLINE invFactMI #-}

-- | @nCk@。O(1)。
chooseMI ::
  (Modulus m) =>
  -- | @n@: 表の大きさ以下
  Int ->
  -- | @k@
  Int ->
  -- | 表
  BinomMI m ->
  -- | @nCk@。@k < 0@ や @k > n@ (や @n < 0@) なら 0
  ModInt m
chooseMI n k t@(BinomMI fact inv)
  | n < 0 || k < 0 || k > n = 0
  | otherwise = binomCheck "chooseMI" n t `seq` (U.unsafeIndex fact n * U.unsafeIndex inv k * U.unsafeIndex inv (n - k))
{-# INLINE chooseMI #-}

-- | @nPk@ (@n@ 個から @k@ 個を選んで並べる)。O(1)。
permMI ::
  (Modulus m) =>
  -- | @n@: 表の大きさ以下
  Int ->
  -- | @k@
  Int ->
  -- | 表
  BinomMI m ->
  -- | @nPk@。@k < 0@ や @k > n@ なら 0
  ModInt m
permMI n k t@(BinomMI fact inv)
  | n < 0 || k < 0 || k > n = 0
  | otherwise = binomCheck "permMI" n t `seq` (U.unsafeIndex fact n * U.unsafeIndex inv (n - k))
{-# INLINE permMI #-}

-- | @nHk = (n + k - 1)Ck@ (@n@ 種類から重複を許して @k@ 個)。O(1)。
multichooseMI ::
  (Modulus m) =>
  -- | @n@: 種類の数
  Int ->
  -- | @k@: 選ぶ個数
  Int ->
  -- | 表 (@n + k - 1@ まで要る)
  BinomMI m ->
  -- | @nHk@ (@nH0 = 1@)
  ModInt m
multichooseMI n k t
  | k == 0 = if n >= 0 then 1 else 0
  | otherwise = chooseMI (n + k - 1) k t
{-# INLINE multichooseMI #-}
