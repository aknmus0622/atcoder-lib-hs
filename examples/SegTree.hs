{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | "Atc.SegTree" を使った問題。
--
-- 値は base の 'Monoid' ('Sum' / 'Min' / 'Max' やそのタプル) をそのまま使う。
-- 区間は半開区間 @[l, r)@、添字は 0 始まり。
module SegTree where

import Atc
import Control.Monad (forM_)
import Data.Semigroup (Min (..), Sum (..))
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 1 点更新・区間最小。@0 i x@ で a_i を x にし、@1 l r@ で [l, r) の最小を出力する。
rangeMin :: IO ()
rangeMin = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildSG (U.map Min as)
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, i, x] -> modifySG i (const (Min x)) t
      [_, l, r] -> foldSG l r t >>= print . getMin
      _ -> error "query"

-- | 区間加算・区間和。@0 l r x@ で [l, r) に x を足し、@1 l r@ で [l, r) の和を出力する。
-- 和に足すには長さが要るので、値を (和, 長さ) にする ('withLenSG')。
rangeAddSum :: IO ()
rangeAddSum = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildLazySG (withLenSG as)
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, l, r, x] -> applySG l r (AddSG x) t
      [_, l, r] -> foldSG l r t >>= print . getSum . fst
      _ -> error "query"

-- | 区間アフィン・区間和 (mod 998244353)。@0 l r b c@ で [l, r) の各 a_i を
-- b a_i + c にし、@1 l r@ で [l, r) の和を出力する。
--
-- 剰余の型 'Mint' を作って 'AffineSG' に渡す。'U.Vector' に置くため、
-- 'U.IsoUnbox' で 'U.Unbox' のインスタンスも作る (下の 6 行)。
rangeAffineSum :: IO ()
rangeAffineSum = do
  [_, q] <- ints
  as <- U.fromList . map fromIntegral <$> ints
  t <- buildLazySG (withLenSG (as :: U.Vector Mint))
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, l, r, b, c] -> applySG l r (AffineSG (fromIntegral b) (fromIntegral c)) t
      [_, l, r] -> foldSG l r t >>= print . getMint . getSum . fst
      _ -> error "query"

-- | 998244353 で割った余り。
newtype Mint = Mint {getMint :: Int}
  deriving (Eq, Show)

instance Num Mint where
  Mint a + Mint b = Mint ((a + b) `mod` 998244353)
  Mint a - Mint b = Mint ((a - b) `mod` 998244353)
  Mint a * Mint b = Mint (a * b `mod` 998244353)
  fromInteger x = Mint (fromInteger (x `mod` 998244353))
  abs = id
  signum = const 1

instance U.IsoUnbox Mint Int where
  toURepr = getMint
  fromURepr = Mint

newtype instance U.MVector s Mint = MV_Mint (U.MVector s Int)

newtype instance U.Vector Mint = V_Mint (U.Vector Int)

deriving via (U.As Mint Int) instance GM.MVector U.MVector Mint

deriving via (U.As Mint Int) instance G.Vector U.Vector Mint

instance U.Unbox Mint

-- | 二分探索: 非負の列で、各問い合わせ @l k@ に「[l, r) の和が k 以下になる最大の r」を出力する。
-- 条件 @(<= k)@ は区間を伸ばすと真から偽に 1 回だけ変わる (値が非負なので)。
longestPrefix :: IO ()
longestPrefix = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildSG (U.map Sum as)
  forM_ [1 .. q] $ \_ -> do
    [l, k] <- ints
    maxRightSG l (\(Sum s) -> s <= k) t >>= print

-- | 非可換の例: 2×2 行列の積 (mod 998244353)。@0 i a b c d@ で i 番目の行列を
-- 置きかえ、@1 l r@ で M_l M_{l+1} ... M_{r-1} を出力する。
-- 'U.Unbox' を作らずに 'V.Vector' に置く (遅延版でなければ速さは十分)。
matrixProduct :: IO ()
matrixProduct = do
  [n, q] <- ints
  ms <- V.replicateM n (toM2 <$> ints)
  t <- buildSG ms
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      0 : i : xs -> modifySG i (const (toM2 xs)) t
      [_, l, r] -> do
        M2 a b c d <- foldSG l r t
        putStrLn (unwords (map (show . getMint) [a, b, c, d]))
      _ -> error "query"
  where
    toM2 [a, b, c, d] = M2 (fromIntegral a) (fromIntegral b) (fromIntegral c) (fromIntegral d)
    toM2 _ = error "matrix"

-- | 2×2 行列 @[[a, b], [c, d]]@。
data M2 = M2 !Mint !Mint !Mint !Mint

instance Semigroup M2 where
  M2 a b c d <> M2 e f g h = M2 (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h)

instance Monoid M2 where
  mempty = M2 1 0 0 1
