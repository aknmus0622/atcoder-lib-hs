-- | "Atc.SegTree" を使った問題。
--
-- 作るときに演算と単位元を渡す。base の 'Monoid' ('Sum' / 'Min' / 'Max' やそのタプル) を
-- 使うときは @(<>)@ と 'mempty' を渡す。
-- 区間は半開区間 @[l, r)@、添字は 0 始まり。
module SegTree where

import Atc
import Control.Monad (forM_)
import Data.Semigroup (Min (..), Sum (..))
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 1 点更新・区間最小。@0 i x@ で a_i を x にし、@1 l r@ で [l, r) の最小を出力する。
rangeMin :: IO ()
rangeMin = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildSG (<>) mempty (U.map Min as)
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, i, x] -> modifySG i (const (Min x)) t
      [_, l, r] -> foldSG l r t >>= print . getMin
      _ -> error "query"

-- | 'rangeMin' を、'Min' で包まずに書いたもの。値は 'Int' のまま。
rangeMinInt :: IO ()
rangeMinInt = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildSG min maxBound as
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, i, x] -> modifySG i (const x) t
      [_, l, r] -> foldSG l r t >>= print
      _ -> error "query"

-- | 区間加算・区間最大。@0 l r x@ で [l, r) に x を足し、
-- @1 l r@ で [l, r) の最大を出力する。
-- 単位元にも作用がかかるので、'minBound' ではなく溢れない @-10^18@ にする。
rangeAddMax :: IO ()
rangeAddMax = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildLazySG max (-(10 ^ (18 :: Int))) (+) (+) 0 as
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, l, r, x] -> applySG l r x t
      [_, l, r] -> foldSG l r t >>= print
      _ -> error "query"

-- | 1 点更新・区間平均。@0 i x@ で a_i を x にし、@1 l r@ で [l, r) の平均を出力する。
-- 平均どうしは合わせられないが、(和, 個数) にすれば成分ごとの和で合わせられる。
-- 平均は最後に 和 / 個数 で出す。
rangeAverage :: IO ()
rangeAverage = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  let op (s1, c1) (s2, c2) = (s1 + s2, c1 + c2)
  t <- buildSG op (0, 0) (U.map (\a -> (a, 1 :: Int)) as)
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, i, x] -> modifySG i (const (x, 1)) t
      [_, l, r] -> do
        (s, c) <- foldSG l r t
        print (fromIntegral s / fromIntegral c :: Double)
      _ -> error "query"

-- | 'rangeAddSum' を、用意してある作用を使わずに書いたもの。値は (和, 長さ)、作用は足す数。
--
-- * 値の演算: 成分ごとの和。単位元は (0, 0)。
-- * @act x (s, len) = (s + x len, len)@: 子を見ずに節点の和を直せる (長さを持つ理由)。
-- * 合成: +x の後に +y は +(x + y)。何もしない作用は 0。
rangeAddSumRaw :: IO ()
rangeAddSumRaw = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  let op (s1, l1) (s2, l2) = (s1 + s2, l1 + l2)
      act x (s, len) = (s + x * len, len)
  t <- buildLazySG op (0, 0) act (+) 0 (U.map (\a -> (a, 1 :: Int)) as)
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, l, r, x] -> applySG l r x t
      [_, l, r] -> foldSG l r t >>= print . fst
      _ -> error "query"

-- | 区間加算・区間和。@0 l r x@ で [l, r) に x を足し、@1 l r@ で [l, r) の和を出力する。
-- 和に足すには長さが要るので、値を (和, 長さ) にする ('withLenSG')。
rangeAddSum :: IO ()
rangeAddSum = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildLazySG (<>) mempty actSG (<>) mempty (withLenSG as)
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, l, r, x] -> applySG l r (AddSG x) t
      [_, l, r] -> foldSG l r t >>= print . getSum . fst
      _ -> error "query"

-- | 区間アフィン・区間和 (mod 998244353)。@0 l r b c@ で [l, r) の各 a_i を
-- b a_i + c にし、@1 l r@ で [l, r) の和を出力する。
--
-- 剰余の型は "Atc.ModInt" の 'Mint' を使う ('U.Vector' にもそのまま置ける)。
rangeAffineSum :: IO ()
rangeAffineSum = do
  [_, q] <- ints
  as <- U.fromList . map fromIntegral <$> ints
  t <- buildLazySG (<>) mempty actSG (<>) mempty (withLenSG (as :: U.Vector Mint))
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      [0, l, r, b, c] -> applySG l r (AffineSG (fromIntegral b) (fromIntegral c)) t
      [_, l, r] -> foldSG l r t >>= print . getSum . fst
      _ -> error "query"

-- | 二分探索: 非負の列で、各問い合わせ @l k@ に「[l, r) の和が k 以下になる最大の r」を出力する。
-- 条件 @(<= k)@ は区間を伸ばすと真から偽に 1 回だけ変わる (値が非負なので)。
longestPrefix :: IO ()
longestPrefix = do
  [_, q] <- ints
  as <- U.fromList <$> ints
  t <- buildSG (+) 0 as
  forM_ [1 .. q] $ \_ -> do
    [l, k] <- ints
    maxRightSG l (<= k) t >>= print

-- | 非可換の例: 2×2 行列の積 (mod 998244353)。@0 i a b c d@ で i 番目の行列を
-- 置きかえ、@1 l r@ で M_l M_{l+1} ... M_{r-1} を出力する。
-- 'U.Unbox' を作らずに 'V.Vector' に置く (遅延版でなければ速さは十分)。
matrixProduct :: IO ()
matrixProduct = do
  [n, q] <- ints
  ms <- V.replicateM n (toM2 <$> ints)
  t <- buildSG (<>) mempty ms
  forM_ [1 .. q] $ \_ -> do
    qu <- ints
    case qu of
      0 : i : xs -> modifySG i (const (toM2 xs)) t
      [_, l, r] -> do
        M2 a b c d <- foldSG l r t
        putStrLn (unwords (map show [a, b, c, d]))
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
