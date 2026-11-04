{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | セグメント木 (可変)。通常のものと遅延伝播のものを同じ型・同じ関数で扱う。
--
-- 区間は半開区間 @[l, r)@、添字は 0 始まり。
--
-- == 型
--
-- > SegTree m v a f     m: IO か ST s
-- >                     v: 置き場所 (U.Vector / V.Vector)。値と作用で共通
-- >                     a: 値。'Monoid' であること
-- >                     f: 作用。通常のセグ木では ()
--
-- 値は base の 'Monoid' をそのまま使う ('Sum' / 'Min' / 'Max' / 'First' / 'Last' /
-- 'Dual' など。タプルも各成分ごとのモノイドになる)。'Data.Semigroup' から import する。
-- 'Min' / 'Max' の単位元は 'maxBound' / 'minBound'。
--
-- > t <- buildSG (U.map Min as)                       -- 1 点更新・区間最小
-- > t <- buildSG (U.replicate n (mempty :: Sum Int))  -- 単位元で埋めて作る
-- > t <- buildLazySG (withLenSG as)                   -- 遅延版 (作用は使い方から決まる)
--
-- 演算をその場で渡して作ることもできる (newtype で包まなくてよい)。
--
-- > t <- buildWithSG (+) 0 as                         -- 区間和 (値は Int のまま)
-- > t <- buildWithSG min maxBound as                  -- 区間最小
-- > t <- buildWithSG gcd 0 as                         -- 区間 gcd
-- > t <- buildLazyWithSG max (-(10 ^ 18)) (+) (+) 0 as  -- 区間加算・区間最大
--
-- 'buildLazyWithSG' の引数は順に、値の演算、単位元、作用のかけ方 @act f x@、
-- 作用の合成 @comp f g@ (「g の後に f」。新しい作用が左)、何もしない作用。
-- 渡した演算が条件 (下の「作用」の節) を満たすかは確かめない。
-- 単位元に作用がかかることがあるので、遅延版の単位元は 'maxBound' のような端の値ではなく、
-- 足しても溢れない値 (@10 ^ 18@ など) にする (Atc.Graph の @inf@ は maxBound なので使わない)。
--
-- 他の関数は、どのビルダーで作った木にも同じように使える。
--
-- == 関数
--
-- > lengthSG t                 Int     要素数
-- > foldSG l r t               m a     [l, r) の集約 (空なら単位元)
-- > modifySG i g t             m ()    i 番目を g で書き換える
-- > applySG l r f t            m ()    [l, r) に作用 f をかける (遅延版のみ意味がある)
-- > maxRightSG l p t           m Int   p (fold [l, r)) が真である最大の r
-- > minLeftSG r p t            m Int   p (fold [l, r)) が真である最小の l
-- > toVecSG t                  m (v a) すべての要素
--
-- > foldSG i (i + 1) t         -- 1 点の取得
-- > modifySG i (const x) t     -- 1 点の代入
-- > modifySG i (<> x) t        -- 1 点に足し込む
-- > foldSG 0 (lengthSG t) t    -- 全体
--
-- 作る関数と 'toVecSG' は O(n)、ほかは O(log n)。
-- 範囲外の添字はエラーになる。
--
-- == 二分探索
--
-- 'maxRightSG' / 'minLeftSG' の @p@ は単位元で真で、区間を伸ばすと真から偽に
-- 1 回だけ切り替わること (単位元で偽ならエラー)。
--
-- > maxRightSG l (\(Sum s) -> s <= k) t    -- l から和が k 以下で伸ばせる右端 (r は含まない)
-- > minLeftSG r (\(Min m) -> m >= x) t     -- r の手前から、最小が x 以上で伸ばせる左端
--
-- == 作用 (遅延版)
--
-- 'buildLazySG' では、作用 @f@ は 'Monoid' で、'ActSG' のインスタンスを持つこと。
-- 次を満たす必要がある ('buildLazyWithSG' でも、渡す関数で同じことが要る)。
--
-- > actSG mempty x = x
-- > actSG (f <> g) x = actSG f (actSG g x)            -- f <> g は「g の後に f」
-- > actSG f (x <> y) = actSG f x <> actSG f y        -- 準同型
--
-- 和に作用させるときは長さが要るので、値を @(Sum 和, Sum 長さ)@ にする ('withLenSG')。
-- 用意してある作用:
--
-- > AddSG c        加算        Min a / Max a / (Sum a, Sum a)
-- > SetSG (Just x) 代入        Min a / Max a / (Sum a, Sum a)
-- > AffineSG b c   x ↦ b x + c  (Sum a, Sum a)
--
-- > t <- buildLazySG (withLenSG (U.replicate n 0))
-- > applySG l r (AddSG 3) t                          -- [l, r) に 3 を足す
-- > getSum . fst <$> foldSG l r t                    -- [l, r) の和
--
-- 剰余つきのアフィン変換などは、剰余の 'Num' を持つ型を自分で作って @AffineSG@ に渡す
-- (例は examples/SegTree.hs)。
--
-- 用意してある値: 'GcdSG' (区間 gcd、単位元は 0)。
--
-- 用意してある作用は、値の型から中身の型が決まる (@AddSG 1@ と書けば @AddSG Int@ になる)。
-- 自分でインスタンスを書くときも、中身を @a ~ Int@ の形にしておくと型注釈が要らない。
--
-- > instance (a ~ Int) => ActSG (AffineSG a) P where ...   -- AffineSG 2 1 で推論できる
--
-- == 置き場所
--
-- 用意してある値と作用は 'U.Vector' に置ける。自分で作った型は 'V.Vector' に置くか、
-- 'U.IsoUnbox' で 'U.Unbox' のインスタンスを作る (例は examples/SegTree.hs)。
--
-- 値と作用は書き込むときに WHNF まで評価する。'V.Vector' では次の点に注意する。
--
-- * タプルの成分は評価されずに残る。タプルは 'U.Vector' に置くか、正格なフィールドの
--   data を作る。
-- * 遅延版は 'U.Vector' より 1 桁ほど遅い (2×10^5 件で約 2 秒。ほとんどが GC)。
--   置けるなら 'U.Vector' にする。通常のセグ木は 2 倍ほどで済む。
module Atc.SegTree where

import Control.Monad (forM_, when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Data.Bits (countTrailingZeros, shiftL, shiftR, (.&.))
import Data.Semigroup (Max (..), Min (..), Sum (..))
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
-- atc bundle は newtype instance を型の宣言として読み、修飾なしの MVector(..) / Vector(..) を
-- export に書く。それが通るよう、修飾なしでも import しておく。
import Data.Vector.Unboxed (MVector, Vector)

-- ---------------------------------------------------------------------
-- 作用

-- | 作用 @f@ を値 @a@ にかける。満たすべき条件はモジュールの説明を参照。
class (Monoid f, Monoid a) => ActSG f a where
  actSG :: f -> a -> a

-- | 通常のセグ木の作用 (何もしない)。
instance (Monoid a) => ActSG () a where
  {-# INLINE actSG #-}
  actSG _ = id

-- ---------------------------------------------------------------------
-- 本体

-- | セグメント木。葉の数を 2 冪 @sizeSG@ にそろえ、@[sizeSG, sizeSG + n)@ に値を置く。
-- 遅延版でなければ作用の配列は空。演算は作るときに渡したものを持つ。
data SegTree m v a f = SegTree
  { lengthSG :: !Int
  , logSG :: !Int
  , sizeSG :: !Int
  , isLazySG :: !Bool
  , nodesSG :: !(G.Mutable v (PrimState m) a)
  , lazySG :: !(G.Mutable v (PrimState m) f)
  , opSG :: a -> a -> a
  , unitSG :: a
  , actOpSG :: f -> a -> a
  , composeSG :: f -> f -> f
  , idActSG :: f
  }

-- | 通常のセグ木を作る。値の 'Monoid' を使う。O(n)。
{-# INLINE buildSG #-}
buildSG :: (PrimMonad m, G.Vector v a, G.Vector v (), Monoid a) => v a -> m (SegTree m v a ())
buildSG = buildWithSG (<>) mempty

-- | 遅延セグ木を作る。値の 'Monoid' と 'ActSG' を使い、作用 @f@ は 'applySG' の使い方から決まる。O(n)。
{-# INLINE buildLazySG #-}
buildLazySG :: (PrimMonad m, G.Vector v a, G.Vector v f, ActSG f a) => v a -> m (SegTree m v a f)
buildLazySG = buildLazyWithSG (<>) mempty actSG (<>) mempty

-- | @buildWithSG op e xs@: 演算 @op@ と単位元 @e@ を渡して通常のセグ木を作る。O(n)。
{-# INLINE buildWithSG #-}
buildWithSG :: (PrimMonad m, G.Vector v a, G.Vector v ()) => (a -> a -> a) -> a -> v a -> m (SegTree m v a ())
buildWithSG op e = buildCoreSG False op e (\_ x -> x) (\_ _ -> ()) ()

-- | @buildLazyWithSG op e act comp idf xs@: 演算と作用を渡して遅延セグ木を作る。O(n)。
--
-- * @op@ / @e@: 値の演算と単位元
-- * @act f x@: 作用 @f@ を値 @x@ にかける
-- * @comp f g@: 「@g@ の後に @f@」をかける作用 (新しい作用が左)
-- * @idf@: 何もしない作用
{-# INLINE buildLazyWithSG #-}
buildLazyWithSG ::
  (PrimMonad m, G.Vector v a, G.Vector v f) =>
  (a -> a -> a) -> a -> (f -> a -> a) -> (f -> f -> f) -> f -> v a -> m (SegTree m v a f)
buildLazyWithSG = buildCoreSG True

-- | @[l, r)@ の集約。空なら単位元。O(log n)。
{-# INLINE foldSG #-}
foldSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> Int -> SegTree m v a f -> m a
foldSG l r t
  | l < 0 || r > lengthSG t || l > r = error ("foldSG: 範囲外: " ++ show (l, r))
  | l == r = pure e
  | otherwise = do
      let l0 = l + sizeSG t
          r0 = r + sizeSG t
      pushBoundsSG l0 r0 t
      let go !i !j !sml !smr
            | i >= j = pure (op sml smr)
            | otherwise = do
                sml' <- if odd i then op sml <$> GM.unsafeRead d i else pure sml
                smr' <- if odd j then (`op` smr) <$> GM.unsafeRead d (j - 1) else pure smr
                go ((i + 1) `shiftR` 1) (j `shiftR` 1) sml' smr'
      go l0 r0 e e
  where
    d = nodesSG t
    op = opSG t
    e = unitSG t

-- | @i@ 番目を @g@ で書き換える。O(log n)。
{-# INLINE modifySG #-}
modifySG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> (a -> a) -> SegTree m v a f -> m ()
modifySG i g t
  | i < 0 || i >= lengthSG t = error ("modifySG: 範囲外: " ++ show i)
  | otherwise = do
      let k = i + sizeSG t
          d = nodesSG t
      when (isLazySG t) $ forM_ [logSG t, logSG t - 1 .. 1] $ \s -> pushSG (k `shiftR` s) t
      x <- GM.unsafeRead d k
      GM.unsafeWrite d k $! g x
      forM_ [1 .. logSG t] $ \s -> updateSG (k `shiftR` s) t

-- | @[l, r)@ に作用 @f@ をかける。通常のセグ木 (作用が ()) では何もしない。O(log n)。
{-# INLINE applySG #-}
applySG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> Int -> f -> SegTree m v a f -> m ()
applySG l r f t
  | l < 0 || r > lengthSG t || l > r = error ("applySG: 範囲外: " ++ show (l, r))
  | l == r || not (isLazySG t) = pure ()
  | otherwise = do
      let l0 = l + sizeSG t
          r0 = r + sizeSG t
      pushBoundsSG l0 r0 t
      let go !i !j = when (i < j) $ do
            when (odd i) $ allApplySG i f t
            when (odd j) $ allApplySG (j - 1) f t
            go ((i + 1) `shiftR` 1) (j `shiftR` 1)
      go l0 r0
      forM_ [1 .. logSG t] $ \s -> do
        when (((l0 `shiftR` s) `shiftL` s) /= l0) $ updateSG (l0 `shiftR` s) t
        when (((r0 `shiftR` s) `shiftL` s) /= r0) $ updateSG ((r0 - 1) `shiftR` s) t

-- | @maxRightSG l p t@: @p (fold [l, r))@ が真である最大の @r@。O(log n)。
{-# INLINE maxRightSG #-}
maxRightSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> (a -> Bool) -> SegTree m v a f -> m Int
maxRightSG l p t
  | l < 0 || l > n = error ("maxRightSG: 範囲外: " ++ show l)
  | not (p (unitSG t)) = error "maxRightSG: p (単位元) が偽"
  | l == n = pure n
  | otherwise = do
      let k0 = l + size
      when (isLazySG t) $ forM_ [logSG t, logSG t - 1 .. 1] $ \s -> pushSG (k0 `shiftR` s) t
      up k0 (unitSG t)
  where
    n = lengthSG t
    size = sizeSG t
    d = nodesSG t
    op = opSG t
    up k0 !sm = do
      let k = k0 `shiftR` countTrailingZeros k0
      x <- GM.unsafeRead d k
      let sm' = op sm x
      if not (p sm')
        then down k sm
        else
          let k' = k + 1
           in if k' .&. negate k' == k' then pure n else up k' sm'
    down k !sm
      | k >= size = pure (k - size)
      | otherwise = do
          when (isLazySG t) $ pushSG k t
          let c = 2 * k
          x <- GM.unsafeRead d c
          let sm' = op sm x
          if p sm' then down (c + 1) sm' else down c sm

-- | @minLeftSG r p t@: @p (fold [l, r))@ が真である最小の @l@。O(log n)。
{-# INLINE minLeftSG #-}
minLeftSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> (a -> Bool) -> SegTree m v a f -> m Int
minLeftSG r p t
  | r < 0 || r > lengthSG t = error ("minLeftSG: 範囲外: " ++ show r)
  | not (p (unitSG t)) = error "minLeftSG: p (単位元) が偽"
  | r == 0 = pure 0
  | otherwise = do
      let k0 = r + size
      when (isLazySG t) $ forM_ [logSG t, logSG t - 1 .. 1] $ \s -> pushSG ((k0 - 1) `shiftR` s) t
      up k0 (unitSG t)
  where
    size = sizeSG t
    d = nodesSG t
    op = opSG t
    shrink k = if k > 1 && odd k then shrink (k `shiftR` 1) else k
    up k0 !sm = do
      let k = shrink (k0 - 1)
      x <- GM.unsafeRead d k
      let sm' = op x sm
      if not (p sm')
        then down k sm
        else if k .&. negate k == k then pure 0 else up k sm'
    down k !sm
      | k >= size = pure (k + 1 - size)
      | otherwise = do
          when (isLazySG t) $ pushSG k t
          let c = 2 * k + 1
          x <- GM.unsafeRead d c
          let sm' = op x sm
          if p sm' then down (c - 1) sm' else down c sm

-- | すべての要素を順に並べたベクタ。O(n)。
{-# INLINE toVecSG #-}
toVecSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => SegTree m v a f -> m (v a)
toVecSG t = do
  when (isLazySG t) $ forM_ [1 .. sizeSG t - 1] $ \k -> pushSG k t
  G.freeze (GM.unsafeSlice (sizeSG t) (lengthSG t) (nodesSG t))

-- | 値を @(Sum 値, Sum 1)@ にする。和に作用させる遅延セグ木の材料。
{-# INLINE withLenSG #-}
withLenSG :: (G.Vector v a, G.Vector v (Sum a, Sum a), Num a) => v a -> v (Sum a, Sum a)
withLenSG = G.map (\x -> (Sum x, Sum 1))

-- ---------------------------------------------------------------------
-- 用意してある値と作用

-- | 区間 gcd の値。単位元は 0。
newtype GcdSG a = GcdSG {getGcdSG :: a}
  deriving (Eq, Ord, Show)

instance (Integral a) => Semigroup (GcdSG a) where
  {-# INLINE (<>) #-}
  GcdSG a <> GcdSG b = GcdSG (gcd a b)

instance (Integral a) => Monoid (GcdSG a) where
  {-# INLINE mempty #-}
  mempty = GcdSG 0

-- | 加算の作用。'Min' / 'Max' の単位元 ('maxBound' / 'minBound') には足さない。
newtype AddSG a = AddSG {getAddSG :: a}
  deriving (Eq, Ord, Show)

instance (Num a) => Semigroup (AddSG a) where
  {-# INLINE (<>) #-}
  AddSG a <> AddSG b = AddSG (a + b)

instance (Num a) => Monoid (AddSG a) where
  {-# INLINE mempty #-}
  mempty = AddSG 0

instance (a ~ b, Ord a, Bounded a, Num a) => ActSG (AddSG a) (Min b) where
  {-# INLINE actSG #-}
  actSG (AddSG c) (Min x)
    | x == maxBound = Min x
    | otherwise = Min (x + c)

instance (a ~ b, Ord a, Bounded a, Num a) => ActSG (AddSG a) (Max b) where
  {-# INLINE actSG #-}
  actSG (AddSG c) (Max x)
    | x == minBound = Max x
    | otherwise = Max (x + c)

instance (a ~ b, a ~ c, Num a) => ActSG (AddSG a) (Sum b, Sum c) where
  {-# INLINE actSG #-}
  actSG (AddSG c) (Sum s, Sum len) = let !s' = s + c * len in (Sum s', Sum len)

-- | 代入の作用。@SetSG Nothing@ が何もしない作用で、@f <> g@ では新しい @f@ が勝つ。
newtype SetSG a = SetSG {getSetSG :: Maybe a}
  deriving (Eq, Ord, Show)

instance Semigroup (SetSG a) where
  {-# INLINE (<>) #-}
  SetSG Nothing <> g = g
  f <> _ = f

instance Monoid (SetSG a) where
  {-# INLINE mempty #-}
  mempty = SetSG Nothing

instance (a ~ b, Ord a, Bounded a) => ActSG (SetSG a) (Min b) where
  {-# INLINE actSG #-}
  actSG (SetSG m) v = maybe v Min m

instance (a ~ b, Ord a, Bounded a) => ActSG (SetSG a) (Max b) where
  {-# INLINE actSG #-}
  actSG (SetSG m) v = maybe v Max m

instance (a ~ b, a ~ c, Num a) => ActSG (SetSG a) (Sum b, Sum c) where
  {-# INLINE actSG #-}
  actSG (SetSG Nothing) v = v
  actSG (SetSG (Just x)) (_, Sum len) = let !s' = x * len in (Sum s', Sum len)

-- | アフィン変換 @x ↦ b x + c@ の作用。@AffineSG b1 c1 <> AffineSG b2 c2@ は
-- 2 を先にかけたもの。
data AffineSG a = AffineSG !a !a
  deriving (Eq, Ord, Show)

instance (Num a) => Semigroup (AffineSG a) where
  {-# INLINE (<>) #-}
  AffineSG b1 c1 <> AffineSG b2 c2 = AffineSG (b1 * b2) (b1 * c2 + c1)

instance (Num a) => Monoid (AffineSG a) where
  {-# INLINE mempty #-}
  mempty = AffineSG 1 0

instance (a ~ b, a ~ c, Num a) => ActSG (AffineSG a) (Sum b, Sum c) where
  {-# INLINE actSG #-}
  actSG (AffineSG b c) (Sum s, Sum len) = let !s' = b * s + c * len in (Sum s', Sum len)

-- U.Vector に置くためのインスタンス。

instance U.IsoUnbox (GcdSG a) a where
  {-# INLINE toURepr #-}
  toURepr (GcdSG x) = x
  {-# INLINE fromURepr #-}
  fromURepr = GcdSG

newtype instance MVector s (GcdSG a) = MV_GcdSG (MVector s a)

newtype instance Vector (GcdSG a) = V_GcdSG (Vector a)

deriving via (U.As (GcdSG a) a) instance (U.Unbox a) => GM.MVector U.MVector (GcdSG a)

deriving via (U.As (GcdSG a) a) instance (U.Unbox a) => G.Vector U.Vector (GcdSG a)

instance (U.Unbox a) => U.Unbox (GcdSG a)

instance U.IsoUnbox (AddSG a) a where
  {-# INLINE toURepr #-}
  toURepr (AddSG x) = x
  {-# INLINE fromURepr #-}
  fromURepr = AddSG

newtype instance MVector s (AddSG a) = MV_AddSG (MVector s a)

newtype instance Vector (AddSG a) = V_AddSG (Vector a)

deriving via (U.As (AddSG a) a) instance (U.Unbox a) => GM.MVector U.MVector (AddSG a)

deriving via (U.As (AddSG a) a) instance (U.Unbox a) => G.Vector U.Vector (AddSG a)

instance (U.Unbox a) => U.Unbox (AddSG a)

-- Nothing は (False, 0) で持つ。
instance (Num a) => U.IsoUnbox (SetSG a) (Bool, a) where
  {-# INLINE toURepr #-}
  toURepr (SetSG Nothing) = (False, 0)
  toURepr (SetSG (Just x)) = (True, x)
  {-# INLINE fromURepr #-}
  fromURepr (b, x) = SetSG (if b then Just x else Nothing)

newtype instance MVector s (SetSG a) = MV_SetSG (MVector s (Bool, a))

newtype instance Vector (SetSG a) = V_SetSG (Vector (Bool, a))

deriving via (U.As (SetSG a) (Bool, a)) instance (Num a, U.Unbox a) => GM.MVector U.MVector (SetSG a)

deriving via (U.As (SetSG a) (Bool, a)) instance (Num a, U.Unbox a) => G.Vector U.Vector (SetSG a)

instance (Num a, U.Unbox a) => U.Unbox (SetSG a)

instance U.IsoUnbox (AffineSG a) (a, a) where
  {-# INLINE toURepr #-}
  toURepr (AffineSG b c) = (b, c)
  {-# INLINE fromURepr #-}
  fromURepr (b, c) = AffineSG b c

newtype instance MVector s (AffineSG a) = MV_AffineSG (MVector s (a, a))

newtype instance Vector (AffineSG a) = V_AffineSG (Vector (a, a))

deriving via (U.As (AffineSG a) (a, a)) instance (U.Unbox a) => GM.MVector U.MVector (AffineSG a)

deriving via (U.As (AffineSG a) (a, a)) instance (U.Unbox a) => G.Vector U.Vector (AffineSG a)

instance (U.Unbox a) => U.Unbox (AffineSG a)

-- ---------------------------------------------------------------------
-- 以下は内部用。

{-# INLINE buildCoreSG #-}
buildCoreSG ::
  (PrimMonad m, G.Vector v a, G.Vector v f) =>
  Bool -> (a -> a -> a) -> a -> (f -> a -> a) -> (f -> f -> f) -> f -> v a -> m (SegTree m v a f)
buildCoreSG lazy op e act comp idf xs = do
  let n = G.length xs
      lg = head [k | k <- [0 ..], 1 `shiftL` k >= n]
      size = 1 `shiftL` lg :: Int
  d <- GM.replicate (2 * size) e
  forM_ [0 .. n - 1] $ \i -> GM.unsafeWrite d (size + i) $! G.unsafeIndex xs i
  lz <- GM.replicate (if lazy then size else 0) idf
  let t = SegTree n lg size lazy d lz op e act comp idf
  forM_ [size - 1, size - 2 .. 1] $ \k -> updateSG k t
  pure t

-- 節点 k を子から作り直す。
{-# INLINE updateSG #-}
updateSG :: (PrimMonad m, G.Vector v a) => Int -> SegTree m v a f -> m ()
updateSG k t = do
  x <- GM.unsafeRead d (2 * k)
  y <- GM.unsafeRead d (2 * k + 1)
  GM.unsafeWrite d k $! opSG t x y
  where
    d = nodesSG t

-- 節点 k に f をかけ、内部の節点なら f を溜める。
{-# INLINE allApplySG #-}
allApplySG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> f -> SegTree m v a f -> m ()
allApplySG k f t = do
  x <- GM.unsafeRead (nodesSG t) k
  GM.unsafeWrite (nodesSG t) k $! actOpSG t f x
  when (k < sizeSG t) $ do
    g <- GM.unsafeRead (lazySG t) k
    GM.unsafeWrite (lazySG t) k $! composeSG t f g

-- 節点 k に溜めた作用を子に流す。
{-# INLINE pushSG #-}
pushSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> SegTree m v a f -> m ()
pushSG k t = do
  f <- GM.unsafeRead (lazySG t) k
  allApplySG (2 * k) f t
  allApplySG (2 * k + 1) f t
  GM.unsafeWrite (lazySG t) k $! idActSG t

-- 葉 l0 と r0 (r0 は含まない) の祖先に溜めた作用を、上から流す。遅延版でなければ何もしない。
{-# INLINE pushBoundsSG #-}
pushBoundsSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> Int -> SegTree m v a f -> m ()
pushBoundsSG l0 r0 t =
  when (isLazySG t) $ forM_ [logSG t, logSG t - 1 .. 1] $ \s -> do
    when (((l0 `shiftR` s) `shiftL` s) /= l0) $ pushSG (l0 `shiftR` s) t
    when (((r0 `shiftR` s) `shiftL` s) /= r0) $ pushSG ((r0 - 1) `shiftR` s) t
