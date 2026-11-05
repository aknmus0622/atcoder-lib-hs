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
-- >                     a: 値
-- >                     f: 作用。通常のセグ木では ()
--
-- == 作る
--
-- 演算と単位元を渡して作る。値は 'Int' のままでよい。
--
-- > t <- buildSG (+) 0 as                              -- 区間和
-- > t <- buildSG min maxBound as                       -- 区間最小
-- > t <- buildSG gcd 0 as                              -- 区間 gcd
-- > t <- buildSG (+) 0 (U.replicate n 0)               -- 単位元で埋めて作る
-- > t <- buildLazySG max (-(10 ^ 18)) (+) (+) 0 as     -- 区間加算・区間最大
--
-- 渡すのは不変のベクトル (中身は木の配列にコピーする)。可変のベクトルは凍らせてから渡す。
--
-- > t <- buildSG (+) 0 =<< U.freeze mv                 -- mv をこの後も使う
-- > t <- buildSG (+) 0 =<< U.unsafeFreeze mv           -- mv をこの後は使わない (凍らせるコピーが要らない)
--
-- 'buildLazySG' の引数は順に、値の演算、単位元、作用のかけ方 @act f x@、
-- 作用の合成 @comp f g@ (「g の後に f」。新しい作用が左)、何もしない作用。
-- 渡した演算が条件 (下の「作用」の節) を満たすかは確かめない。
-- 単位元に作用がかかることがあるので、遅延版の単位元は 'maxBound' のような端の値ではなく、
-- 足しても溢れない値 (@10 ^ 18@ など) にする (Atc.Graph の @inf@ は maxBound なので使わない)。
--
-- base の 'Monoid' ('Sum' / 'Min' / 'Max' / 'First' / 'Last' / 'Dual' やそのタプル) を
-- 使うときは @(<>)@ と 'mempty' を渡す。遅延版で 'ActSG' の作用を使うときは 'actSG' も渡す。
--
-- > t <- buildSG (<>) mempty (U.map Min as)
-- > t <- buildLazySG (<>) mempty actSG (<>) mempty (withLenSG as)   -- 作用は使い方から決まる
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
-- > maxRightSG l (<= k) t      -- 区間和の木で、l から和が k 以下で伸ばせる右端 (r は含まない)
-- > minLeftSG r (>= x) t       -- 区間最小の木で、r の手前から最小が x 以上で伸ばせる左端
--
-- == 作用 (遅延版)
--
-- 値の演算 @op@ と単位元 @e@、作用 @act@ / @comp@ / @idf@ は次を満たすこと。
--
-- > op (op x y) z = op x (op y z),  op e x = op x e = x   -- 値がモノイド
-- > comp (comp f g) h = comp f (comp g h)                 -- 作用がモノイド
-- > act idf x = x
-- > act (comp f g) x = act f (act g x)                    -- comp f g は「g の後に f」
-- > act f (op x y) = op (act f x) (act f y)               -- 準同型
--
-- 和に作用させるときは長さが要るので、値を (和, 長さ) にする ('withLenSG')。
--
-- 'ActSG' はこの条件を満たす作用をまとめたクラスで、'actSG' と @(<>)@ / 'mempty' を
-- 'buildLazySG' に渡して使う。用意してある作用:
--
-- > AddSG c        加算        Min a / Max a / (Sum a, Sum a)
-- > SetSG (Just x) 代入        Min a / Max a / (Sum a, Sum a)
-- > AffineSG b c   x ↦ b x + c  (Sum a, Sum a)
--
-- > t <- buildLazySG (<>) mempty actSG (<>) mempty (withLenSG (U.replicate n 0))
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
-- == 仕組み
--
-- 列を半分ずつに分けた区間 (節点) ごとに、その区間の集約を持っておく。
-- 葉の数を 2 冪 @sizeSG@ にそろえ、節点を 1 本の配列 'nodesSG' に置く。
-- 根が 1、節点 @k@ の子が @2k@ と @2k+1@、i 番目の要素が葉 @sizeSG + i@。
-- 余った葉は単位元で埋める。
--
-- > n = 8 (sizeSG = 8) のとき             節点の値 = 左の子 `op` 右の子 (updateSG)
-- >
-- >                     1 [0,8)
-- >           2 [0,4)             3 [4,8)
-- >      4 [0,2)   5 [2,4)   6 [4,6)   7 [6,8)
-- >      8   9    10  11    12  13    14  15      <- 葉 = a_0 .. a_7
--
-- * 取得 ('foldSG'): どの区間も、各段から左右 1 個ずつまでの節点に分けられる
--   (例: [1,6) = 節点 9 [1,2) ・ 節点 5 [2,4) ・ 節点 6 [4,6))。それらを左から順に
--   @op@ で合わせる。O(log n)。
-- * 1 点更新 ('modifySG'): 葉を書き換え、根までの祖先 (@k/2, k/4, ..., 1@) を作り直す。O(log n)。
--
-- このため値の演算に要るのは次の 2 つで、交換則は要らない (左右の順は保つ)。
--
-- * 結合則: 区間の分け方によらず同じ答えになる。
-- * 単位元: 空の区間の答えと、余った葉に使う。
--
-- そのままでは合わせられない値は、情報を足すと合わせられることがある。
-- 例えば平均は (和, 個数) にすれば合わせられる (例は examples/SegTree.hs の @rangeAverage@)。
--
-- === 遅延版
--
-- 区間に作用をかけるとき、葉まで降りると O(n) かかる。そこで、区間を節点に分けたら
-- その節点の値だけ @act f@ で直し、子にかける分は作用の配列 'lazySG' に溜めておく。
-- 子を見る必要が出たときに初めて子に流す。
--
-- > 理論                               ライブラリ
-- > 節点の値に作用をかけて溜める       allApplySG k f   値 = act f 値、溜め = comp f 溜め
-- > 溜めた作用を子に流す               pushSG k         子 2 つに allApplySG、溜め = idf
-- > 読み書きの前に通り道の作用を流す   pushBoundsSG     区間の両端の祖先だけ、上から
--
-- 上の「作用」の節の条件は、それぞれ次のために要る。
--
-- * @act f (op x y) = op (act f x) (act f y)@: 子を見ずに節点の値を直せる。
--   和に足すなら長さが要るので、値を (和, 長さ) にする ('withLenSG')。
-- * @act (comp f g) x = act f (act g x)@: 溜めた作用が 1 つにまとまり、大きさが増えない。
-- * @act idf x = x@: 溜めた作用がないことを表す。
--
-- 'applySG' は、作用を流す ('pushBoundsSG') → 区間を節点に分けて 'allApplySG' →
-- 両端の祖先を作り直す ('updateSG') の順に動く。先に流すのは、祖先に溜めた作用を
-- 作り直しで消さないため。
--
-- 'buildSG' は作用を @()@ にした遅延版で、@isLazySG = False@ により溜める配列を持たず、
-- 流す処理も飛ばす。
--
-- === 二分探索
--
-- 'maxRightSG' は @l@ から右へ節点単位で集約を伸ばし、次の節点を足すと @p@ が偽になる
-- ところで、その節点の中へ降りる (左の子を足しても真なら右の子へ、偽なら左の子へ)。
-- 外から 'foldSG' を二分探索すると O(log² n) だが、これは O(log n)。'minLeftSG' は左向き。
--
-- == 置き場所
--
-- 用意してある値と作用、"Atc.ModInt" の 'Mint' は 'U.Vector' に置ける。自分で作った型は
-- 'V.Vector' に置くか、'U.IsoUnbox' で 'U.Unbox' のインスタンスを作る
-- (作り方は "Atc.ModInt" の 'ModInt' のインスタンスと同じ)。
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
-- 'buildLazySG' に @(<>) mempty actSG (<>) mempty@ と渡して使う。
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

-- | @buildSG op e xs@: 演算 @op@ と単位元 @e@ を渡して通常のセグ木を作る。O(n)。
{-# INLINE buildSG #-}
buildSG :: (PrimMonad m, G.Vector v a, G.Vector v ()) => (a -> a -> a) -> a -> v a -> m (SegTree m v a ())
buildSG op e = buildCoreSG False op e (\_ x -> x) (\_ _ -> ()) ()

-- | @buildLazySG op e act comp idf xs@: 演算と作用を渡して遅延セグ木を作る。O(n)。
--
-- * @op@ / @e@: 値の演算と単位元
-- * @act f x@: 作用 @f@ を値 @x@ にかける
-- * @comp f g@: 「@g@ の後に @f@」をかける作用 (新しい作用が左)
-- * @idf@: 何もしない作用
{-# INLINE buildLazySG #-}
buildLazySG ::
  (PrimMonad m, G.Vector v a, G.Vector v f) =>
  (a -> a -> a) -> a -> (f -> a -> a) -> (f -> f -> f) -> f -> v a -> m (SegTree m v a f)
buildLazySG = buildCoreSG True

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
      -- 葉の段から 1 段ずつ上がる。i が奇数 (右の子) ならその親は区間からはみ出すので、
      -- 節点 i を取って右へずらす。j の側も同じ。左で取ったものは sml の右に、
      -- 右で取ったものは smr の左に付けて、左右の順を保つ。
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
      -- 葉までの祖先に溜めた作用を上から流し、葉を書き換え、祖先を下から作り直す。
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
      -- 先に両端の祖先の作用を流す (後で作り直すときに消さないため)。
      pushBoundsSG l0 r0 t
      -- foldSG と同じ分け方で節点を取り、読む代わりに作用をかけて溜める。
      let go !i !j = when (i < j) $ do
            when (odd i) $ allApplySG i f t
            when (odd j) $ allApplySG (j - 1) f t
            go ((i + 1) `shiftR` 1) (j `shiftR` 1)
      go l0 r0
      -- 値が変わった節点の祖先 (両端の祖先) を下から作り直す。
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
-- 値は子を見ずに act f で直す (準同型の条件)。溜めた作用 g とは comp f g にまとめる
-- (g の後に f。合成の条件)。葉は子がないので溜めない。
{-# INLINE allApplySG #-}
allApplySG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> f -> SegTree m v a f -> m ()
allApplySG k f t = do
  x <- GM.unsafeRead (nodesSG t) k
  GM.unsafeWrite (nodesSG t) k $! actOpSG t f x
  when (k < sizeSG t) $ do
    g <- GM.unsafeRead (lazySG t) k
    GM.unsafeWrite (lazySG t) k $! composeSG t f g

-- 節点 k に溜めた作用を子に流し、溜めを何もしない作用 idf に戻す。
-- 節点 k の値は作用をかけた後のものなので、そのまま。
{-# INLINE pushSG #-}
pushSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> SegTree m v a f -> m ()
pushSG k t = do
  f <- GM.unsafeRead (lazySG t) k
  allApplySG (2 * k) f t
  allApplySG (2 * k + 1) f t
  GM.unsafeWrite (lazySG t) k $! idActSG t

-- 葉 l0 と r0 (r0 は含まない) の祖先に溜めた作用を、上から流す。遅延版でなければ何もしない。
-- [l0, r0) を分けた節点の祖先は、両端の祖先のどれか。端がその段の区切りにちょうど
-- 合う祖先 ((l0 >> s) << s == l0) はその端で区間に切られないので、流さなくてよい
-- (もう一方の端で切られるなら、そちらの判定で流す)。
{-# INLINE pushBoundsSG #-}
pushBoundsSG :: (PrimMonad m, G.Vector v a, G.Vector v f) => Int -> Int -> SegTree m v a f -> m ()
pushBoundsSG l0 r0 t =
  when (isLazySG t) $ forM_ [logSG t, logSG t - 1 .. 1] $ \s -> do
    when (((l0 `shiftR` s) `shiftL` s) /= l0) $ pushSG (l0 `shiftR` s) t
    when (((r0 `shiftR` s) `shiftL` s) /= r0) $ pushSG ((r0 - 1) `shiftR` s) t
