{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}

-- | 尺取法。
--
-- 窓は半開区間 @[l, r)@。窓の条件は 'Window' で書く: 窓に要素を足す・除く
-- ときの状態の更新と、状態から「満たすなら @Just 値@」を返す判定。
-- 'slideWindow' は各 @l@ について、@l@ から始まる最長の窓の値を返す
-- (@[l, l + 1)@ も満たさなければ @Nothing@)。
--
-- 条件は単調であること: 条件を満たす窓の内側の窓も満たす。
-- 和 (要素が非負) が K 以下、種類数が K 以下、などがそう。
--
-- 'Window' は組み合わせられる。@fmap@ で値を加工し、@\<*\>@ / @*>@ で
-- 条件の AND を取り (単調性は保たれる)、'premap' で要素を変換してから渡す。
--
-- > let lens = slideWindow (sumIf (<= k) *> lengthWindow) as  -- 和が K 以下の窓の長さ
-- > sum (fromMaybe 0 <$> lens)                              -- その区間の個数
-- > maximum (0 : catMaybes (V.toList lens))                 -- 最長の長さ
-- >
-- > slideWindow (sumIf (<= k) *> distinctIf (<= m) *> lengthWindow) as
-- > slideWindow ((,) <$> lengthWindow <*> sumIf (const True)) as   -- 長さと和
-- > slideWindow (premap abs (sumIf (<= k)) *> lengthWindow) as     -- 絶対値の和
--
-- 「和が K 以上の最短」のように満たさない側を探すときは、条件を裏返す。
-- 長さ @len@ の最長の窓が @l + len < n@ なら、@l + len + 1@ までが最短。
--
-- 添字が要るときは @slideWindow w (U.indexed as)@ のように組で渡し、
-- 'premap' で取り出す。
--
-- 'slideWindow' の値は遅延したまま返るので、@fmap@ や @\<*\>@ で作った値は
-- 窓の状態 (種類数なら IntMap) を抱えたサンクになる。全部の値を使うなら
-- 書き込み時に WHNF まで評価する 'slideWindow'' を使う。
module Atc.TwoPointers where

import Control.Monad.ST (runST)
import qualified Data.IntMap.Strict as IntMapS
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Mutable as MV

-- | 窓の条件。状態 @s@ は外から見えない。
data Window a b
  = forall s.
    Window
      (s -> a -> s) -- ^ 右端に要素を足す
      (s -> a -> s) -- ^ 左端から要素を除く
      (s -> Maybe b) -- ^ 満たすなら @Just 値@
      !s -- ^ 空の窓の状態

data P s t = P !s !t

instance Functor (Window a) where
  {-# INLINE fmap #-}
  fmap f (Window add del check s) = Window add del (fmap f . check) s

-- | @\<*\>@ は条件の AND。値は両方の組み合わせ。
instance Applicative (Window a) where
  {-# INLINE pure #-}
  pure b = Window const const (const (Just b)) ()
  {-# INLINE (<*>) #-}
  Window add1 del1 check1 s1 <*> Window add2 del2 check2 s2 =
    Window
      (\(P x y) e -> P (add1 x e) (add2 y e))
      (\(P x y) e -> P (del1 x e) (del2 y e))
      (\(P x y) -> check1 x <*> check2 y)
      (P s1 s2)

-- | 要素を変換してから窓に入れる。
{-# INLINE premap #-}
premap :: (a -> a') -> Window a' b -> Window a b
premap f (Window add del check s) = Window (\x -> add x . f) (\x -> del x . f) check s

-- | 窓の長さ。常に満たす。
{-# INLINE lengthWindow #-}
lengthWindow :: Window a Int
lengthWindow = Window (\n _ -> n + 1) (\n _ -> n - 1) Just 0

-- | 窓の和が @p@ を満たすか。値は和。
{-# INLINE sumIf #-}
sumIf :: (Num a) => (a -> Bool) -> Window a a
sumIf p = Window (+) (-) (\s -> if p s then Just s else Nothing) 0

-- | 窓の種類数が @p@ を満たすか。値は種類数。O(log n)。
{-# INLINE distinctIf #-}
distinctIf :: (Int -> Bool) -> Window Int Int
distinctIf p = Window add del check (P IntMapS.empty 0)
  where
    -- 種類数は別に数える (IntMapS.size は O(n))。
    add (P m k) x = case IntMapS.insertLookupWithKey (const (+)) x (1 :: Int) m of
      (Nothing, m') -> P m' (k + 1)
      (Just _, m') -> P m' k
    del (P m k) x = case IntMapS.updateLookupWithKey (\_ c -> if c == 1 then Nothing else Just (c - 1)) x m of
      (Just 1, m') -> P m' (k - 1)
      (_, m') -> P m' k
    check (P _ k) = if p k then Just k else Nothing

-- | 各 @l@ について、@l@ から始まる最長の窓の値。
-- 足す・判定は高々 @2n@ 回、除くは @n@ 回、除いた後の判定が @n@ 回。
{-# INLINE slideWindow #-}
slideWindow :: (G.Vector v a) => Window a b -> v a -> V.Vector (Maybe b)
slideWindow = slideCore False

-- | 'slideWindow' の正格版。値は書き込み時に WHNF まで評価する
-- (タプルの中身までは評価しないので、要るなら @fmap@ で正格な型にする)。
{-# INLINE slideWindow' #-}
slideWindow' :: (G.Vector v a) => Window a b -> v a -> V.Vector (Maybe b)
slideWindow' = slideCore True

-- 第 1 引数が True なら値を WHNF まで評価してから書き込む。
{-# INLINE slideCore #-}
slideCore :: (G.Vector v a) => Bool -> Window a b -> v a -> V.Vector (Maybe b)
slideCore strict (Window add del check s0) xs = runST $ do
  out <- MV.unsafeNew n
  -- cur は窓 [l, r) の値 (空の窓なら Nothing)。
  let go !l !r !s !cur
        | l == n = pure ()
        | r < n
        , let s' = add s (G.unsafeIndex xs r)
        , Just b <- check s' =
            go l (r + 1) s' (Just b)
        | otherwise = do
            case cur of
              Just b | strict -> b `seq` MV.unsafeWrite out l cur
              _ -> MV.unsafeWrite out l cur
            if l < r
              then do
                let s' = del s (G.unsafeIndex xs l)
                go (l + 1) r s' (if l + 1 < r then check s' else Nothing)
              else go (l + 1) (l + 1) s Nothing
  go 0 0 s0 Nothing
  V.unsafeFreeze out
  where
    n = G.length xs
