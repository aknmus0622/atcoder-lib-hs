{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

-- | 配列の DP。もらう DP は 'pullDP'、くばる DP は 'pushDP'。
--
-- キーは 'Ix' ('Int' やそのタプル) で、範囲 @(lo, hi)@ を 'range' の順
-- (タプルなら辞書順) に 1 回ずつ処理する。結果は @k -> Maybe a@ で、
-- 到達していない状態 (範囲外を含む) は 'Nothing'。
--
-- > -- Frog 1
-- > pullDP (0, n - 1) min [(0, 0)] $ \i ->
-- >   [(j, (+ abs (h U.! i - h U.! j))) | j <- [i - 1, i - 2]]
-- > pushDP (0, n - 1) min [(0, 0)] $ \i x ->
-- >   [(j, x + abs (h U.! i - h U.! j)) | j <- [i + 1, i + 2], j < n]
-- >
-- > -- ナップサック
-- > pushDP ((0, 0), (n, w)) max [((0, 0), 0)] $ \(i, c) x ->
-- >   [((i + 1, c), x), ((i + 1, c + ws U.! i), x + vs U.! i)]
-- > maximum (mapMaybe dp (range ((n, 0), (n, w))))
-- >
-- > -- 自由な漸化式 (dp は前の状態を引く)
-- > pullDPWith (0, n) $ \dp i -> if i == 0 then Just 1 else (\x -> 2 * x - ...) <$> dp (i - 1)
--
-- 共通の決まり:
--
-- * 到達していない状態は飛ばす。範囲外のキーは無視する ('Nothing' 扱い)。
--   キーは評価するが、値は範囲内で到達済みのときだけ評価するので、境界の条件は要らない。
-- * もらう元は今のキーより前、送り先は後ろでないとエラー。
-- * 表は 'Int' / 'Bool' / 'Double' / 'Char' なら U.Vector、ほかは V.Vector
--   (書き込み時に WHNF まで評価する)。値の型が決まらないとコンパイルエラーになる。
module Atc.DP where

import Control.Monad (foldM_, forM_, when)
import Control.Monad.Primitive (unsafeInlineST)
import Control.Monad.ST (ST, runST)
import qualified Data.Foldable as F
import Data.Ix (Ix, inRange, range, rangeSize)
import GHC.Ix (unsafeIndex)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- | もらう DP。@k@ について @f k@ の @(k', g)@ のうち到達済みの @k'@ から
-- @g dp[k']@ をもらい、@op@ でまとめる。@k@ が始点なら始点の値もまとめる。
{-# INLINE pullDP #-}
pullDP :: (Ix k, DPValue a, F.Foldable t) => (k, k) -> (a -> a -> a) -> [(k, a)] -> (k -> t (k, a -> a)) -> k -> Maybe a
pullDP bnds op starts f = withDPVector $ \asV -> runST $ do
  t@(Table mv ms) <- newTable "pullDP" bnds [(k, mergeWith op x) | (k, x) <- starts]
  forKeys bnds $ \i k ->
    F.forM_ (f k) $ \(k', g) ->
      when (inRange bnds k') $ do
        let j = unsafeIndex bnds k'
        when (j >= i) $ error "pullDP: もらう元が今のキー以降"
        s <- UM.unsafeRead ms j
        when s $ do
          v <- GM.unsafeRead mv j
          update t i (mergeWith op (g v))
  freezeTable asV bnds t

-- | 自由な漸化式のもらう DP。@f dp k@ が @k@ の値で、@dp@ で前の状態を引く。
-- 'Nothing' を返すと到達していない扱い。
{-# INLINE pullDPWith #-}
pullDPWith :: (Ix k, DPValue a) => (k, k) -> ((k -> Maybe a) -> k -> Maybe a) -> k -> Maybe a
pullDPWith bnds f = withDPVector $ \asV ->
  pullCore asV "pullDPWith" bnds [] $ \dp k _ -> f dp k

-- | くばる DP。到達した状態 @k@ (値 @x@) について @f k x@ の @(k', c)@ を送る。
-- @k'@ に初めて届いた値はそのまま、2 回目以降は @op 今の値 c@ でまとめる。
{-# INLINE pushDP #-}
pushDP :: (Ix k, DPValue a, F.Foldable t) => (k, k) -> (a -> a -> a) -> [(k, a)] -> (k -> a -> t (k, a)) -> k -> Maybe a
pushDP bnds op starts f = withDPVector $ \asV ->
  pushCore asV "pushDP" bnds [(k, mergeWith op x) | (k, x) <- starts] f (\(k', c) -> (k', mergeWith op c))

-- | 自由に更新するくばる DP。@f k x@ の @(k', g)@ で @dp[k']@ を @g 今の値@ にする
-- (今の値は到達していなければ 'Nothing')。始点は値をそのまま置く。
{-# INLINE pushDPWith #-}
pushDPWith :: (Ix k, DPValue a, F.Foldable t) => (k, k) -> [(k, a)] -> (k -> a -> t (k, Maybe a -> a)) -> k -> Maybe a
pushDPWith bnds starts f = withDPVector $ \asV ->
  pushCore asV "pushDPWith" bnds [(k, const x) | (k, x) <- starts] f id

-- | DP の表を選ぶ。'Int' / 'Bool' / 'Double' / 'Char' は U.Vector、ほかは V.Vector。
class DPValue a where
  withDPVector :: (forall v. (G.Vector v a) => (v a -> v a) -> r) -> r

instance {-# OVERLAPPING #-} DPValue Int where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Int -> U.Vector Int)

instance {-# OVERLAPPING #-} DPValue Bool where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Bool -> U.Vector Bool)

instance {-# OVERLAPPING #-} DPValue Double where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Double -> U.Vector Double)

instance {-# OVERLAPPING #-} DPValue Char where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Char -> U.Vector Char)

instance {-# OVERLAPPABLE #-} DPValue a where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: V.Vector a -> V.Vector a)

-- 今の値があれば op でまとめ、なければ c。
{-# INLINE mergeWith #-}
mergeWith :: (a -> a -> a) -> a -> Maybe a -> a
mergeWith op c = maybe c (`op` c)

-- 以下の core は呼び出し側で特殊化されるよう INLINE にする (表は結果の関数に付く)。
-- 第 1 引数は表の型を決めるためだけに使う。

-- 表: 値と到達済みフラグ。
data Table v s a = Table !(G.Mutable v s a) !(UM.MVector s Bool)

{-# INLINE newTable #-}
newTable :: (G.Vector v a, Ix k) => String -> (k, k) -> [(k, Maybe a -> a)] -> ST s (Table v s a)
newTable name bnds starts = do
  let n = rangeSize bnds
  t <- Table <$> GM.new n <*> UM.replicate n False
  forM_ starts $ \(k, g) ->
    if inRange bnds k then update t (unsafeIndex bnds k) g else error (name ++ ": 始点が範囲外")
  pure t

{-# INLINE readTable #-}
readTable :: (G.Vector v a) => Table v s a -> Int -> ST s (Maybe a)
readTable (Table mv ms) i = do
  s <- UM.unsafeRead ms i
  if s then Just <$> GM.unsafeRead mv i else pure Nothing

{-# INLINE update #-}
update :: (G.Vector v a) => Table v s a -> Int -> (Maybe a -> a) -> ST s ()
update (Table mv ms) i g = do
  s <- UM.unsafeRead ms i
  if s
    then do
      old <- GM.unsafeRead mv i
      GM.unsafeWrite mv i $! g (Just old)
    else do
      UM.unsafeWrite ms i True
      GM.unsafeWrite mv i $! g Nothing

{-# INLINE freezeTable #-}
freezeTable :: (G.Vector v a, Ix k) => (v a -> v a) -> (k, k) -> Table v s a -> ST s (k -> Maybe a)
freezeTable asV bnds (Table mv ms) = do
  vals <- asV <$> G.unsafeFreeze mv
  seen <- U.unsafeFreeze ms
  pure $ \k ->
    if inRange bnds k
      then let i = unsafeIndex bnds k in if U.unsafeIndex seen i then Just (G.unsafeIndex vals i) else Nothing
      else Nothing

-- range のリストは foldM_ と融合する (自前の再帰にすると遅くなる)。
{-# INLINE forKeys #-}
forKeys :: (Ix k) => (k, k) -> (Int -> k -> ST s ()) -> ST s ()
forKeys bnds step = foldM_ (\ !i k -> (i + 1) <$ step i k) 0 (range bnds)

{-# INLINE pushCore #-}
pushCore ::
  (G.Vector v a, Ix k, F.Foldable t) =>
  (v a -> v a) -> String -> (k, k) -> [(k, Maybe a -> a)] -> (k -> a -> t e) -> (e -> (k, Maybe a -> a)) -> k -> Maybe a
pushCore asV name bnds starts f dec = runST $ do
  t@(Table mv ms) <- newTable name bnds starts
  forKeys bnds $ \i k -> do
    s <- UM.unsafeRead ms i
    when s $ do
      x <- GM.unsafeRead mv i
      F.forM_ (f k x) $ \e -> do
        let (k', g) = dec e
        when (inRange bnds k') $ do
          let j = unsafeIndex bnds k'
          when (j <= i) $ error (name ++ ": 送り先が今のキー以前")
          update t j g
  freezeTable asV bnds t

-- body dp k 始点の値 が k の値。dp は前の状態を引く。pullDPWith 用。
-- dp の読み出しは確定済みの要素だけなので (以後書き換えない)、純粋な関数として渡せる。
{-# INLINE pullCore #-}
pullCore ::
  (G.Vector v a, Ix k) =>
  (v a -> v a) -> String -> (k, k) -> [(k, Maybe a -> a)] -> ((k -> Maybe a) -> k -> Maybe a -> Maybe a) -> k -> Maybe a
pullCore asV name bnds starts body = runST $ do
  t@(Table mv ms) <- newTable name bnds starts
  forKeys bnds $ \i k -> do
    st <- readTable t i
    let dp k'
          | not (inRange bnds k') = Nothing
          | j >= i = error (name ++ ": もらう元が今のキー以降")
          | otherwise = unsafeInlineST (readTable t j)
          where
            j = unsafeIndex bnds k'
    case body dp k st of
      Nothing -> UM.unsafeWrite ms i False
      Just v -> do
        UM.unsafeWrite ms i True
        GM.unsafeWrite mv i $! v
  freezeTable asV bnds t
