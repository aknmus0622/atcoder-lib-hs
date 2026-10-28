{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | 配列の DP。もらう DP は 'pullDP'、くばる DP は 'pushDP'。
--
-- > -- もらう DP: 前の要素を見て次の要素を決める (Data.Vector の constructN)
-- > pullDP n $ \dp -> let i = U.length dp in ...
-- >
-- > -- くばる DP: 確定した状態から先の状態へ送る
-- > let dp = pushDP (0, n - 1) min [(0, 0)] $ \i x ->
-- >       [(j, x + abs (h U.! i - h U.! j)) | j <- [i + 1, i + 2], j < n]
-- > print (fromJust (dp (n - 1)))
-- >
-- > let dp = pushDP ((0, 0), (n, w)) max [((0, 0), 0)] $ \(i, c) x ->
-- >       [((i + 1, c), x), ((i + 1, c + ws U.! i), x + vs U.! i)]
-- > print (maximum (mapMaybe dp (range ((n, 0), (n, w)))))
module Atc.DP where

import Control.Monad (foldM_, forM_, when)
import Control.Monad.ST (runST)
import qualified Data.Foldable as F
import Data.Ix (Ix, inRange, index, range, rangeSize)
import GHC.Ix (unsafeIndex)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- | もらう DP。@pullDP n f@ の @i@ 番目は @f@ に @0 .. i-1@ 番目を渡した値。
-- 'G.constructN' の別名。
{-# INLINE pullDP #-}
pullDP :: (G.Vector v a) => Int -> (v a -> a) -> v a
pullDP = G.constructN

-- | くばる DP の表を選ぶ。'Int' / 'Bool' / 'Double' / 'Char' は U.Vector、
-- ほかは V.Vector (書き込み時に WHNF まで評価する)。
--
-- @pushDP bnds op starts f@:
--
-- * 範囲 @bnds@ のキーを 'range' の順 (組なら辞書順) に処理する。
-- * 到達した状態 @k@ (値 @x@ が確定している) について @f k x@ の @(k', c)@ を送る。
--   @k'@ に初めて届いた値はそのまま、2 回目以降は @op 今の値 c@ でまとめる。
-- * 到達していない状態は飛ばす (@f@ は呼ばれない)。
-- * 範囲外の送り先は無視する。送り先のキーは評価するが、値は範囲内のときだけ評価する。
-- * 送り先が今のキー以前ならエラー。
--
-- 結果の @dp k@ は到達していない (範囲外を含む) なら 'Nothing'。
-- 値の型が決まらないとコンパイルエラーになるので、そのときは型を書く。
class DPValue a where
  pushDP :: (Ix k, F.Foldable t) => (k, k) -> (a -> a -> a) -> [(k, a)] -> (k -> a -> t (k, a)) -> k -> Maybe a

instance {-# OVERLAPPING #-} DPValue Int where
  {-# INLINE pushDP #-}
  pushDP = pushDPWith (id :: U.Vector Int -> U.Vector Int)

instance {-# OVERLAPPING #-} DPValue Bool where
  {-# INLINE pushDP #-}
  pushDP = pushDPWith (id :: U.Vector Bool -> U.Vector Bool)

instance {-# OVERLAPPING #-} DPValue Double where
  {-# INLINE pushDP #-}
  pushDP = pushDPWith (id :: U.Vector Double -> U.Vector Double)

instance {-# OVERLAPPING #-} DPValue Char where
  {-# INLINE pushDP #-}
  pushDP = pushDPWith (id :: U.Vector Char -> U.Vector Char)

instance {-# OVERLAPPABLE #-} DPValue a where
  {-# INLINE pushDP #-}
  pushDP = pushDPWith (id :: V.Vector a -> V.Vector a)

-- 第 1 引数は表の型を決めるためだけに使う。
-- 呼び出し側で特殊化されるよう INLINE にする (表は結果の関数に付く)。
{-# INLINE pushDPWith #-}
pushDPWith ::
  (G.Vector v a, Ix k, F.Foldable t) =>
  (v a -> v a) -> (k, k) -> (a -> a -> a) -> [(k, a)] -> (k -> a -> t (k, a)) -> k -> Maybe a
pushDPWith asV bnds op starts f = look
  where
    n = rangeSize bnds
    (vals, seen) = runST $ do
      mv <- GM.new n
      ms <- UM.replicate n False
      let put j c = do
            s <- UM.unsafeRead ms j
            if s
              then do
                old <- GM.unsafeRead mv j
                GM.unsafeWrite mv j $! op old c
              else do
                UM.unsafeWrite ms j True
                GM.unsafeWrite mv j $! c
      forM_ starts $ \(k, x) ->
        if inRange bnds k then put (index bnds k) x else error "pushDP: 始点が範囲外"
      let step i k = do
            s <- UM.unsafeRead ms i
            when s $ do
              x <- GM.unsafeRead mv i
              F.forM_ (f k x) $ \(k', c) ->
                when (inRange bnds k') $ do
                  let j = unsafeIndex bnds k'
                  when (j <= i) $ error "pushDP: 送り先が今のキー以前"
                  put j c
      -- range のリストは foldM_ と融合する (自前の再帰にすると遅くなる)。
      foldM_ (\ !i k -> (i + 1) <$ step i k) 0 (range bnds)
      v <- G.unsafeFreeze mv
      s <- U.unsafeFreeze ms
      pure (asV v, s)
    look k
      | inRange bnds k
      , let i = unsafeIndex bnds k
      , U.unsafeIndex seen i =
          Just (G.unsafeIndex vals i)
      | otherwise = Nothing
