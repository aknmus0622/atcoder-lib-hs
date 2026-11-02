{-# LANGUAGE BangPatterns #-}

-- | 単調スタック。
--
-- 列を左から順に push する。push の前に、条件 @pop top x@ が成り立つ間
-- (かつ予算が残っている間) スタックの上を pop する。pop は合計で予算 @b@ 回まで。
-- 予算の要らない普通の単調スタックは @b = maxBound@。
--
-- * 'monoStack': 最後に残ったスタック (下から順)。
-- * 'monoStackTops': 各要素を push する直前の、スタックの上の添字 (空なら -1)。
--
-- 条件の向きと残る列:
--
-- > monoStack maxBound (>)  xs   -- 広義増加の列が残る
-- > monoStack maxBound (>=) xs   -- 狭義増加の列が残る
-- > monoStack maxBound (<)  xs   -- 広義減少の列が残る
--
-- 長さ K の部分列で辞書順最小 (捨ててよいのは N - K 個):
--
-- > U.take k (monoStack (n - k) (>) s)
--
-- 左で最も近い「より小さい」要素の添字 (無ければ -1):
--
-- > monoStackTops maxBound (>=) as
--
-- 右側を見たいときは列を反転して渡し、添字を @n - 1 - i@ で戻す。
--
-- どちらも O(N)。各要素は 1 回 push され、pop も高々 1 回。
module Atc.MonoStack (monoStack, monoStackTops) where

import Control.Monad.ST (runST)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as MU

-- | 予算 @b@ の範囲で、@pop top x@ の間 pop しながら全部 push する。
-- 残ったスタックを下から順に返す。
{-# INLINE monoStack #-}
monoStack :: (G.Vector v a) => Int -> (a -> a -> Bool) -> v a -> v a
monoStack b pop xs = G.generate (U.length idx) (G.unsafeIndex xs . U.unsafeIndex idx)
  where
    idx = fst (runStack b pop xs)

-- | 'monoStack' と同じ動きで、各 @i@ について「@xs ! i@ を push する直前の
-- スタックの上の添字」を返す (空なら -1)。
{-# INLINE monoStackTops #-}
monoStackTops :: (G.Vector v a) => Int -> (a -> a -> Bool) -> v a -> U.Vector Int
monoStackTops b pop xs = snd (runStack b pop xs)

-- | スタックには添字を積む。返すのは (残った添字, 各 push 直前の上)。
{-# INLINE runStack #-}
runStack :: (G.Vector v a) => Int -> (a -> a -> Bool) -> v a -> (U.Vector Int, U.Vector Int)
runStack b0 pop xs = runST $ do
  let n = G.length xs
  st <- MU.unsafeNew n
  tops <- MU.unsafeNew n
  let -- 予算 b、スタックの高さ h で x を push する前の pop
      popWhile x = go
        where
          go !b !h
            | b <= 0 || h <= 0 = pure (b, h)
            | otherwise = do
                j <- MU.unsafeRead st (h - 1)
                if pop (G.unsafeIndex xs j) x then go (b - 1) (h - 1) else pure (b, h)
      loop !i !b !h
        | i >= n = pure h
        | otherwise = do
            (b', h') <- popWhile (G.unsafeIndex xs i) b h
            top <- if h' > 0 then MU.unsafeRead st (h' - 1) else pure (-1)
            MU.unsafeWrite tops i top
            MU.unsafeWrite st h' i
            loop (i + 1) b' (h' + 1)
  h <- loop 0 b0 0
  st' <- U.unsafeFreeze (MU.take h st)
  tops' <- U.unsafeFreeze tops
  pure (st', tops')
