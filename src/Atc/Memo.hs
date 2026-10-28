{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | メモ化再帰。Python の @\@lru_cache@ のように、再帰関数をそのまま包む。
--
-- 包む関数は第 1 引数で自分自身 (メモ化された版) を受け取る。同じ名前にすると
-- 普通の再帰と同じ見た目になる。引数が複数ならタプルにする。
--
-- > f = memo $ \f n -> if n == 0 then 1 else f (n `div` 2) + f (n `div` 3)
-- > f (10 ^ 18 :: Int)
-- >
-- > dp = memoIx ((0, 0), (n, w)) $ \dp (i, c) -> ...   -- 範囲が分かる密な DP
-- > dp (0, w)
--
-- * 'memo' は範囲指定なしで、疎なキーにも使える。表は 'Int' なら IntMap、
--   それ以外の 'Ord' なら Map で、参照は O(log 状態数)。
-- * 'memoIx' は範囲 @(lo, hi)@ の配列を表にする。速いので、状態数が多い密な DP 向け。
--   キーは 'Ix' のインスタンス ('Int', 'Char', 'Bool' とそのタプル)。
-- * 'memoIxAsc' / 'memoIxDesc' は範囲内の全状態を添字の昇順 / 降順に先に計算する。
--   依存先が常に小さい (大きい) 添字なら再帰が深くならない。全状態で計算できること。
--
-- 値は表に入れる時点で WHNF まで評価する。'Int' などならサンクは溜まらない
-- (遅延したタプルの中身までは評価しないので、値は 'Int' や正格なデータ型にする)。
--
-- 表は包んだ結果に付く。@let f = memo ...@ と一度束縛すれば何度呼んでも共有される。
-- 循環する依存は @\<\<loop\>\>@ で止まる。
--
-- 'memo' はキーの型で表を選ぶので、キーの型が決まらないとコンパイルエラーになる
-- (数値リテラルだけで呼ぶときなど)。入力から読んだ値なら決まっている。
-- 決まらないときは @f = memo $ \\f (n :: Int) -> ...@ か、@f :: Int -> Int@ と書く。
module Atc.Memo where

import Control.Exception (evaluate)
import Data.IORef
import qualified Data.IntMap.Lazy as IM
import Data.Ix (Ix, inRange, index, range, rangeSize)
import qualified Data.Map.Lazy as M
import qualified Data.Vector as V
import System.IO.Unsafe (unsafePerformIO)

-- | 'memo' の表を選ぶ。'Int' は IntMap、ほかの 'Ord' は Map。
class MemoKey k where
  memo :: ((k -> v) -> k -> v) -> k -> v

instance {-# OVERLAPPING #-} MemoKey Int where
  memo = memoTable IM.empty IM.lookup IM.insert

instance {-# OVERLAPPABLE #-} (Ord k) => MemoKey k where
  memo = memoTable M.empty M.lookup M.insert

-- 表は IORef に持つ。f が純粋なら外からは普通の関数と区別できない。
-- インライン展開で表が複製されないよう NOINLINE にする。
-- 値はサンクのまま先に表に入れてから評価する。評価後は表の中も値になり、
-- 循環する依存は評価中のサンクに戻ってくるので @\<\<loop\>\>@ で止まる。
{-# NOINLINE memoTable #-}
memoTable :: t -> (k -> t -> Maybe v) -> (k -> v -> t -> t) -> ((k -> v) -> k -> v) -> k -> v
memoTable empty lookupT insertT f = unsafePerformIO $ do
  ref <- newIORef empty
  let go k = unsafePerformIO $ do
        t <- readIORef ref
        case lookupT k t of
          Just v -> evaluate v
          Nothing -> do
            let v = f go k
            writeIORef ref $! insertT k v t
            evaluate v
  pure go

-- | 範囲 @(lo, hi)@ の配列を表にする。必要になった状態だけ計算する。
{-# NOINLINE memoIx #-}
memoIx :: (Ix k) => (k, k) -> ((k -> v) -> k -> v) -> k -> v
memoIx bnds f = fst (memoIxTable bnds f)

-- | 'memoIx' と同じだが、全状態を添字の昇順に先に計算する。
{-# NOINLINE memoIxAsc #-}
memoIxAsc :: (Ix k) => (k, k) -> ((k -> v) -> k -> v) -> k -> v
memoIxAsc bnds f = V.foldl' (\() x -> x `seq` ()) () tbl `seq` go
  where
    (go, tbl) = memoIxTable bnds f

-- | 'memoIx' と同じだが、全状態を添字の降順に先に計算する。
{-# NOINLINE memoIxDesc #-}
memoIxDesc :: (Ix k) => (k, k) -> ((k -> v) -> k -> v) -> k -> v
memoIxDesc bnds f = V.foldr' (\x () -> x `seq` ()) () tbl `seq` go
  where
    (go, tbl) = memoIxTable bnds f

-- 要素は遅延 (参照されたときに WHNF まで評価され、以後は値)。
memoIxTable :: (Ix k) => (k, k) -> ((k -> v) -> k -> v) -> (k -> v, V.Vector v)
memoIxTable bnds f = (go, tbl)
  where
    tbl = V.fromListN (rangeSize bnds) (map (f go) (range bnds))
    go k
      | inRange bnds k = V.unsafeIndex tbl (index bnds k)
      | otherwise = error "memoIx: キーが範囲外"
