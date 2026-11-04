-- | "Atc.BinarySearch" を使った問題。
--
-- 'SortedVec' は要素の型を問わず、キー関数を作るときに 1 回だけ渡す。
-- 境界の探索は 'bisectSV' に条件を渡し、その添字を 'atSV' で引く。
module BinarySearch where

import Atc
import qualified Data.ByteString.Char8 as C
import Data.List (mapAccumL)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 多重集合のクエリ。@1 x@ で x を入れ、@2 x@ で x を 1 つ消し、
-- @3 x@ で x 以上で最小の値 (なければ @-1@) を出力する。
multiset :: IO ()
multiset = do
  q <- head <$> ints
  qs <- mapM (const ints) [1 .. q]
  let step s [1, x] = (insertSV x s, Nothing)
      step s [2, x] = (deleteKeySV x s, Nothing)
      step s [_, x] = (s, Just (maybe (-1) id (atSV (bisectSV (< x) s) s)))
      step s _ = (s, Nothing)
      s0 = fromVecSV id (U.empty :: U.Vector Int)
  mapM_ print [r | Just r <- snd (mapAccumL step s0 qs)]

-- | 名前と得点の組を得点で並べ、各問い合わせ @lo hi@ に、得点がその範囲に入る人数と、
-- 範囲の中で得点が最も高い人の名前を出力する。同点なら入力の後ろの人。
scoreRange :: IO ()
scoreRange = do
  n <- head <$> ints
  people <- V.replicateM n (parse . C.words <$> C.getLine)
  q <- head <$> ints
  qs <- mapM (const ints) [1 .. q]
  let s = fromVecSV snd people
  mapM_
    ( \[lo, hi] -> do
        let c = bisectSV (<= hi) s - bisectSV (< lo) s
        putStrLn (show c ++ " " ++ (if c == 0 then "-" else maybe "-" fst (atSV (bisectSV (<= hi) s - 1) s)))
    )
    qs
  where
    parse [name, score] = (C.unpack name, readBS score :: Int)
    parse _ = error "parse"

-- | 答えの二分探索: 長さ @a_i@ の丸太を合わせて k 回まで切るとき、最長の破片の長さの最小値。
-- 長さ x 以下にできるかを ok 側にして、'bisect' の ng 側を 0 にする。
logs :: IO ()
logs = do
  [_, k] <- ints
  as <- U.fromList <$> ints
  let cuts x = U.sum (U.map (\a -> (a - 1) `div` x) as)
  print (bisect (U.maximum as) 0 (\x -> cuts x <= k))

-- | 'Double' の二分探索: x^3 + x = c の実数解。
cubic :: Double -> Double
cubic c = bisect 1e9 (-1e9) (\x -> x * x * x + x >= c)

