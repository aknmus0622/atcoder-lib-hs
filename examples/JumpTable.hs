-- | "Atc.JumpTable" を使ったダブリング。
--
-- 遷移と重みの配列を渡して表を作る。グラフなら "Atc.Graph.Functional" の
-- 'jumpTableFG' / 'weightedJumpTableFG' からも作れる。
module JumpTable where

import Atc
import Data.List (transpose)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 経路の最小値: 始点ごとの k 回分。重みの合成は結合的なら何でもよい。
minOnPath :: IO ()
minOnPath = do
  [n, q] <- ints
  next <- U.fromListN n . map (subtract 1) <$> ints
  w <- U.fromListN n <$> ints
  qs <- mapM (const ints) [1 .. q]
  let t = buildJT min (10 ^ (18 :: Int)) next w
  mapM_ (\[v, k] -> print (snd (foldJT min maxBound t (v - 1) k))) qs

-- | 区間の貪欲: 各位置から届く最遠点へ跳び、終点まで何回かかるか。
--
-- 終点 @n - 1@ を自己ループの番兵にして、終点の手前に留まる最大の回数を 'climbJT' で求める。
-- @reach ! i@ は位置 @i@ から届く最遠の位置。
jumpsToEnd :: Int -> U.Vector Int -> Int -> Maybe Int
jumpsToEnd n reach s
  | s == n - 1 = Just 0
  | u == n - 1 = Just (k + 1)
  | otherwise = Nothing
  where
    t = buildJT (\_ _ -> ()) n reach (U.replicate n ())
    (k, v, _) = climbJT (\_ _ -> ()) () (\p _ -> p /= n - 1) t s
    u = reach U.! v

-- | 木の LCA。親を遷移にする (根は自己ループ)。@lg@ は @2 ^ lg@ が表の範囲に入る段。
--
-- 深さをそろえてから、行き先が異なる間だけ大きい段から一緒に登る。
-- 2 つの頂点を同時に動かすので 'climbJT' ではなく 'jumpJT' で試す。O(log^2 n)。
lcaOf :: JumpTable U.Vector () -> Int -> U.Vector Int -> Int -> Int -> Int
lcaOf t lg depth a b
  | u == v = u
  | otherwise = jumpJT t (fst (foldl step (u, v) [lg, lg - 1 .. 0])) 1
  where
    (deep, shallow) = if depth U.! a >= depth U.! b then (a, b) else (b, a)
    u = jumpJT t deep (depth U.! deep - depth U.! shallow)
    v = shallow
    step (x, y) i =
      let x' = jumpJT t x (2 ^ i)
          y' = jumpJT t y (2 ^ i)
       in if x' /= y' then (x', y') else (x, y)

-- | 行列累乗: 状態を 1 つにする。重みは unbox できないので 'V.Vector' の表にする。
--
-- フィボナッチ数の第 k 項 (mod 998244353)。@F_0 = 0, F_1 = 1@。
fibonacci :: Int -> Int
fibonacci k = head (snd (foldJT mul identity t 0 k)) !! 1
  where
    md = 998244353
    mul x y = [[sum (zipWith (*) r c) `mod` md | c <- transpose y] | r <- x]
    identity = [[1, 0], [0, 1]]
    t = buildJT mul k (U.singleton 0) (V.singleton [[0, 1], [1, 1 :: Int]])
