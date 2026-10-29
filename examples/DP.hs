-- | "Atc.DP" を使った配列の DP。
--
-- もらう DP は 'pullDP'、くばる DP は 'pushDP'。どちらも範囲 @(lo, hi)@ を
-- 'range' の順に 1 回ずつ処理し、結果は @k -> Maybe a@
-- (到達していない状態は 'Nothing')。
module DP where

import Atc
import Data.Ix (range)
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | Frog 1 (EDPC A) をもらう DP で。
--
-- 状態 @i@ の値は、@i-1@ と @i-2@ から「来るときの費用」を足したものの最小。
-- @f i@ が返す @(j, g)@ は「@j@ の値に @g@ をかけて候補にする」。
-- 範囲外や未到達の @j@ は自動で飛ぶので、@i == 0@ の場合分けは要らない。
frogPull :: IO ()
frogPull = do
  n <- head <$> ints
  h <- U.fromList <$> ints
  let dp = pullDP (0, n - 1) min [(0, 0 :: Int)] $ \i ->
        [(j, (+ abs (h U.! i - h U.! j))) | j <- [i - 1, i - 2]]
  print (fromMaybe 0 (dp (n - 1)))

-- | 同じ問題をくばる DP で。
--
-- 到達した @i@ (値 @x@) から、@i+1@ と @i+2@ へ候補を送る。
-- 送り先は今のキーより後ろでなければならない。
frogPush :: IO ()
frogPush = do
  n <- head <$> ints
  h <- U.fromList <$> ints
  let dp = pushDP (0, n - 1) min [(0, 0 :: Int)] $ \i x ->
        [(j, x + abs (h U.! i - h U.! j)) | j <- [i + 1, i + 2], j < n]
  print (fromMaybe 0 (dp (n - 1)))

-- | ナップサック (EDPC D): キーをタプルにする。
--
-- 範囲は @((0, 0), (n, w))@ で、'range' の順 = 辞書順に処理される。
-- 答えは @i == n@ の行をまとめて見る。
knapsack :: IO ()
knapsack = do
  [n, w] <- ints
  items <- mapM (const ((\[a, b] -> (a, b)) <$> ints)) [1 .. n]
  let ws = U.fromList (map fst items)
      vs = U.fromList (map snd items)
      dp = pushDP ((0, 0), (n, w)) max [((0, 0), 0 :: Int)] $ \(i, c) x ->
        [((i + 1, c), x)]
          ++ [((i + 1, c + ws U.! i), x + vs U.! i) | c + ws U.! i <= w]
  print (maximum (mapMaybe dp (range ((n, 0), (n, w)))))

-- | 経路の数を数える (壁ありの格子)。
--
-- まとめ方を @(+)@ にすれば個数の DP。法を取るなら @\\a b -> (a + b) `mod` m@。
countPaths :: IO ()
countPaths = do
  [h, w] <- ints
  g <- getCharGrid w h
  let m = 1000000007 :: Int
      add a b = (a + b) `mod` m
      dp = pushDP ((0, 0), (h - 1, w - 1)) add [((0, 0), 1)] $ \(r, c) x ->
        [ ((r', c'), x)
        | (r', c') <- [(r + 1, c), (r, c + 1)]
        , r' < h
        , c' < w
        , elemAt (r', c') g /= '#'
        ]
  print (fromMaybe 0 (dp (h - 1, w - 1)))

-- | 自由な漸化式: 'pullDPWith' は値そのものを書く。
--
-- @f dp k@ が @k@ の値。@dp@ で前の状態を引ける (未到達なら 'Nothing')。
-- 「まとめ方」が max や min の形に収まらないときに使う。
freeRecurrence :: IO ()
freeRecurrence = do
  n <- head <$> ints
  let dp = pullDPWith (0, n) $ \self i ->
        if i == 0
          then Just (1 :: Int)
          else (\x -> 2 * x + i) <$> self (i - 1)
  print (fromMaybe 0 (dp n))

-- | 自由に更新するくばる DP: 'pushDPWith'。
--
-- 送り先の @(k', g)@ の @g@ は @Maybe a -> a@ で、「今の値 (無ければ
-- 'Nothing')」から新しい値を作る。'mergeWith' を使えば普通のまとめ方に戻る。
freeUpdate :: IO ()
freeUpdate = do
  n <- head <$> ints
  as <- U.fromList <$> ints
  let dp = pushDPWith (0, n) [(0, 0 :: Int)] $ \i x ->
        [(i + 1, mergeWith max (x + as U.! i)) | i < n]
  print (fromMaybe 0 (dp n))

-- | 'mergeWith' を直に: 「今の値があれば op、なければ初期値」。
--
-- 'pushDP' はこれを内側で使っている。
mergeByHand :: Maybe Int -> Int
mergeByHand = mergeWith max 10

-- | 最長増加部分列の長さ (もらう DP を素朴に)。
--
-- O(n^2) 版。@j < i@ で @a j < a i@ のものから最大を取る。
lis :: IO ()
lis = do
  n <- head <$> ints
  as <- U.fromList <$> ints
  let dp = pullDP (0, n - 1) max [(i, 1 :: Int) | i <- [0 .. n - 1]] $ \i ->
        [(j, (+ 1)) | j <- [0 .. i - 1], as U.! j < as U.! i]
  print (maximum (mapMaybe dp [0 .. n - 1]))

-- | 'DPValue' を制約にすれば、表に入る型を決めずに書ける。
--
-- 'Int' / 'Bool' / 'Double' / 'Char' は U.Vector、ほかは V.Vector が選ばれる。
-- 値の型が決まらないとコンパイルエラーになるので、呼ぶ側で決める。
chain :: (DPValue a) => Int -> (a -> a -> a) -> a -> (Int -> a -> a) -> Int -> Maybe a
chain n op start step = pushDP (0, n) op [(0, start)] $ \i x ->
  [(i + 1, step i x) | i < n]
