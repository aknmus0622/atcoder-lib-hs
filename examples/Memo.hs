-- | "Atc.Memo" を使ったメモ化再帰。
--
-- 漸化式をそのまま書いて包むだけ。表の形を 'memo' / 'memoIx' で選ぶ。
module Memo where

import Atc
import Input (int, ints)

-- | 疎な状態: 'memo' は Map / IntMap に持つので、範囲を決めなくてよい。
--
-- @f n = f (n/2) + f (n/3)@ のように、到達する状態が n の割に少ないとき向き。
-- 第 1 引数の @f@ が「自分自身 (メモ付き)」。
sparse :: IO ()
sparse = do
  n <- int
  let f = memo $ \self k -> if k == 0 then 1 else self (k `div` 2) + self (k `div` 3)
  print (f n :: Int)

-- | 密な状態: 範囲が分かるなら 'memoIx' のほうが速い (配列になる)。
--
-- 必要になった状態だけ計算するので、全状態を埋めなくても損はしない。
knapsack :: IO ()
knapsack = do
  [n, w] <- ints
  items <- mapM (const ((\[a, b] -> (a, b)) <$> ints)) [1 .. n]
  let ws = map fst items
      vs = map snd items
      dp = memoIx ((0, 0), (n, w)) $ \self (i, c) ->
        if i == n
          then 0
          else
            let skip = self (i + 1, c)
                wi = ws !! i
                take' = if c + wi <= w then vs !! i + self (i + 1, c + wi) else 0
             in max skip take' :: Int
  print (dp (0, 0))

-- | 全状態を先に埋める: 添字の昇順なら 'memoIxAsc'。
--
-- 再帰が深くなりすぎてスタックが心配なときに、順番を自分で決められる。
-- 「前の状態だけを見る」漸化式は昇順で埋まる。
ascending :: IO ()
ascending = do
  n <- int
  let dp = memoIxAsc (0, n) $ \self i -> if i <= 1 then 1 else self (i - 1) + self (i - 2) :: Int
  print (dp n)

-- | 降順に埋めるなら 'memoIxDesc'。
--
-- 「後の状態を見る」漸化式 (ゲームの後退解析など) はこちら。
descending :: IO ()
descending = do
  n <- int
  let dp = memoIxDesc (0, n) $ \self i -> if i >= n then 0 else 1 + self (i + 1) :: Int
  print (dp 0)

-- | 表そのものが欲しいとき: 'memoIxTable' は関数と Vector の両方を返す。
--
-- 最大値や合計を取るなど、全状態をまとめて見るときに使う。
wholeTable :: IO ()
wholeTable = do
  n <- int
  let (_, table) = memoIxTable (0, n) $ \self i -> if i <= 1 then 1 else self (i - 1) + self (i - 2) :: Int
  print (maximum table)

-- | 表を自分で用意する: 'memoTable' は空の表と読み書きを受け取る。
--
-- 'memo' も 'memoIx' もこれを使っている。普通は要らない。
customTable :: Int -> Int
customTable =
  memoTable
    (mempty :: [(Int, Int)])
    lookup
    (\k v t -> (k, v) : t)
    (\self k -> if k <= 0 then 0 else k + self (k - 1))

-- | 'MemoKey' を制約にすれば、キーの型を決めずに書ける。
--
-- 'Int' は IntMap、ほかの 'Ord' な型は Map が選ばれる。
countReachable :: (MemoKey k) => (k -> [k]) -> k -> Int
countReachable next = memo $ \self k -> 1 + sum (map self (next k))
