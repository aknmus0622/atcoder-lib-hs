-- | "Atc.DP" を使った配列の DP。
--
-- もらう DP は 'pullDP'、くばる DP は 'pushDP'。どちらも範囲 @(lo, hi)@ を
-- 'range' の順に 1 回ずつ処理し、結果は @k -> Maybe a@
-- (到達していない状態は 'Nothing')。もらう元・送り先は 1 点なら 'At'、
-- 区間なら 'Span' で書く。
module DP where

import Atc
import Data.Maybe (fromMaybe)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | Frog 1 (EDPC A) をもらう DP で。
--
-- 状態 @i@ の値は、@i-1@ と @i-2@ から「来るときの費用」を足したものの最小。
-- @f i@ が返す @(At j, g)@ は「@j@ の値に @g@ をかけて候補にする」。
-- 範囲外や未到達の @j@ は自動で飛ぶので、@i == 0@ の場合分けは要らない。
frogPull :: IO ()
frogPull = do
  n <- head <$> ints
  h <- U.fromList <$> ints
  let dp = pullDP (0, n - 1) min [(0, 0 :: Int)] $ \i ->
        [(At j, (+ abs (h U.! i - h U.! j))) | j <- [i - 1, i - 2]]
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
        [(At j, x + abs (h U.! i - h U.! j)) | j <- [i + 1, i + 2], j < n]
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
        [(At (i + 1, c), x)]
          ++ [(At (i + 1, c + ws U.! i), x + vs U.! i) | c + ws U.! i <= w]
  print (fromMaybe 0 (foldDP max ((n, 0), (n, w)) dp))

-- | 経路の数を数える (壁ありの格子)。
--
-- まとめ方を @(+)@ にすれば個数の DP。法を取るなら @\\a b -> (a + b) `mod` m@。
countPaths :: IO ()
countPaths = do
  [h, w] <- ints
  g <- getCharGrid w h :: IO (Grid U.Vector Char)
  let m = 1000000007 :: Int
      add a b = (a + b) `mod` m
      dp = pushDP ((0, 0), (h - 1, w - 1)) add [((0, 0), 1)] $ \(r, c) x ->
        [ (At (r', c'), x)
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
        [(At j, (+ 1)) | j <- [0 .. i - 1], as U.! j < as U.! i]
  print (fromMaybe 0 (foldDP max (0, n - 1) dp))

-- | 'DPValue' を制約にすれば、表に入る型を決めずに書ける。
--
-- 'Int' / 'Bool' / 'Double' / 'Char' / @(Int, Int)@ / 'ModInt' は U.Vector、ほかは V.Vector が選ばれる。
-- 値の型が決まらないとコンパイルエラーになるので、呼ぶ側で決める。
chain :: (DPValue a) => Int -> (a -> a -> a) -> a -> (Int -> a -> a) -> Int -> Maybe a
chain n op start step = pushDP (0, n) op [(0, start)] $ \i x ->
  [(At (i + 1), step i x) | i < n]

-- | 区間からもらう DP (典型 037 Don't Leave the Spice): 'Span'。
--
-- 料理 i は L_i..R_i mg 使って価値 V_i。ちょうど W mg にする価値の最大 (無理なら -1)。
-- @dp[i][j] = max(dp[i-1][j], max dp[i-1][j-R..j-L] + V)@ の区間を 'Span' で 1 本にする
-- (1 本 O(log))。端は自分で範囲内に収める (@max 0 (j - r)@)。@j - l < 0@ なら端が範囲外で無視される。
spanPull :: IO ()
spanPull = do
  [w, n] <- ints
  items <- V.fromList <$> mapM (const ((\[l, r, v] -> (l, r, v)) <$> ints)) [1 .. n]
  let dp = pullDP ((0, 0), (n, w)) max [((0, 0), 0 :: Int)] $ \(i, j) ->
        [ src
        | i > 0,
          let (l, r, v) = items V.! (i - 1),
          src <- [(At (i - 1, j), id), (Span (i - 1, max 0 (j - r)) (i - 1, j - l), (+ v))]
        ]
  print (maybe (-1) id (dp (n, w)))

-- | 同じ問題をくばる DP で: 区間へまとめて送る。
spanPush :: IO ()
spanPush = do
  [w, n] <- ints
  items <- V.fromList <$> mapM (const ((\[l, r, v] -> (l, r, v)) <$> ints)) [1 .. n]
  let dp = pushDP ((0, 0), (n, w)) max [((0, 0), 0 :: Int)] $ \(i, j) x ->
        [ dst
        | i < n,
          let (l, r, v) = items V.! i,
          dst <- [(At (i + 1, j), x), (Span (i + 1, j + l) (i + 1, min w (j + r)), x + v)]
        ]
  print (maybe (-1) id (dp (n, w)))

-- | 区間 DP: キーを @(長さ, 左端)@ にする。
--
-- @(l, r)@ をキーにすると、辞書順では @(m + 1, r)@ が @(l, r)@ より後ろになり
-- 「もらう元が今のキー以降」になる。長さを先にすれば短い区間が先に決まる。
-- 2 つの部分区間を足し合わせるので 'pullDPWith' で書く。
-- 例: 長さ n の列を隣どうし合わせて 1 つにする費用 (合わせた和) の最小 (EDPC N)。
intervalDP :: IO ()
intervalDP = do
  n <- head <$> ints
  as <- U.fromList <$> ints
  let pre = U.scanl (+) 0 as
      dp = pullDPWith ((1, 0), (n, n - 1)) $ \self (len, l) ->
        let cands =
              [ a + b
              | k <- [1 .. len - 1],
                Just a <- [self (k, l)],
                Just b <- [self (len - k, l + k)]
              ]
         in if l + len > n
              then Nothing
              else
                if len == 1
                  then Just (0 :: Int)
                  else (+ (pre U.! (l + len) - pre U.! l)) <$> foldr (\x m -> Just (maybe x (min x) m)) Nothing cands
  print (fromMaybe 0 (dp (n, 0)))
