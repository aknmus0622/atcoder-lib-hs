-- | "Atc.TwoPointers" を使った尺取法。
--
-- 窓は半開区間 @[l, r)@。'slideWindow' は各 @l@ について「@l@ から始まる
-- 最長の窓の値」を返す。条件が単調 (満たす窓の内側も満たす) であることが前提。
module TwoPointers where

import Atc
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 和が K 以下の区間の個数 (ABC130 D の裏返し)。
--
-- 各 @l@ の最長の長さがそのまま「@l@ から始まる条件を満たす区間の個数」。
-- 満たす窓が無ければ 'Nothing' なので 0 として足す。
countIntervals :: IO ()
countIntervals = do
  [_, k] <- ints
  as <- U.fromList <$> ints
  let lens = slideWindow (sumIf (<= k) *> lengthWindow) as
  print (sum (fromMaybe 0 <$> lens))

-- | 和が K 以下の最長の区間の長さ。
--
-- 'catMaybes' で満たした窓だけ集めて最大を取る。空のときに備えて 0 を混ぜる。
longest :: IO ()
longest = do
  [_, k] <- ints
  as <- U.fromList <$> ints
  let lens = slideWindow (sumIf (<= k) *> lengthWindow) as
  print (maximum (0 : catMaybes (V.toList lens)))

-- | 種類数が M 以下の窓: 'distinctIf'。
--
-- 条件は @\<*\>@ / @*>@ で AND を取れる。ここは「和が K 以下」かつ
-- 「種類数が M 以下」。単調性は保たれる。
twoConditions :: IO ()
twoConditions = do
  [_, k, m] <- ints
  as <- U.fromList <$> ints
  let lens = slideWindow (sumIf (<= k) *> distinctIf (<= m) *> lengthWindow) as
  print (maximum (0 : catMaybes (V.toList lens)))

-- | 長さと和を同時に取る: @\<$\>@ と @\<*\>@ で組にする。
--
-- @sumIf (const True)@ は常に満たすので、条件は長さ側だけが決める。
lengthAndSum :: IO ()
lengthAndSum = do
  as <- U.fromList <$> ints
  let both = slideWindow ((,) <$> lengthWindow <*> sumIf (const True)) as
  print (V.toList both :: [Maybe (Int, Int)])

-- | 要素を変換してから入れる: 'premap'。
--
-- 絶対値の和で条件を見たいときなど、窓に入れる前に加工する。
transformed :: IO ()
transformed = do
  [_, k] <- ints
  as <- U.fromList <$> ints
  let lens = slideWindow (premap abs (sumIf (<= k)) *> lengthWindow) as
  print (maximum (0 : catMaybes (V.toList lens)))

-- | 添字が要るとき: 組で渡して 'premap' で取り出す。
--
-- @U.indexed@ で @(添字, 値)@ にし、条件は値側、結果は添字側で見る。
withIndex :: IO ()
withIndex = do
  [_, k] <- ints
  as <- U.fromList <$> ints
  let lens = slideWindow (premap snd (sumIf (<= k)) *> premap fst lengthWindow) (U.indexed as)
  print (V.toList lens :: [Maybe Int])

-- | 「和が K 以上の最短」: 満たさない側を探すので条件を裏返す。
--
-- 長さ @len@ の最長の窓 (和 < K) が @l + len < n@ なら、1 つ伸ばした
-- @len + 1@ が「@l@ から始まる和 K 以上の最短」。
shortest :: IO ()
shortest = do
  [n, k] <- ints
  as <- U.fromList <$> ints
  let lens = slideWindow (sumIf (< k) *> lengthWindow) as
      best =
        minimum
          [ len + 1
          | (l, Just len) <- zip [0 ..] (V.toList lens)
          , l + len < n
          ]
  print best

-- | 値を全部使うなら正格版 'slideWindow''。
--
-- 'slideWindow' の値は遅延したままなので、@fmap@ で作った値は窓の状態
-- (種類数なら IntMap) を抱えたサンクになる。全部読むならこちら。
strictValues :: IO ()
strictValues = do
  [_, m] <- ints
  as <- U.fromList <$> ints
  let counts = slideWindow' (distinctIf (<= m)) as
  print (sum (fromMaybe 0 <$> counts))

-- | 条件を自分で書く: 'Window' を直に作る。
--
-- 「右端に足す」「左端から除く」「満たすなら @Just 値@」と、空の窓の状態。
-- 状態の型は外から見えないので、何を持ってもよい。ここは @(最大値の個数表)@
-- ではなく素朴に @(和, 個数)@ を持って「平均が K 以下」を見る。
averageAtMost :: Int -> Window Int Int
averageAtMost k = Window add del check (0, 0)
  where
    add (s, c) x = (s + x, c + 1)
    del (s, c) x = (s - x, c - 1)
    check (s, c) = if c == 0 || s <= k * c then Just c else Nothing

-- | 作った条件を 'slideWindow' に渡す。
--
-- 自作の 'Window' も @fmap@ / @\<*\>@ / 'premap' で組み合わせられる。
customWindow :: IO ()
customWindow = do
  [_, k] <- ints
  as <- U.fromList <$> ints
  print (maximum (0 : catMaybes (V.toList (slideWindow (averageAtMost k) as))))
  print (V.toList (slideWindow (averageAtMost k *> lengthWindow) as))
