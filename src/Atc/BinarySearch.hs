{-# LANGUAGE FlexibleContexts #-}

-- | 二分探索・三分探索と、要素を出し入れできるソート済みベクタ 'SortedVec'。
--
-- 'bisect' はめぐる式の二分探索、'ternaryMin' は下に凸な関数の最小を探す三分探索。'SortedVec' は要素の型を問わず
-- ('U.Vector' 'Int' でも 'V.Vector' (Int, Data) でも)、キー関数を 1 回渡して作る。
--
-- > let s = fromVecSV fst ps                     -- キーは fst
-- > atSV (bisectSV (< k) s) s                    -- k 以上で最小の要素
-- > atSV (bisectSV (<= k) s - 1) s               -- k 以下で最大の要素
-- > atSV 0 s / atSV (-1) s                       -- 最小 / 最大
-- > bisectSV (<= hi) s - bisectSV (< lo) s       -- キーが lo 以上 hi 以下の個数
-- > bisectSV (const True) s                      -- 全体の個数
-- > bisectSV (<= k) s > bisectSV (< k) s         -- キーが k の要素があるか
-- > fromVecSV key (toVecSV s <> news)            -- まとめて入れる
-- > bisect (-1) n (\i -> p (v V.! i))            -- ベクタで条件が真になる最後の添字
--
-- == 条件の向き
--
-- 'bisect' も 'bisectSV' も、条件が片側で真、反対側で偽に分かれていることを前提にする。
-- 'bisectSV' では先頭側が真で後ろ側が偽 (@(< k)@ や @(<= k)@ の形)。
-- 単調でない条件を渡すと、エラーにはならず意味のない値が返る。
--
-- == 中身と計算量
--
-- 約 √n 個ずつのソート済みの塊と、塊までの要素数の累積和を持つ。値は不変で、
-- 更新すると新しい値を返す (古い値もそのまま使える)。
--
-- * 'fromVecSV' O(n log n)、'toVecSV' O(n)
-- * 'insertSV' / 'deleteKeySV' O(√n)
-- * 'bisectSV' / 'atSV' O(log n) (キー関数の呼び出しを含む)
--
-- 同じキーの要素は入れた順に並ぶ ('fromVecSV' は安定ソートで、'insertSV' は
-- 同じキーの後ろに入れる)。
module Atc.BinarySearch where

import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Merge as Merge
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U

-- | めぐる式の二分探索の型クラス。
--
-- * 'Int': @ok@ と @ng@ が隣り合うまで。O(log |ok - ng|)。
-- * 'Double': 100 回で打ち切る (幅は元の 2^-100 倍になる)。
--
-- > bisect 0 (10 ^ 9 + 1) (\x -> x * x <= n)   -- floor (sqrt n)
-- > bisect (-1) n (\i -> v U.! i < x)           -- x 未満の最後の添字 (ソート済みの v)
class Bisect t where
  -- | @bisect ok ng p@: めぐる式の二分探索。@ok@ と @ng@ の大小は問わない。
  bisect ::
    -- | @ok@: @p@ が真になる側の端 (@p@ はここでは呼ばれない)
    t ->
    -- | @ng@: @p@ が偽になる側の端 (@p@ はここでは呼ばれない)
    t ->
    -- | @p x@: @x@ が真の側か。@ok@ と @ng@ の間で真偽が 1 回だけ切り替わること
    (t -> Bool) ->
    -- | 境界の真の側の値 (どこも偽なら @ok@)
    t

instance Bisect Int where
  bisect ok0 ng0 p = go ok0 ng0
    where
      go ok ng
        | abs (ng - ok) <= 1 = ok
        | p mid = go mid ng
        | otherwise = go ok mid
        where
          mid = ok + (ng - ok) `div` 2

instance Bisect Double where
  bisect ok0 ng0 p = go (100 :: Int) ok0 ng0
    where
      go 0 ok _ = ok
      go i ok ng
        | p mid = go (i - 1) mid ng
        | otherwise = go (i - 1) ok mid
        where
          mid = (ok + ng) / 2

-- | 下に凸な関数の最小を探す三分探索の型クラス。
--
-- * 'Int': O(log (hi - lo)) 回 @f@ を呼ぶ。
-- * 'Double': 200 回で打ち切る。
--
-- > ternaryMin 0 (10 ^ 9) (\x -> abs (x - 7) + 3)   -- 7
-- > ternaryMin 0 100 (\t -> (t - 1.5) ^ 2 :: Double) -- 1.5 付近
class Ternary t where
  -- | @ternaryMin lo hi f@: 三分探索。閉区間 @[lo, hi]@ で @f@ を最小にする @x@ を返す。
  -- 最大を探すときは @negate . f@ か @Down . f@ を渡す。
  ternaryMin ::
    (Ord b) =>
    -- | @lo@: 区間の左端 (含む)
    t ->
    -- | @hi@: 区間の右端 (含む。'Int' で @lo > hi@ なら 'error')
    t ->
    -- | @f x@: @x@ での値。下に凸 (谷が 1 つで、谷以外に平らな所がない) であること
    (t -> b) ->
    -- | @f@ を最小にする @x@ (最小が複数あればそのどれか)
    t

instance Ternary Int where
  ternaryMin lo0 hi0 f
    | lo0 > hi0 = error "Atc.BinarySearch.ternaryMin: lo > hi"
    | otherwise = go lo0 hi0
    where
      go lo hi
        | hi - lo <= 2 = snd (minimum [(f x, x) | x <- [lo .. hi]])
        | otherwise =
            let m1 = lo + (hi - lo) `div` 3
                m2 = hi - (hi - lo) `div` 3
             in case compare (f m1) (f m2) of
                  LT -> go lo (m2 - 1)
                  GT -> go (m1 + 1) hi
                  -- 凸なので、等しければ [m1, m2] に最小がある。
                  EQ -> go m1 m2

instance Ternary Double where
  ternaryMin lo0 hi0 f = go (200 :: Int) lo0 hi0
    where
      go 0 lo hi = (lo + hi) / 2
      go i lo hi =
        let m1 = lo + (hi - lo) / 3
            m2 = hi - (hi - lo) / 3
         in if f m1 <= f m2 then go (i - 1) lo m2 else go (i - 1) m1 hi

-- | キー @k@ で整列した、要素 @a@ のベクタ。@v@ は 'V.Vector' や 'U.Vector'。
data SortedVec v k a = SortedVec
  { -- | 要素からキーを取る関数
    keySV :: a -> k
  , -- | ソート済みの塊 (空でない)
    bucketsSV :: !(V.Vector (v a))
  , -- | 塊までの要素数の累積和 (塊の数 + 1 個、先頭は 0)
    prefixSV :: !(U.Vector Int)
  }

instance (G.Vector v a, Show (v a)) => Show (SortedVec v k a) where
  showsPrec d = showsPrec d . toVecSV

-- | @fromVecSV key v@: @key@ で安定にソートして作る。O(n log n)。
{-# INLINE fromVecSV #-}
fromVecSV ::
  (G.Vector v a, Ord k) =>
  -- | @key x@: 要素 @x@ のキー
  (a -> k) ->
  -- | @v@: 要素 (ソートされていなくてよい)
  v a ->
  -- | @key@ で整列したベクタ (同じキーは元の順)
  SortedVec v k a
fromVecSV key v = fromSortedSV key (G.modify (Merge.sortBy (\x y -> compare (key x) (key y))) v)

-- | すべての要素を順に並べたベクタ。O(n)。
{-# INLINE toVecSV #-}
toVecSV :: G.Vector v a => SortedVec v k a -> v a
toVecSV = G.concat . V.toList . bucketsSV

-- | @bisectSV p s@: 先頭から @p (キー)@ が真である要素の個数。O(log n)。
--
-- @bisectSV (< k)@ が lower bound、@bisectSV (<= k)@ が upper bound。
{-# INLINE bisectSV #-}
bisectSV ::
  G.Vector v a =>
  -- | @p k@: キー @k@ についての条件。先頭側で真、後ろ側で偽でなければならない
  (k -> Bool) ->
  -- | @s@: ソート済みベクタ
  SortedVec v k a ->
  -- | 最初に @p@ が偽になる添字 (なければ全体の個数)
  Int
bisectSV p s@(SortedVec key bs pre)
  | b == V.length bs = U.last pre
  | otherwise = U.unsafeIndex pre b + firstFalseSV (p . key) (V.unsafeIndex bs b)
  where
    b = bucketOfSV p s

-- | @atSV i s@: 先頭から @i@ 番目の要素。O(log n)。
{-# INLINE atSV #-}
atSV ::
  G.Vector v a =>
  -- | @i@: 添字 (0 始まり)。負なら後ろから数える (@-1@ が最後)
  Int ->
  -- | @s@: ソート済みベクタ
  SortedVec v k a ->
  -- | その要素 (範囲外なら 'Nothing')
  Maybe a
atSV i0 (SortedVec _ bs pre)
  | i < 0 || i >= n = Nothing
  | otherwise = Just (G.unsafeIndex (V.unsafeIndex bs b) (i - U.unsafeIndex pre b))
  where
    n = U.last pre
    i = if i0 < 0 then i0 + n else i0
    b = bisect 0 (V.length bs) (\j -> U.unsafeIndex pre j <= i)

-- | 要素を 1 つ入れる。同じキーの要素があれば、その後ろに入る。O(√n)。
{-# INLINE insertSV #-}
insertSV ::
  (G.Vector v a, Ord k) =>
  -- | @x@: 入れる要素
  a ->
  -- | @s@: ソート済みベクタ
  SortedVec v k a ->
  -- | @x@ を入れたもの (@s@ はそのまま使える)
  SortedVec v k a
insertSV x s@(SortedVec key bs pre)
  | V.null bs = SortedVec key (V.singleton (G.singleton x)) (U.fromListN 2 [0, 1])
  | G.length new > maxBucketSV (U.last pre + 1) = rebuildSV key (V.concat [V.take b bs, V.fromListN 2 [l, r], V.drop (b + 1) bs])
  | otherwise = SortedVec key (V.unsafeUpd bs [(b, new)]) (shiftPrefixSV b 1 pre)
  where
    kx = key x
    b0 = bucketOfSV (<= kx) s
    b = min b0 (V.length bs - 1)
    bucket = V.unsafeIndex bs b
    i = if b0 == V.length bs then G.length bucket else firstFalseSV ((<= kx) . key) bucket
    new = insertAtSV i x bucket
    (l, r) = G.splitAt (G.length new `div` 2) new

-- | キーが @k@ の要素を 1 つ (先頭のもの) 消す。O(√n)。
{-# INLINE deleteKeySV #-}
deleteKeySV ::
  (G.Vector v a, Ord k) =>
  -- | @k@: 消す要素のキー
  k ->
  -- | @s@: ソート済みベクタ
  SortedVec v k a ->
  -- | 1 つ消したもの (なければ @s@ のまま)
  SortedVec v k a
deleteKeySV k s@(SortedVec key bs pre)
  | b == V.length bs || key (G.unsafeIndex bucket i) /= k = s
  | G.length bucket == 1 = rebuildSV key (V.take b bs <> V.drop (b + 1) bs)
  | otherwise = SortedVec key (V.unsafeUpd bs [(b, deleteAtSV i bucket)]) (shiftPrefixSV b (-1) pre)
  where
    b = bucketOfSV (< k) s
    bucket = V.unsafeIndex bs b
    i = firstFalseSV ((< k) . key) bucket

-- 以下は内部用。

-- | ソート済みのベクタから、約 √n 個ずつの塊に分けて作る。
{-# INLINE fromSortedSV #-}
fromSortedSV :: G.Vector v a => (a -> k) -> v a -> SortedVec v k a
fromSortedSV key v = rebuildSV key (V.generate m (\j -> G.slice (j * w) (min w (n - j * w)) v))
  where
    n = G.length v
    w = maxBucketSV n `div` 2
    m = (n + w - 1) `div` w

-- | 塊から累積和を作り直す。O(塊の数)。
{-# INLINE rebuildSV #-}
rebuildSV :: G.Vector v a => (a -> k) -> V.Vector (v a) -> SortedVec v k a
rebuildSV key bs = SortedVec key bs (U.scanl' (+) 0 (U.convert (V.map G.length bs)))

-- | 塊 @b@ の要素数が @d@ 変わったときの累積和。O(塊の数)。
{-# INLINE shiftPrefixSV #-}
shiftPrefixSV :: Int -> Int -> U.Vector Int -> U.Vector Int
shiftPrefixSV b d = U.imap (\j p -> if j > b then p + d else p)

-- | 要素数 n のときの塊の大きさの上限。これを超えたら半分に割る。
maxBucketSV :: Int -> Int
maxBucketSV n = max 32 (2 * floor (sqrt (fromIntegral n :: Double)))

-- | 最後の要素で @p@ が偽になる最初の塊。どの塊でも真なら塊の数。
{-# INLINE bucketOfSV #-}
bucketOfSV :: G.Vector v a => (k -> Bool) -> SortedVec v k a -> Int
bucketOfSV p (SortedVec key bs _) = bisect (-1) (V.length bs) (\j -> p (key (G.last (V.unsafeIndex bs j)))) + 1

-- | 塊の中で @p@ が偽になる最初の添字。
{-# INLINE firstFalseSV #-}
firstFalseSV :: G.Vector v a => (a -> Bool) -> v a -> Int
firstFalseSV p v = bisect (-1) (G.length v) (p . G.unsafeIndex v) + 1

-- | @i@ 番目に @x@ を入れたベクタ。O(長さ)。
{-# INLINE insertAtSV #-}
insertAtSV :: G.Vector v a => Int -> a -> v a -> v a
insertAtSV i x v = G.create $ do
  m <- GM.unsafeNew (n + 1)
  G.unsafeCopy (GM.unsafeSlice 0 i m) (G.unsafeSlice 0 i v)
  GM.unsafeWrite m i x
  G.unsafeCopy (GM.unsafeSlice (i + 1) (n - i) m) (G.unsafeSlice i (n - i) v)
  pure m
  where
    n = G.length v

-- | @i@ 番目を除いたベクタ。O(長さ)。
{-# INLINE deleteAtSV #-}
deleteAtSV :: G.Vector v a => Int -> v a -> v a
deleteAtSV i v = G.create $ do
  m <- GM.unsafeNew (n - 1)
  G.unsafeCopy (GM.unsafeSlice 0 i m) (G.unsafeSlice 0 i v)
  G.unsafeCopy (GM.unsafeSlice i (n - 1 - i) m) (G.unsafeSlice (i + 1) (n - 1 - i) v)
  pure m
  where
    n = G.length v
