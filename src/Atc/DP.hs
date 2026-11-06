{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 配列の DP。もらう DP は 'pullDP'、くばる DP は 'pushDP'。
--
-- キーは 'Ix' ('Int' やそのタプル) で、範囲 @(lo, hi)@ を 'range' の順
-- (タプルなら辞書順) に 1 回ずつ処理する。結果は @k -> Maybe a@ で、
-- 到達していない状態 (範囲外を含む) は 'Nothing'。
--
-- もらう元・送り先は 'DPKeys' で書く。'At' は 1 点、'Span' は 'range' の順で
-- 連続する区間 (端を含む) をまとめて扱い、1 本 O(log n) で済む。
--
-- > -- Frog 1
-- > pullDP (0, n - 1) min [(0, 0)] $ \i ->
-- >   [(At j, (+ abs (h U.! i - h U.! j))) | j <- [i - 1, i - 2]]
-- > pushDP (0, n - 1) min [(0, 0)] $ \i x ->
-- >   [(At j, x + abs (h U.! i - h U.! j)) | j <- [i + 1, i + 2], j < n]
-- >
-- > -- ナップサック
-- > pushDP ((0, 0), (n, w)) max [((0, 0), 0)] $ \(i, c) x ->
-- >   [(At (i + 1, c), x), (At (i + 1, c + ws U.! i), x + vs U.! i)]
-- > foldDP max ((n, 0), (n, w)) dp
-- >
-- > -- 区間からもらう (典型 037: 料理 i は L_i..R_i mg、価値 V_i)
-- > pullDP ((0, 0), (n, w)) max [((0, 0), 0)] $ \(i, j) ->
-- >   [ src | i > 0, let (l, r, v) = items V.! (i - 1)
-- >         , src <- [(At (i - 1, j), id), (Span (i - 1, max 0 (j - r)) (i - 1, j - l), (+ v))] ]
-- >
-- > -- 経路の復元: 結果を組で受ける (始点から k までのキーの並び)
-- > let (dp, path) = pushDP ((0, 0), (n, w)) max [((0, 0), 0)] $ \(i, c) x -> ...
-- > path (n, c)
-- >
-- > -- 自由な漸化式 (dp は前の状態を引く)
-- > pullDPWith (0, n) $ \dp i -> if i == 0 then Just 1 else (\x -> 2 * x - ...) <$> dp (i - 1)
--
-- 共通の決まり:
--
-- * 到達していない状態は飛ばす。範囲外のキーは無視する ('Nothing' 扱い)。
--   キーは評価するが、値は範囲内で到達済みのときだけ評価するので、境界の条件は要らない。
-- * もらう元は今のキーより前、送り先は後ろでないとエラー。
-- * 'Span' は端のどちらかが範囲外なら丸ごと無視し、@lo > hi@ なら空。
--   タプルのキーは成分ごとに切り詰められないので、端は自分で範囲内に収める
--   (上の例の @max 0 (j - r)@)。
-- * 'Span' を使うときの @op@ は結合的かつ可換であること ('max' / 'min' / @(+)@ など)。
--   もらう DP の @g@ は @op@ に分配すること (@op (g x) (g y) = g (op x y)@)。
--   区間を先にまとめてから @g@ を 1 回かけるため。@max@ と @(+ v)@、@(+)@ と @(* c)@ は満たす。
-- * 'Span' が一度も出てこなければ区間用の木は作らない (点だけの DP は遅くならない)。
-- * 経路の復元は、結果を @(dp, path)@ の組で受けたときだけ ('DPResult')。@op@ は
--   'min' / 'max' のように候補を選ぶ演算で、値に 'Eq' が要る。関数のまま受ければ今までどおり
--   (記録しないので遅くならない)。'pullDPWith' / 'pushDPWith' には無い。
-- * 表は 'Int' / 'Bool' / 'Double' / 'Char' / @(Int, Int)@ / 'ModInt' なら U.Vector、
--   ほかは V.Vector (書き込み時に WHNF まで評価する)。値の型が決まらないとコンパイルエラーになる。
module Atc.DP where

import Atc.ModInt (ModInt)
import Control.Monad (foldM_, forM_, when)
import Control.Monad.Primitive (unsafeInlineST)
import Control.Monad.ST (ST, runST)
import qualified Data.Foldable as F
import Data.Int (Int32)
import qualified Data.IntMap.Strict as IM
import Data.Ix (Ix, inRange, range, rangeSize)
import Data.Maybe (isJust, listToMaybe, mapMaybe)
import Data.STRef (newSTRef, readSTRef, writeSTRef)
import GHC.Ix (unsafeIndex)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- | もらう元・送り先。
data DPKeys k
  = -- | 1 点
    At !k
  | -- | @'Span' lo hi@: 'range' の順で @lo@ から @hi@ まで (両端を含む)
    Span !k !k
  deriving (Eq, Show)

-- | もらう DP。各キーについて、もらう元のうち到達済みのものから値をもらって @op@ でまとめる。
{-# INLINE pullDP #-}
pullDP ::
  (Ix k, DPValue a, F.Foldable t, DPResult k a r) =>
  -- | @bnds@: キーの範囲 @(lo, hi)@
  (k, k) ->
  -- | @op@: もらった値どうしをまとめる演算 ('min' / 'max' / @(+)@ など)
  (a -> a -> a) ->
  -- | @starts@: 始点とその値。始点も遷移でもらった値を @op@ でまとめる
  -- (同じ始点が複数あれば @op@ でまとめる)
  [(k, a)] ->
  -- | @f k@: キー @k@ のもらう元の並び。各 @(src, g)@ は、もらう元 @src@ と、
  -- もらう値 @x@ (@dp[src]@) を @k@ の値の候補 @g x@ にする関数 @g@。
  -- 'Span' なら区間の到達済みの値を @op@ でまとめてから @g@ をかける。
  -- @src@ は @k@ より前であること (範囲外・到達していなければ飛ばす)
  (k -> t (DPKeys k, a -> a)) ->
  -- | DP の表 @k -> Maybe a@ (到達していない・範囲外なら 'Nothing')。
  -- 組 @(dp, path)@ で受けると経路の復元も付く ('DPResult')
  r
pullDP bnds op starts f = withDPVector $ \asV -> dpResult bnds $ \meq -> runST $ do
  t@(Table mv ms) <- newTable "pullDP" bnds [(k, mergeWith op x) | (k, x) <- starts]
  segRef <- newSTRef Nothing
  forKeys bnds $ \i k -> do
    F.forM_ (f k) $ \(src, g) -> case src of
      At k' ->
        when (inRange bnds k') $ do
          let j = unsafeIndex bnds k'
          when (j >= i) $ error "pullDP: もらう元が今のキー以降"
          s <- UM.unsafeRead ms j
          when s $ do
            v <- GM.unsafeRead mv j
            update t i (mergeWith op (g v))
      Span lo hi ->
        when (inRange bnds lo && inRange bnds hi) $ do
          let l = unsafeIndex bnds lo
              r = unsafeIndex bnds hi
          when (l <= r) $ do
            when (r >= i) $ error "pullDP: もらう元の区間が今のキー以降"
            seg <-
              readSTRef segRef >>= \m -> case m of
                Just sg -> pure sg
                Nothing -> do
                  sg <- buildAgg op (rangeSize bnds) t
                  writeSTRef segRef (Just sg)
                  pure sg
            mx <- queryAgg op seg l r
            F.forM_ mx $ \v -> update t i (mergeWith op (g v))
    -- i の値が決まったので、区間用の木があれば反映する。
    readSTRef segRef >>= F.mapM_ (\sg -> setAgg op sg t i)
  (vals, seen) <- freezeRaw asV t
  mseg <- readSTRef segRef >>= traverse freezeSeg
  let path = case meq of
        Nothing -> \_ _ -> []
        Just eq -> pullPath bnds op starts f eq vals seen mseg
  pure (frozenLookup bnds vals seen, path)

-- | 自由な漸化式のもらう DP。
{-# INLINE pullDPWith #-}
pullDPWith ::
  (Ix k, DPValue a) =>
  -- | @bnds@: キーの範囲 @(lo, hi)@
  (k, k) ->
  -- | @f dp k@: キー @k@ の値。@dp k'@ で前の状態 @k'@ の値を引く (範囲外・到達していなければ
  -- 'Nothing'、@k'@ が @k@ 以降ならエラー)。'Nothing' を返すと到達していない扱い
  ((k -> Maybe a) -> k -> Maybe a) ->
  -- | 引くキー
  k ->
  -- | そのキーの値 (到達していない・範囲外なら 'Nothing')
  Maybe a
pullDPWith bnds f = withDPVector $ \asV ->
  pullCore asV "pullDPWith" bnds [] $ \dp k _ -> f dp k

-- | くばる DP。到達した状態から、送り先へ値を送って @op@ でまとめる。
{-# INLINE pushDP #-}
pushDP ::
  (Ix k, DPValue a, F.Foldable t, DPResult k a r) =>
  -- | @bnds@: キーの範囲 @(lo, hi)@
  (k, k) ->
  -- | @op@: 届いた値をまとめる演算。@op 今の値 c@ でまとめる (初めてならそのまま)
  (a -> a -> a) ->
  -- | @starts@: 始点とその値 (同じ始点が複数あれば @op@ でまとめる)
  [(k, a)] ->
  -- | @f k x@: 到達した状態 @k@ (値 @x@) からの送り先の並び。各 @(dst, c)@ は、
  -- 送り先 @dst@ と送る値 @c@ ('Span' なら区間の全部へ)。
  -- @dst@ は @k@ より後ろであること (範囲外なら飛ばす)
  (k -> a -> t (DPKeys k, a)) ->
  -- | DP の表 @k -> Maybe a@ (到達していない・範囲外なら 'Nothing')。
  -- 組 @(dp, path)@ で受けると経路の復元も付く ('DPResult')
  r
pushDP bnds op starts f = withDPVector $ \asV -> dpResult bnds $ \meq -> runST $ do
  t@(Table mv ms) <- newTable "pushDP" bnds [(k, mergeWith op x) | (k, x) <- starts]
  -- 経路を復元するときだけ、親 (送り元の通し番号、始点は -1) を記録する。
  par <- UM.replicate (if isJust meq then rangeSize bnds else 0) (-1)
  segRef <- newSTRef Nothing
  forKeys bnds $ \i k -> do
    -- 区間で送られてきた値を、読む前に受け取る。
    readSTRef segRef >>= F.mapM_ (\sg -> collectTags op meq sg t par i)
    s <- UM.unsafeRead ms i
    when s $ do
      x <- GM.unsafeRead mv i
      F.forM_ (f k x) $ \(dst, c) -> case dst of
        At k' ->
          when (inRange bnds k') $ do
            let j = unsafeIndex bnds k'
            when (j <= i) $ error "pushDP: 送り先が今のキー以前"
            updateFrom op meq t par j c (fromIntegral i)
        Span lo hi ->
          when (inRange bnds lo && inRange bnds hi) $ do
            let l = unsafeIndex bnds lo
                r = unsafeIndex bnds hi
            when (l <= r) $ do
              when (l <= i) $ error "pushDP: 送り先の区間が今のキー以前"
              sg <-
                readSTRef segRef >>= \m -> case m of
                  Just sg -> pure sg
                  Nothing -> do
                    sg <- newTagSeg (isJust meq) (rangeSize bnds)
                    writeSTRef segRef (Just sg)
                    pure sg
              sendTags op meq sg l r c (fromIntegral i)
  (vals, seen) <- freezeRaw asV t
  parF <- U.unsafeFreeze par
  let path unidx goal
        | not (inRange bnds goal) = []
        | not (U.unsafeIndex seen g0) = []
        | otherwise = go g0 []
        where
          g0 = unsafeIndex bnds goal
          go j acc =
            let acc' = unidx j : acc
                p = U.unsafeIndex parF j
             in if p < 0 then acc' else go (fromIntegral p) acc'
  pure (frozenLookup bnds vals seen, path)

-- | 自由に更新するくばる DP。
{-# INLINE pushDPWith #-}
pushDPWith ::
  (Ix k, DPValue a, F.Foldable t) =>
  -- | @bnds@: キーの範囲 @(lo, hi)@
  (k, k) ->
  -- | @starts@: 始点とその値。値をそのまま置く (同じ始点が複数あれば後のもので上書き)
  [(k, a)] ->
  -- | @f k x@: 到達した状態 @k@ (値 @x@) からの更新の並び。各 @(k', g)@ で @dp[k']@ を
  -- @g 今の値@ にする (今の値は到達していなければ 'Nothing')。
  -- @k'@ は @k@ より後ろであること (範囲外なら飛ばす)
  (k -> a -> t (k, Maybe a -> a)) ->
  -- | 引くキー
  k ->
  -- | そのキーの値 (到達していない・範囲外なら 'Nothing')
  Maybe a
pushDPWith bnds starts f = withDPVector $ \asV ->
  pushCore asV "pushDPWith" bnds [(k, const x) | (k, x) <- starts] f id

-- | 範囲の到達済みの値をまとめる。
--
-- > foldDP max ((n, 0), (n, w)) dp   -- 最後の行の最大
-- > maybe (-1) id (foldDP min (k, k) dp)   -- 届かなければ -1
{-# INLINE foldDP #-}
foldDP ::
  (Ix k) =>
  -- | @op@: まとめる演算 ('range' の順に左から畳む)
  (a -> a -> a) ->
  -- | @bnds@: まとめる範囲 @(lo, hi)@
  (k, k) ->
  -- | @dp@: DP の表 ('pullDP' などの結果)
  (k -> Maybe a) ->
  -- | まとめた値 (到達済みが 1 つも無ければ 'Nothing')
  Maybe a
foldDP op bnds dp = F.foldl' step Nothing (range bnds)
  where
    step acc k = case dp k of
      Nothing -> acc
      Just x -> Just $! maybe x (`op` x) acc

-- | DP の表を選ぶ。'Int' / 'Bool' / 'Double' / 'Char' / @(Int, Int)@ / 'ModInt' は U.Vector、
-- ほかは V.Vector。
class DPValue a where
  -- | 値の型に合う Vector の型 @v@ を選び、型を決めるための @id :: v a -> v a@ を継続に渡す。
  withDPVector :: (forall v. (G.Vector v a) => (v a -> v a) -> r) -> r

instance {-# OVERLAPPING #-} DPValue Int where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Int -> U.Vector Int)

instance {-# OVERLAPPING #-} DPValue Bool where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Bool -> U.Vector Bool)

instance {-# OVERLAPPING #-} DPValue Double where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Double -> U.Vector Double)

instance {-# OVERLAPPING #-} DPValue Char where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector Char -> U.Vector Char)

instance {-# OVERLAPPING #-} DPValue (Int, Int) where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector (Int, Int) -> U.Vector (Int, Int))

instance {-# OVERLAPPING #-} DPValue (ModInt m) where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: U.Vector (ModInt m) -> U.Vector (ModInt m))

instance {-# OVERLAPPABLE #-} DPValue a where
  {-# INLINE withDPVector #-}
  withDPVector k = k (id :: V.Vector a -> V.Vector a)

-- | 'pullDP' / 'pushDP' の結果の受け取り方。結果を受ける型で決まる。
--
-- * @k -> Maybe a@ (関数のまま使う): DP の表だけ。経路のための記録はしない。
-- * @(k -> Maybe a, k -> [k])@ (組で受ける): DP の表と、経路の復元
--   (@path k@ は始点から @k@ までのキーの並び。到達していない・範囲外なら @[]@)。
--   値に 'Eq' が要る。
--
-- > let dp = pushDP bnds max starts f            -- 今までどおり
-- > let (dp, path) = pushDP bnds max starts f    -- 経路も
--
-- 経路は、@op@ が候補のどちらかを選ぶ演算 ('min' / 'max' など) のときだけ意味がある。
-- 値が同じ候補があれば、先に来たもの (始点、'range' の順で前のもの、並びの前のもの) を選ぶ。
--
-- * 'pullDP' は表を作る間は何も記録せず、@path k@ を引いたときに @k@ から逆にたどる
--   (@f k@ のもらう元のうち @g (dp src) == dp k@ のものへ戻る)。追加のメモリは無く、
--   時間は経路の長さ × もらう元の数 × O(log n)。@op@ が値を選ぶ演算でないと
--   戻る先が見つからずエラーになる。
-- * 'pushDP' は送り先しか分からないので、組で受けたときだけ表を作りながら
--   親 (Int32、状態 1 つにつき 4 バイト。'Span' があれば区間用の木にも同じだけ) を記録する。
--   時間は経路の長さ。
class DPResult k a r where
  -- | @run meq@ が表と経路を返す (@meq@ は経路が要るときの値の比較)。
  -- 経路は通し番号をキーに戻す関数を受け取る。
  dpResult :: (k, k) -> (Maybe (a -> a -> Bool) -> (k -> Maybe a, (Int -> k) -> k -> [k])) -> r

instance (k' ~ k, m ~ Maybe a) => DPResult k a (k' -> m) where
  {-# INLINE dpResult #-}
  dpResult _ run = fst (run Nothing)

instance (f1 ~ (k -> Maybe a), f2 ~ (k -> [k]), Eq a, DPKey k) => DPResult k a (f1, f2) where
  {-# INLINE dpResult #-}
  dpResult bnds run = let (dp, path) = run (Just (==)) in (dp, path (unindexer bnds))

-- | 通し番号 ('Ix' の 'unsafeIndex') からキーに戻す。経路の復元で使う。
-- 'Int' / @(Int, Int)@ / @(Int, Int, Int)@ は計算で戻し、ほかは 'range' の表を作って引く。
class (Ix k) => DPKey k where
  -- | @unindexer bnds i@: 範囲 @bnds@ で通し番号 @i@ のキー
  unindexer :: (k, k) -> Int -> k

instance {-# OVERLAPPING #-} DPKey Int where
  {-# INLINE unindexer #-}
  unindexer (l, _) i = l + i

instance {-# OVERLAPPING #-} DPKey (Int, Int) where
  {-# INLINE unindexer #-}
  unindexer ((l1, l2), (_, h2)) i =
    let (q, r) = i `quotRem` (h2 - l2 + 1) in (l1 + q, l2 + r)

instance {-# OVERLAPPING #-} DPKey (Int, Int, Int) where
  {-# INLINE unindexer #-}
  unindexer ((l1, l2, l3), (_, h2, h3)) i =
    let (q, c) = i `quotRem` (h3 - l3 + 1)
        (a, b) = q `quotRem` (h2 - l2 + 1)
     in (l1 + a, l2 + b, l3 + c)

instance {-# OVERLAPPABLE #-} (Ix k) => DPKey k where
  unindexer bnds = let ks = V.fromList (range bnds) in V.unsafeIndex ks

-- | 今の値があれば op でまとめ、なければ c。
{-# INLINE mergeWith #-}
mergeWith :: (a -> a -> a) -> a -> Maybe a -> a
mergeWith op c = maybe c (`op` c)

-- 以下の core は呼び出し側で特殊化されるよう INLINE にする (表は結果の関数に付く)。
-- 第 1 引数は表の型を決めるためだけに使う。

-- | DP の表。
data Table v s a
  = Table
      -- | 値 (通し番号で引く)
      !(G.Mutable v s a)
      -- | 到達済みフラグ
      !(UM.MVector s Bool)

-- | 表を作り、始点を 'update' で書く (範囲外の始点は 'error')。
{-# INLINE newTable #-}
newTable :: (G.Vector v a, Ix k) => String -> (k, k) -> [(k, Maybe a -> a)] -> ST s (Table v s a)
newTable name bnds starts = do
  let n = rangeSize bnds
  t <- Table <$> GM.new n <*> UM.replicate n False
  forM_ starts $ \(k, g) ->
    if inRange bnds k then update t (unsafeIndex bnds k) g else error (name ++ ": 始点が範囲外")
  pure t

-- | 通し番号 @i@ の値。到達していなければ 'Nothing'。
{-# INLINE readTable #-}
readTable :: (G.Vector v a) => Table v s a -> Int -> ST s (Maybe a)
readTable (Table mv ms) i = do
  s <- UM.unsafeRead ms i
  if s then Just <$> GM.unsafeRead mv i else pure Nothing

-- | 通し番号 @i@ を @g 今の値@ にする (今の値は到達していなければ 'Nothing')。到達済みになる。
{-# INLINE update #-}
update :: (G.Vector v a) => Table v s a -> Int -> (Maybe a -> a) -> ST s ()
update (Table mv ms) i g = do
  s <- UM.unsafeRead ms i
  if s
    then do
      old <- GM.unsafeRead mv i
      GM.unsafeWrite mv i $! g (Just old)
    else do
      UM.unsafeWrite ms i True
      GM.unsafeWrite mv i $! g Nothing

-- | 表を固めて、キーから値を引く関数にする。
{-# INLINE freezeTable #-}
freezeTable :: (G.Vector v a, Ix k) => (v a -> v a) -> (k, k) -> Table v s a -> ST s (k -> Maybe a)
freezeTable asV bnds t = uncurry (frozenLookup bnds) <$> freezeRaw asV t

-- | 表を固める (値と到達済みフラグ)。
{-# INLINE freezeRaw #-}
freezeRaw :: (G.Vector v a) => (v a -> v a) -> Table v s a -> ST s (v a, U.Vector Bool)
freezeRaw asV (Table mv ms) = (,) <$> (asV <$> G.unsafeFreeze mv) <*> U.unsafeFreeze ms

-- | 固めた表からキーで引く。
{-# INLINE frozenLookup #-}
frozenLookup :: (G.Vector v a, Ix k) => (k, k) -> v a -> U.Vector Bool -> k -> Maybe a
frozenLookup bnds vals seen k
  | inRange bnds k = let i = unsafeIndex bnds k in if U.unsafeIndex seen i then Just (G.unsafeIndex vals i) else Nothing
  | otherwise = Nothing

-- | 範囲のキーを 'range' の順に、通し番号と一緒に回す。
-- range のリストは foldM_ と融合する (自前の再帰にすると遅くなる)。
{-# INLINE forKeys #-}
forKeys :: (Ix k) => (k, k) -> (Int -> k -> ST s ()) -> ST s ()
forKeys bnds step = foldM_ (\ !i k -> (i + 1) <$ step i k) 0 (range bnds)

-- | 'pushDPWith' の本体。@dec@ で @f@ の要素を (送り先, 更新) に直す。
{-# INLINE pushCore #-}
pushCore ::
  (G.Vector v a, Ix k, F.Foldable t) =>
  (v a -> v a) -> String -> (k, k) -> [(k, Maybe a -> a)] -> (k -> a -> t e) -> (e -> (k, Maybe a -> a)) -> k -> Maybe a
pushCore asV name bnds starts f dec = runST $ do
  t@(Table mv ms) <- newTable name bnds starts
  forKeys bnds $ \i k -> do
    s <- UM.unsafeRead ms i
    when s $ do
      x <- GM.unsafeRead mv i
      F.forM_ (f k x) $ \e -> do
        let (k', g) = dec e
        when (inRange bnds k') $ do
          let j = unsafeIndex bnds k'
          when (j <= i) $ error (name ++ ": 送り先が今のキー以前")
          update t j g
  freezeTable asV bnds t

-- | 'pullDPWith' の本体。body dp k 始点の値 が k の値。dp は前の状態を引く。
-- dp の読み出しは確定済みの要素だけなので (以後書き換えない)、純粋な関数として渡せる。
{-# INLINE pullCore #-}
pullCore ::
  (G.Vector v a, Ix k) =>
  (v a -> v a) -> String -> (k, k) -> [(k, Maybe a -> a)] -> ((k -> Maybe a) -> k -> Maybe a -> Maybe a) -> k -> Maybe a
pullCore asV name bnds starts body = runST $ do
  t@(Table mv ms) <- newTable name bnds starts
  forKeys bnds $ \i k -> do
    st <- readTable t i
    let dp k'
          | not (inRange bnds k') = Nothing
          | j >= i = error (name ++ ": もらう元が今のキー以降")
          | otherwise = unsafeInlineST (readTable t j)
          where
            j = unsafeIndex bnds k'
    case body dp k st of
      Nothing -> UM.unsafeWrite ms i False
      Just v -> do
        UM.unsafeWrite ms i True
        GM.unsafeWrite mv i $! v
  freezeTable asV bnds t

-- | 'Span' 用の木 (添字は表の通し番号)。節点 p の子は 2p, 2p+1、葉 j は sz + j。
-- もらう DP では「区間の到達済みの値のまとめ」、くばる DP では「区間に送られた値のまとめ」を持つ。
data Seg v s a
  = Seg
      -- | 節点の値
      !(G.Mutable v s a)
      -- | 節点に値があるか
      !(UM.MVector s Bool)
      -- | 葉の数 @sz@ (2 の冪)
      !Int

-- | 要素数 @n@ の空の木を作る。
{-# INLINE newSeg #-}
newSeg :: (G.Vector v a) => Int -> ST s (Seg v s a)
newSeg n = do
  let sz = head (dropWhile (< n) (iterate (* 2) 1))
  Seg <$> GM.new (2 * sz) <*> UM.replicate (2 * sz) False <*> pure sz

-- | 節点 @p@ の値 (無ければ 'Nothing')。
{-# INLINE readSeg #-}
readSeg :: (G.Vector v a) => Seg v s a -> Int -> ST s (Maybe a)
readSeg (Seg sv sf _) p = do
  s <- UM.unsafeRead sf p
  if s then Just <$> GM.unsafeRead sv p else pure Nothing

-- | 節点 @p@ に書く ('Nothing' なら値なしにする)。
{-# INLINE writeSeg #-}
writeSeg :: (G.Vector v a) => Seg v s a -> Int -> Maybe a -> ST s ()
writeSeg (Seg sv sf _) p m = case m of
  Nothing -> UM.unsafeWrite sf p False
  Just x -> do
    UM.unsafeWrite sf p True
    GM.unsafeWrite sv p $! x

-- | 値なしを単位元として op でまとめる。
{-# INLINE combine #-}
combine :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
combine _ Nothing y = y
combine _ x Nothing = x
combine op (Just x) (Just y) = Just $! op x y

-- | 節点 p を子から計算し直す。
{-# INLINE pullNode #-}
pullNode :: (G.Vector v a) => (a -> a -> a) -> Seg v s a -> Int -> ST s ()
pullNode op sg p = do
  a <- readSeg sg (2 * p)
  b <- readSeg sg (2 * p + 1)
  writeSeg sg p (combine op a b)

-- | もらう DP: 今の表から木を作る。O(n)。
{-# INLINE buildAgg #-}
buildAgg :: (G.Vector v a) => (a -> a -> a) -> Int -> Table v s a -> ST s (Seg v s a)
buildAgg op n t = do
  sg@(Seg _ _ sz) <- newSeg n
  forM_ [0 .. n - 1] $ \j -> readTable t j >>= writeSeg sg (sz + j)
  forM_ [sz - 1, sz - 2 .. 1] $ pullNode op sg
  pure sg

-- | もらう DP: 表の i を葉に写す。i で受け持ちの葉が全部決まった節点 (i が右端の節点) だけ
-- 計算する。問い合わせは決まった節点しか触らないので、各節点は 1 回計算すれば足り、均して O(1)。
{-# INLINE setAgg #-}
setAgg :: (G.Vector v a) => (a -> a -> a) -> Seg v s a -> Table v s a -> Int -> ST s ()
setAgg op sg@(Seg _ _ sz) t i = do
  readTable t i >>= writeSeg sg (sz + i)
  let go p = when (odd p && p > 1) $ do
        let q = p `div` 2
        pullNode op sg q
        go q
  go (sz + i)

-- | もらう DP: 通し番号 [l, r] のまとめ。値の有無はフラグで持ち、Maybe を作らずに回す。
{-# INLINE queryAgg #-}
queryAgg :: (G.Vector v a) => (a -> a -> a) -> Seg v s a -> Int -> Int -> ST s (Maybe a)
queryAgg op (Seg sv sf sz) l0 r0 = go (l0 + sz) (r0 + sz + 1) False unused False unused
  where
    unused = error "queryAgg: unused"
    go !l !r !hl vl !hr vr
      | l >= r = pure $ case (hl, hr) of
          (True, True) -> Just $! op vl vr
          (True, False) -> Just vl
          (False, True) -> Just vr
          _ -> Nothing
      | otherwise = do
          (hl', vl') <-
            if odd l
              then do
                s <- UM.unsafeRead sf l
                if s
                  then do
                    x <- GM.unsafeRead sv l
                    let !v = if hl then op vl x else x
                    pure (True, v)
                  else pure (hl, vl)
              else pure (hl, vl)
          (hr', vr') <-
            if odd r
              then do
                s <- UM.unsafeRead sf (r - 1)
                if s
                  then do
                    x <- GM.unsafeRead sv (r - 1)
                    let !v = if hr then op x vr else x
                    pure (True, v)
                  else pure (hr, vr)
              else pure (hr, vr)
          go ((l + 1) `div` 2) (r `div` 2) hl' vl' hr' vr'

-- | くばる DP で 'Span' の送り先を貯める木。経路を復元するときは、節点ごとに
-- 貯めた値の送り元 (通し番号) も持つ (しないときは長さ 0)。
data TagSeg v s a = TagSeg !(Seg v s a) !(UM.MVector s Int32)

{-# INLINE newTagSeg #-}
newTagSeg :: (G.Vector v a) => Bool -> Int -> ST s (TagSeg v s a)
newTagSeg rec n = do
  sg@(Seg _ _ sz) <- newSeg n
  TagSeg sg <$> UM.replicate (if rec then 2 * sz else 0) (-1)

-- | 値 @c@ (送り元 @src@) を、今の値に @op@ でまとめる。経路を復元するとき
-- (@meq@ が 'Just') は、値が変わったら送り元を書き換える (同じなら先のものを残す)。
-- 表と木の節点で共通に使うため、読み書きを受け取る。
{-# INLINE mergeFrom #-}
mergeFrom ::
  (a -> a -> a) -> Maybe (a -> a -> Bool) -> ST s (Maybe a) -> (a -> ST s ()) -> (Int32 -> ST s ()) -> a -> Int32 -> ST s ()
mergeFrom op meq rd wr wsrc c src = do
  m <- rd
  case m of
    Nothing -> wr c >> when (isJust meq) (wsrc src)
    Just old -> do
      let !new = op old c
      wr new
      case meq of
        Just eq | not (eq new old) -> wsrc src
        _ -> pure ()

-- | 表の通し番号 @j@ に、送り元 @src@ からの値 @c@ をまとめる。
{-# INLINE updateFrom #-}
updateFrom ::
  (G.Vector v a) => (a -> a -> a) -> Maybe (a -> a -> Bool) -> Table v s a -> UM.MVector s Int32 -> Int -> a -> Int32 -> ST s ()
updateFrom op meq t@(Table mv ms) par j =
  mergeFrom op meq (readTable t j) (\x -> UM.unsafeWrite ms j True >> (GM.unsafeWrite mv j $! x)) (UM.unsafeWrite par j)

-- | 木の節点 @p@ に、送り元 @src@ からの値 @c@ をまとめる。
{-# INLINE addTag #-}
addTag :: (G.Vector v a) => (a -> a -> a) -> Maybe (a -> a -> Bool) -> TagSeg v s a -> Int -> a -> Int32 -> ST s ()
addTag op meq (TagSeg sg srcs) p =
  mergeFrom op meq (readSeg sg p) (writeSeg sg p . Just) (UM.unsafeWrite srcs p)

-- | くばる DP: 通し番号 [l, r] に c (送り元 src) を送る (区間を覆う節点に貯める)。
{-# INLINE sendTags #-}
sendTags :: (G.Vector v a) => (a -> a -> a) -> Maybe (a -> a -> Bool) -> TagSeg v s a -> Int -> Int -> a -> Int32 -> ST s ()
sendTags op meq tg@(TagSeg (Seg _ _ sz) _) l0 r0 c src = go (l0 + sz) (r0 + sz + 1)
  where
    go !l !r = when (l < r) $ do
      when (odd l) $ addTag op meq tg l c src
      when (odd r) $ addTag op meq tg (r - 1) c src
      go ((l + 1) `div` 2) (r `div` 2)

-- | くばる DP: 葉 i に届いた値を表の i にまとめる。
-- 節点に値が送られるのは、その節点の左端より前のキーからだけなので、左端の葉を処理する時点で
-- 節点の値は決まっている。そこで i が左端の節点を上から順に子へ押し下げる (各節点 1 回、均して O(1))。
-- 経路を復元するときは、送り元も一緒に押し下げる。
{-# INLINE collectTags #-}
collectTags ::
  (G.Vector v a) => (a -> a -> a) -> Maybe (a -> a -> Bool) -> TagSeg v s a -> Table v s a -> UM.MVector s Int32 -> Int -> ST s ()
collectTags op meq tg@(TagSeg sg@(Seg _ _ sz) srcs) t par i = do
  let leaf = sz + i
      top = until odd (`div` 2) leaf
      srcOf p = if isJust meq then UM.unsafeRead srcs p else pure (-1)
      down p = when (p < leaf) $ do
        readSeg sg p >>= F.mapM_ (\c -> do
          s <- srcOf p
          addTag op meq tg (2 * p) c s
          addTag op meq tg (2 * p + 1) c s)
        down (2 * p)
  down top
  readSeg sg leaf >>= F.mapM_ (\c -> srcOf leaf >>= updateFrom op meq t par i c)

-- ---------------------------------------------------------------------
-- もらう DP の経路の復元 (表を作り終えてから、引かれたときに逆にたどる)

-- | 固めた 'Seg'。
data FSeg v a = FSeg !(v a) !(U.Vector Bool) !Int

{-# INLINE freezeSeg #-}
freezeSeg :: (G.Vector v a) => Seg v s a -> ST s (FSeg v a)
freezeSeg (Seg sv sf sz) = FSeg <$> G.unsafeFreeze sv <*> U.unsafeFreeze sf <*> pure sz

-- | 通し番号 [l, r] を覆う節点 (左から順)。
segNodes :: Int -> Int -> Int -> [Int]
segNodes sz l0 r0 = go (l0 + sz) (r0 + sz + 1) [] []
  where
    go !l !r ls rs
      | l >= r = reverse ls ++ rs
      | otherwise =
          let (ls', l') = if odd l then (l : ls, l + 1) else (ls, l)
              (rs', r') = if odd r then (r - 1 : rs, r - 1) else (rs, r)
           in go (l' `div` 2) (r' `div` 2) ls' rs'

-- | 通し番号 [l, r] のうち、値が @ok@ を満たす葉を 1 つ (左を優先)。
-- 節点の値は子の値の @op@ なので、@op@ が値を選ぶ演算なら @ok@ を満たす子が必ずある。
{-# INLINE findLeaf #-}
findLeaf :: (G.Vector v a) => FSeg v a -> Int -> Int -> (a -> Bool) -> Maybe Int
findLeaf (FSeg sv sf sz) l r ok = listToMaybe (mapMaybe (\p -> if good p then Just (down p) else Nothing) (segNodes sz l r))
  where
    good p = U.unsafeIndex sf p && ok (G.unsafeIndex sv p)
    down p
      | p >= sz = p - sz
      | good (2 * p) = down (2 * p)
      | good (2 * p + 1) = down (2 * p + 1)
      | otherwise = noPath "pullDP"

noPath :: String -> b
noPath name = error (name ++ ": 経路を復元できない (op が候補のどちらかを選ぶ演算でない?)")

-- | もらう DP の経路: goal から、値を作ったもらう元へ戻っていく。
-- 始点の値と同じならそこで止める (始点を優先)。
{-# INLINE pullPath #-}
pullPath ::
  (G.Vector v a, Ix k, F.Foldable t) =>
  (k, k) -> (a -> a -> a) -> [(k, a)] -> (k -> t (DPKeys k, a -> a)) -> (a -> a -> Bool) ->
  v a -> U.Vector Bool -> Maybe (FSeg v a) -> (Int -> k) -> k -> [k]
pullPath bnds op starts f eq vals seen mseg unidx goal
  | not (inRange bnds goal) = []
  | not (U.unsafeIndex seen g0) = []
  | otherwise = go g0 goal []
  where
    g0 = unsafeIndex bnds goal
    startVals = IM.fromListWith (\new old -> op old new) [(unsafeIndex bnds k, x) | (k, x) <- starts, inRange bnds k]
    go i k acc
      | Just sv <- IM.lookup i startVals, eq sv v = acc'
      | otherwise = case listToMaybe (mapMaybe from (F.toList (f k))) of
          Just j -> go j (unidx j) acc'
          Nothing -> noPath "pullDP"
      where
        v = G.unsafeIndex vals i
        acc' = k : acc
        from (src, g) = case src of
          At k'
            | inRange bnds k',
              let j = unsafeIndex bnds k',
              j < i,
              U.unsafeIndex seen j,
              eq (g (G.unsafeIndex vals j)) v ->
                Just j
            | otherwise -> Nothing
          Span lo hi
            | inRange bnds lo && inRange bnds hi,
              let l = unsafeIndex bnds lo
                  r = unsafeIndex bnds hi,
              l <= r,
              r < i,
              Just sg <- mseg ->
                findLeaf sg l r (\x -> eq (g x) v)
            | otherwise -> Nothing
