{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | 幅・高さと Vector をひとまとめにした 2 次元グリッド。
--
-- 座標は 0 始まりの @(行, 列)@。サイズを渡す関数は @幅 高さ@ の順、
-- グリッドを受け取る関数はグリッドを最後に取る。
--
-- == 不変版と可変版で同じ関数
--
-- 下の関数は不変の 'Grid' にも可変の 'MGrid' にも使える。返り値の形が
-- グリッドの型で決まる。
--
-- > 関数                Grid v a        MGrid v m a
-- > getElem p g         Maybe a         m (Maybe a)
-- > elemAt p g          a               m a
-- > setElem p x g       Grid v a        m ()
-- > adjustElem p f g    Grid v a        m ()
-- > neighbors4 p g      [(Pos, a)]      m [(Pos, a)]
-- > to2D g              t (s a)         m (t (s a))
-- > transposeGrid g     Grid v a        m (MGrid v m a)
-- > mapGrid f g         Grid v b        m (MGrid v m b)   (imapGrid も同じ)
-- > mapRow f g          Grid v b        m (MGrid v m b)   (imapRow / mapColumn / imapColumn も同じ)
-- > scanRow f z g       Grid v b        m (MGrid v m b)   (scanColumn も同じ)
-- > foldRow f z g       t b             m (t b)           (foldColumn も同じ)
-- > foldGrid f z g      b               m b
--
-- ほかに 'inGrid' / 'neighborPos4' / 'gridWidth' / 'gridHeight' / 'gridData' も共通。
--
-- == strict 版
--
-- 値を計算して格納する関数には、名前に @'@ を付けた strict 版がある
-- ('setElem'' / 'adjustElem'' / 'mapGrid'' / 'imapGrid'' / 'mapRow'' / 'imapRow'' /
-- 'mapColumn'' / 'imapColumn'' / 'scanRow'' / 'scanColumn'' / 'foldRow'' / 'foldColumn'' / 'foldGrid'')。
-- 値を評価してから格納する (fold は途中結果を評価しながら畳む)。
--
-- @U.Vector@ / @UM.MVector@ は格納するときに必ず評価されるので、どちらでも同じ。
-- 違いが出るのは @V.Vector@ / @MV.MVector@ で、評価待ちの値が積み上がって
-- 遅くなったりスタックを使い切ったりするのを防げる。fold は中身によらず差が出る
-- (途中結果は格納先と関係なく積み上がる)。
--
-- 範囲外は、'getElem' が 'Nothing'、'elemAt' が 'error'、
-- 'setElem' / 'adjustElem' は何もしない。
--
-- グリッドを返すもの ('transposeGrid' / 'mapGrid' / 'mapRow' / 'scanRow' など) は、
-- 可変版でも新しいグリッドを作り、元は変えない。
--
-- == 不変版 'Grid'
--
-- 中身は @U.Vector@ (Int / Char / Bool など) か @V.Vector@ (それ以外)。
--
-- > let g = from2D [[1, 2, 3], [4, 5, 6]] :: Grid U.Vector Int
-- > getElem (1, 1) g                 -- Just 5
-- > to2D (setElem (1, 1) 99 g) :: [[Int]]   -- [[1,2,3],[4,99,6]]
-- > neighbors4 (0, 1) g              -- [((1,1),5),((0,0),1),((0,2),3)]
--
-- 'setElem' / 'adjustElem' は 1 回ごとに全体をコピーする (O(HW))。
-- 何度も書き換えるなら可変版を使う。
--
-- == 行・列ごとの処理
--
-- 'mapRow' / 'mapColumn' は各行 (各列) をリストとして変換する。長さが変わっても
-- よいが、全行 (全列) で揃っていなければ 'error'。
--
-- 'scanRow' / 'scanColumn' は各行 (各列) に @scanl@ をかける。幅 (高さ) が 1 増える。
-- 'scanRow'' / 'scanColumn'' は @scanl'@ 版で、値を評価してから格納する。
-- 2 次元累積和はこう書ける。
--
-- > scanColumn (+) 0 (scanRow (+) 0 g)
--
-- 'foldRow' / 'foldColumn' は各行 (各列) を @foldl@ で 1 つの値に畳む
-- ('foldRow'' / 'foldColumn'' は @foldl'@)。和や最大値なら strict 版を使う。
-- 並べる先 (リスト・@V.Vector@・@U.Vector@) は使い方から推論される。
-- 決まらないときは型を書く。
--
-- > let rowSum = foldRow' (+) 0 g
-- > rowSum U.! r                            -- U.Vector になる
-- > print (foldColumn' max 0 g :: [Int])    -- print だけだと決まらないので書く
--
-- 'to2D' も同じで、外側 (行の並び) と内側 (1 行) をそれぞれ推論する。
-- 内側はリスト・@V.Vector@・@U.Vector@、外側はリストか @V.Vector@
-- (@U.Vector@ は中に Vector を入れられない)。
--
-- > let rows = to2D g :: V.Vector (U.Vector Int)
-- > rows V.! r U.! c
-- > mapM_ print (to2D g :: [[Int]])
--
-- == 全要素の畳み込み
--
-- 'foldGrid' / 'foldGrid'' は全マスを行優先 (左上から右へ、上の行から下へ) に
-- @foldl@ / @foldl'@ で畳む。中身が @U.Vector@ でも 'MGrid' でも使える。
--
-- > foldGrid' (+) 0 g                -- 全マスの和
-- > foldGrid' max minBound g         -- 最大値
--
-- 中身が @V.Vector@ (やリスト) の 'Grid' は 'Foldable' でもあるので、
-- @sum@ / @maximum@ / @toList@ / @elem@ / @length@ などがそのまま使える。
-- @U.Vector@ は 'Foldable' にできない (要素に @Unbox@ が要る) ので、'foldGrid' を使う。
--
-- > let g = from2D [[1, 2], [3, 4]] :: Grid V.Vector Int
-- > sum g                            -- 10
--
-- == 可変版 'MGrid'
--
-- @MGrid v m a@ の @v@ は @UM.MVector@ か @MV.MVector@、@m@ は使うモナド
-- (@IO@ か @ST s@)。読み書きは O(1)。
--
-- 'createGrid' で ST の中で作って、不変の 'Grid' として取り出すのが基本形。
--
-- > -- '#' を壁として (0, 0) からの BFS 距離。届かないマスは -1。
-- > bfs :: Grid U.Vector Char -> Grid U.Vector Int
-- > bfs g = createGrid $ do
-- >   dist <- newMGrid (gridWidth g) (gridHeight g) (-1)
-- >   setElem (0, 0) 0 dist
-- >   let go [] = pure ()
-- >       go (p : ps) = do
-- >         d <- elemAt p dist
-- >         next <- filterM (\q -> (== -1) <$> elemAt q dist)
-- >                   [q | (q, x) <- neighbors4 p g, x /= '#']
-- >         forM_ next $ \q -> setElem q (d + 1) dist
-- >         go (ps ++ next)
-- >   go [(0, 0)]
-- >   pure dist
--
-- IO で直接使うなら型を書いて決める。
--
-- > g <- newMGrid w h 0 :: IO (MGrid UM.MVector IO Int)
-- > adjustElem (1, 2) (+ 1) g
-- > frozen <- freezeGrid g          -- :: Grid U.Vector Int
--
-- 既にある 'Grid' から始めるなら 'thawGrid'。
--
-- == 仕組みと、関数の足し方
--
-- 処理はすべて可変版 'MGrid' の上で 1 回だけ書いてある。型ごとに書くのは
-- 'GridKind' の 4 つ ('primRun' / 'primNew' / 'primUpdate' / 'primUnchanged') だけで、
-- 可変版はそのグリッド自身に対して処理を実行し、不変版は 'runST' の中で実行する。
--
-- 共通関数を足すときは、'MGrid' を受け取る処理を書いて 'primRun' (値を返す) か
-- 'primNew' (新しいグリッドを返す) に渡す。渡した処理の中で元のグリッドに
-- 書き込んではいけない (不変版はコピーせずに渡している)。
--
-- > {-# INLINE countElem #-}
-- > countElem :: (GridOf k a, Eq a) => a -> k a -> Ret k Int
-- > countElem x g = primRun g $ \(MGrid w h d) ->
-- >   length . filter (== x) <$> mapM (GM.unsafeRead d) [0 .. w * h - 1]
module Atc.Grid where

import Control.Monad (forM, forM_)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST, runST)
import qualified Data.Foldable as F
import Data.Kind (Constraint, Type)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed as U

-- ---------------------------------------------------------------------
-- 座標計算
--
-- @import Atc@ で入るので、解答側で自前定義しがちな名前 (@inBounds@,
-- @toIndex@, @Width@ …) は避けている。

-- | @(r, c)@ : (行, 列)
type Pos = (Int, Int)

-- | 幅 @w@ のグリッドで、行優先の 1 次元添字に直す。
posToIndex :: Int -> Pos -> Int
posToIndex w (r, c) = r * w + c

-- | 'posToIndex' の逆。
indexToPos :: Int -> Int -> Pos
indexToPos w i = i `divMod` w

-- | 幅 @w@ 高さ @h@ の範囲に入っているか。
inRange2D :: Int -> Int -> Pos -> Bool
inRange2D w h (r, c) = 0 <= r && r < h && 0 <= c && c < w

-- | 上・下・左・右の順。範囲は見ない。
around4 :: Pos -> [Pos]
around4 (r, c) = [(r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)]

-- ---------------------------------------------------------------------
-- 型

-- | 幅・高さ・中身。@v@ は @U.Vector@ か @V.Vector@。
data Grid v a = Grid !Int !Int !(v a)

-- | 幅・高さ・中身。@v@ は @UM.MVector@ か @MV.MVector@、@m@ は @IO@ か @ST s@。
data MGrid v m a = MGrid !Int !Int !(v (PrimState m) a)

instance (Eq (v a)) => Eq (Grid v a) where
  Grid w h d == Grid w' h' d' = w == w' && h == h' && d == d'

instance (Show (v a)) => Show (Grid v a) where
  show (Grid w h d) =
    "Grid {width = " ++ show w ++ ", height = " ++ show h ++ ", data = " ++ show d ++ "}"

-- | 要素を行優先に並べたものとして畳む。中身が 'Foldable' のとき (@V.Vector@ やリスト) だけ。
-- @U.Vector@ には 'foldGrid' を使う。
--
-- 右辺は @F.@ を付けて呼ぶ。@atc bundle@ は解答と 1 ファイルにまとめるので、
-- 解答側が @import Data.IntMap (toList)@ などをしていても名前がぶつからないように。
instance (Foldable v) => Foldable (Grid v) where
  foldr f z (Grid _ _ d) = F.foldr f z d
  foldl' f z (Grid _ _ d) = F.foldl' f z d
  foldMap f (Grid _ _ d) = F.foldMap f d
  toList (Grid _ _ d) = F.toList d
  null (Grid w h _) = w * h == 0
  length (Grid w h _) = w * h

-- | 大きさだけ分かればよい操作。
class GridShape g where
  gridWidth :: g -> Int
  gridHeight :: g -> Int

instance GridShape (Grid v a) where
  gridWidth (Grid w _ _) = w
  gridHeight (Grid _ h _) = h

instance GridShape (MGrid v m a) where
  gridWidth (MGrid w _ _) = w
  gridHeight (MGrid _ h _) = h

-- ---------------------------------------------------------------------
-- 型ごとに書く部分

-- | 不変版 (@Grid v@) と可変版 (@MGrid v m@) の違いを吸収する。
--
-- 処理は「'MGrid' を受け取る、どのモナドでも動く関数」として渡す。
class GridKind k where
  -- | 要素 @a@ を入れられるか。
  type CanHold k a :: Constraint

  -- | 処理に渡される 'MGrid' の中身の型。
  type MutOf k :: Type -> Type -> Type

  -- | 読んだ結果 @x@ の返り方。不変版は @x@ そのまま、可変版は @m x@。
  type Ret k x

  -- | 書いた結果。不変版は新しいグリッド、可変版は @m ()@。
  type Updated k a

  -- | 中身の型。
  type StoreOf k a

  gridData :: k a -> StoreOf k a

  -- | 元を読むだけの処理を実行する。
  primRun ::
    (CanHold k a) => k a -> (forall n. (PrimMonad n) => MGrid (MutOf k) n a -> n x) -> Ret k x

  -- | 元を読んで新しいグリッドを作る処理を実行する。
  primNew ::
    (CanHold k a, CanHold k b) =>
    k a ->
    (forall n. (PrimMonad n) => MGrid (MutOf k) n a -> n (MGrid (MutOf k) n b)) ->
    Ret k (k b)

  -- | 元を書き換える処理を実行する。不変版はコピーを書き換える。
  primUpdate ::
    (CanHold k a) => k a -> (forall n. (PrimMonad n) => MGrid (MutOf k) n a -> n ()) -> Updated k a

  -- | 何も書き換えなかったときの結果。
  primUnchanged :: k a -> Updated k a

instance GridKind (Grid v) where
  type CanHold (Grid v) a = G.Vector v a
  type MutOf (Grid v) = G.Mutable v
  type Ret (Grid v) x = x
  type Updated (Grid v) a = Grid v a
  type StoreOf (Grid v) a = v a

  gridData (Grid _ _ d) = d

  {-# INLINE primRun #-}
  primRun (Grid w h d) op = runST (G.unsafeThaw d >>= op . MGrid w h)

  {-# INLINE primNew #-}
  primNew (Grid w h d) op = runST $ do
    MGrid w' h' d' <- G.unsafeThaw d >>= op . MGrid w h
    Grid w' h' <$> G.unsafeFreeze d'

  {-# INLINE primUpdate #-}
  primUpdate (Grid w h d) op = runST $ do
    md <- G.thaw d
    op (MGrid w h md)
    Grid w h <$> G.unsafeFreeze md

  primUnchanged = id

instance (PrimMonad m) => GridKind (MGrid v m) where
  type CanHold (MGrid v m) a = GM.MVector v a
  type MutOf (MGrid v m) = v
  type Ret (MGrid v m) x = m x
  type Updated (MGrid v m) a = m ()
  type StoreOf (MGrid v m) a = v (PrimState m) a

  gridData (MGrid _ _ d) = d

  {-# INLINE primRun #-}
  primRun g op = op g

  {-# INLINE primNew #-}
  primNew g op = op g

  {-# INLINE primUpdate #-}
  primUpdate g op = op g

  primUnchanged _ = pure ()

-- | @k a@ がグリッドとして使える。共通関数の制約はこれ。
type GridOf k a = (GridKind k, GridShape (k a), CanHold k a, GM.MVector (MutOf k) a)

-- | 'foldRow' / 'foldColumn' / 'to2D' の結果を並べる先 (リスト・@V.Vector@・@U.Vector@)。
class Collect t a where
  collectList :: [a] -> t a

instance Collect [] a where
  collectList = id

instance Collect V.Vector a where
  collectList = V.fromList

instance (U.Unbox a) => Collect U.Vector a where
  collectList = U.fromList

-- ---------------------------------------------------------------------
-- 共通関数

-- | 範囲に入っているか。
inGrid :: (GridShape g) => Pos -> g -> Bool
inGrid pos g = inRange2D (gridWidth g) (gridHeight g) pos

-- | 上・下・左・右の順に、範囲内の座標だけ返す。
neighborPos4 :: (GridShape g) => Pos -> g -> [Pos]
neighborPos4 pos g = filter (`inGrid` g) (around4 pos)

-- | 範囲外は 'Nothing'。
{-# INLINE getElem #-}
getElem :: (GridOf k a) => Pos -> k a -> Ret k (Maybe a)
getElem pos g =
  primRun g $ \m -> if inGrid pos g then Just <$> readAt m pos else pure Nothing

-- | 範囲外は 'error'。範囲内と分かっている座標を読むとき用。
{-# INLINE elemAt #-}
elemAt :: (GridOf k a) => Pos -> k a -> Ret k a
elemAt pos g
  | inGrid pos g = primRun g $ \m -> readAt m pos
  | otherwise = error ("Atc.Grid.elemAt: 範囲外 " ++ show pos)

-- | 範囲外なら何もしない。不変版は全体をコピーするので O(HW)。
{-# INLINE setElem #-}
setElem :: (GridOf k a) => Pos -> a -> k a -> Updated k a
setElem = setElemWith False

-- | 'setElem' の strict 版。
{-# INLINE setElem' #-}
setElem' :: (GridOf k a) => Pos -> a -> k a -> Updated k a
setElem' = setElemWith True

-- | 範囲外なら何もしない。不変版は全体をコピーするので O(HW)。
{-# INLINE adjustElem #-}
adjustElem :: (GridOf k a) => Pos -> (a -> a) -> k a -> Updated k a
adjustElem = adjustElemWith False

-- | 'adjustElem' の strict 版。
{-# INLINE adjustElem' #-}
adjustElem' :: (GridOf k a) => Pos -> (a -> a) -> k a -> Updated k a
adjustElem' = adjustElemWith True

{-# INLINE setElemWith #-}
setElemWith :: (GridOf k a) => Bool -> Pos -> a -> k a -> Updated k a
setElemWith strict pos x g
  | inGrid pos g = primUpdate g $ \(MGrid w _ d) -> writeWith strict d (posToIndex w pos) x
  | otherwise = primUnchanged g

{-# INLINE adjustElemWith #-}
adjustElemWith :: (GridOf k a) => Bool -> Pos -> (a -> a) -> k a -> Updated k a
adjustElemWith strict pos f g
  | inGrid pos g = primUpdate g $ \(MGrid w _ d) -> do
      let i = posToIndex w pos
      x <- GM.unsafeRead d i
      writeWith strict d i (f x)
  | otherwise = primUnchanged g

-- | 上・下・左・右の順に、範囲内のものだけ値と一緒に返す。
{-# INLINE neighbors4 #-}
neighbors4 :: (GridOf k a) => Pos -> k a -> Ret k [(Pos, a)]
neighbors4 pos g = primRun g $ \m -> mapM (\q -> (,) q <$> readAt m q) (neighborPos4 pos g)

-- | 行を上から順に並べる。外側 @t@ も 1 行 @s@ も使い方から推論される
-- (リスト・@V.Vector@・@U.Vector@)。
{-# INLINE to2D #-}
to2D :: forall t s k a. (GridOf k a, Collect s a, Collect t (s a)) => k a -> Ret k (t (s a))
to2D g = primRun g $ \m -> collectList @t . map (collectList @s) <$> to2DM m

-- | 転置。幅と高さが入れ替わる。
{-# INLINE transposeGrid #-}
transposeGrid :: (GridOf k a) => k a -> Ret k (k a)
transposeGrid g = primNew g transposeM

-- | 全マスに @f@ を適用した新しいグリッド。要素型が変わってもよい。
{-# INLINE mapGrid #-}
mapGrid :: (GridOf k a, GridOf k b) => (a -> b) -> k a -> Ret k (k b)
mapGrid f = imapGrid (const f)

-- | 'mapGrid' の strict 版。
{-# INLINE mapGrid' #-}
mapGrid' :: (GridOf k a, GridOf k b) => (a -> b) -> k a -> Ret k (k b)
mapGrid' f = imapGrid' (const f)

-- | 座標付きの 'mapGrid'。
{-# INLINE imapGrid #-}
imapGrid :: (GridOf k a, GridOf k b) => (Pos -> a -> b) -> k a -> Ret k (k b)
imapGrid f g = primNew g (imapM False f)

-- | 'imapGrid' の strict 版。
{-# INLINE imapGrid' #-}
imapGrid' :: (GridOf k a, GridOf k b) => (Pos -> a -> b) -> k a -> Ret k (k b)
imapGrid' f g = primNew g (imapM True f)

-- | 各行をリストとして変換した新しいグリッド。
-- 長さが変わってもよいが、全行で揃っていなければ 'error'。
{-# INLINE mapRow #-}
mapRow :: (GridOf k a, GridOf k b) => ([a] -> [b]) -> k a -> Ret k (k b)
mapRow f = imapRow (const f)

-- | 'mapRow' の strict 版。
{-# INLINE mapRow' #-}
mapRow' :: (GridOf k a, GridOf k b) => ([a] -> [b]) -> k a -> Ret k (k b)
mapRow' f = imapRow' (const f)

-- | 行番号付きの 'mapRow'。
{-# INLINE imapRow #-}
imapRow :: (GridOf k a, GridOf k b) => (Int -> [a] -> [b]) -> k a -> Ret k (k b)
imapRow f g = primNew g (imapRowM False f)

-- | 'imapRow' の strict 版。
{-# INLINE imapRow' #-}
imapRow' :: (GridOf k a, GridOf k b) => (Int -> [a] -> [b]) -> k a -> Ret k (k b)
imapRow' f g = primNew g (imapRowM True f)

-- | 各列をリストとして (上から下へ) 変換した新しいグリッド。
-- 長さが変わってもよいが、全列で揃っていなければ 'error'。
{-# INLINE mapColumn #-}
mapColumn :: (GridOf k a, GridOf k b) => ([a] -> [b]) -> k a -> Ret k (k b)
mapColumn f = imapColumn (const f)

-- | 'mapColumn' の strict 版。
{-# INLINE mapColumn' #-}
mapColumn' :: (GridOf k a, GridOf k b) => ([a] -> [b]) -> k a -> Ret k (k b)
mapColumn' f = imapColumn' (const f)

-- | 列番号付きの 'mapColumn'。
{-# INLINE imapColumn #-}
imapColumn :: (GridOf k a, GridOf k b) => (Int -> [a] -> [b]) -> k a -> Ret k (k b)
imapColumn f g = primNew g (imapColumnM False f)

-- | 'imapColumn' の strict 版。
{-# INLINE imapColumn' #-}
imapColumn' :: (GridOf k a, GridOf k b) => (Int -> [a] -> [b]) -> k a -> Ret k (k b)
imapColumn' f g = primNew g (imapColumnM True f)

-- | 各行に左から @scanl f z@ をかける。幅が 1 増える。
{-# INLINE scanRow #-}
scanRow :: (GridOf k a, GridOf k b) => (b -> a -> b) -> b -> k a -> Ret k (k b)
scanRow f z g = primNew g (scanRowM False f z)

-- | 'scanRow' の @scanl'@ 版。値を評価してから格納する。
{-# INLINE scanRow' #-}
scanRow' :: (GridOf k a, GridOf k b) => (b -> a -> b) -> b -> k a -> Ret k (k b)
scanRow' f z g = primNew g (scanRowM True f z)

-- | 各列に上から @scanl f z@ をかける。高さが 1 増える。
{-# INLINE scanColumn #-}
scanColumn :: (GridOf k a, GridOf k b) => (b -> a -> b) -> b -> k a -> Ret k (k b)
scanColumn f z g = primNew g (scanColumnM False f z)

-- | 'scanColumn' の @scanl'@ 版。値を評価してから格納する。
{-# INLINE scanColumn' #-}
scanColumn' :: (GridOf k a, GridOf k b) => (b -> a -> b) -> b -> k a -> Ret k (k b)
scanColumn' f z g = primNew g (scanColumnM True f z)

-- | 各行を左から @foldl@ で畳んで、上の行から順に並べる。
-- 並べる先 (リスト・@V.Vector@・@U.Vector@) は使い方から推論される。
{-# INLINE foldRow #-}
foldRow :: forall t k a b. (GridOf k a, Collect t b) => (b -> a -> b) -> b -> k a -> Ret k (t b)
foldRow f z g = primRun g $ \m -> collectList @t <$> foldRowM False f z m

-- | 'foldRow' の @foldl'@ 版。途中結果を評価しながら畳む。
{-# INLINE foldRow' #-}
foldRow' :: forall t k a b. (GridOf k a, Collect t b) => (b -> a -> b) -> b -> k a -> Ret k (t b)
foldRow' f z g = primRun g $ \m -> collectList @t <$> foldRowM True f z m

-- | 各列を上から @foldl@ で畳んで、左の列から順に並べる。
-- 並べる先 (リスト・@V.Vector@・@U.Vector@) は使い方から推論される。
{-# INLINE foldColumn #-}
foldColumn :: forall t k a b. (GridOf k a, Collect t b) => (b -> a -> b) -> b -> k a -> Ret k (t b)
foldColumn f z g = primRun g $ \m -> collectList @t <$> foldColumnM False f z m

-- | 'foldColumn' の @foldl'@ 版。途中結果を評価しながら畳む。
{-# INLINE foldColumn' #-}
foldColumn' :: forall t k a b. (GridOf k a, Collect t b) => (b -> a -> b) -> b -> k a -> Ret k (t b)
foldColumn' f z g = primRun g $ \m -> collectList @t <$> foldColumnM True f z m

-- | 全マスを行優先に @foldl@ で畳む。
{-# INLINE foldGrid #-}
foldGrid :: (GridOf k a) => (b -> a -> b) -> b -> k a -> Ret k b
foldGrid f z g = primRun g (foldGridM False f z)

-- | 'foldGrid' の @foldl'@ 版。途中結果を評価しながら畳む。
{-# INLINE foldGrid' #-}
foldGrid' :: (GridOf k a) => (b -> a -> b) -> b -> k a -> Ret k b
foldGrid' f z g = primRun g (foldGridM True f z)

-- ---------------------------------------------------------------------
-- MGrid の上の処理 (共通関数の中身)

readAt :: (PrimMonad n, GM.MVector v a) => MGrid v n a -> Pos -> n a
readAt (MGrid w _ d) pos = GM.unsafeRead d (posToIndex w pos)
{-# INLINE readAt #-}

-- | 長さが @expected@ ならそれを返す。違えば 'error'。
checkLength :: String -> Int -> [b] -> Int
checkLength name expected ys
  | length ys == expected = expected
  | otherwise = error ("Atc.Grid." ++ name ++ ": 結果の長さが揃っていません")

-- | @strict@ なら値を評価してから書く。
writeWith :: (PrimMonad n, GM.MVector v a) => Bool -> v (PrimState n) a -> Int -> a -> n ()
writeWith strict d i x
  | strict = x `seq` GM.unsafeWrite d i x
  | otherwise = GM.unsafeWrite d i x
{-# INLINE writeWith #-}

to2DM :: (PrimMonad n, GM.MVector v a) => MGrid v n a -> n [[a]]
to2DM (MGrid w h d) = forM [0 .. h - 1] $ \r -> mapM (\c -> GM.unsafeRead d (r * w + c)) [0 .. w - 1]
{-# INLINABLE to2DM #-}

transposeM :: (PrimMonad n, GM.MVector v a) => MGrid v n a -> n (MGrid v n a)
transposeM (MGrid w h d) = do
  d' <- GM.unsafeNew (w * h)
  forM_ [0 .. h - 1] $ \r ->
    forM_ [0 .. w - 1] $ \c ->
      GM.unsafeRead d (r * w + c) >>= GM.unsafeWrite d' (c * h + r)
  pure (MGrid h w d')
{-# INLINABLE transposeM #-}

imapM ::
  (PrimMonad n, GM.MVector v a, GM.MVector v b) => Bool -> (Pos -> a -> b) -> MGrid v n a -> n (MGrid v n b)
imapM strict f (MGrid w h d) = do
  d' <- GM.unsafeNew (w * h)
  forM_ [0 .. w * h - 1] $ \i -> do
    x <- GM.unsafeRead d i
    writeWith strict d' i (f (indexToPos w i) x)
  pure (MGrid w h d')
{-# INLINABLE imapM #-}

imapRowM ::
  (PrimMonad n, GM.MVector v a, GM.MVector v b) => Bool -> (Int -> [a] -> [b]) -> MGrid v n a -> n (MGrid v n b)
imapRowM strict f (MGrid w h d) = do
  let row r = f r <$> mapM (\c -> GM.unsafeRead d (r * w + c)) [0 .. w - 1]
  -- 1 行目の長さで新しい幅を決め、残りの行はそれと揃っているか確かめながら書く。
  first <- if h == 0 then pure [] else row 0
  let w' = if h == 0 then w else length first
  d' <- GM.unsafeNew (w' * h)
  forM_ [0 .. h - 1] $ \r -> do
    ys <- if r == 0 then pure first else row r
    forM_ (zip [0 .. checkLength "imapRow" w' ys - 1] ys) $ \(c, y) ->
      writeWith strict d' (r * w' + c) y
  pure (MGrid w' h d')
{-# INLINABLE imapRowM #-}

imapColumnM ::
  (PrimMonad n, GM.MVector v a, GM.MVector v b) => Bool -> (Int -> [a] -> [b]) -> MGrid v n a -> n (MGrid v n b)
imapColumnM strict f (MGrid w h d) = do
  let column c = f c <$> mapM (\r -> GM.unsafeRead d (r * w + c)) [0 .. h - 1]
  first <- if w == 0 then pure [] else column 0
  let h' = if w == 0 then h else length first
  d' <- GM.unsafeNew (w * h')
  forM_ [0 .. w - 1] $ \c -> do
    ys <- if c == 0 then pure first else column c
    forM_ (zip [0 .. checkLength "imapColumn" h' ys - 1] ys) $ \(r, y) ->
      writeWith strict d' (r * w + c) y
  pure (MGrid w h' d')
{-# INLINABLE imapColumnM #-}

scanRowM ::
  (PrimMonad n, GM.MVector v a, GM.MVector v b) => Bool -> (b -> a -> b) -> b -> MGrid v n a -> n (MGrid v n b)
scanRowM strict f z (MGrid w h d) = do
  let w' = w + 1
  d' <- GM.unsafeNew (w' * h)
  forM_ [0 .. h - 1] $ \r -> do
    let go c acc
          | c == w = pure ()
          | otherwise = do
              x <- GM.unsafeRead d (r * w + c)
              let acc' = f acc x
              writeWith strict d' (r * w' + c + 1) acc'
              go (c + 1) acc'
    writeWith strict d' (r * w') z
    go 0 z
  pure (MGrid w' h d')
{-# INLINABLE scanRowM #-}

-- 転置せず、「1 つ上の行の結果 + 今の行」を上から順に書いていく。
scanColumnM ::
  (PrimMonad n, GM.MVector v a, GM.MVector v b) => Bool -> (b -> a -> b) -> b -> MGrid v n a -> n (MGrid v n b)
scanColumnM strict f z (MGrid w h d) = do
  d' <- GM.unsafeNew (w * (h + 1))
  forM_ [0 .. w - 1] $ \c -> writeWith strict d' c z
  forM_ [1 .. h] $ \r ->
    forM_ [0 .. w - 1] $ \c -> do
      prev <- GM.unsafeRead d' ((r - 1) * w + c)
      x <- GM.unsafeRead d ((r - 1) * w + c)
      writeWith strict d' (r * w + c) (f prev x)
  pure (MGrid w (h + 1) d')
{-# INLINABLE scanColumnM #-}

foldRowM :: (PrimMonad n, GM.MVector v a) => Bool -> (b -> a -> b) -> b -> MGrid v n a -> n [b]
foldRowM strict f z (MGrid w h d) = forM [0 .. h - 1] $ \r -> do
  let go acc c
        | c == w = pure acc
        | otherwise = do
            x <- GM.unsafeRead d (r * w + c)
            let acc' = f acc x
            if strict then acc' `seq` go acc' (c + 1) else go acc' (c + 1)
  if strict then z `seq` go z 0 else go z 0
{-# INLINABLE foldRowM #-}

foldGridM :: (PrimMonad n, GM.MVector v a) => Bool -> (b -> a -> b) -> b -> MGrid v n a -> n b
foldGridM strict f z (MGrid w h d) = if strict then z `seq` go z 0 else go z 0
  where
    go acc i
      | i == w * h = pure acc
      | otherwise = do
          x <- GM.unsafeRead d i
          let acc' = f acc x
          if strict then acc' `seq` go acc' (i + 1) else go acc' (i + 1)
{-# INLINABLE foldGridM #-}

-- 列ごとの途中結果を持ち、行優先で読みながら更新する。
foldColumnM :: (PrimMonad n, GM.MVector v a) => Bool -> (b -> a -> b) -> b -> MGrid v n a -> n [b]
foldColumnM strict f z (MGrid w h d) = do
  acc <- MV.replicate w z
  forM_ [0 .. h - 1] $ \r ->
    forM_ [0 .. w - 1] $ \c -> do
      x <- GM.unsafeRead d (r * w + c)
      s <- MV.unsafeRead acc c
      writeWith strict acc c (f s x)
  V.toList <$> V.freeze acc
{-# INLINABLE foldColumnM #-}

-- ---------------------------------------------------------------------
-- 作る・変換する

-- | 行のリストから作る。行の長さが揃っていなければ 'error'。
from2D :: (G.Vector v a) => [[a]] -> Grid v a
from2D [] = Grid 0 0 G.empty
from2D rows@(row : _)
  | all ((== w) . length) rows = Grid w (length rows) (G.fromList (concat rows))
  | otherwise = error "Atc.Grid.from2D: 行の長さが揃っていません"
  where
    w = length row

-- | 行優先に並んだ 1 次元リストから、幅 @w@ 高さ @h@ で作る。
-- 長さが @w * h@ でなければ 'error'。
from1D :: (G.Vector v a) => Int -> Int -> [a] -> Grid v a
from1D w h xs
  | length xs == w * h = Grid w h (G.fromListN (w * h) xs)
  | otherwise = error "Atc.Grid.from1D: 要素数が width * height と一致しません"

-- | 幅 @w@ 高さ @h@ で、全マスを @x@ で埋めて作る。
newMGrid :: (PrimMonad m, GM.MVector v a) => Int -> Int -> a -> m (MGrid v m a)
newMGrid w h x = MGrid w h <$> GM.replicate (w * h) x

-- | 不変版をコピーして可変版を作る。
thawGrid :: (PrimMonad m, G.Vector v a) => Grid v a -> m (MGrid (G.Mutable v) m a)
thawGrid (Grid w h d) = MGrid w h <$> G.thaw d

-- | 可変版をコピーして不変版を作る。元の 'MGrid' はこの後も使ってよい。
freezeGrid :: (PrimMonad m, G.Vector v a) => MGrid (G.Mutable v) m a -> m (Grid v a)
freezeGrid (MGrid w h d) = Grid w h <$> G.freeze d

-- | ST の中で可変版を組み立てて、コピーせずに不変版として取り出す。
createGrid :: (G.Vector v a) => (forall s. ST s (MGrid (G.Mutable v) (ST s) a)) -> Grid v a
createGrid st = runST $ do
  MGrid w h d <- st
  Grid w h <$> G.unsafeFreeze d
