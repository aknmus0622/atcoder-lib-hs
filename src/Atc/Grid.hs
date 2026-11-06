{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
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
-- > toRows g              t (s a)         m (t (s a))
-- > flattenRow g        t a             m (t a)           (flattenColumn も同じ)
-- > transposeGrid g     Grid v a        m (MGrid v m a)
-- > chebyshevGrid x g   Grid v a        m (MGrid v m a)   (45 度回転。下の節を参照)
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
-- 作る関数には、型を決めた版 (末尾 @U@ / @V@。可変版は @UM@ / @MV@) がある:
-- @fromRowsU@ / @unflattenRowU@ / @unflattenColumnU@ / @createGridU@ / @freezeGridU@ / @newMGridUM@ など。
--
-- > let g = fromRowsU [[1, 2, 3], [4, 5, 6]]   -- Grid U.Vector Int
-- > getElem (1, 1) g                 -- Just 5
-- > toRows (setElem (1, 1) 99 g) :: [[Int]]   -- [[1,2,3],[4,99,6]]
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
-- 'toRows' も同じで、外側 (行の並び) と内側 (1 行) をそれぞれ推論する。
-- 内側はリスト・@V.Vector@・@U.Vector@、外側はリストか @V.Vector@
-- (@U.Vector@ は中に Vector を入れられない)。
--
-- > let rows = toRows g :: V.Vector (U.Vector Int)
-- > rows V.! r U.! c
-- > mapM_ print (toRows g :: [[Int]])
--
-- 'flattenRow' / 'flattenColumn' は 1 列に並べる。並べる先は 'toRows' と同じく推論される。
--
-- > flattenRow g :: [Int]              -- 行優先: 上の行から、各行は左から
-- > flattenColumn g :: U.Vector Int    -- 列優先: 左の列から、各列は上から
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
-- > let g = fromRowsV [[1, 2], [3, 4]]   -- Grid V.Vector Int
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
-- IO で直接使うなら、型を決めた版 (末尾 @UM@ / @MV@ / @U@ / @V@) を使うと型を書かなくてよい。
--
-- > g <- newMGridUM w h (0 :: Int)  -- MGrid UM.MVector IO Int
-- > adjustElem (1, 2) (+ 1) g
-- > frozen <- freezeGridU g         -- Grid U.Vector Int
--
-- 既にある 'Grid' から始めるなら 'thawGrid'。
--
-- == マンハッタン距離と 45 度回転
--
-- @(r, c)@ を 'toChebyshev' で @(X, Y) = (r + c, r - c)@ に移すと、マンハッタン距離が
-- チェビシェフ距離 (各成分の差の max) になる。
--
-- > |r1 - r2| + |c1 - c2| == max |X1 - X2| |Y1 - Y2|
-- > manhattanDist p q == chebyshevDist (toChebyshev p) (toChebyshev q)
--
-- X と Y を別々に扱えるので、「最も遠い点」は X と Y それぞれの端だけを見ればよい。
-- 点の集合の端を 'ManhattanBox' に集めておくと、最遠距離が O(1) で出る。
--
-- > let box = foldMap boxOfPos ps
-- > farthestFromBox q box          -- q から ps の中で最も遠い点までの距離
-- > diameterOfBox box              -- ps の中の 2 点の距離の最大
-- > t <- buildSG (<>) mempty (U.map boxOfPos ps)   -- 区間の点で最遠距離 (セグ木に載る)
--
-- 中心 @(r, c)@・半径 @d@ のひし形 (マンハッタン距離 d 以下) は、
-- 回転後は軸に平行な正方形 @X ∈ [r+c-d, r+c+d]@, @Y ∈ [r-c-d, r-c+d]@ になる。
-- 'chebyshevGrid' でグリッドごと回すと、2 次元累積和などの長方形の処理がそのまま使える。
--
-- > let s   = chebyshevGrid 0 g                     -- 一辺 H + W - 1。隙間は 0
-- > let acc = scanColumn' (+) 0 (scanRow' (+) 0 s)  -- 2 次元累積和
-- > -- (r, c) から距離 d 以下のマスの和: 中心を chebyshevPos で移し、±d の正方形の和を取る
-- > -- (範囲は 0 .. H + W - 2 に切り詰める)
--
-- 回したグリッドは @(H + W - 1)^2@ マスある。H と W の差が大きいと元より大幅に大きくなる
-- (H = 1, W = 2×10^5 で 4×10^10)。そのときや点がまばらなときは、点だけを
-- 'toChebyshev' で移して座標圧縮・Fenwick の平面走査などで数える。
--
-- == 入力の頂点番号
--
-- 辺の並びなどを読んだ 'Grid' (や @U.Vector Int@) をグラフや Union-Find に渡すときは、
-- 'fromOneBased' か 'fromZeroBased' で 'ZeroBased' に包む。ライブラリの中はすべて
-- 0 始まりで、包まずに渡すと型エラーになる。
--
-- > es <- getIntGridU 2 m
-- > let g = undirectedGraph (fromOneBased es)    -- 入力が 1 始まり (AtCoder の普通の形)
-- > let g = undirectedGraph (fromZeroBased es)   -- 入力が 0 始まり
--
-- 'Grid' は各行の先頭 2 列 (@u v@) だけを直し、3 列目以降 (重みなど) はそのまま。
-- @U.Vector Int@ はすべての要素を直す。
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
import Data.Vector.Unboxed (MVector, Vector)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 座標計算
--
-- @import Atc@ で入るので、解答側で自前定義しがちな名前 (@inBounds@,
-- @toIndex@, @Width@ …) は避けている。

-- | @(r, c)@ : (行, 列)
type Pos = (Int, Int)

-- | 行優先の 1 次元添字に直す。
posToIndex ::
  -- | @w@: グリッドの幅
  Int ->
  -- | @(r, c)@: 座標
  Pos ->
  -- | 行優先の 1 次元添字 @r * w + c@
  Int
posToIndex w (r, c) = r * w + c

-- | 'posToIndex' の逆。
indexToPos ::
  -- | @w@: グリッドの幅
  Int ->
  -- | @i@: 行優先の 1 次元添字
  Int ->
  -- | 座標 (@i@ を @w@ で割った商と余り)
  Pos
indexToPos w i = i `divMod` w

-- | 範囲に入っているか。
inRange2D ::
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @(r, c)@: 座標
  Pos ->
  -- | @0 <= r < h@ かつ @0 <= c < w@ か
  Bool
inRange2D w h (r, c) = 0 <= r && r < h && 0 <= c && c < w

-- | 上・下・左・右の順。範囲は見ない。
around4 :: Pos -> [Pos]
around4 (r, c) = [(r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)]

-- | マンハッタン距離 (各成分の差の絶対値の和)。
manhattanDist ::
  -- | @(r1, c1)@: 1 つ目の点
  Pos ->
  -- | @(r2, c2)@: 2 つ目の点
  Pos ->
  -- | @|r1 - r2| + |c1 - c2|@
  Int
manhattanDist (r1, c1) (r2, c2) = abs (r1 - r2) + abs (c1 - c2)

-- | チェビシェフ距離 (各成分の差の絶対値の max)。
chebyshevDist ::
  -- | @(r1, c1)@: 1 つ目の点
  Pos ->
  -- | @(r2, c2)@: 2 つ目の点
  Pos ->
  -- | @max |r1 - r2| |c1 - c2|@
  Int
chebyshevDist (r1, c1) (r2, c2) = max (abs (r1 - r2)) (abs (c1 - c2))

-- | 45 度回転: @(r, c)@ を @(r + c, r - c)@ に。マンハッタン距離がチェビシェフ距離になる。
toChebyshev :: Pos -> Pos
toChebyshev (r, c) = (r + c, r - c)

-- | 'toChebyshev' の逆。2 成分の偶奇が違う点は元の格子点がないので 'Nothing'。
fromChebyshev :: Pos -> Maybe Pos
fromChebyshev (x, y)
  | odd (x - y) = Nothing
  | otherwise = Just ((x + y) `div` 2, (x - y) `div` 2)

-- | マス @(r, c)@ が、'chebyshevGrid' で回したグリッドのどこに来るか
-- ('toChebyshev' を列が 0 以上になるようずらしたもの)。
chebyshevPos ::
  -- | @w@: 元のグリッドの幅
  Int ->
  -- | @(r, c)@: 元のグリッドのマス
  Pos ->
  -- | 回したグリッドでの位置 @(r + c, r - c + w - 1)@
  Pos
chebyshevPos w (r, c) = (r + c, r - c + w - 1)

-- ---------------------------------------------------------------------
-- 点の集合の端 (マンハッタン距離の最遠点)

-- | 点の集合を 'toChebyshev' で移したときの X と Y の最小・最大。
-- 'boxOfPos' で 1 点から作り、@<>@ で合わせる。
-- 'mempty' は空の集合。
data ManhattanBox
  = ManhattanBox
      -- | @minX@: X の最小
      !Int
      -- | @maxX@: X の最大
      !Int
      -- | @minY@: Y の最小
      !Int
      -- | @maxY@: Y の最大
      !Int
  deriving (Eq, Show)

instance Semigroup ManhattanBox where
  ManhattanBox a b c d <> ManhattanBox a' b' c' d' =
    ManhattanBox (min a a') (max b b') (min c c') (max d d')

instance Monoid ManhattanBox where
  mempty = ManhattanBox maxBound minBound maxBound minBound

-- | 1 点だけの集合。
boxOfPos :: Pos -> ManhattanBox
boxOfPos p = let (x, y) = toChebyshev p in ManhattanBox x x y y

-- | 点 @p@ から集合の中で最も遠い点までのマンハッタン距離。O(1)。空の集合なら 'error'。
farthestFromBox ::
  -- | @p@: 点
  Pos ->
  -- | 点の集合の端
  ManhattanBox ->
  -- | @p@ から集合の中で最も遠い点までのマンハッタン距離
  Int
farthestFromBox p box@(ManhattanBox x0 x1 y0 y1)
  | box == mempty = error "Atc.Grid.farthestFromBox: 空の集合"
  | otherwise = maximum [x - x0, x1 - x, y - y0, y1 - y]
  where
    (x, y) = toChebyshev p

-- | 集合の中の 2 点のマンハッタン距離の最大。O(1)。空の集合なら 'error'。
diameterOfBox :: ManhattanBox -> Int
diameterOfBox box@(ManhattanBox x0 x1 y0 y1)
  | box == mempty = error "Atc.Grid.diameterOfBox: 空の集合"
  | otherwise = max (x1 - x0) (y1 - y0)

-- U.Vector に置くためのインスタンス (4 つ組として並べる)。
-- MVector / Vector は修飾なしで書く (atc bundle が書き出す export に合わせるため)。
instance U.IsoUnbox ManhattanBox (Int, Int, Int, Int) where
  toURepr (ManhattanBox a b c d) = (a, b, c, d)
  fromURepr (a, b, c, d) = ManhattanBox a b c d

newtype instance MVector s ManhattanBox = MV_ManhattanBox (MVector s (Int, Int, Int, Int))

newtype instance Vector ManhattanBox = V_ManhattanBox (Vector (Int, Int, Int, Int))

deriving via (U.As ManhattanBox (Int, Int, Int, Int)) instance GM.MVector U.MVector ManhattanBox

deriving via (U.As ManhattanBox (Int, Int, Int, Int)) instance G.Vector U.Vector ManhattanBox

instance U.Unbox ManhattanBox

-- ---------------------------------------------------------------------
-- 型

-- | 不変のグリッド。@v@ は @U.Vector@ か @V.Vector@。
data Grid v a
  = Grid
      -- | 幅
      !Int
      -- | 高さ
      !Int
      -- | 中身 (行優先。長さは幅 × 高さ)
      !(v a)

-- | 可変のグリッド。@v@ は @UM.MVector@ か @MV.MVector@、@m@ は @IO@ か @ST s@。
data MGrid v m a
  = MGrid
      -- | 幅
      !Int
      -- | 高さ
      !Int
      -- | 中身 (行優先。長さは幅 × 高さ)
      !(v (PrimState m) a)

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
  -- | 幅 (列の数)。
  gridWidth :: g -> Int

  -- | 高さ (行の数)。
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

  -- | 中身 (行優先に並んだ Vector)。
  gridData :: k a -> StoreOf k a

  -- | 元を読むだけの処理を実行する。
  primRun ::
    (CanHold k a) =>
    -- | 元のグリッド
    k a ->
    -- | @op m@: 元のグリッドを 'MGrid' として受け取り、読むだけで結果 @x@ を返す処理
    -- (@m@ に書き込んではいけない)
    (forall n. (PrimMonad n) => MGrid (MutOf k) n a -> n x) ->
    -- | 処理の結果
    Ret k x

  -- | 元を読んで新しいグリッドを作る処理を実行する。
  primNew ::
    (CanHold k a, CanHold k b) =>
    -- | 元のグリッド
    k a ->
    -- | @op m@: 元のグリッドを 'MGrid' として受け取り、新しいグリッドを返す処理
    -- (@m@ に書き込んではいけない)
    (forall n. (PrimMonad n) => MGrid (MutOf k) n a -> n (MGrid (MutOf k) n b)) ->
    -- | 処理が作った新しいグリッド
    Ret k (k b)

  -- | 元を書き換える処理を実行する。不変版はコピーを書き換える。
  primUpdate ::
    (CanHold k a) =>
    -- | 元のグリッド
    k a ->
    -- | @op m@: グリッドを 'MGrid' として受け取って書き換える処理 (不変版ではコピーが渡る)
    (forall n. (PrimMonad n) => MGrid (MutOf k) n a -> n ()) ->
    -- | 書き換えた結果 (不変版は新しいグリッド、可変版は @m ()@)
    Updated k a

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

-- | 'foldRow' / 'foldColumn' / 'toRows' / 'flattenRow' / 'flattenColumn' の結果を並べる先 (リスト・@V.Vector@・@U.Vector@)。
class Collect t a where
  -- | リストを並べる先の型に直す。
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
inGrid ::
  (GridShape g) =>
  -- | @pos@: 座標
  Pos ->
  -- | グリッド
  g ->
  -- | @pos@ がグリッドの範囲内か
  Bool
inGrid pos g = inRange2D (gridWidth g) (gridHeight g) pos

-- | 上・下・左・右の順に、範囲内の座標だけ返す。
neighborPos4 ::
  (GridShape g) =>
  -- | @pos@: 中心の座標
  Pos ->
  -- | グリッド
  g ->
  -- | @pos@ の上下左右のうち範囲内の座標 (上・下・左・右の順)
  [Pos]
neighborPos4 pos g = filter (`inGrid` g) (around4 pos)

-- | マスの値を読む。範囲外は 'Nothing'。
{-# INLINE getElem #-}
getElem ::
  (GridOf k a) =>
  -- | @pos@: 座標
  Pos ->
  -- | グリッド
  k a ->
  -- | @pos@ の値 (範囲外なら 'Nothing')
  Ret k (Maybe a)
getElem pos g =
  primRun g $ \m -> if inGrid pos g then Just <$> readAt m pos else pure Nothing

-- | マスの値を読む。範囲外は 'error'。範囲内と分かっている座標を読むとき用。
{-# INLINE elemAt #-}
elemAt ::
  (GridOf k a) =>
  -- | @pos@: 座標 (範囲内)
  Pos ->
  -- | グリッド
  k a ->
  -- | @pos@ の値
  Ret k a
elemAt pos g
  | inGrid pos g = primRun g $ \m -> readAt m pos
  | otherwise = error ("Atc.Grid.elemAt: 範囲外 " ++ show pos)

-- | マスに値を書く。範囲外なら何もしない。不変版は全体をコピーするので O(HW)。
{-# INLINE setElem #-}
setElem ::
  (GridOf k a) =>
  -- | @pos@: 座標
  Pos ->
  -- | @x@: 書く値
  a ->
  -- | グリッド
  k a ->
  -- | 不変版は書き換えた新しいグリッド、可変版はその場で書き換える
  Updated k a
setElem = setElemWith False

-- | 'setElem' の strict 版。
{-# INLINE setElem' #-}
setElem' ::
  (GridOf k a) =>
  -- | @pos@: 座標
  Pos ->
  -- | @x@: 書く値 (評価してから書く)
  a ->
  -- | グリッド
  k a ->
  -- | 不変版は書き換えた新しいグリッド、可変版はその場で書き換える
  Updated k a
setElem' = setElemWith True

-- | マスの値を @f@ で変える。範囲外なら何もしない。不変版は全体をコピーするので O(HW)。
{-# INLINE adjustElem #-}
adjustElem ::
  (GridOf k a) =>
  -- | @pos@: 座標
  Pos ->
  -- | @f x@: 今の値 @x@ から新しい値を作る
  (a -> a) ->
  -- | グリッド
  k a ->
  -- | 不変版は書き換えた新しいグリッド、可変版はその場で書き換える
  Updated k a
adjustElem = adjustElemWith False

-- | 'adjustElem' の strict 版。
{-# INLINE adjustElem' #-}
adjustElem' ::
  (GridOf k a) =>
  -- | @pos@: 座標
  Pos ->
  -- | @f x@: 今の値 @x@ から新しい値を作る (評価してから書く)
  (a -> a) ->
  -- | グリッド
  k a ->
  -- | 不変版は書き換えた新しいグリッド、可変版はその場で書き換える
  Updated k a
adjustElem' = adjustElemWith True

-- | 'setElem' / 'setElem'' の本体。
{-# INLINE setElemWith #-}
setElemWith :: (GridOf k a) => Bool -> Pos -> a -> k a -> Updated k a
setElemWith strict pos x g
  | inGrid pos g = primUpdate g $ \(MGrid w _ d) -> writeWith strict d (posToIndex w pos) x
  | otherwise = primUnchanged g

-- | 'adjustElem' / 'adjustElem'' の本体。
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
neighbors4 ::
  (GridOf k a) =>
  -- | @pos@: 中心の座標
  Pos ->
  -- | グリッド
  k a ->
  -- | 範囲内の隣の @(座標, 値)@ (上・下・左・右の順)
  Ret k [(Pos, a)]
neighbors4 pos g = primRun g $ \m -> mapM (\q -> (,) q <$> readAt m q) (neighborPos4 pos g)

-- | 行を上から順に並べる。外側 @t@ も 1 行 @s@ も使い方から推論される
-- (リスト・@V.Vector@・@U.Vector@)。
{-# INLINE toRows #-}
toRows :: forall t s k a. (GridOf k a, Collect s a, Collect t (s a)) => k a -> Ret k (t (s a))
toRows g = primRun g $ \m -> collectList @t . map (collectList @s) <$> toRowsM m

-- | 行優先 (上の行から、各行は左から) に 1 列に並べる。並べる先 @t@ は使い方から推論される
-- (リスト・@V.Vector@・@U.Vector@)。
{-# INLINE flattenRow #-}
flattenRow :: forall t k a. (GridOf k a, Collect t a) => k a -> Ret k (t a)
flattenRow g = primRun g $ \(MGrid w h d) ->
  collectList @t <$> mapM (GM.unsafeRead d) [0 .. w * h - 1]

-- | 列優先 (左の列から、各列は上から) に 1 列に並べる。並べる先は 'flattenRow' と同じ。
{-# INLINE flattenColumn #-}
flattenColumn :: forall t k a. (GridOf k a, Collect t a) => k a -> Ret k (t a)
flattenColumn g = primRun g $ \(MGrid w h d) ->
  collectList @t <$> sequence [GM.unsafeRead d (r * w + c) | c <- [0 .. w - 1], r <- [0 .. h - 1]]

-- | 転置。幅と高さが入れ替わる。
{-# INLINE transposeGrid #-}
transposeGrid :: (GridOf k a) => k a -> Ret k (k a)
transposeGrid g = primNew g transposeM

-- | 45 度回したグリッド。マス @(r, c)@ は 'chebyshevPos' の位置 @(r + c, r - c + w - 1)@ に移る。
-- 大きさは幅・高さとも @H + W - 1@ (空のグリッドなら 0)。
-- O((H + W)^2)。
{-# INLINE chebyshevGrid #-}
chebyshevGrid ::
  (GridOf k a) =>
  -- | @fill@: 元のマスに当たらない位置を埋める値
  a ->
  -- | 元のグリッド
  k a ->
  -- | 回したグリッド (一辺 @H + W - 1@)
  Ret k (k a)
chebyshevGrid fill g = primNew g (chebyshevM fill)

-- | 全マスに @f@ を適用した新しいグリッド。要素型が変わってもよい。
{-# INLINE mapGrid #-}
mapGrid ::
  (GridOf k a, GridOf k b) =>
  -- | @f x@: マスの値 @x@ から新しい値を作る
  (a -> b) ->
  -- | 元のグリッド
  k a ->
  -- | 全マスに @f@ を適用したグリッド
  Ret k (k b)
mapGrid f = imapGrid (const f)

-- | 'mapGrid' の strict 版。
{-# INLINE mapGrid' #-}
mapGrid' ::
  (GridOf k a, GridOf k b) =>
  -- | @f x@: マスの値 @x@ から新しい値を作る (評価してから格納する)
  (a -> b) ->
  -- | 元のグリッド
  k a ->
  -- | 全マスに @f@ を適用したグリッド
  Ret k (k b)
mapGrid' f = imapGrid' (const f)

-- | 座標付きの 'mapGrid'。
{-# INLINE imapGrid #-}
imapGrid ::
  (GridOf k a, GridOf k b) =>
  -- | @f p x@: マス @p@ の値 @x@ から新しい値を作る
  (Pos -> a -> b) ->
  -- | 元のグリッド
  k a ->
  -- | 全マスに @f@ を適用したグリッド
  Ret k (k b)
imapGrid f g = primNew g (imapM False f)

-- | 'imapGrid' の strict 版。
{-# INLINE imapGrid' #-}
imapGrid' ::
  (GridOf k a, GridOf k b) =>
  -- | @f p x@: マス @p@ の値 @x@ から新しい値を作る (評価してから格納する)
  (Pos -> a -> b) ->
  -- | 元のグリッド
  k a ->
  -- | 全マスに @f@ を適用したグリッド
  Ret k (k b)
imapGrid' f g = primNew g (imapM True f)

-- | 各行をリストとして変換した新しいグリッド。全行で長さが揃っていなければ 'error'。
{-# INLINE mapRow #-}
mapRow ::
  (GridOf k a, GridOf k b) =>
  -- | @f xs@: 1 行 @xs@ (左から右) を新しい行にする。長さが変わってもよい
  ([a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各行を @f@ で変換したグリッド (幅は @f@ の結果の長さ)
  Ret k (k b)
mapRow f = imapRow (const f)

-- | 'mapRow' の strict 版。
{-# INLINE mapRow' #-}
mapRow' ::
  (GridOf k a, GridOf k b) =>
  -- | @f xs@: 1 行 @xs@ (左から右) を新しい行にする。長さが変わってもよい
  -- (各要素を評価してから格納する)
  ([a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各行を @f@ で変換したグリッド (幅は @f@ の結果の長さ)
  Ret k (k b)
mapRow' f = imapRow' (const f)

-- | 行番号付きの 'mapRow'。
{-# INLINE imapRow #-}
imapRow ::
  (GridOf k a, GridOf k b) =>
  -- | @f r xs@: 第 @r@ 行 @xs@ (左から右) を新しい行にする。長さが変わってもよい
  (Int -> [a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各行を @f@ で変換したグリッド (幅は @f@ の結果の長さ)
  Ret k (k b)
imapRow f g = primNew g (imapRowM False f)

-- | 'imapRow' の strict 版。
{-# INLINE imapRow' #-}
imapRow' ::
  (GridOf k a, GridOf k b) =>
  -- | @f r xs@: 第 @r@ 行 @xs@ (左から右) を新しい行にする。長さが変わってもよい
  -- (各要素を評価してから格納する)
  (Int -> [a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各行を @f@ で変換したグリッド (幅は @f@ の結果の長さ)
  Ret k (k b)
imapRow' f g = primNew g (imapRowM True f)

-- | 各列をリストとして変換した新しいグリッド。全列で長さが揃っていなければ 'error'。
{-# INLINE mapColumn #-}
mapColumn ::
  (GridOf k a, GridOf k b) =>
  -- | @f xs@: 1 列 @xs@ (上から下) を新しい列にする。長さが変わってもよい
  ([a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各列を @f@ で変換したグリッド (高さは @f@ の結果の長さ)
  Ret k (k b)
mapColumn f = imapColumn (const f)

-- | 'mapColumn' の strict 版。
{-# INLINE mapColumn' #-}
mapColumn' ::
  (GridOf k a, GridOf k b) =>
  -- | @f xs@: 1 列 @xs@ (上から下) を新しい列にする。長さが変わってもよい
  -- (各要素を評価してから格納する)
  ([a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各列を @f@ で変換したグリッド (高さは @f@ の結果の長さ)
  Ret k (k b)
mapColumn' f = imapColumn' (const f)

-- | 列番号付きの 'mapColumn'。
{-# INLINE imapColumn #-}
imapColumn ::
  (GridOf k a, GridOf k b) =>
  -- | @f c xs@: 第 @c@ 列 @xs@ (上から下) を新しい列にする。長さが変わってもよい
  (Int -> [a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各列を @f@ で変換したグリッド (高さは @f@ の結果の長さ)
  Ret k (k b)
imapColumn f g = primNew g (imapColumnM False f)

-- | 'imapColumn' の strict 版。
{-# INLINE imapColumn' #-}
imapColumn' ::
  (GridOf k a, GridOf k b) =>
  -- | @f c xs@: 第 @c@ 列 @xs@ (上から下) を新しい列にする。長さが変わってもよい
  -- (各要素を評価してから格納する)
  (Int -> [a] -> [b]) ->
  -- | 元のグリッド
  k a ->
  -- | 各列を @f@ で変換したグリッド (高さは @f@ の結果の長さ)
  Ret k (k b)
imapColumn' f g = primNew g (imapColumnM True f)

-- | 各行に左から @scanl f z@ をかける。幅が 1 増える。
{-# INLINE scanRow #-}
scanRow ::
  (GridOf k a, GridOf k b) =>
  -- | @f acc x@: 左までの結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各行の先頭 (第 0 列) に置く初期値
  b ->
  -- | 元のグリッド
  k a ->
  -- | 第 @c@ 列が元の第 0 〜 @c - 1@ 列を畳んだ値のグリッド (幅 + 1)
  Ret k (k b)
scanRow f z g = primNew g (scanRowM False f z)

-- | 'scanRow' の @scanl'@ 版。値を評価してから格納する。
{-# INLINE scanRow' #-}
scanRow' ::
  (GridOf k a, GridOf k b) =>
  -- | @f acc x@: 左までの結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各行の先頭 (第 0 列) に置く初期値
  b ->
  -- | 元のグリッド
  k a ->
  -- | 第 @c@ 列が元の第 0 〜 @c - 1@ 列を畳んだ値のグリッド (幅 + 1)
  Ret k (k b)
scanRow' f z g = primNew g (scanRowM True f z)

-- | 各列に上から @scanl f z@ をかける。高さが 1 増える。
{-# INLINE scanColumn #-}
scanColumn ::
  (GridOf k a, GridOf k b) =>
  -- | @f acc x@: 上までの結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各列の先頭 (第 0 行) に置く初期値
  b ->
  -- | 元のグリッド
  k a ->
  -- | 第 @r@ 行が元の第 0 〜 @r - 1@ 行を畳んだ値のグリッド (高さ + 1)
  Ret k (k b)
scanColumn f z g = primNew g (scanColumnM False f z)

-- | 'scanColumn' の @scanl'@ 版。値を評価してから格納する。
{-# INLINE scanColumn' #-}
scanColumn' ::
  (GridOf k a, GridOf k b) =>
  -- | @f acc x@: 上までの結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各列の先頭 (第 0 行) に置く初期値
  b ->
  -- | 元のグリッド
  k a ->
  -- | 第 @r@ 行が元の第 0 〜 @r - 1@ 行を畳んだ値のグリッド (高さ + 1)
  Ret k (k b)
scanColumn' f z g = primNew g (scanColumnM True f z)

-- | 各行を左から @foldl@ で畳んで、上の行から順に並べる。
{-# INLINE foldRow #-}
foldRow ::
  forall t k a b.
  (GridOf k a, Collect t b) =>
  -- | @f acc x@: 途中結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各行の初期値
  b ->
  -- | グリッド
  k a ->
  -- | 各行を畳んだ値を上の行から並べたもの。並べる先 (リスト・@V.Vector@・@U.Vector@) は
  -- 使い方から推論される
  Ret k (t b)
foldRow f z g = primRun g $ \m -> collectList @t <$> foldRowM False f z m

-- | 'foldRow' の @foldl'@ 版。途中結果を評価しながら畳む。
{-# INLINE foldRow' #-}
foldRow' ::
  forall t k a b.
  (GridOf k a, Collect t b) =>
  -- | @f acc x@: 途中結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各行の初期値
  b ->
  -- | グリッド
  k a ->
  -- | 各行を畳んだ値を上の行から並べたもの。並べる先 (リスト・@V.Vector@・@U.Vector@) は
  -- 使い方から推論される
  Ret k (t b)
foldRow' f z g = primRun g $ \m -> collectList @t <$> foldRowM True f z m

-- | 各列を上から @foldl@ で畳んで、左の列から順に並べる。
{-# INLINE foldColumn #-}
foldColumn ::
  forall t k a b.
  (GridOf k a, Collect t b) =>
  -- | @f acc x@: 途中結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各列の初期値
  b ->
  -- | グリッド
  k a ->
  -- | 各列を畳んだ値を左の列から並べたもの。並べる先 (リスト・@V.Vector@・@U.Vector@) は
  -- 使い方から推論される
  Ret k (t b)
foldColumn f z g = primRun g $ \m -> collectList @t <$> foldColumnM False f z m

-- | 'foldColumn' の @foldl'@ 版。途中結果を評価しながら畳む。
{-# INLINE foldColumn' #-}
foldColumn' ::
  forall t k a b.
  (GridOf k a, Collect t b) =>
  -- | @f acc x@: 途中結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 各列の初期値
  b ->
  -- | グリッド
  k a ->
  -- | 各列を畳んだ値を左の列から並べたもの。並べる先 (リスト・@V.Vector@・@U.Vector@) は
  -- 使い方から推論される
  Ret k (t b)
foldColumn' f z g = primRun g $ \m -> collectList @t <$> foldColumnM True f z m

-- | 全マスを行優先に @foldl@ で畳む。
{-# INLINE foldGrid #-}
foldGrid ::
  (GridOf k a) =>
  -- | @f acc x@: 途中結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 初期値
  b ->
  -- | グリッド
  k a ->
  -- | 全マスを畳んだ値
  Ret k b
foldGrid f z g = primRun g (foldGridM False f z)

-- | 'foldGrid' の @foldl'@ 版。途中結果を評価しながら畳む。
{-# INLINE foldGrid' #-}
foldGrid' ::
  (GridOf k a) =>
  -- | @f acc x@: 途中結果 @acc@ とマスの値 @x@ から次の結果を作る
  (b -> a -> b) ->
  -- | @z@: 初期値
  b ->
  -- | グリッド
  k a ->
  -- | 全マスを畳んだ値
  Ret k b
foldGrid' f z g = primRun g (foldGridM True f z)

-- ---------------------------------------------------------------------
-- MGrid の上の処理 (共通関数の中身)

-- | 座標 @pos@ の値を読む (範囲は見ない)。
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

-- | 'toRows' の本体。
toRowsM :: (PrimMonad n, GM.MVector v a) => MGrid v n a -> n [[a]]
toRowsM (MGrid w h d) = forM [0 .. h - 1] $ \r -> mapM (\c -> GM.unsafeRead d (r * w + c)) [0 .. w - 1]
{-# INLINABLE toRowsM #-}

-- | 'transposeGrid' の本体。
transposeM :: (PrimMonad n, GM.MVector v a) => MGrid v n a -> n (MGrid v n a)
transposeM (MGrid w h d) = do
  d' <- GM.unsafeNew (w * h)
  forM_ [0 .. h - 1] $ \r ->
    forM_ [0 .. w - 1] $ \c ->
      GM.unsafeRead d (r * w + c) >>= GM.unsafeWrite d' (c * h + r)
  pure (MGrid h w d')
{-# INLINABLE transposeM #-}

-- | 'chebyshevGrid' の本体。
chebyshevM :: (PrimMonad n, GM.MVector v a) => a -> MGrid v n a -> n (MGrid v n a)
chebyshevM fill (MGrid w h d) = do
  let s = if w * h == 0 then 0 else w + h - 1
  d' <- GM.replicate (s * s) fill
  forM_ [0 .. h - 1] $ \r ->
    forM_ [0 .. w - 1] $ \c ->
      GM.unsafeRead d (r * w + c) >>= GM.unsafeWrite d' ((r + c) * s + (r - c + w - 1))
  pure (MGrid s s d')
{-# INLINABLE chebyshevM #-}

-- | 'imapGrid' / 'imapGrid'' の本体。
imapM ::
  (PrimMonad n, GM.MVector v a, GM.MVector v b) => Bool -> (Pos -> a -> b) -> MGrid v n a -> n (MGrid v n b)
imapM strict f (MGrid w h d) = do
  d' <- GM.unsafeNew (w * h)
  forM_ [0 .. w * h - 1] $ \i -> do
    x <- GM.unsafeRead d i
    writeWith strict d' i (f (indexToPos w i) x)
  pure (MGrid w h d')
{-# INLINABLE imapM #-}

-- | 'imapRow' / 'imapRow'' の本体。
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

-- | 'imapColumn' / 'imapColumn'' の本体。
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

-- | 'scanRow' / 'scanRow'' の本体。
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

-- | 'scanColumn' / 'scanColumn'' の本体。
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

-- | 'foldRow' / 'foldRow'' の本体。
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

-- | 'foldGrid' / 'foldGrid'' の本体。
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

-- | 'foldColumn' / 'foldColumn'' の本体。
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
fromRows ::
  (G.Vector v a) =>
  -- | @rows@: 上の行から順に並べた行 (各行は左から)
  [[a]] ->
  -- | 幅が行の長さ、高さが行の数のグリッド
  Grid v a
fromRows [] = Grid 0 0 G.empty
fromRows rows@(row : _)
  | all ((== w) . length) rows = Grid w (length rows) (G.fromList (concat rows))
  | otherwise = error "Atc.Grid.fromRows: 行の長さが揃っていません"
  where
    w = length row

-- | 'fromRows' の型を決めたもの (@U.Vector@)。
fromRowsU ::
  (U.Unbox a) =>
  -- | @rows@: 上の行から順に並べた行 (各行は左から)
  [[a]] ->
  -- | 幅が行の長さ、高さが行の数のグリッド
  Grid U.Vector a
fromRowsU = fromRows

-- | 'fromRows' の型を決めたもの (@V.Vector@)。
fromRowsV ::
  -- | @rows@: 上の行から順に並べた行 (各行は左から)
  [[a]] ->
  -- | 幅が行の長さ、高さが行の数のグリッド
  Grid V.Vector a
fromRowsV = fromRows

-- | 行優先に並んだリストから作る。'flattenRow' の逆。長さが @w * h@ でなければ 'error'。
unflattenRow ::
  (G.Vector v a) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @xs@: 行優先 (上の行から、各行は左から)に並んだ要素 (長さ @w * h@)
  [a] ->
  -- | 幅 @w@ 高さ @h@ のグリッド
  Grid v a
unflattenRow w h xs
  | length xs == w * h = Grid w h (G.fromListN (w * h) xs)
  | otherwise = error "Atc.Grid.unflattenRow: 要素数が width * height と一致しません"

-- | 'unflattenRow' の型を決めたもの (@U.Vector@)。
unflattenRowU ::
  (U.Unbox a) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @xs@: 行優先 (上の行から、各行は左から)に並んだ要素 (長さ @w * h@)
  [a] ->
  -- | 幅 @w@ 高さ @h@ のグリッド
  Grid U.Vector a
unflattenRowU = unflattenRow

-- | 'unflattenRow' の型を決めたもの (@V.Vector@)。
unflattenRowV ::
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @xs@: 行優先 (上の行から、各行は左から)に並んだ要素 (長さ @w * h@)
  [a] ->
  -- | 幅 @w@ 高さ @h@ のグリッド
  Grid V.Vector a
unflattenRowV = unflattenRow

-- | 列優先に並んだリストから作る。'flattenColumn' の逆。長さが @w * h@ でなければ 'error'。
unflattenColumn ::
  (G.Vector v a) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @xs@: 列優先 (左の列から、各列は上から)に並んだ要素 (長さ @w * h@)
  [a] ->
  -- | 幅 @w@ 高さ @h@ のグリッド
  Grid v a
unflattenColumn w h xs
  | length xs == w * h = Grid w h (G.generate (w * h) (\i -> let (r, c) = i `divMod` w in V.unsafeIndex cs (c * h + r)))
  | otherwise = error "Atc.Grid.unflattenColumn: 要素数が width * height と一致しません"
  where
    cs = V.fromListN (w * h) xs

-- | 'unflattenColumn' の型を決めたもの (@U.Vector@)。
unflattenColumnU ::
  (U.Unbox a) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @xs@: 列優先 (左の列から、各列は上から)に並んだ要素 (長さ @w * h@)
  [a] ->
  -- | 幅 @w@ 高さ @h@ のグリッド
  Grid U.Vector a
unflattenColumnU = unflattenColumn

-- | 'unflattenColumn' の型を決めたもの (@V.Vector@)。
unflattenColumnV ::
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @xs@: 列優先 (左の列から、各列は上から)に並んだ要素 (長さ @w * h@)
  [a] ->
  -- | 幅 @w@ 高さ @h@ のグリッド
  Grid V.Vector a
unflattenColumnV = unflattenColumn

-- | 全マスを同じ値で埋めて作る。
newMGrid ::
  (PrimMonad m, GM.MVector v a) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @x@: 全マスに入れる値
  a ->
  -- | 幅 @w@ 高さ @h@ の新しい可変グリッド
  m (MGrid v m a)
newMGrid w h x = MGrid w h <$> GM.replicate (w * h) x

-- | 'newMGrid' の型を決めたもの (@UM.MVector@)。
newMGridUM ::
  (PrimMonad m, U.Unbox a) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @x@: 全マスに入れる値
  a ->
  -- | 幅 @w@ 高さ @h@ の新しい可変グリッド
  m (MGrid UM.MVector m a)
newMGridUM = newMGrid

-- | 'newMGrid' の型を決めたもの (@MV.MVector@)。
newMGridMV ::
  (PrimMonad m) =>
  -- | @w@: 幅
  Int ->
  -- | @h@: 高さ
  Int ->
  -- | @x@: 全マスに入れる値
  a ->
  -- | 幅 @w@ 高さ @h@ の新しい可変グリッド
  m (MGrid MV.MVector m a)
newMGridMV = newMGrid

-- | 不変版をコピーして可変版を作る。
thawGrid :: (PrimMonad m, G.Vector v a) => Grid v a -> m (MGrid (G.Mutable v) m a)
thawGrid (Grid w h d) = MGrid w h <$> G.thaw d

-- | 可変版をコピーして不変版を作る。元の 'MGrid' はこの後も使ってよい。
freezeGrid :: (PrimMonad m, G.Vector v a) => MGrid (G.Mutable v) m a -> m (Grid v a)
freezeGrid (MGrid w h d) = Grid w h <$> G.freeze d

-- | 'freezeGrid' の型を決めたもの (@U.Vector@)。
freezeGridU :: (PrimMonad m, U.Unbox a) => MGrid UM.MVector m a -> m (Grid U.Vector a)
freezeGridU = freezeGrid

-- | 'freezeGrid' の型を決めたもの (@V.Vector@)。
freezeGridV :: (PrimMonad m) => MGrid MV.MVector m a -> m (Grid V.Vector a)
freezeGridV = freezeGrid

-- | ST の中で可変版を組み立てて、コピーせずに不変版として取り出す。
createGrid :: (G.Vector v a) => (forall s. ST s (MGrid (G.Mutable v) (ST s) a)) -> Grid v a
createGrid st = runST $ do
  MGrid w h d <- st
  Grid w h <$> G.unsafeFreeze d

-- | 'createGrid' の型を決めたもの (@U.Vector@)。
createGridU :: (U.Unbox a) => (forall s. ST s (MGrid UM.MVector (ST s) a)) -> Grid U.Vector a
createGridU st = createGrid st

-- | 'createGrid' の型を決めたもの (@V.Vector@)。
createGridV :: (forall s. ST s (MGrid MV.MVector (ST s) a)) -> Grid V.Vector a
createGridV st = createGrid st

-- ---------------------------------------------------------------------
-- 入力の頂点番号

-- | 頂点番号を 0 始まりにそろえた入力。'fromOneBased' / 'fromZeroBased' で作る。
newtype ZeroBased a = ZeroBased a

-- | 頂点番号を持つ入力。'Grid' は各行の先頭 2 列、@U.Vector Int@ はすべての要素が頂点番号。
class VertexInput a where
  -- | 1 始まりの頂点番号から 1 を引いて包む。
  fromOneBased :: a -> ZeroBased a

  -- | 0 始まりの頂点番号をそのまま包む。
  fromZeroBased :: a -> ZeroBased a
  fromZeroBased = ZeroBased

instance (G.Vector v Int) => VertexInput (Grid v Int) where
  fromOneBased (Grid w h d) = ZeroBased (Grid w h (G.imap (\i x -> if i `mod` w < 2 then x - 1 else x) d))

instance VertexInput (U.Vector Int) where
  fromOneBased = ZeroBased . U.map (subtract 1)
