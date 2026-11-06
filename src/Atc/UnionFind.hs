{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Union-Find (素集合データ構造)。重み (ポテンシャル) と成分ごとの値も持てる。
--
-- 頂点は 0 始まりの @0 .. n - 1@。
--
-- == 型
--
-- 不変版 'UnionFind' と可変版 'MUnionFind' がある (Grid と MGrid の関係と同じ)。
--
-- > UnionFind    w v a     w: 重みの型 (なければ ())
-- > MUnionFind m w v a     v a: 成分の値の Vector と要素の型 (なければ U.Vector ())
-- >                        m: IO か ST s
--
-- 型は作る関数と使い方から推論されるので、普通は書かなくてよい。
--
-- > uf <- newUF n                                   -- 重みなし・値なし
-- > uf <- newWUF n                                  -- 重みあり (重みの型は使い方から決まる)
-- > uf <- newUFWith (+) (U.replicate n (1 :: Int))  -- 値あり (U.Vector Int)
-- > uf <- newUFWith (<>) (V.generate n pure)        -- 値あり (V.Vector [Int]: 成分の頂点)
-- > uf <- newWUFWith max xs                         -- 重みと値の両方
--
-- 値の Vector は渡したものの種類 (U.Vector / V.Vector) がそのまま使われる。
-- 重みの置き場所は型から選ぶ ('Int' / 'Double' は U.Vector、ほかは V.Vector)。
--
-- == 不変版と可変版で同じ関数
--
-- > 関数                   UnionFind w v a           MUnionFind m w v a
-- > rootUF x uf            Int                       m Int
-- > sameUF x y uf          Bool                      m Bool
-- > sizeUF x uf            Int                       m Int        (x を含む成分の頂点数)
-- > countUF uf             Int                       m Int        (成分の数)
-- > groupsUF uf            V.Vector (U.Vector Int)   m (V.Vector (U.Vector Int))
-- > valueUF x uf           a                         m a          (x を含む成分の値)
-- > diffUF x y uf          Maybe w                   m (Maybe w)  (x_y - x_x。別の成分なら Nothing)
-- > membersUF x uf         U.Vector Int              m (U.Vector Int)  (x を含む成分の頂点)
--
-- 'groupsUF' は成分を最小の頂点の順に、各成分の中は頂点の昇順に並べる。O(n)。
-- 'membersUF' は O(成分の大きさ) で、頂点は x から始まり、昇順とは限らない
-- (並べたいなら @U.modify Intro.sort@ などをかける)。
--
-- 可変版だけ:
--
-- > uniteUF x y uf         m Bool    つなぐ。新しくつないだら True
-- > uniteDiffUF x y d uf   m Bool    x_y - x_x = d としてつなぐ。矛盾したら False (矛盾しなければ True)
-- > modifyValueUF f x uf   m ()      x を含む成分の値を書き換える
--
-- つなぐと、成分の値は作るときに渡した @op@ でまとめる ('newUFWith' の引数の説明)。
-- 重みありで 'uniteUF' を使うと、差 0 ('zeroW') でつなぐ。
-- 値と重みは書き込むときに WHNF まで評価する。
--
-- > uf <- newUF n
-- > forM_ qs $ \(t, a, b) ->
-- >   if t == 0 then void (uniteUF a b uf) else sameUF a b uf >>= putStrLn . bool "No" "Yes"
-- >
-- > -- x_r - x_l = d の制約が矛盾しないか (ABC087 D)
-- > uf <- newWUF n
-- > oks <- forM cs $ \(l, r, d) -> uniteDiffUF l r d uf
-- > putStrLn (if and oks then "Yes" else "No")
--
-- == 不変版を作る
--
-- > let uf = buildUF n (fromOneBased es)    -- es は getIntGridU 2 m で読んだ辺 (Graph と同じ)
-- > let muf = buildWUF n (fromOneBased es)  -- 幅 3 (u v d: x_v - x_u = d)。矛盾したら Nothing
-- > let uf = createUF $ do ...  -- ST の中で可変版を作って取り出す
-- > uf <- freezeUF muf          -- 可変版を写し取る (以後も可変版は使える)
-- > muf <- thawUF uf
--
-- 不変版は全頂点の根を求めてあるので、問い合わせは O(1) ('groupsUF' は O(n))。
--
-- == 重みの型
--
-- 重みは 'UFWeight' (差を取れる型) のインスタンス。'Num' の型 ('Int' / 'Integer' /
-- 'Double' / ModInt など) は @+@ で、"Data.Bits" の @Xor a@ は XOR で差を取る。
-- 重みの型が決まらない (数値リテラルだけを渡す) とコンパイルエラーになるので、
-- そのときは @(d :: Int)@ のように書く。入力から読んだ値なら決まっている。
--
-- > uf <- newWUF n
-- > uniteDiffUF u v (Xor 1) uf                -- u と v は偶奇が違う
-- > fmap getXor <$> diffUF u v uf            -- Just 0 / Just 1 / Nothing
--
-- 内部は親の配列 1 本 (根なら @-大きさ@) と、親から見た重み・根に置いた値。
-- 成分の頂点は、次の頂点を指す配列で輪につないでおく (つなぐときは 2 つの輪を 1 つにする)。
-- 大きさで併合するので木の深さは O(log n) で、経路圧縮は再帰で行う。
module Atc.UnionFind where

import Atc.Grid (Grid (..), ZeroBased (..))
import Control.Monad (forM_, when)
import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.ST (ST, runST)
import Data.Bits (Bits, Xor (..), xor, zeroBits)
import Data.Kind (Type)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM

-- ---------------------------------------------------------------------
-- 重み

-- | 差を取れる型 (可換群)。@x_y - x_x@ を @addW wy (negW wx)@ で求める。
class (Eq w) => UFWeight w where
  -- | 差 0 (単位元)。
  zeroW :: w

  -- | 重みの和。
  addW ::
    -- | 重み
    w ->
    -- | 重み
    w ->
    -- | 2 つの和
    w

  -- | 符号を反転した重み (逆元)。
  negW :: w -> w

instance {-# OVERLAPPING #-} UFWeight () where
  {-# INLINE zeroW #-}
  zeroW = ()
  {-# INLINE addW #-}
  addW _ _ = ()
  {-# INLINE negW #-}
  negW _ = ()

instance {-# OVERLAPPING #-} (Bits a) => UFWeight (Xor a) where
  {-# INLINE zeroW #-}
  zeroW = Xor zeroBits
  {-# INLINE addW #-}
  addW (Xor a) (Xor b) = Xor (xor a b)
  {-# INLINE negW #-}
  negW = id

instance {-# OVERLAPPABLE #-} (Eq w, Num w) => UFWeight w where
  {-# INLINE zeroW #-}
  zeroW = 0
  {-# INLINE addW #-}
  addW = (+)
  {-# INLINE negW #-}
  negW = negate

-- | 重みの置き場所。
type family WStore w :: Type -> Type where
  WStore () = U.Vector
  WStore Int = U.Vector
  WStore Double = U.Vector
  WStore w = V.Vector

-- | 重みとして使える型。
type WeightOf w = (UFWeight w, G.Vector (WStore w) w)

-- | 重み @w@ と値 @v a@ の組で使える。
type UFOf w v a = (WeightOf w, G.Vector v a)

-- ---------------------------------------------------------------------
-- 型

-- | 不変版。各配列は頂点番号で引く。
data UnionFind w v a
  = UnionFind
      -- | 根
      !(U.Vector Int)
      -- | 大きさ (根の位置)
      !(U.Vector Int)
      -- | 同じ成分の次の頂点
      !(U.Vector Int)
      -- | 根から見た重み
      !(WStore w w)
      -- | 値 (根の位置)
      !(v a)
      -- | 成分の数
      !Int
      -- | 値の op
      (a -> a -> a)

-- | 可変版。各配列は頂点番号で引く。
data MUnionFind m w v a
  = MUnionFind
      -- | 親 (根なら -大きさ)
      !(UM.MVector (PrimState m) Int)
      -- | 同じ成分の次の頂点
      !(UM.MVector (PrimState m) Int)
      -- | 親から見た重み
      !(G.Mutable (WStore w) (PrimState m) w)
      -- | 値 (根の位置)
      !(G.Mutable v (PrimState m) a)
      -- | 成分の数 (長さ 1)
      !(UM.MVector (PrimState m) Int)
      -- | 値の op
      (a -> a -> a)

-- | 不変版と可変版で共通の関数。可変版は返り値が @m@ に包まれる。
class UFKind k where
  -- | 返り値の型 (不変版はそのまま、可変版は @m@ に包む)。
  type UFRet k x

  -- | 根。
  rootUF ::
    (UFOf w v a) =>
    -- | @x@: 頂点
    Int ->
    -- | Union-Find
    k w v a ->
    -- | @x@ を含む成分の根
    UFRet k Int

  -- | 同じ成分か。
  sameUF ::
    (UFOf w v a) =>
    -- | @x@: 頂点
    Int ->
    -- | @y@: 頂点
    Int ->
    -- | Union-Find
    k w v a ->
    -- | @x@ と @y@ が同じ成分か
    UFRet k Bool

  -- | 成分の大きさ。
  sizeUF ::
    (UFOf w v a) =>
    -- | @x@: 頂点
    Int ->
    -- | Union-Find
    k w v a ->
    -- | @x@ を含む成分の頂点数
    UFRet k Int

  -- | 成分の数。
  countUF :: (UFOf w v a) => k w v a -> UFRet k Int

  -- | すべての成分。成分を最小の頂点の順に、各成分の中は頂点の昇順に並べる。O(n)。
  groupsUF :: (UFOf w v a) => k w v a -> UFRet k (V.Vector (U.Vector Int))

  -- | 成分の値。
  valueUF ::
    (UFOf w v a) =>
    -- | @x@: 頂点
    Int ->
    -- | Union-Find
    k w v a ->
    -- | @x@ を含む成分の値
    UFRet k a

  -- | 重みの差。
  diffUF ::
    (UFOf w v a) =>
    -- | @x@: 頂点
    Int ->
    -- | @y@: 頂点
    Int ->
    -- | Union-Find
    k w v a ->
    -- | @x_y - x_x@。別の成分なら 'Nothing'
    UFRet k (Maybe w)

  -- | 成分の頂点。O(成分の大きさ)。
  membersUF ::
    (UFOf w v a) =>
    -- | @x@: 頂点
    Int ->
    -- | Union-Find
    k w v a ->
    -- | @x@ を含む成分の頂点。@x@ から始まり、昇順とは限らない
    UFRet k (U.Vector Int)

instance UFKind UnionFind where
  type UFRet UnionFind x = x
  {-# INLINE rootUF #-}
  rootUF x uf@(UnionFind rs _ _ _ _ _ _) = ufCheck uf x `seq` U.unsafeIndex rs x
  {-# INLINE sameUF #-}
  sameUF x y uf = rootUF x uf == rootUF y uf
  {-# INLINE sizeUF #-}
  sizeUF x uf@(UnionFind _ ss _ _ _ _ _) = U.unsafeIndex ss (rootUF x uf)
  {-# INLINE countUF #-}
  countUF (UnionFind _ _ _ _ _ c _) = c
  {-# INLINE groupsUF #-}
  groupsUF (UnionFind rs _ _ _ _ _ _) = ufGroups rs
  {-# INLINE valueUF #-}
  valueUF x uf@(UnionFind _ _ _ _ vs _ _) = G.unsafeIndex vs (rootUF x uf)
  {-# INLINE diffUF #-}
  diffUF x y uf@(UnionFind _ _ _ ws _ _ _)
    | sameUF x y uf = Just (addW (G.unsafeIndex ws y) (negW (G.unsafeIndex ws x)))
    | otherwise = Nothing
  {-# INLINE membersUF #-}
  membersUF x uf@(UnionFind _ _ nx _ _ _ _) =
    U.iterateN (sizeUF x uf) (U.unsafeIndex nx) x

instance (PrimMonad m) => UFKind (MUnionFind m) where
  type UFRet (MUnionFind m) x = m x
  {-# INLINE rootUF #-}
  rootUF x uf = fst <$> ufFind uf x
  {-# INLINE sameUF #-}
  sameUF x y uf = (==) <$> rootUF x uf <*> rootUF y uf
  {-# INLINE sizeUF #-}
  sizeUF x uf@(MUnionFind par _ _ _ _ _) = do
    r <- rootUF x uf
    negate <$> UM.unsafeRead par r
  {-# INLINE countUF #-}
  countUF (MUnionFind _ _ _ _ cnt _) = UM.unsafeRead cnt 0
  {-# INLINE groupsUF #-}
  groupsUF uf = ufGroups <$> ufRoots uf
  {-# INLINE valueUF #-}
  valueUF x uf@(MUnionFind _ _ _ vals _ _) = rootUF x uf >>= GM.unsafeRead vals
  {-# INLINE diffUF #-}
  diffUF x y uf = do
    (rx, wx) <- ufFind uf x
    (ry, wy) <- ufFind uf y
    pure $ if rx == ry then Just (addW wy (negW wx)) else Nothing
  {-# INLINE membersUF #-}
  membersUF x uf@(MUnionFind _ nxt _ _ _ _) = do
    k <- sizeUF x uf
    U.unfoldrExactNM k (\c -> (,) c <$> UM.unsafeRead nxt c) x

-- ---------------------------------------------------------------------
-- 作る

-- | 重みなし・値なし。
{-# INLINE newUF #-}
newUF :: (PrimMonad m) => Int -> m (MUnionFind m () U.Vector ())
newUF = newWUF

-- | 重みあり・値なし。
{-# INLINE newWUF #-}
newWUF :: (PrimMonad m, WeightOf w) => Int -> m (MUnionFind m w U.Vector ())
newWUF n = newWUFWith (\_ _ -> ()) (U.replicate n ())

-- | 重みなし・値あり。
{-# INLINE newUFWith #-}
newUFWith ::
  (PrimMonad m, G.Vector v a) =>
  -- | @op vx vy@: つないだ成分の値。@vx@ は @x@ 側 ('uniteUF' の第 1 引数の側)、@vy@ は @y@ 側の値
  (a -> a -> a) ->
  -- | @xs@: 各頂点の初めの値 (頂点数はこの長さ)
  v a ->
  -- | 可変版
  m (MUnionFind m () v a)
newUFWith = newWUFWith

-- | 重みあり・値あり。
{-# INLINE newWUFWith #-}
newWUFWith ::
  (PrimMonad m, UFOf w v a) =>
  -- | @op vx vy@: つないだ成分の値。@vx@ は @x@ 側 ('uniteUF' / 'uniteDiffUF' の第 1 引数の側)、
  -- @vy@ は @y@ 側の値
  (a -> a -> a) ->
  -- | @xs@: 各頂点の初めの値 (頂点数はこの長さ)
  v a ->
  -- | 可変版
  m (MUnionFind m w v a)
newWUFWith op xs = do
  let n = G.length xs
  par <- UM.replicate n (-1)
  nxt <- UM.generate n id
  ws <- GM.replicate n zeroW
  vals <- G.thaw xs
  forM_ [0 .. n - 1] $ \i -> GM.unsafeRead vals i >>= \x -> GM.unsafeWrite vals i $! x
  cnt <- UM.replicate 1 n
  pure (MUnionFind par nxt ws vals cnt op)

-- | 辺の並びから不変版を作る。
{-# INLINE buildUF #-}
buildUF ::
  (G.Vector u Int) =>
  -- | @n@: 頂点数
  Int ->
  -- | @g@: 辺 @u v@ (幅 2) の並び。頂点番号の始まりは 'fromOneBased' / 'fromZeroBased' で示す
  ZeroBased (Grid u Int) ->
  -- | 全部つないだ不変版
  UnionFind () U.Vector ()
buildUF n g = createUF $ do
  uf <- newUF n
  forM_ (ufEdges "buildUF" 2 g) $ \(x, y, _) -> uniteUF x y uf
  pure uf

-- | 重みつきの辺の並びから不変版を作る。
{-# INLINE buildWUF #-}
buildWUF ::
  (G.Vector u Int) =>
  -- | @n@: 頂点数
  Int ->
  -- | @g@: @u v d@ (幅 3、x_v - x_u = d) の並び。頂点番号の始まりは 'fromOneBased' / 'fromZeroBased' で示す
  ZeroBased (Grid u Int) ->
  -- | 全部つないだ不変版。矛盾したら 'Nothing'
  Maybe (UnionFind Int U.Vector ())
buildWUF n g = runST $ do
  uf <- newWUF n
  ok <- and <$> mapM (\(x, y, d) -> uniteDiffUF x y d uf) (ufEdges "buildWUF" 3 g)
  if ok then Just <$> ufFreeze G.unsafeFreeze uf else pure Nothing

-- | ST の中で可変版を作って、不変版として取り出す (写さない)。
{-# INLINE createUF #-}
createUF :: (UFOf w v a) => (forall s. ST s (MUnionFind (ST s) w v a)) -> UnionFind w v a
createUF act = runST (act >>= ufFreeze G.unsafeFreeze)

-- | 可変版を写し取る。以後も可変版は使える。
{-# INLINE freezeUF #-}
freezeUF :: (PrimMonad m, UFOf w v a) => MUnionFind m w v a -> m (UnionFind w v a)
freezeUF = ufFreeze G.freeze

-- | 不変版から可変版を作る (写す)。
{-# INLINE thawUF #-}
thawUF :: (PrimMonad m, UFOf w v a) => UnionFind w v a -> m (MUnionFind m w v a)
thawUF (UnionFind rs ss nx ws vs c op) = do
  par <- U.thaw (U.imap (\i r -> if r == i then negate (U.unsafeIndex ss i) else r) rs)
  MUnionFind par <$> U.thaw nx <*> G.thaw ws <*> G.thaw vs <*> UM.replicate 1 c <*> pure op

-- ---------------------------------------------------------------------
-- 可変版だけ

-- | つなぐ。重みありなら差 0 ('zeroW') でつなぐ。
{-# INLINE uniteUF #-}
uniteUF ::
  (PrimMonad m, UFOf w v a) =>
  -- | @x@: 頂点
  Int ->
  -- | @y@: 頂点
  Int ->
  -- | 可変版
  MUnionFind m w v a ->
  -- | 新しくつないだら True (もともと同じ成分なら False)
  m Bool
uniteUF x y uf = (== 2) <$> ufUnite x y zeroW uf

-- | @x_y - x_x = d@ としてつなぐ。
{-# INLINE uniteDiffUF #-}
uniteDiffUF ::
  (PrimMonad m, UFOf w v a) =>
  -- | @x@: 頂点
  Int ->
  -- | @y@: 頂点
  Int ->
  -- | @d@: 重みの差 @x_y - x_x@
  w ->
  -- | 可変版
  MUnionFind m w v a ->
  -- | 矛盾したら False (もともと同じ成分で矛盾しなければ True)
  m Bool
uniteDiffUF x y d uf = (/= 0) <$> ufUnite x y d uf

-- | 成分の値を書き換える。
{-# INLINE modifyValueUF #-}
modifyValueUF ::
  (PrimMonad m, UFOf w v a) =>
  -- | @f v@: 今の値 @v@ から新しい値を作る
  (a -> a) ->
  -- | @x@: 頂点
  Int ->
  -- | 可変版
  MUnionFind m w v a ->
  -- | なし (@x@ を含む成分の値を書き換える)
  m ()
modifyValueUF f x uf@(MUnionFind _ _ _ vals _ _) = do
  r <- rootUF x uf
  v <- GM.unsafeRead vals r
  GM.unsafeWrite vals r $! f v

-- ---------------------------------------------------------------------
-- 中身

-- | 頂点数。
{-# INLINE ufSize #-}
ufSize :: (PrimMonad m) => MUnionFind m w v a -> Int
ufSize (MUnionFind par _ _ _ _ _) = UM.length par

-- | 頂点番号が範囲内か確かめる (範囲外なら 'error')。
ufCheck :: UnionFind w v a -> Int -> ()
ufCheck (UnionFind rs _ _ _ _ _ _) x
  | 0 <= x && x < U.length rs = ()
  | otherwise = error "Atc.UnionFind: 頂点番号が範囲外です"

-- | 根と、根から見た重み (x_x - x_根)。経路を圧縮する。
{-# INLINE ufFind #-}
ufFind :: (PrimMonad m, WeightOf w) => MUnionFind m w v a -> Int -> m (Int, w)
ufFind uf@(MUnionFind par _ ws _ _ _) x0
  | x0 < 0 || ufSize uf <= x0 = error "Atc.UnionFind: 頂点番号が範囲外です"
  | otherwise = go x0
  where
    go x = do
      p <- UM.unsafeRead par x
      if p < 0
        then pure (x, zeroW)
        else do
          (r, wp) <- go p
          wx <- GM.unsafeRead ws x
          if r == p
            then pure (r, wx)
            else do
              let !w = addW wx wp
              UM.unsafeWrite par x r
              GM.unsafeWrite ws x w
              pure (r, w)

-- | 'uniteUF' / 'uniteDiffUF' の本体。0: 矛盾、1: もともと同じ成分、2: 新しくつないだ。
{-# INLINE ufUnite #-}
ufUnite :: (PrimMonad m, UFOf w v a) => Int -> Int -> w -> MUnionFind m w v a -> m Int
ufUnite x y d uf@(MUnionFind par nxt ws vals cnt op) = do
  (rx, wx) <- ufFind uf x
  (ry, wy) <- ufFind uf y
  if rx == ry
    then pure (if addW wy (negW wx) == d then 1 else 0)
    else do
      sx <- negate <$> UM.unsafeRead par rx
      sy <- negate <$> UM.unsafeRead par ry
      vx <- GM.unsafeRead vals rx
      vy <- GM.unsafeRead vals ry
      let !v = op vx vy
          -- x_ry - x_rx
          !w = addW (addW wx d) (negW wy)
          link r c wc = do
            UM.unsafeWrite par c r
            UM.unsafeWrite par r (negate (sx + sy))
            GM.unsafeWrite ws c $! wc
            GM.unsafeWrite vals r v
      if sx >= sy then link rx ry w else link ry rx (negW w)
      -- 2 つの輪の次の頂点を入れ替えると 1 つの輪になる
      nx <- UM.unsafeRead nxt rx
      UM.unsafeRead nxt ry >>= UM.unsafeWrite nxt rx
      UM.unsafeWrite nxt ry nx
      UM.unsafeModify cnt (subtract 1) 0
      pure 2

-- | 全頂点の根。
{-# INLINE ufRoots #-}
ufRoots :: (PrimMonad m, WeightOf w) => MUnionFind m w v a -> m (U.Vector Int)
ufRoots uf = U.generateM (ufSize uf) (fmap fst . ufFind uf)

-- | 可変版から不変版を作る。freeze は写すかどうか (G.freeze / G.unsafeFreeze)。
{-# INLINE ufFreeze #-}
ufFreeze ::
  (PrimMonad m, UFOf w v a) =>
  (forall u b. (G.Vector u b) => G.Mutable u (PrimState m) b -> m (u b)) -> MUnionFind m w v a -> m (UnionFind w v a)
ufFreeze frz uf@(MUnionFind par nxt _ vals cnt op) = do
  let n = ufSize uf
  rw <- V.generateM n (ufFind uf)
  ss <- U.generateM n $ \i -> do
    p <- UM.unsafeRead par i
    pure (if p < 0 then negate p else 0)
  nx <- frz nxt
  vs <- frz vals
  c <- UM.unsafeRead cnt 0
  pure (UnionFind (U.convert (V.map fst rw)) ss nx (G.convert (V.map snd rw)) vs c op)

-- | 根の並びから、成分を最小の頂点の順に、成分の中を昇順に並べる。
ufGroups :: U.Vector Int -> V.Vector (U.Vector Int)
ufGroups rs = runST $ do
  let n = U.length rs
  gid <- UM.replicate n (-1)
  -- k: 次に振る成分の番号
  k <- UM.replicate 1 (0 :: Int)
  forM_ [0 .. n - 1] $ \i -> do
    let r = U.unsafeIndex rs i
    g <- UM.unsafeRead gid r
    when (g < 0) $ UM.unsafeRead k 0 >>= \c -> UM.unsafeWrite gid r c >> UM.unsafeWrite k 0 (c + 1)
  m <- UM.unsafeRead k 0
  sz <- UM.replicate m (0 :: Int)
  forM_ [0 .. n - 1] $ \i -> UM.unsafeRead gid (U.unsafeIndex rs i) >>= UM.unsafeModify sz (+ 1)
  szs <- U.unsafeFreeze sz
  let off = U.prescanl' (+) 0 szs
  pos <- U.thaw off
  out <- UM.unsafeNew n
  forM_ [0 .. n - 1] $ \i -> do
    g <- UM.unsafeRead gid (U.unsafeIndex rs i)
    p <- UM.unsafeRead pos g
    UM.unsafeWrite pos g (p + 1)
    UM.unsafeWrite out p i
  flat <- U.unsafeFreeze out
  pure (V.generate m (\g -> U.unsafeSlice (U.unsafeIndex off g) (U.unsafeIndex szs g) flat))

-- | 辺の並びを (u, v, d) に直す。幅 2 なら d = 0。
ufEdges :: (G.Vector u Int) => String -> Int -> ZeroBased (Grid u Int) -> [(Int, Int, Int)]
ufEdges name w (ZeroBased (Grid gw h d))
  | gw /= w = error ("Atc.UnionFind." ++ name ++ ": 幅は " ++ show w)
  | w == 2 = [(at (2 * i), at (2 * i + 1), 0) | i <- [0 .. h - 1]]
  | otherwise = [(at (3 * i), at (3 * i + 1), at (3 * i + 2)) | i <- [0 .. h - 1]]
  where
    at = G.unsafeIndex d
