{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | キューで回す BFS を、手続きのまま書くためのモナド。
--
-- 'runBFS' に「表の持ち方」と本体を渡す。本体では 'visitQ' で積み、
-- 'whileQ' (または 'pullQ') で取り出して回す。結果は本体の戻り値と、
-- 値の表 @k -> Maybe a@ (訪れていないキーは 'Nothing')。
--
-- > -- グリッド迷路の距離
-- > let (_, dist) = runBFS (dense ((0, 0), (h - 1, w - 1))) $ do
-- >       visitQ (0, 0) (0 :: Int)
-- >       whileQ $ \p d -> forM_ (around4 p) $ \q -> when (ok q) $ void (visitQ q (d + 1))
-- > dist (h - 1, w - 1)
--
-- 表の持ち方 ('Space'):
--
-- * 'dense' @(lo, hi)@: 配列。キーは 'Int' / 'Bool' / 'Char' とそのタプル ('BFSKey')。
--   タプルは辞書順 ('Data.Ix.range' と同じ順) に並べる。グリッド・グラフ・状態つきのキー向け。
--   範囲外のキーは無視する ('visitQ' は 'False'、読むと 'Nothing')。境界の条件は要らない。
-- * 'sparse': Map ('Int' キーなら IntMap)。状態空間が広くて配列に載らないとき。
--   キーは上のほか、リスト ('String')・'Integer'・Vector とそのタプル。
--   自作の型は @instance BFSKey T@ を 1 行書けば使える ('Ord' も要る)。
--
-- 値の表は "Atc.DP" と同じく 'Int' / 'Bool' / 'Double' / 'Char' なら U.Vector、ほかは V.Vector。
--
-- 探索の仕方は本体で使う操作で決まる:
--
-- * 普通の BFS: 'visitQ' (初めてのキーだけ値を書いて末尾に積む)。
-- * 書き換えの条件・積む位置を自分で決める: 'updateQ'。今の値 (未訪問なら 'Nothing') から
--   新しい値と積む位置 ('PushFront' / 'PushBack' / 'NoPush') を返す。
--   0-1 BFS (コスト 0 なら先頭、1 なら末尾)、同じ距離どうしの足し込み、
--   距離が同じ中での 2 番目の基準の改善などを 1 回で書ける。
-- * 最短経路の数え上げなど: 'visitQ' が 'False' のとき 'modifyValue' で足し込む。
--   FIFO なので、取り出した時点の値は確定している。
-- * 連結成分: 本体で始点を何度でも積める。'valueOf' で未訪問を確かめて始める。
-- * 早期終了: 'whileQ' の代わりに 'pullQ' で自分で回し、ゴールで戻り値を返す。
--
-- 同じキーは 2 回取り出さない (0-1 BFS などで古くなった要素は読み飛ばす)。
-- 取り出した順は 'orderQ' で取れる (木の BFS 順で葉から DP するときなど)。
--
-- 値は書き込み時に WHNF まで評価する。値の型が決まらないとコンパイルエラーになるので、
-- 数値リテラルだけで始めるときは @visitQ s (0 :: Int)@ のように型を書く。
module Atc.BFS where

import Atc.DP (DPValue (..))
import Control.Monad (when)
import Control.Monad.ST (ST, runST)
import qualified Data.IntMap.Strict as IntMapS
import qualified Data.Map.Strict as MapS
import Data.Maybe (fromMaybe)
import Data.STRef
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import Data.Word (Word8)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

-- ---------------------------------------------------------------------
-- 表の持ち方

-- | BFS の表の持ち方。'dense' か 'sparse' で作る。
--
-- 内部ではキーを 0 始まりの添字にして、キューも表も添字で持つ。
data Space k
  = Dense !(k, k)
  | Sparse (forall s. ST s (SparseKeys s k))

-- Map で振った添字。find は無ければ -1、ensure は無ければ振る。
data SparseKeys s k = SparseKeys
  { sparseFind :: k -> ST s Int,
    sparseEnsure :: k -> ST s Int,
    sparseKeyAt :: Int -> ST s k,
    sparseFreeze :: ST s (k -> Int)
  }

-- | 範囲 @(lo, hi)@ の配列を表にする。
{-# INLINE dense #-}
dense :: (BFSKey k) => (k, k) -> Space k
dense = Dense

-- | 'dense' のキー。範囲の中のキーと @0 .. keySize - 1@ の添字を行き来する。
-- タプルは辞書順 (前の成分が上位)。
--
-- BFS の操作はキーの変換をこのクラスから直接引く (ループの中で関数を呼ばずに済む)。
-- そのため 'sparse' のキーにもインスタンスが要る。メソッドを書かない空のインスタンスは
-- 'sparse' 専用になる ('dense' に渡すと始めた時点でエラー)。リスト ('String')・'Integer'・
-- Vector は用意してある。自作の型なら @instance BFSKey T@ の 1 行を書く。
class BFSKey k where
  keySize :: (k, k) -> Int
  keySize _ = error "dense: このキーの型は sparse 専用 (dense は Int / Bool / Char とそのタプル)"
  keyInRange :: (k, k) -> k -> Bool
  keyInRange _ _ = False
  keyIndex :: (k, k) -> k -> Int
  keyIndex _ _ = -1
  keyAt :: (k, k) -> Int -> k
  keyAt _ _ = error "dense: このキーの型は sparse 専用"

instance BFSKey [a]

instance BFSKey Integer

instance BFSKey (U.Vector a)

instance BFSKey (V.Vector a)

instance BFSKey Char where
  {-# INLINE keySize #-}
  keySize (l, h) = max 0 (fromEnum h - fromEnum l + 1)
  {-# INLINE keyInRange #-}
  keyInRange (l, h) x = l <= x && x <= h
  {-# INLINE keyIndex #-}
  keyIndex (l, _) x = fromEnum x - fromEnum l
  {-# INLINE keyAt #-}
  keyAt (l, _) i = toEnum (fromEnum l + i)

instance BFSKey Int where
  {-# INLINE keySize #-}
  keySize (l, h) = max 0 (h - l + 1)
  {-# INLINE keyInRange #-}
  keyInRange (l, h) x = l <= x && x <= h
  {-# INLINE keyIndex #-}
  keyIndex (l, _) x = x - l
  {-# INLINE keyAt #-}
  keyAt (l, _) i = l + i

instance BFSKey Bool where
  {-# INLINE keySize #-}
  keySize (l, h) = max 0 (fromEnum h - fromEnum l + 1)
  {-# INLINE keyInRange #-}
  keyInRange (l, h) x = l <= x && x <= h
  {-# INLINE keyIndex #-}
  keyIndex (l, _) x = fromEnum x - fromEnum l
  {-# INLINE keyAt #-}
  keyAt (l, _) i = toEnum (fromEnum l + i)

instance (BFSKey a, BFSKey b) => BFSKey (a, b) where
  {-# INLINE keySize #-}
  keySize ((la, lb), (ha, hb)) = keySize (la, ha) * keySize (lb, hb)
  {-# INLINE keyInRange #-}
  keyInRange ((la, lb), (ha, hb)) (a, b) = keyInRange (la, ha) a && keyInRange (lb, hb) b
  {-# INLINE keyIndex #-}
  keyIndex ((la, lb), (ha, hb)) (a, b) = keyIndex (la, ha) a * keySize (lb, hb) + keyIndex (lb, hb) b
  {-# INLINE keyAt #-}
  keyAt ((la, lb), (ha, hb)) i =
    let (q, r) = i `quotRem` keySize (lb, hb) in (keyAt (la, ha) q, keyAt (lb, hb) r)

instance (BFSKey a, BFSKey b, BFSKey c) => BFSKey (a, b, c) where
  {-# INLINE keySize #-}
  keySize ((la, lb, lc), (ha, hb, hc)) = keySize (la, ha) * keySize (lb, hb) * keySize (lc, hc)
  {-# INLINE keyInRange #-}
  keyInRange ((la, lb, lc), (ha, hb, hc)) (a, b, c) =
    keyInRange (la, ha) a && keyInRange (lb, hb) b && keyInRange (lc, hc) c
  {-# INLINE keyIndex #-}
  keyIndex ((la, lb, lc), (ha, hb, hc)) (a, b, c) =
    (keyIndex (la, ha) a * keySize (lb, hb) + keyIndex (lb, hb) b) * keySize (lc, hc) + keyIndex (lc, hc) c
  {-# INLINE keyAt #-}
  keyAt ((la, lb, lc), (ha, hb, hc)) i =
    let (q, r) = i `quotRem` keySize (lc, hc)
        (q', r') = q `quotRem` keySize (lb, hb)
     in (keyAt (la, ha) q', keyAt (lb, hb) r', keyAt (lc, hc) r)

-- | Map を表にする。'Int' キーは IntMap、ほかの 'Ord' は Map。
class SparseKey k where
  sparse :: Space k

instance {-# OVERLAPPING #-} SparseKey Int where
  sparse = Sparse (mapKeys IntMapS.empty IntMapS.lookup IntMapS.insert)

instance {-# OVERLAPPABLE #-} (Ord k) => SparseKey k where
  sparse = Sparse (mapKeys MapS.empty MapS.lookup MapS.insert)

{-# INLINE mapKeys #-}
mapKeys :: t -> (k -> t -> Maybe Int) -> (k -> Int -> t -> t) -> ST s (SparseKeys s k)
mapKeys empty lookupT insertT = do
  ref <- newSTRef empty
  keys <- newGrow
  let ensure k = do
        m <- readSTRef ref
        case lookupT k m of
          Just i -> pure i
          Nothing -> do
            i <- pushGrow keys k
            writeSTRef ref $! insertT k i m
            pure i
  pure
    SparseKeys
      { sparseFind = \k -> fromMaybe (-1) . lookupT k <$> readSTRef ref,
        sparseEnsure = ensure,
        sparseKeyAt = readGrow keys,
        sparseFreeze = (\m k -> fromMaybe (-1) (lookupT k m)) <$> readSTRef ref
      }

-- 伸びる boxed の列 (sparse のキー用)。
data Grow s k = Grow !(STRef s (VM.MVector s k)) !(UM.MVector s Int)

newGrow :: ST s (Grow s k)
newGrow = Grow <$> (VM.unsafeNew 16 >>= newSTRef) <*> UM.replicate 1 0

pushGrow :: Grow s k -> k -> ST s Int
pushGrow (Grow ref cnt) k = do
  buf <- readSTRef ref
  n <- UM.unsafeRead cnt 0
  buf' <-
    if n < VM.length buf
      then pure buf
      else do
        b <- VM.unsafeGrow buf (VM.length buf)
        writeSTRef ref b
        pure b
  VM.unsafeWrite buf' n k
  UM.unsafeWrite cnt 0 (n + 1)
  pure n

readGrow :: Grow s k -> Int -> ST s k
readGrow (Grow ref _) i = readSTRef ref >>= \buf -> VM.unsafeRead buf i

-- ---------------------------------------------------------------------
-- モナド

-- 添字ごとの状態 (0 = 未訪問, 1 = 値あり (キューにいるかも), 2 = 取り出し済み) と値。
-- 値の配列の型は 'DPValue' が値の型から決めるので、ここでは伏せて持ち、
-- 使う側で 'withDPVector' から戻す (ループの中で Vector の辞書を引かずに済む)。
data Arr s = Arr !(UM.MVector s Word8) Any

{-# INLINE castMV #-}
castMV :: (v a -> v a) -> Any -> G.Mutable v s a
castMV _ = unsafeCoerce

data Keys s k = KeysDense !(k, k) | KeysSparse !(SparseKeys s k)

data Env s k a = Env
  { envKeys :: !(Keys s k),
    -- 状態と値 (sparse では伸びる)
    envArr :: !(STRef s (Arr s)),
    -- 両端キュー (リングバッファ) と、取り出した順
    envQue :: !(STRef s (UM.MVector s Int)),
    envOrd :: !(STRef s (UM.MVector s Int)),
    -- 0: キューの先頭, 1: キューの要素数, 2: 取り出した数
    envReg :: !(UM.MVector s Int)
  }

-- | 状態 @s@、キー @k@、表の値 @a@ の BFS で、@r@ を返す計算。
newtype BFS s k a r = BFS (Env s k a -> ST s r)

instance Functor (BFS s k a) where
  {-# INLINE fmap #-}
  fmap f (BFS m) = BFS $ \e -> fmap f (m e)

instance Applicative (BFS s k a) where
  {-# INLINE pure #-}
  pure x = BFS $ \_ -> pure x
  {-# INLINE (<*>) #-}
  BFS mf <*> BFS mx = BFS $ \e -> mf e <*> mx e

instance Monad (BFS s k a) where
  {-# INLINE (>>=) #-}
  BFS m >>= f = BFS $ \e -> m e >>= \x -> runWith (f x) e

-- @Just x <- valueOf k@ のように書ける (外れたらエラー)。
instance MonadFail (BFS s k a) where
  fail = error

{-# INLINE runWith #-}
runWith :: BFS s k a r -> Env s k a -> ST s r
runWith (BFS m) = m

-- | BFS を回す。本体の戻り値と、値の表を返す。
{-# INLINE runBFS #-}
runBFS :: (BFSKey k, DPValue a) => Space k -> (forall s. BFS s k a r) -> (r, k -> Maybe a)
runBFS sp body = runST $ do
  e <- newEnv sp
  r <- runWith body e
  tbl <- freezeEnv e
  pure (r, tbl)

{-# INLINE newEnv #-}
newEnv :: forall s k a. (BFSKey k, DPValue a) => Space k -> ST s (Env s k a)
newEnv sp = do
  (keys, n) <- case sp of
    Dense bnds -> pure (KeysDense bnds, max 1 (keySize bnds))
    Sparse mk -> (\sk -> (KeysSparse sk, 16)) <$> mk
  mv <- withDPVector @a $ \asV -> unsafeCoerce <$> GM.unsafeNew n `asMutOf` asV
  arr <- (`Arr` mv) <$> UM.replicate n 0
  Env keys
    <$> newSTRef arr
    <*> (UM.unsafeNew (n + 1) >>= newSTRef)
    <*> (UM.unsafeNew n >>= newSTRef)
    <*> U.thaw (U.fromListN 3 [0, 0, 0])

{-# INLINE freezeEnv #-}
freezeEnv :: forall s k a. (BFSKey k, DPValue a) => Env s k a -> ST s (k -> Maybe a)
freezeEnv e = withDPVector @a $ \asV -> do
  Arr fl mv <- readSTRef (envArr e)
  flags <- U.unsafeFreeze fl
  vals <- asV <$> G.unsafeFreeze (castMV asV mv)
  find <- case envKeys e of
    KeysDense bnds -> pure $ \k -> if keyInRange bnds k then keyIndex bnds k else -1
    KeysSparse sk -> sparseFreeze sk
  pure $ \k ->
    let i = find k
     in if i >= 0 && U.unsafeIndex flags i /= 0 then Just (G.unsafeIndex vals i) else Nothing

-- 型を合わせるだけ。
{-# INLINE asMutOf #-}
asMutOf :: ST s (G.Mutable v s a) -> (v a -> v a) -> ST s (G.Mutable v s a)
asMutOf m _ = m

-- キーの添字。範囲外か (ins が False で) 未登録なら -1。
-- sparse で新しく振ったときは表を伸ばす。
{-# INLINE indexOf #-}
indexOf :: (BFSKey k, DPValue a) => Bool -> Env s k a -> k -> ST s Int
indexOf ins e k = case envKeys e of
  KeysDense bnds -> pure $! if keyInRange bnds k then keyIndex bnds k else -1
  KeysSparse sk
    | ins -> do
        i <- sparseEnsure sk k
        growArr e (i + 1)
        pure i
    | otherwise -> sparseFind sk k

{-# INLINE keyOf #-}
keyOf :: (BFSKey k) => Env s k a -> Int -> ST s k
keyOf e i = case envKeys e of
  KeysDense bnds -> pure $! keyAt bnds i
  KeysSparse sk -> sparseKeyAt sk i

-- 状態と値を n 以上に伸ばす (増えた状態は 0)。
growArr :: forall s k a. (DPValue a) => Env s k a -> Int -> ST s ()
growArr e n = withDPVector @a $ \asV -> do
  Arr fl mv <- readSTRef (envArr e)
  let cap = UM.length fl
  when (n > cap) $ do
    let cap' = max n (2 * cap)
    fl' <- UM.unsafeGrow fl (cap' - cap)
    UM.set (UM.unsafeSlice cap (cap' - cap) fl') 0
    mv' <- GM.unsafeGrow (castMV asV mv) (cap' - cap)
    writeSTRef (envArr e) (Arr fl' (unsafeCoerce mv'))

-- 状態と値。
{-# INLINE readFlag #-}
readFlag :: Env s k a -> Int -> ST s Word8
readFlag e i = readSTRef (envArr e) >>= \(Arr fl _) -> UM.unsafeRead fl i

{-# INLINE writeFlag #-}
writeFlag :: Env s k a -> Int -> Word8 -> ST s ()
writeFlag e i f = readSTRef (envArr e) >>= \(Arr fl _) -> UM.unsafeWrite fl i f

{-# INLINE readVal #-}
readVal :: forall s k a. (DPValue a) => Env s k a -> Int -> ST s a
readVal e i = withDPVector @a $ \asV -> readSTRef (envArr e) >>= \(Arr _ mv) -> GM.unsafeRead (castMV asV mv) i

{-# INLINE writeVal #-}
writeVal :: forall s k a. (DPValue a) => Env s k a -> Int -> a -> ST s ()
writeVal e i x = withDPVector @a $ \asV -> readSTRef (envArr e) >>= \(Arr _ mv) -> GM.unsafeWrite (castMV asV mv) i $! x

-- | ST の計算をそのまま実行する。自前の MVector (prev など) を読み書きするとき。
{-# INLINE liftST #-}
liftST :: ST s x -> BFS s k a x
liftST m = BFS $ \_ -> m

-- | まだ値のないキーなら値を書いて末尾に積み、'True'。訪問済みか範囲外なら 'False'。
{-# INLINE visitQ #-}
visitQ :: (BFSKey k, DPValue a) => k -> a -> BFS s k a Bool
visitQ k x = BFS $ \e -> do
  i <- indexOf True e k
  if i < 0
    then pure False
    else do
      f <- readFlag e i
      if f /= 0
        then pure False
        else do
          writeFlag e i 1
          writeVal e i x
          pushBack e i
          pure True

-- | 'updateQ' で書いた値をどこに積むか。
data Push
  = -- | 先頭 (0-1 BFS のコスト 0)
    PushFront
  | -- | 末尾
    PushBack
  | -- | 値だけ書き、積まない
    NoPush
  deriving (Eq, Show)

-- | 今の値 (未訪問なら 'Nothing') を渡し、@Just (新しい値, 積む位置)@ なら書いて積む。
-- 'Nothing' なら何もしない。書いたら 'True'。範囲外・取り出し済みのキーは関数を呼ばずに 'False'。
--
-- > -- 0-1 BFS: コスト c (0 か 1) の辺
-- > updateQ q $ \old -> if maybe True (d + c <) old
-- >   then Just (d + c, if c == 0 then PushFront else PushBack) else Nothing
--
-- 既にキューにいるキーをまた積むと 2 回入るが、後の方は取り出すときに読み飛ばす。
-- 未訪問のキーに 'NoPush' で書くと、訪問済みだが取り出されないキーになる ('writeValue' と同じ)。
{-# INLINE updateQ #-}
updateQ :: (BFSKey k, DPValue a) => k -> (Maybe a -> Maybe (a, Push)) -> BFS s k a Bool
updateQ k g = BFS $ \e -> do
  i <- indexOf True e k
  if i < 0
    then pure False
    else do
      f <- readFlag e i
      if f == 2
        then pure False
        else do
          old <- if f == 0 then pure Nothing else Just <$> readVal e i
          case g old of
            Nothing -> pure False
            Just (x, p) -> do
              writeFlag e i 1
              writeVal e i x
              case p of
                PushFront -> pushFront e i
                PushBack -> pushBack e i
                NoPush -> pure ()
              pure True

-- 先頭を取り出して、キーと値を k に渡す。空なら z。
{-# INLINE pullWith #-}
pullWith :: (BFSKey k, DPValue a) => Env s k a -> ST s r -> (k -> a -> ST s r) -> ST s r
pullWith e z k = go
  where
    go = do
      n <- UM.unsafeRead (envReg e) 1
      if n == 0
        then z
        else do
          i <- popFront e
          f <- readFlag e i
          if f == 2
            then go
            else do
              writeFlag e i 2
              pushOrder e i
              x <- readVal e i
              key <- keyOf e i
              k key x

-- | 先頭を取り出し、そのキーと今の値を返す。空なら 'Nothing'。
-- 取り出し済みのキー (0-1 BFS で古くなった要素) は読み飛ばす。
{-# INLINE pullQ #-}
pullQ :: (BFSKey k, DPValue a) => BFS s k a (Maybe (k, a))
pullQ = BFS $ \e -> pullWith e (pure Nothing) (\k x -> pure (Just (k, x)))

-- | キューが空になるまで取り出し、キーと値を本体に渡す。
{-# INLINE whileQ #-}
whileQ :: (BFSKey k, DPValue a) => (k -> a -> BFS s k a ()) -> BFS s k a ()
whileQ f = BFS $ \e ->
  let loop = pullWith e (pure ()) (\k x -> runWith (f k x) e >> loop)
   in loop

-- | キーの今の値。訪れていないか範囲外なら 'Nothing'。
{-# INLINE valueOf #-}
valueOf :: (BFSKey k, DPValue a) => k -> BFS s k a (Maybe a)
valueOf k = BFS $ \e -> do
  i <- indexOf False e k
  if i < 0
    then pure Nothing
    else do
      f <- readFlag e i
      if f == 0 then pure Nothing else Just <$> readVal e i

-- | 値を書く (訪問済みになる)。キューには積まない。範囲外なら何もしない。
{-# INLINE writeValue #-}
writeValue :: (BFSKey k, DPValue a) => k -> a -> BFS s k a ()
writeValue k x = BFS $ \e -> do
  i <- indexOf True e k
  when (i >= 0) $ do
    f <- readFlag e i
    when (f == 0) $ writeFlag e i 1
    writeVal e i x

-- | 値があれば @f@ で書き換える。なければ何もしない。キューには積まない。
{-# INLINE modifyValue #-}
modifyValue :: (BFSKey k, DPValue a) => k -> (a -> a) -> BFS s k a ()
modifyValue k g = BFS $ \e -> do
  i <- indexOf False e k
  when (i >= 0) $ do
    f <- readFlag e i
    when (f /= 0) $ readVal e i >>= writeVal e i . g

-- | これまでに取り出したキーを、取り出した順に。
{-# INLINE orderQ #-}
orderQ :: (BFSKey k) => BFS s k a [k]
orderQ = BFS $ \e -> do
  n <- UM.unsafeRead (envReg e) 2
  buf <- readSTRef (envOrd e)
  mapM (\j -> UM.unsafeRead buf j >>= keyOf e) [0 .. n - 1]

-- ---------------------------------------------------------------------
-- 両端キュー (伸びるリングバッファ) と、取り出した順の記録

-- 満杯なら倍の大きさに移す (先頭を 0 に揃える)。
growQue :: Env s k a -> ST s ()
growQue e = do
  buf <- readSTRef (envQue e)
  hd <- UM.unsafeRead (envReg e) 0
  n <- UM.unsafeRead (envReg e) 1
  let cap = UM.length buf
  buf' <- UM.unsafeNew (2 * cap)
  let copy !j = when (j < n) $ do
        UM.unsafeRead buf ((hd + j) `rem` cap) >>= UM.unsafeWrite buf' j
        copy (j + 1)
  copy 0
  UM.unsafeWrite (envReg e) 0 0
  writeSTRef (envQue e) buf'

{-# INLINE pushBack #-}
pushBack :: Env s k a -> Int -> ST s ()
pushBack e i = do
  n <- UM.unsafeRead (envReg e) 1
  cap <- UM.length <$> readSTRef (envQue e)
  when (n == cap) $ growQue e
  buf <- readSTRef (envQue e)
  hd <- UM.unsafeRead (envReg e) 0
  let t = hd + n
  UM.unsafeWrite buf (if t >= UM.length buf then t - UM.length buf else t) i
  UM.unsafeWrite (envReg e) 1 (n + 1)

{-# INLINE pushFront #-}
pushFront :: Env s k a -> Int -> ST s ()
pushFront e i = do
  n <- UM.unsafeRead (envReg e) 1
  cap <- UM.length <$> readSTRef (envQue e)
  when (n == cap) $ growQue e
  buf <- readSTRef (envQue e)
  hd <- UM.unsafeRead (envReg e) 0
  let hd' = if hd == 0 then UM.length buf - 1 else hd - 1
  UM.unsafeWrite buf hd' i
  UM.unsafeWrite (envReg e) 0 hd'
  UM.unsafeWrite (envReg e) 1 (n + 1)

-- 空でないときだけ呼ぶ。
{-# INLINE popFront #-}
popFront :: Env s k a -> ST s Int
popFront e = do
  buf <- readSTRef (envQue e)
  hd <- UM.unsafeRead (envReg e) 0
  n <- UM.unsafeRead (envReg e) 1
  i <- UM.unsafeRead buf hd
  let hd' = hd + 1
  UM.unsafeWrite (envReg e) 0 (if hd' == UM.length buf then 0 else hd')
  UM.unsafeWrite (envReg e) 1 (n - 1)
  pure i

{-# INLINE pushOrder #-}
pushOrder :: Env s k a -> Int -> ST s ()
pushOrder e i = do
  n <- UM.unsafeRead (envReg e) 2
  buf <- readSTRef (envOrd e)
  buf' <-
    if n < UM.length buf
      then pure buf
      else do
        b <- UM.unsafeGrow buf (UM.length buf)
        writeSTRef (envOrd e) b
        pure b
  UM.unsafeWrite buf' n i
  UM.unsafeWrite (envReg e) 2 (n + 1)
