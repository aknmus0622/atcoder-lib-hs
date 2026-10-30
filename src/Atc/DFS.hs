{-# LANGUAGE RankNTypes #-}

-- | 再帰で回す DFS を、手続きのまま書くためのモナド。
--
-- 表の持ち方 ('dense' / 'sparse')・値の読み書き ('valueOf' / 'writeValue' / 'modifyValue')・
-- 'liftST' は "Atc.BFS" と共通。モナドも同じもの ('DFS' は 'BFS' の別名)。
-- 違うのはループの回し方で、キューの代わりに Haskell の再帰で潜る。
-- GHC の再帰はヒープに伸びるスタックで回るので、深さ 10^6 でも落ちない。
--
-- > -- グリッドの塗りつぶし
-- > let (_, seen) = runDFS (dense ((0, 0), (h - 1, w - 1))) $ do
-- >       let go p = visitS p () $ forM_ (around4 p) $ \q -> when (ok q) $ void (go q)
-- >       go (0, 0)
-- > isJust (seen (h - 1, w - 1))
--
-- 操作:
--
-- * 'visitS' @k x body@: 未訪問なら値 @x@ を書いて @body@ を実行し 'True'。
--   訪問済みか範囲外なら何もせず 'False'。@body@ の中で子へ再帰する。
--   子の 'visitS' が 'True' を返したあと (子の部分木を抜けたあと) に、子の値を読んで
--   自分の値に足せば木 DP になる。
-- * 'backtrackS': 'visitS' と同じだが、抜けるときに未訪問に戻す。単純パスの全列挙など。
--   値も消えるので、結果は本体の戻り値か 'liftST' の配列で受け取る。
-- * 'onStackS': 今潜っている経路の上にあるか。有向グラフの閉路 (後退辺) の判定に使う。
-- * 'preorderS' / 'postorderS': 'visitS' で入った順 / 抜けた順。
--   抜けた順を逆にすればトポロジカル順、入った順と抜けた順でオイラーツアーが作れる。
--
-- 'runDFS' の中で 'visitQ' / 'whileQ' などのキューの操作は使わない
-- (抜けた順の記録にキューの領域を使っている)。
module Atc.DFS where

import Atc.BFS
import Atc.DP (DPValue (..))
import Control.Monad (when)
import Data.STRef (readSTRef)
import qualified Data.Vector.Unboxed.Mutable as UM

-- | 状態 @s@、キー @k@、表の値 @a@ の DFS で、@r@ を返す計算。中身は 'BFS' と同じ。
type DFS = BFS

-- | DFS を回す。本体の戻り値と、値の表を返す。
{-# INLINE runDFS #-}
runDFS :: (BFSKey k, DPValue a) => Space k -> (forall s. DFS s k a r) -> (r, k -> Maybe a)
runDFS = runBFS

-- キーの状態は 0 = 未訪問, 1 = 潜っている途中, 2 = 抜けた。
-- 入った順は取り出し順の記録 ('orderQ' と同じ)、抜けた順はキューの領域に末尾から積む。

-- 未訪問なら値を書いて body を回し、抜けるときの状態を done にする。
{-# INLINE enterWith #-}
enterWith :: (BFSKey k, DPValue a) => Bool -> k -> a -> DFS s k a () -> DFS s k a Bool
enterWith keep k x body = BFS $ \e -> do
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
          when keep $ pushOrder e i
          runWith body e
          if keep
            then writeFlag e i 2 >> pushBack e i
            else writeFlag e i 0
          pure True

-- | まだ値のないキーなら値を書き、本体を実行して 'True'。訪問済みか範囲外なら 'False'。
-- 本体の中ではこのキーは 'onStackS' が 'True'、抜けたあとは 'False'。
{-# INLINE visitS #-}
visitS :: (BFSKey k, DPValue a) => k -> a -> DFS s k a () -> DFS s k a Bool
visitS = enterWith True

-- | 'visitS' と同じだが、抜けるときに未訪問へ戻す (値も消える)。
-- 別の経路からまた入れるので、単純パスを全部たどれる。入った順・抜けた順には記録しない。
{-# INLINE backtrackS #-}
backtrackS :: (BFSKey k, DPValue a) => k -> a -> DFS s k a () -> DFS s k a Bool
backtrackS = enterWith False

-- | 今潜っている経路の上にあるか ('visitS' / 'backtrackS' の本体の途中か)。
{-# INLINE onStackS #-}
onStackS :: (BFSKey k, DPValue a) => k -> DFS s k a Bool
onStackS k = BFS $ \e -> do
  i <- indexOf False e k
  if i < 0 then pure False else (== 1) <$> readFlag e i

-- | 'visitS' で入ったキーを、入った順に。
{-# INLINE preorderS #-}
preorderS :: (BFSKey k) => DFS s k a [k]
preorderS = orderQ

-- | 'visitS' で抜けたキーを、抜けた順に。逆にすればトポロジカル順。
{-# INLINE postorderS #-}
postorderS :: (BFSKey k) => DFS s k a [k]
postorderS = BFS $ \e -> do
  n <- UM.unsafeRead (envReg e) 1
  buf <- readSTRef (envQue e)
  mapM (\j -> UM.unsafeRead buf j >>= keyOf e) [0 .. n - 1]
