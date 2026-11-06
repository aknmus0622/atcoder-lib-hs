{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | 入出力: 1 語を読む型 ('Parsable') と、グリッドの読み書き。
module Atc.IO where

import Atc.Grid (CanHold, Grid (..), GridKind, MGrid (..), toRows)
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as C
import Data.Char (isSpace)
import Data.Maybe (fromJust)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as UM
import System.IO (stdout)

-- | 1 語の 'C.ByteString' から読める型。
class Parsable a where
  -- | 1 語を読む。読めなければ 'error'。
  readBS :: C.ByteString -> a

instance Parsable Int where
  readBS = fst . fromJust . C.readInt

instance Parsable Integer where
  readBS = fst . fromJust . C.readInteger

instance Parsable String where
  readBS = C.unpack

-- ---------------------------------------------------------------------
-- グリッドの入出力
--
-- 標準入力を 1 行ずつ読むので、前後で @C.getLine@ を使っていても混ぜてよい。
-- サイズは "Atc.Grid" と同じく @幅 高さ@ の順。入力の @H W@ とは逆なので注意。
--
-- > [h, w] <- map readBS . C.words <$> C.getLine
-- > g <- getIntGridU w h               -- Grid U.Vector Int
-- > putIntGrid (mapGrid (* 2) g)
--
-- 読む型は名前の末尾で選ぶ (末尾は import の別名 @U@ / @V@ / @UM@ / @MV@ と同じ)。
--
-- > getIntGridU  w h   -- Grid U.Vector Int          (不変・unboxed。普通はこれ)
-- > getIntGridV  w h   -- Grid V.Vector Int          (不変・boxed)
-- > getIntGridUM w h   -- MGrid UM.MVector IO Int    (可変・unboxed)
-- > getIntGridMV w h   -- MGrid MV.MVector IO Int    (可変・boxed)
--
-- 'getCharGrid' も同じ (@getCharGridU@ など)。末尾なしの 'getIntGrid' / 'getCharGrid' は
-- 型を使い方から推論する多相版で、決まらないときは型を書く。

-- | 読んだ行を、不変版 (@Grid v@) か可変版 (@MGrid v IO@) に入れる。
class (GridKind k) => GridInput k where
  -- | 読んだ中身からグリッドを作る。
  fromUnboxed ::
    (U.Unbox a, CanHold k a) =>
    -- | @w@: 幅
    Int ->
    -- | @h@: 高さ
    Int ->
    -- | @d@: 行優先に並んだ中身 (長さ @w * h@)
    U.Vector a ->
    -- | 幅 @w@ 高さ @h@ のグリッド
    IO (k a)

instance GridInput (Grid v) where
  fromUnboxed w h = pure . Grid w h . G.convert

instance (m ~ IO) => GridInput (MGrid v m) where
  fromUnboxed w h d = MGrid w h <$> GM.generate (U.length d) (U.unsafeIndex d)

-- | 空白区切りの整数が @w@ 個ずつ並んだ行を @h@ 行読む。
getIntGrid ::
  (GridInput k, CanHold k Int) =>
  -- | @w@: 幅 (1 行の個数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (k Int)
getIntGrid w h = fromUnboxed w h . U.concat =<< mapM (const getRow) [1 .. h]
  where
    getRow = U.unfoldrExactN w (fromJust . C.readInt . C.dropWhile isSpace) <$> C.getLine

-- | @#.#@ のような、区切りなしの文字が @w@ 個ずつ並んだ行を @h@ 行読む。
getCharGrid ::
  (GridInput k, CanHold k Char) =>
  -- | @w@: 幅 (1 行の文字数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (k Char)
getCharGrid w h = fromUnboxed w h . U.concat =<< mapM (const getRow) [1 .. h]
  where
    getRow = (\line -> U.generate w (C.index line)) <$> C.getLine

-- | 'getIntGrid' の型を決めたもの (@U.Vector@)。
getIntGridU ::
  -- | @w@: 幅 (1 行の個数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (Grid U.Vector Int)
getIntGridU = getIntGrid

-- | 'getIntGrid' の型を決めたもの (@V.Vector@)。
getIntGridV ::
  -- | @w@: 幅 (1 行の個数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (Grid V.Vector Int)
getIntGridV = getIntGrid

-- | 'getIntGrid' の型を決めたもの (@UM.MVector@)。
getIntGridUM ::
  -- | @w@: 幅 (1 行の個数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (MGrid UM.MVector IO Int)
getIntGridUM = getIntGrid

-- | 'getIntGrid' の型を決めたもの (@MV.MVector@)。
getIntGridMV ::
  -- | @w@: 幅 (1 行の個数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (MGrid MV.MVector IO Int)
getIntGridMV = getIntGrid

-- | 'getCharGrid' の型を決めたもの (@U.Vector@)。
getCharGridU ::
  -- | @w@: 幅 (1 行の文字数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (Grid U.Vector Char)
getCharGridU = getCharGrid

-- | 'getCharGrid' の型を決めたもの (@V.Vector@)。
getCharGridV ::
  -- | @w@: 幅 (1 行の文字数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (Grid V.Vector Char)
getCharGridV = getCharGrid

-- | 'getCharGrid' の型を決めたもの (@UM.MVector@)。
getCharGridUM ::
  -- | @w@: 幅 (1 行の文字数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (MGrid UM.MVector IO Char)
getCharGridUM = getCharGrid

-- | 'getCharGrid' の型を決めたもの (@MV.MVector@)。
getCharGridMV ::
  -- | @w@: 幅 (1 行の文字数)
  Int ->
  -- | @h@: 高さ (読む行数)
  Int ->
  -- | 読んだグリッド
  IO (MGrid MV.MVector IO Char)
getCharGridMV = getCharGrid

-- | 1 行ずつ、空白区切りで出力する。
putIntGrid :: (G.Vector v Int) => Grid v Int -> IO ()
putIntGrid g = B.hPutBuilder stdout (foldMap row (toRows g :: [[Int]]))
  where
    row xs = mconcat (zipWith (<>) (mempty : repeat (B.char7 ' ')) (map B.intDec xs)) <> B.char7 '\n'

-- | 1 行ずつ、区切りなしで出力する。
putCharGrid :: (G.Vector v Char) => Grid v Char -> IO ()
putCharGrid g = B.hPutBuilder stdout (foldMap (\xs -> B.stringUtf8 xs <> B.char7 '\n') (toRows g :: [String]))
