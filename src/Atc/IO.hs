{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Atc.IO where

import Atc.Grid (CanHold, Grid (..), GridKind, MGrid (..), toRows)
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as C
import Data.Char (isSpace)
import Data.Maybe (fromJust)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Unboxed as U
import System.IO (stdout)

class Parsable a where
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
-- > g <- getIntGrid w h :: IO (Grid U.Vector Int)
-- > putIntGrid (mapGrid (* 2) g)
--
-- 'getIntGrid' / 'getCharGrid' の返す型は使い方から推論される。決まらないときは型を書く。
--
-- > getIntGrid w h :: IO (Grid U.Vector Int)
-- > getIntGrid w h :: IO (Grid V.Vector Int)
-- > getIntGrid w h :: IO (MGrid UM.MVector IO Int)
-- > getIntGrid w h :: IO (MGrid MV.MVector IO Int)
-- > getCharGrid w h :: IO (Grid U.Vector Char)

-- | 読んだ行を、不変版 (@Grid v@) か可変版 (@MGrid v IO@) に入れる。
class (GridKind k) => GridInput k where
  fromUnboxed :: (U.Unbox a, CanHold k a) => Int -> Int -> U.Vector a -> IO (k a)

instance GridInput (Grid v) where
  fromUnboxed w h = pure . Grid w h . G.convert

instance (m ~ IO) => GridInput (MGrid v m) where
  fromUnboxed w h d = MGrid w h <$> GM.generate (U.length d) (U.unsafeIndex d)

-- | 空白区切りの整数が @w@ 個ずつ並んだ行を @h@ 行読む。
getIntGrid :: (GridInput k, CanHold k Int) => Int -> Int -> IO (k Int)
getIntGrid w h = fromUnboxed w h . U.concat =<< mapM (const getRow) [1 .. h]
  where
    getRow = U.unfoldrExactN w (fromJust . C.readInt . C.dropWhile isSpace) <$> C.getLine

-- | @#.#@ のような、区切りなしの文字が @w@ 個ずつ並んだ行を @h@ 行読む。
getCharGrid :: (GridInput k, CanHold k Char) => Int -> Int -> IO (k Char)
getCharGrid w h = fromUnboxed w h . U.concat =<< mapM (const getRow) [1 .. h]
  where
    getRow = (\line -> U.generate w (C.index line)) <$> C.getLine

-- | 1 行ずつ、空白区切りで出力する。
putIntGrid :: (G.Vector v Int) => Grid v Int -> IO ()
putIntGrid g = B.hPutBuilder stdout (foldMap row (toRows g :: [[Int]]))
  where
    row xs = mconcat (zipWith (<>) (mempty : repeat (B.char7 ' ')) (map B.intDec xs)) <> B.char7 '\n'

-- | 1 行ずつ、区切りなしで出力する。
putCharGrid :: (G.Vector v Char) => Grid v Char -> IO ()
putCharGrid g = B.hPutBuilder stdout (foldMap (\xs -> B.stringUtf8 xs <> B.char7 '\n') (toRows g :: [String]))
