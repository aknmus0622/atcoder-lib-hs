{-# LANGUAGE BangPatterns #-}

-- | ダブリングの表: 同じ遷移を 2^i 回くり返した結果を前もって持つ。
--
-- 状態は @0 .. n - 1@ の番号で、遷移 @next@ と、その遷移の重み @w@ を渡す。
-- @i@ 段目は「2^i 回進んだ先」と「その間の重みの合成」で、前の段から
--
-- > next[i + 1][v] = next[i][next[i][v]]
-- > w[i + 1][v]    = w[i][v] <> w[i][next[i][v]]
--
-- と作る。表は O(n log K)、1 回の問い合わせは O(log K)。
--
-- == 使える条件
--
-- * 状態が有限で、番号を付けられる。
-- * 各状態の行き先が 1 つに決まる。行き先のない状態があるなら、自己ループする
--   番兵の状態を足す。
-- * 遷移と重みが回数によらず、状態だけで決まる。
-- * 重みの合成が結合的。可換でなくてよく (経路の順に合成する)、逆元も要らない。
--
-- 状態を 1 つにすれば、ただの累乗 @a ^ K@ になる。
--
-- > -- 頂点 v から k 回進んだ先と、経路の重みの和
-- > let t = buildJT (+) (10 ^ 12) next weight
-- > foldJT (+) 0 t v k
-- >
-- > -- 重みが要らないときは ()
-- > let t = buildJT (\_ _ -> ()) maxK next (U.replicate n ())
-- > jumpJT t v k
--
-- 重みの和は 'Int' を超えうるので、K と重みの大きさに気をつける。
-- 使わない上の段は作られない。
module Atc.JumpTable where

import Data.Bits (countLeadingZeros, finiteBitSize, shiftL, shiftR, testBit)
import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Unboxed as U

-- | 各段の @(2 ^ i 回進んだ先, その間の重みの合成)@。
newtype JumpTable v w = JumpTable (V.Vector (U.Vector Int, v w))

-- | @buildJT merge maxK next w@: @k <= maxK@ の問い合わせに使える表を作る。O(n log maxK)。
--
-- @w ! v@ は @v@ から @next ! v@ へ進むときの重み。
-- @next@ の値が範囲外か、@next@ と @w@ の長さが違えば 'error'。
{-# INLINE buildJT #-}
buildJT :: (G.Vector v w) => (w -> w -> w) -> Int -> U.Vector Int -> v w -> JumpTable v w
buildJT merge maxK next w
  | maxK < 0 = error "buildJT: maxK が負"
  | G.length w /= n = error "buildJT: next と重みの長さが違う"
  | U.any (\u -> u < 0 || u >= n) next = error "buildJT: 行き先が範囲外"
  | otherwise = JumpTable (V.iterateN levels double (next, w))
  where
    n = U.length next
    levels = finiteBitSize maxK - countLeadingZeros maxK
    double (nx, wt) =
      ( U.backpermute nx nx
      , G.generate n (\v -> merge (G.unsafeIndex wt v) (G.unsafeIndex wt (U.unsafeIndex nx v)))
      )

-- 表で扱える k か確かめる。
checkSteps :: String -> V.Vector a -> Int -> Int
checkSteps name rows k
  | k < 0 || (k `shiftR` V.length rows) /= 0 = error (name ++ ": k が範囲外: " ++ show k)
  | otherwise = k

-- | 状態 @v@ から @k@ 回進んだ先。O(log k)。@k@ が表の範囲を超えると 'error'。
jumpJT :: JumpTable v w -> Int -> Int -> Int
jumpJT (JumpTable rows) v0 k0 = go 0 v0
  where
    k = checkSteps "jumpJT" rows k0
    go !i !v
      | i >= V.length rows = v
      | testBit k i = go (i + 1) (fst (V.unsafeIndex rows i) U.! v)
      | otherwise = go (i + 1) v

-- | @foldJT op z t v k@: @v@ から @k@ 回進みながら、経路の順に重みを @z@ へ畳み込む。
-- @(行き先, 結果)@ を返す。O(log k) (@op@ の分を除く)。
--
-- @k = 0@ なら @(v, z)@。@op@ は重みそのものの合成でなくてもよく、
-- @z@ をベクトル、重みを行列にすれば行列どうしの積なしで掛けられる。
{-# INLINE foldJT #-}
foldJT :: (G.Vector v w) => (b -> w -> b) -> b -> JumpTable v w -> Int -> Int -> (Int, b)
foldJT op z (JumpTable rows) v0 k0 = go 0 v0 z
  where
    k = checkSteps "foldJT" rows k0
    go !i !v !b
      | i >= V.length rows = (v, b)
      | testBit k i =
          let (nx, wt) = V.unsafeIndex rows i
           in go (i + 1) (nx U.! v) (op b (wt G.! v))
      | otherwise = go (i + 1) v b

-- | @climbJT op z ok t v@: @ok@ を満たしたまま進める最大の回数を求める。
-- @(回数, 行き先, 結果)@ を返す。O(log maxK)。
--
-- @ok u b@ は「行き先が @u@、畳み込んだ結果が @b@ のところまで進んでよいか」。
-- 一度偽になったら、それ以上進んでも真に戻らないこと。0 回は調べずに進めるものとする。
-- 回数の上限は表の段数で決まる @2 ^ 段数 - 1@。
{-# INLINE climbJT #-}
climbJT :: (G.Vector v w) => (b -> w -> b) -> b -> (Int -> b -> Bool) -> JumpTable v w -> Int -> (Int, Int, b)
climbJT op z ok (JumpTable rows) v0 = go (V.length rows - 1) 0 v0 z
  where
    go !i !k !v !b
      | i < 0 = (k, v, b)
      | ok u b' = go (i - 1) (k + (1 `shiftL` i)) u b'
      | otherwise = go (i - 1) k v b
      where
        (nx, wt) = V.unsafeIndex rows i
        u = nx U.! v
        b' = op b (wt G.! v)
