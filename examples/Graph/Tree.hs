-- | "Atc.Graph.Tree" を使った木の問い合わせ。
--
-- 木は無向グラフで作る ('undirectedGraph')。頂点は 0 始まり。
module Graph.Tree where

import Atc
import Control.Monad (replicateM_)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | 木を読む (辺は @u v@ で n - 1 行、1 始まり)。
readTree :: IO AtcGraph
readTree = do
  [n] <- ints
  es <- getIntGrid 2 (n - 1) :: IO (Grid U.Vector Int)
  pure (undirectedGraph (fromOneBased es))

-- | 2 頂点の距離のクエリ: 'buildLCA' で表を作って 'distanceLCA'。
distances :: IO ()
distances = do
  g <- readTree
  let t = buildLCA g 0
  [q] <- ints
  replicateM_ q $ do
    qu <- ints
    case qu of
      [u, v] -> print (distanceLCA (u - 1) (v - 1) t)
      _ -> error "query"

-- | 最小共通祖先と、k 個上の祖先。根は頂点 0 (入力の 1)。
ancestors :: IO ()
ancestors = do
  g <- readTree
  let t = buildLCA g 0
  [u, v, k] <- ints
  print (lcaOf (u - 1) (v - 1) t + 1)
  print (ancestorLCA k (u - 1) t + 1) -- 根を越えれば 0 (-1 + 1)
  print (map (+ 1) (pathLCA (u - 1) (v - 1) t)) -- u から v への道

-- | 全方位木 DP: 各頂点から最も遠い頂点までの距離 (辺 1 本を 1 とする)。
--
-- 部分木の値は「その頂点から部分木の中で最も遠い距離」、子から集める値はその最大。
-- 子 c の値を親から見ると 1 遠い (@d + w@)。
farthest :: IO ()
farthest = do
  g <- readTree
  let far = rerootDP max 0 (\_ _ w d -> d + w) (\_ a -> a) g
  print (V.toList far)

-- | 全方位木 DP: 各頂点から全頂点への距離の和。
--
-- 部分木の値は (距離の和, 頂点数)。親から見ると、部分木の全頂点が w ずつ遠い。
-- 頂点数を足すのは @finish@ (自分の分の 1)。
sumOfDistances :: IO ()
sumOfDistances = do
  g <- readTree
  let res = rerootDP add (0, 0) (\_ _ w (s, c) -> (s + w * c, c)) (\_ (s, c) -> (s, c + 1)) g
      add (s1, c1) (s2, c2) = (s1 + s2, c1 + c2 :: Int)
  print (V.toList (V.map fst res))
