-- | "Atc.UnionFind" を使った解答。
--
-- 頂点は 0 始まり。可変版 ('MUnionFind') でつなぎ、不変版 ('UnionFind') は
-- 作ってしまえば問い合わせが O(1)。
module UnionFind where

import Atc
import Control.Monad (forM, forM_, void)
import Control.Monad.ST (runST)
import Data.Bits (Xor (..))
import Data.Bool (bool)
import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Unboxed as U
import Input (ints)

-- | つないで、同じ成分か答える (ATC001 B)。
--
-- 1 行目が @n q@、続く @q@ 行が @0 a b@ (つなぐ) か @1 a b@ (同じ成分か)。
-- 'uniteUF' の返り値は「新しくつないだか」なので、要らなければ 'void'。
connectivity :: IO ()
connectivity = do
  [n, q] <- ints
  uf <- newUF n
  forM_ [1 .. q] $ \_ -> do
    [t, a, b] <- ints
    if t == 0
      then void (uniteUF a b uf)
      else sameUF a b uf >>= putStrLn . bool "No" "Yes"

-- | 成分の数と、一番大きい成分の頂点数。
--
-- 'countUF' が成分の数、'sizeUF' が「その頂点を含む成分」の頂点数。
-- 代表 1 つずつを見たいなら 'rootUF' で根を取って重複を除く。
sizes :: IO ()
sizes = do
  [n, m] <- ints
  uf <- newUF n
  forM_ [1 .. m] $ \_ -> do
    [a, b] <- ints
    void (uniteUF (a - 1) (b - 1) uf)
  countUF uf >>= print
  biggest <- maximum <$> forM [0 .. n - 1] (`sizeUF` uf)
  print biggest
  -- 'rootUF' は成分の代表。どの頂点が代表になるかは決め打ちできないので、
  -- 「同じ成分か」は 'sameUF'、「成分の数」は 'countUF' を使う。
  rootUF 0 uf >>= print

-- | 成分ごとの頂点を並べて出す。
--
-- 'groupsUF' は成分を「最小の頂点の順」に、成分の中は昇順に並べる。O(n)。
-- 1 つの成分だけなら 'membersUF' が O(成分の大きさ) で済むが、
-- 並び順は昇順とは限らない。
groups :: IO ()
groups = do
  [n, m] <- ints
  uf <- newUF n
  forM_ [1 .. m] $ \_ -> do
    [a, b] <- ints
    void (uniteUF (a - 1) (b - 1) uf)
  gs <- groupsUF uf
  V.forM_ gs $ \g -> putStrLn (unwords (map show (U.toList g)))
  members <- membersUF 0 uf
  print (U.toList (U.modify Intro.sort members))

-- | 重みつき: @x_r - x_l = d@ の制約がすべて成り立つか (ABC087 D)。
--
-- 'uniteDiffUF' は矛盾したときだけ False を返すので、全部の and が答え。
-- 重みの型は @d@ が 'Int' なので決まる。
consistent :: IO ()
consistent = do
  [n, m] <- ints
  uf <- newWUF n
  oks <- forM [1 .. m] $ \_ -> do
    [l, r, d] <- ints
    uniteDiffUF (l - 1) (r - 1) d uf
  putStrLn (if and oks then "Yes" else "No")

-- | 重みつき: 2 頂点の差を答える。
--
-- 'diffUF' は @x_y - x_x@ を返す。別の成分なら 'Nothing'。
differences :: IO ()
differences = do
  [n, m, q] <- ints
  uf <- newWUF n
  forM_ [1 .. m] $ \_ -> do
    [l, r, d] <- ints
    void (uniteDiffUF (l - 1) (r - 1) d uf)
  forM_ [1 .. q] $ \_ -> do
    [x, y] <- ints
    d <- diffUF (x - 1) (y - 1) uf
    putStrLn (maybe "?" show (d :: Maybe Int))

-- | 重みを XOR で取る: 偶奇の制約 (二部グラフ判定の言い換え)。
--
-- 重みは 'UFWeight' のインスタンスなら何でもよい。@Xor a@ は差を XOR で取るので
-- 「u と v の偶奇が違う」を @Xor 1@ で書ける。
parity :: IO ()
parity = do
  [n, m] <- ints
  uf <- newWUF n
  oks <- forM [1 .. m] $ \_ -> do
    [u, v] <- ints
    uniteDiffUF (u - 1) (v - 1) (Xor (1 :: Int)) uf
  putStrLn (if and oks then "Yes" else "No")
  d <- diffUF 0 1 uf
  print (getXor <$> d)

-- | 成分ごとに値を持たせる: 成分の最大値を答える。
--
-- 'newUFWith' には「つないだときに値をまとめる関数」と頂点ごとの初期値を渡す。
-- @max@ でまとめれば成分の最大値、@(+)@ なら合計。'modifyValueUF' で後から書き換える。
values :: IO ()
values = do
  [n, m, q] <- ints
  as <- ints
  uf <- newUFWith max (U.fromList as)
  forM_ [1 .. m] $ \_ -> do
    [a, b] <- ints
    void (uniteUF (a - 1) (b - 1) uf)
  forM_ [1 .. q] $ \_ -> do
    [t, x] <- ints
    if t == 0
      then valueUF (x - 1) uf >>= print
      else modifyValueUF (* 2) (x - 1) uf

-- | 重みと値の両方: 'newWUFWith'。
--
-- 値の Vector は渡したものの種類がそのまま使われる。@V.Vector [Int]@ を渡せば
-- 「成分に属する頂点のリスト」のような値も持てる。
bothWeightAndValue :: IO ()
bothWeightAndValue = do
  [n, m] <- ints
  uf <- newWUFWith (<>) (V.generate n pure)
  forM_ [1 .. m] $ \_ -> do
    [u, v, d] <- ints
    void (uniteDiffUF (u - 1) (v - 1) d uf)
  vs <- valueUF 0 uf
  print (vs :: [Int])

-- | 辺をまとめて読んで 'buildUF' で一息に作る。
--
-- 幅 2 のグリッドで 1 始まりの辺を受け取る ("Atc.Graph" と同じ形)。
-- 不変版なので、作ったあとは @m@ に包まれず、そのまま値として読める。
fromEdges :: IO ()
fromEdges = do
  [n, m] <- ints
  es <- getIntGrid 2 m
  let uf = buildUF n es
  putStrLn (unwords [show (sizeUF v uf) | v <- [0 .. n - 1]])
  print (countUF uf)

-- | 重みつきをまとめて作る: 'buildWUF' は幅 3 (@u v d@)。
--
-- 矛盾していたら 'Nothing' が返るので、判定もこれで済む。
fromWeightedEdges :: IO ()
fromWeightedEdges = do
  [n, m] <- ints
  es <- getIntGrid 3 m
  case buildWUF n es of
    Nothing -> putStrLn "No"
    Just uf -> print (diffUF 0 (n - 1) uf)

-- | 'ST' の中で組み立てて不変版として取り出す: 'createUF' は写さない。
--
-- 'freezeUF' は写し取る (元の可変版もその後使える)。写す必要がなければ
-- 'createUF' のほうが速い。
buildInST :: Int -> [(Int, Int)] -> UnionFind () U.Vector ()
buildInST n es = createUF $ do
  uf <- newUF n
  forM_ es $ \(a, b) -> void (uniteUF a b uf)
  pure uf

-- | 可変版と不変版を行き来する: 'freezeUF' と 'thawUF'。
--
-- 「ここまでの状態を保存して、続きもつなぐ」ときに使う。
snapshot :: IO ()
snapshot = do
  [n, m] <- ints
  uf <- newUF n
  forM_ [1 .. m] $ \_ -> do
    [a, b] <- ints
    void (uniteUF (a - 1) (b - 1) uf)
  frozen <- freezeUF uf
  print (countUF frozen)
  void (uniteUF 0 (n - 1) uf) -- 元の可変版はそのまま使える
  countUF uf >>= print
  again <- thawUF frozen
  countUF again >>= print

-- | 純粋な関数の中で使う: 'runST' に閉じ込める。
--
-- 'IO' が要らない計算なら 'ST' で書けば、関数として呼べる。
componentCount :: Int -> [(Int, Int)] -> Int
componentCount n es = runST $ do
  uf <- newUF n
  forM_ es $ \(a, b) -> void (uniteUF a b uf)
  countUF uf

-- | 重みの型を自分で作る: 'UFWeight' のインスタンスにする。
--
-- 差が取れる (可換群である) ことだけが条件。'zeroW' が単位元、'addW' が足し算、
-- 'negW' が符号反転。@Int@ の mod 3 で「3 種類のじゃんけんの関係」を持たせる例。
newtype Mod3 = Mod3 Int
  deriving (Eq, Show)

instance UFWeight Mod3 where
  zeroW = Mod3 0
  addW (Mod3 a) (Mod3 b) = Mod3 ((a + b) `mod` 3)
  negW (Mod3 a) = Mod3 ((3 - a) `mod` 3)

-- | 作った重みをそのまま使う。
--
-- 重みの置き場所は型から選ばれる ('WStore': 'Int' と 'Double' は U.Vector、
-- ほかは V.Vector)。'Mod3' は V.Vector に入る。
customWeight :: IO ()
customWeight = do
  [n, m] <- ints
  uf <- newWUF n
  oks <- forM [1 .. m] $ \_ -> do
    [u, v, d] <- ints
    uniteDiffUF (u - 1) (v - 1) (Mod3 d) uf
  putStrLn (if and oks then "Yes" else "No")
  diffUF 0 1 uf >>= print

-- | 制約を型で書く: 'UFOf' は「重み @w@ と値 @v a@ の組で使える」。
--
-- 共通関数の制約はこれ ('WeightOf' は重みだけの版)。自分で補助関数を
-- 書くときは、この制約を付けて不変版・可変版の両方に使えるようにする。
biggestComponent :: (UFOf w v a) => Int -> UnionFind w v a -> Int
biggestComponent n uf = maximum [sizeUF v uf | v <- [0 .. n - 1]]
