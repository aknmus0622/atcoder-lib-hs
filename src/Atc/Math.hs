module Atc.Math where

gcdAll :: [Int] -> Int
gcdAll = foldr gcd 0

lcmAll :: [Int] -> Int
lcmAll = foldr lcm 1

isPrime :: Int -> Bool
isPrime n
  | n < 2 = False
  | n < 4 = True
  | even n = False
  | otherwise = go 3
  where
    go d
      | d * d > n = True
      | n `mod` d == 0 = False
      | otherwise = go (d + 2)
