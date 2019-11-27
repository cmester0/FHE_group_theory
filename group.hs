module Group where

import System.Random
import PrimeNumbers

-- Finds generator for unit group of order as safe prime
find_generator :: Integer -> Integer -> Integer -> IO Integer
find_generator order prime power =
  randomRIO (1,order-1) >>= \a ->
  let checks = [1..power] >>= \i -> return $ modPow a (prime ^ i) order == 1 in
    if filter (not) checks == []
    then find_generator order prime power
    else return a

inverse order value =
  let (a,b,g) = extended_gcd value order in
  mod a order
