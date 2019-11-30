module Group where

import System.Random
import PrimeNumbers

-- Finds generator for unit group of order as safe prime
find_generator :: Integer -> Integer -> Integer -> Integer -> IO Integer
find_generator order prime q power =
  randomRIO (1,order-1) >>= \a ->
  let checks = [modPow a q order == 1,
                modPow a 2 order == 1] in
    if checks == [False,False]
    then return a
    else find_generator order prime q power

inverse order value =
  let (a,b,g) = extended_gcd value order in
  mod a order
