module PrimeNumbers where

import System.Random

   --------------------------
   -- Generate Large prime --
   --------------------------

-- Returns a random k-1 bit prime
large_prime :: Integer -> IO Integer
large_prime k =
  randomRIO (2 ^ (k-2), 2 ^ (k-1)) >>= \rr ->
  let r = 2 * rr + 1 in
    is_prime r >>= \b ->
    if b
    then return r
    else large_prime k

modPow :: Integer -> Integer -> Integer -> Integer
modPow a b n =
  if b == 1
  then a
  else
    if mod b 2 == 0
    then
      let cal = modPow a (div b 2) n in
        mod (cal * cal) n
    else
      let cal = (modPow a (div (b-1) 2) n) in
      mod (cal * cal * a) n

miller_rabin_sub_test :: Bool -> Integer -> Integer -> Integer -> Integer -> (Bool, Integer)
miller_rabin_sub_test False _ y _ _ = (True, y)
miller_rabin_sub_test True j y s n =
  let y' = modPow y 2 n in
    if y' == 1
    then (False, y')
    else
      let j' = j + 1 in
        miller_rabin_sub_test ((j' <= s - 1) && (y' /= n - 1)) j' y' s n

miller_rabin_test :: Integer -> Integer -> Integer -> Integer -> IO Bool
miller_rabin_test n r s 0 = return True
miller_rabin_test n r s i =
  randomRIO (2, n - 1) >>= \a -> 
  let y = modPow a r n in
    if (y /= 1) && (y /= (n - 1))
    then
      let j = 1 in
        let (bb, y') = miller_rabin_sub_test ((j <= s-1) && (y /= n - 1)) 1 y s n in
          if bb
          then
            if (y' /= (n - 1))
            then return False
            else miller_rabin_test n r s (i-1)
          else return False
    else
      miller_rabin_test n r s (i-1)
  
rest :: Integer -> Integer -> (Integer,Integer)
rest n d =
  if mod n d == 0
  then
    let (a,b) = rest (div n d) d in
      (a,b+1)
  else
    (n,0)

miller_rabin :: Integer -> Integer -> IO Bool
miller_rabin n t =
  let (r,s) = rest (n-1) 2 in
    miller_rabin_test n r s t
    
is_prime :: Integer -> IO Bool
is_prime p =
  miller_rabin p 1 -- security param, t = 10

-- Extended euclidian algorithm
extended_gcd :: Integer -> Integer -> (Integer, Integer, Integer)
extended_gcd a 0 = (1,0,a)
extended_gcd a b =
  let (q,r) = a `quotRem` b in
    let (s,t,g) = extended_gcd b r in
      (t,s-q * t, g)
