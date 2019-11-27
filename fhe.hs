{-# LANGUAGE ViewPatterns #-}

import Matrix
import GroupRepresentation

   ----------------------------
   -- Knuth-Bendix procedure --
   ----------------------------

-- Matrix operations (SL2)

commutator :: Integer -> [[Integer]] -> [[Integer]] -> [[Integer]]
commutator pq a b =
  let mm = matrix_mult pq in
  let mi = matrix_inverse pq in
    a `mm` b `mm` (mi a) `mm` (mi b)

and_operation :: Integer -> ([[Integer]],[[Integer]]) -> ([[Integer]],[[Integer]]) -> IO [[Integer]] -> IO ([[Integer]],[[Integer]])
and_operation pq (a1,a2) (b1,b2) sample =
  sample >>= \z -> 
  let mm = matrix_mult pq in
  let mi = matrix_inverse pq in
  return (commutator pq (z `mm` a1 `mm` (mi z)) b1,
          commutator pq (z `mm` a2 `mm` (mi z)) b2)
  
not_operation pq (a1,a2) =
  let mm = matrix_mult pq in
  let mi = matrix_inverse pq in
  (a1, (mi a2) `mm` a1)

-- Token operations:

token_commutator :: Token -> Token -> Token
token_commutator a b =  
  let cmi = (\a -> POW a (-1)) in
    a `MULT` b `MULT` (cmi a) `MULT` (cmi b)

token_and_operation :: (Token,Token) -> (Token,Token) -> IO Token -> IO (Token,Token)
token_and_operation (a1,a2) (b1,b2) sample =
  sample >>= \z -> 
  let cmi = (\a -> POW a (-1)) in
  return (token_commutator (z `MULT` a1 `MULT` (cmi z)) b1,
          token_commutator (z `MULT` a2 `MULT` (cmi z)) b2)

token_not_operation :: (Token,Token) -> (Token,Token)
token_not_operation (a1,a2) =
  let cmi = (\a -> POW a (-1)) in
  (a1, (cmi a2) `MULT` a1)
  
   -----------------------
   -- Lifted operations --
   -----------------------

lift_and :: (Token,Token) -> (Token,Token) -> (Token -> Token) -> IO Token -> IO (Token, Token)
lift_and (a1,a2) (b1,b2) phi sample =
  token_and_operation (phi a1,phi a2) (phi b1,phi b2) sample

lift_not :: (Token,Token) -> (Token -> Token) -> (Token, Token)
lift_not (a1,a2) phi =
  token_not_operation (phi a1,phi a2)
    
   ------------------
   -- Construction --
   ------------------

encode :: Integer -> IO Token -> IO Token -> IO (Token,Token)
encode 0 sample_G sample_K =
  sample_G >>= \a ->
  sample_K >>= \b ->
  return (a, b)
encode 1 sample_G sample_K =
  sample_G >>= \a ->
  return (a,a)
  
decode :: IO (Token,Token) -> (Token -> Bool) -> IO Integer
decode t ker =
  t >>= \(a,b) ->
  return $
  if ker b
  then 0
  else
    if token_eq a b
    then 1
    else -1

generate_group_rep k =
  fq (k+1) >>= \(p1,q1,pq1) -> sl2_fq_rep_sym (p1,q1,pq1) ("u_1","t_1","h2_1","h_1") >>= \sl2_rep_1 ->
  fq (k+1) >>= \(p2,q2,pq2) -> sl2_fq_rep_sym (p2,q2,pq2) ("u_2","t_2","h2_2","h_2") >>= \sl2_rep_2 ->
  return (fst sl2_rep_1, snd sl2_rep_1)

obfuscate_group :: Integer -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k rep =
  random_tietze rep (\rep -> sample_from_rep_2 k rep) k

show_1 pq sl2_rep rev_trace sl2_rep_obfuscated v =
  show sl2_rep ++ "\n" ++
  show sl2_rep_obfuscated ++ "\n" ++
  show (fst v) ++ "\n" ++
  show (snd v) ++ "\n" ++
  (foldr (\a b -> a ++ "\n" ++ b) "" (map show (reverse rev_trace))) ++ 
  show (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated (fst v)) ++ "\n" -- ++f
  -- show (evaluate (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated (fst v)) (fst sl2_rep) pq) ++ "\n" ++
  -- show (evaluate (fst v) (fst sl2_rep_obfuscated) pq) ++ "\n"

main =
  let k = 10 in
  generate_group_rep k >>= \sl2_rep ->
  obfuscate_group k sl2_rep >>= \(sl2_rep_obfuscated,rev_trace) ->
  let phi = (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated) in
  let sample_G = sample_from_rep_2 k sl2_rep in
  let sample_K = sample_from_rep_2 k sl2_rep_obfuscated in
  sample_G >>= \v ->
  putStrLn . show $ (v , phi v)

  -- putStrLn $ show_1 pq sl2_rep rev_trace sl2_rep_obfuscated v
