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

generate_group_rep k s =
  fq (k+1) >>= \(p,q,pq) -> sl2_fq_rep_sym (p,q,pq) s >>= \sl2_rep ->
  return (fst sl2_rep, snd sl2_rep)

obfuscate_group :: Integer -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k rep =
  random_tietze rep (\rep -> sample_from_rep_2 k rep) k

construct_group_sampler k =
  generate_group_rep k ("u_1","t_1","h2_1","h_1") >>= \sl2_rep_1 ->
  generate_group_rep k ("u_2","t_2","h2_2","h_2") >>= \sl2_rep_2 ->
  let sl2_rep = (fst sl2_rep_1 ++ fst sl2_rep_2, snd sl2_rep_1 ++ snd sl2_rep_2) in
  obfuscate_group k sl2_rep >>= \(sl2_rep_obfuscated,rev_trace) ->
  let phi = (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated) in
  let psi = (calculate_value_from_rev_trace (reverse rev_trace) sl2_rep) in
  let sample_G = sample_from_rep_2 k sl2_rep_obfuscated in
  let sample_K = (sample_from_rep_2 k sl2_rep_2) >>= \x -> return $ psi x in
  let pi1 = (replace_name_by_token "u_2" IDENTITY) .
            (replace_name_by_token "t_2" IDENTITY) .
            (replace_name_by_token "h2_2" IDENTITY) .
            (replace_name_by_token "h_2" IDENTITY) in
  let pi1_sim = simplify_token_expression_fix . pi1 . phi in
  let ker = (token_eq IDENTITY) . pi1_sim in
  return ((sample_G,sample_K,sl2_rep_obfuscated),(pi1_sim,ker))

main =
  let k = 10 in
  construct_group_sampler k >>= \((sample_G,sample_K,sl2_rep_obfuscated),(pi1_sim,ker)) ->
  sample_K >>= \k ->
  sample_G >>= \g ->
  putStrLn $
  show k ++ "\n\n\n" ++
  show (pi1_sim k) ++ "\n\n\n" ++
  show (ker k) ++ "\n\n\n\n\n\n" ++
  show g ++ "\n\n\n" ++
  show (pi1_sim g) ++ "\n\n\n" ++
  show (ker g)
  
  
  
  -- putStrLn $ show_1 pq sl2_rep rev_trace sl2_rep_obfuscated v
