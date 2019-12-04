module FHE where

import PrimeNumbers
import Group

import Matrix
import GroupRepresentation
import Data.Maybe

   ------------------------------
   -- Logic operations to lift --
   ------------------------------

token_commutator :: Token -> Token -> Token
token_commutator a b =  
  let cmi = (\x -> POW x (-1)) in
    a `MULT` b `MULT` (cmi a) `MULT` (cmi b)

token_and_operation :: IO Token -> (Token,Token) -> (Token,Token) -> IO (Token,Token)
token_and_operation sample (a1,a2) (b1,b2) =
  sample >>= \z ->
  let cmi = (\a -> POW a (-1)) in
  return (token_commutator (z `MULT` a1 `MULT` (cmi z)) b1,
          token_commutator (z `MULT` a2 `MULT` (cmi z)) b2)

token_not_operation :: (Token,Token) -> (Token,Token)
token_not_operation (a1,a2) =
  let cmi = (\a -> POW a (-1)) in
  ((a1 `POW` (-1)) `MULT` a2, a2)

   ---------------------------
   -- Encoding and Decoding --
   ---------------------------

encode :: IO Token -> IO Token -> Integer -> IO (Token,Token)
encode sample_G sample_K 0 =
  sample_G >>= \ct ->
  sample_K >>= \h ->
  return (h, ct)
encode sample_G sample_K 1 =
  sample_G >>= \ct ->
  sample_K >>= \h ->
  return (MULT ct h, ct)
  
decode :: (Token -> Bool) -> (Token -> Maybe [[Integer]]) -> (Token,Token) -> Maybe Integer
decode ker pi (h,t) =
  if ker h
  then Just 0
  else
    if (pi h) == (pi t)
    then Just 1
    else Nothing

   -------------------
   -- Group sampler --
   -------------------

generate_group_rep k s =
  fq (k+1) >>= \(pq,q) -> sl2_fq_rep_sym (pq,1,pq) s >>= \(sl2_rep,matri) ->
  return (sl2_rep,matri,pq)

obfuscate_group :: Integer -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k rep =
  random_tietze rep (\rep -> sample_from_rep_2 k rep) k

construct_group_sampler :: Integer -> IO ((([Token],[Token]), Integer -> IO (Token,Token)), ((Token,Token) -> (Token,Token) -> IO (Token,Token), (Token,Token) -> (Token,Token)), (Token -> Bool, (Token,Token) -> Maybe Integer))
construct_group_sampler k =
  generate_group_rep k ("u_1","t_1","h2_1","h_1") >>= \(sl2_rep_1,matri1,pq1) ->
  generate_group_rep k ("u_2","t_2","h2_2","h_2") >>= \(sl2_rep_2,matri2,pq2) ->
  let sl2_rep = (fst sl2_rep_1 ++ fst sl2_rep_2, snd sl2_rep_1 ++ snd sl2_rep_2) in
  let k2 = div k 20 in
  obfuscate_group k2 sl2_rep >>= \(sl2_rep_obfuscated,rev_trace) ->
  let phi = (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated) in
  let psi = (calculate_value_from_trace (reverse rev_trace) sl2_rep) in
  let sample_G = sample_from_rep_2 k sl2_rep_obfuscated in
  let sample_K = sample_from_rep_2 k sl2_rep_2 >>= return . psi in
  let pi1 = (replace_name_by_token "u_2" IDENTITY) .
            (replace_name_by_token "t_2" IDENTITY) .
            (replace_name_by_token "h2_2" IDENTITY) .
            (replace_name_by_token "h_2" IDENTITY) in
  let pi1_sim = pi1 . phi in
  let ker_aux = evaluate (zip [NAME "u_1",NAME "t_1",NAME "h2_1",NAME "h_1"] matri1) pq1 . pi1_sim in
  let ker = (maybe False (\a -> a == identity)) . ker_aux in  -- TODO: REMOVE matrix
  let pi2 = (replace_name_by_token "u_1" IDENTITY) .
            (replace_name_by_token "t_1" IDENTITY) .
            (replace_name_by_token "h2_1" IDENTITY) .
            (replace_name_by_token "h_1" IDENTITY) in
  let pi2_sim = pi2 . phi in
  let and_op = (token_and_operation sample_G) in
  let not_op = token_not_operation in
  let enc = (encode sample_G sample_K) in
  let dec = (decode ker ker_aux) in
  return ((sl2_rep_obfuscated,enc),(and_op,not_op),(ker,dec))
  
  ------------
  --- TESTS --
  ------------

testEquationSolver =
  putStrLn $
  let val = MULT (NAME "c") (MULT (NAME "a") (MULT (POW (NAME "a") (-2)) (NAME "b"))) in
  "Pure: " ++ show val ++ "\n" ++
  "Left: " ++ show (normal_form_left val) ++ "\n" ++
  "Right: " ++ show (normal_form_right val) ++ "\n" ++
  "RemLeft: " ++ show (remove_left "a" (normal_form_left val)) ++ "\n" ++
  "RemRight: " ++ show (remove_right "a" (normal_form_right val)) ++ "\n" ++
  "Rem: " ++ show (remove_right "a" (normal_form_right (remove_left "a" (normal_form_left val)))) ++ "\n" ++
  "Pure Col: " ++ show (collapse val) ++ "\n" ++
  "Rem Col: " ++ show (collapse (remove_right "a" (normal_form_right (remove_left "a" (normal_form_left val))))) ++ "\n" ++
  "Rem Col Col: " ++ show (collapse (collapse (remove_right "a" (normal_form_right (remove_left "a" (normal_form_left val)))))) ++ "\n" ++
  "Rem Col Col: " ++ show (reduced "a" (collapse (collapse (remove_right "a" (normal_form_right (remove_left "a" (normal_form_left val))))))) ++ "\n" ++
  "Solveable: " ++ show (solvable "a" val) ++ "\n" ++
  "Solution: " ++ show (solve_for_token "a" val) ++ "\n" ++
  "Find generator: " ++ show (find_solution_for_generator "a" [val])
    
testEncodeZeroAndOne =
  let k = 4 in
  construct_group_sampler k >>= \((sl2_rep_obfuscated,enc),(and_op,not_op),(ker,dec)) ->
  enc 0 >>= \k ->
  enc 1 >>= \g ->
  putStrLn $
  show (ker (snd k)) ++ " " ++ show (ker (snd g))

testEncodeAnd =
  let k = 4 in
  construct_group_sampler k >>= \((sl2_rep_obfuscated,enc),(and_op,not_op),(ker,dec)) ->
  (enc 1) >>= \a ->
  (enc 1) >>= \b ->
  (enc 0) >>= \c ->
  (enc 1) >>= \d ->    
  (enc 0) >>= \e ->
  (enc 0) >>= \f ->
  and_op a b >>= \ab ->
  and_op c d >>= \cd ->
  and_op e f >>= \ef ->
  putStrLn $
  show (dec ab) ++ "\n" ++
  show (dec cd) ++ "\n" ++
  show (dec ef) ++ "\n"

testEncodeNot =
  let k = 5 in
  construct_group_sampler k >>= \((sl2_rep_obfuscated,enc),(and_op,not_op),(ker,dec)) ->
  (enc 1) >>= \(aa1,aa2) ->
  (enc 0) >>= \(ab1,ab2) ->
  let (a1,a2) = not_op (aa1,aa2) in
  let (b1,b2) = not_op (ab1,ab2) in
  putStrLn $
  
  show (dec (aa1,aa2)) ++ "\n" ++
  show (dec (a1,a2)) ++ "\n\n" ++
  
  show (dec (ab1,ab2)) ++ "\n" ++
  show (dec (b1,b2)) ++ "\n---"
