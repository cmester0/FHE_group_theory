{-# LANGUAGE ViewPatterns #-}

import Matrix
import GroupRepresentation
import Data.Maybe

   ------------------------------
   -- Logic operations to lift --
   ------------------------------

token_commutator :: Token -> Token -> Token
token_commutator a b =  
  let cmi = (\a -> POW a (-1)) in
    a `MULT` b `MULT` (cmi a) `MULT` (cmi b)

token_and_operation :: IO Token -> IO Token -> (Token,Token) -> (Token,Token) -> IO (Token,Token)
token_and_operation sample1 sample2 (a1,a2) (b1,b2) =
  sample1 >>= \z1 ->
  sample2 >>= \z2 -> 
  let cmi = (\a -> POW a (-1)) in
  return (token_commutator (z1 `MULT` a1 `MULT` (cmi z1)) b1,
          token_commutator (z2 `MULT` a2 `MULT` (cmi z2)) b2)

token_not_operation :: (Token,Token) -> (Token,Token)
token_not_operation (a1,a2) =
  let cmi = (\a -> POW a (-1)) in
  (a1, (cmi a2) `MULT` a1)

   -------------------
   -- Group sampler --
   -------------------

generate_group_rep k s =
  fq (k+1) >>= \(p,q,pq) -> sl2_fq_rep_sym (p,q,pq) s >>= \(sl2_rep,matri) ->
  return (sl2_rep,matri,pq)

obfuscate_group :: Integer -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k rep =
  random_tietze rep (\rep -> sample_from_rep_2 k rep) k

construct_group_sampler :: Integer -> IO ((IO Token, IO Token, ([Token],[Token])), ((Token,Token) -> (Token,Token) -> IO (Token,Token), (Token,Token) -> (Token,Token)), (Token -> Bool, Token -> Maybe [[Integer]]))
construct_group_sampler k =
  generate_group_rep k ("u_1","t_1","h2_1","h_1") >>= \(sl2_rep_1,matri1,pq1) ->
  generate_group_rep k ("u_2","t_2","h2_2","h_2") >>= \(sl2_rep_2,matri2,pq2) ->
  let sl2_rep = (fst sl2_rep_1 ++ fst sl2_rep_2, snd sl2_rep_1 ++ snd sl2_rep_2) in
  obfuscate_group k sl2_rep >>= \(sl2_rep_obfuscated,rev_trace) ->
  let phi = (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated) in
  let psi = (calculate_value_from_trace (reverse rev_trace) sl2_rep) in
  let sample_G = sample_from_rep_2 k sl2_rep_obfuscated in
  let sample_K = sample_from_rep_2 k sl2_rep_2 >>= \x -> return $ psi x in
  let pi1 = (replace_name_by_token "u_2" IDENTITY) .
            (replace_name_by_token "t_2" IDENTITY) .
            (replace_name_by_token "h2_2" IDENTITY) .
            (replace_name_by_token "h_2" IDENTITY) in
  let pi1_sim = simplify_token_expression_fix . pi1 . phi in
  let ker_aux = evaluate (zip [NAME "u_1",NAME "t_1",NAME "h2_1",NAME "h_1"] matri1) pq1 . pi1_sim in
  let ker = (maybe False (\a -> a == identity)) . ker_aux in
  let pi2 = (replace_name_by_token "u_1" IDENTITY) .
            (replace_name_by_token "t_1" IDENTITY) .
            (replace_name_by_token "h2_1" IDENTITY) .
            (replace_name_by_token "h_1" IDENTITY) in
  let pi2_sim = simplify_token_expression_fix . pi2 . phi in
  let and_op = (token_and_operation sample_K sample_K) in
  let not_op = token_not_operation in
  return ((sample_G,sample_K,sl2_rep_obfuscated),(and_op,not_op),(ker,ker_aux))
  
   ---------------------------
   -- Encoding and Decoding --
   ---------------------------

encode :: IO Token -> IO Token -> Integer -> IO (Token,Token)
encode sample_G sample_K 0 =
  sample_G >>= \a ->
  sample_K >>= \b ->
  return (a, b)
encode sample_G sample_K 1 =
  sample_G >>= \a ->
  sample_K >>= \b ->
  return (a,MULT a b)
  
decode :: (Token,Token) -> (Token -> Bool) -> (Token -> Maybe [[Integer]]) -> Maybe Integer
decode (h,t) ker pi =
  if ker t
  then Just 0
  else
    if (pi h) == (pi t)
    then Just 1
    else Nothing

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
  construct_group_sampler k >>= \((sample_G,sample_K,sl2_rep_obfuscated),(and_op,not_op),(ker,pi)) ->
  sample_K >>= \k ->
  sample_G >>= \g ->
  putStrLn $
  show (ker k) ++ " " ++ show (ker g)

testEncodeDecode =
  let k = 4 in
  construct_group_sampler k >>= \((sample_G,sample_K,sl2_rep_obfuscated),(and_op,not_op),(ker,pi)) ->
  let enc = (encode sample_G sample_K) in
  (enc 0) >>= \(z00,z01) ->
  (enc 1) >>= \(z10,z11) ->
  putStrLn $
  show (decode (z00,z01) ker pi) ++ "\n" ++
  show (decode (z10,z11) ker pi) ++ "\n" ++
  show (pi z10) ++ " " ++ show (pi z11)

testEncodeNot =
  let k = 4 in
  construct_group_sampler k >>= \((sample_G,sample_K,sl2_rep_obfuscated),(and_op,not_op),(ker,pi)) ->
  let enc = (encode sample_G sample_K) in
  (enc 1) >>= \a ->
  (enc 0) >>= \b ->
  let (a1,a2) = not_op a in
  putStrLn $
  show (decode (a1,a2) ker pi) ++ "\n"
  
testEncodeAnd =
  let k = 4 in
  construct_group_sampler k >>= \((sample_G,sample_K,sl2_rep_obfuscated),(and_op,not_op),(ker,pi)) ->
  let enc = (encode sample_G sample_K) in
  (enc 1) >>= \a ->
  (enc 1) >>= \b ->
  and_op a b >>= \(ab1,ab2) ->
  putStrLn $
  show (decode (ab1,ab2) ker pi)

main = testEncodeNot

-- Conjugate every element in representation by random element.
