{-# LANGUAGE ViewPatterns #-}

import Matrix
import GroupRepresentation
import Data.Maybe

   -------------------
   -- Group sampler --
   -------------------

generate_group_rep k s =
  fq (k+1) >>= \(p,q,pq) -> sl2_fq_rep_sym (p,q,pq) s >>= \(sl2_rep,matri) ->
  return (sl2_rep,matri,pq)

obfuscate_group :: Integer -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k rep =
  random_tietze rep (\rep -> sample_from_rep_2 k rep) k

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
  return ((sample_G,sample_K,sl2_rep_obfuscated),(pi1_sim,ker),(pq1,pq2,ker_aux,rev_trace,sl2_rep))

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
  return (a,a)
  
decode :: Token -> (Token -> Bool) -> Integer
decode t ker =
  if ker t
  then 0
  else 1

  ---
  --- TESTS
  ---

testEquationSolver = 
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

main =
  let k = 4 in
  construct_group_sampler k >>= \((sample_G,sample_K,sl2_rep_obfuscated),(pi1_sim,ker),(pq1,pq2,ker_aux,rev_trace,sl2_rep)) ->
  sample_K >>= \k ->
  sample_G >>= \g ->
  putStrLn $
  show (sl2_rep) ++ "\n\n\n" ++
  show (pi1_sim k) ++ "\n\n\n" ++
  show (pq1,pq2) ++ "\n\n\n" ++
  (foldr (\a b -> a ++ "\n" ++ b) "n" (map show rev_trace)) ++ "\n\n\n" ++
  show (ker_aux k) ++ "\n\n\n" ++
  show (decode k ker) 
