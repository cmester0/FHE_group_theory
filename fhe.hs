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

encode :: IO Token -> IO Token -> Bool -> IO (Token,Token)
encode sample_G sample_K False =
  sample_G >>= \ct ->
  sample_K >>= \h ->
  return (h, ct)
encode sample_G sample_K True =
  sample_G >>= \ct ->
  sample_K >>= \h ->
  return (MULT ct h, ct)
  
decode :: (Token -> Bool) -> (Token -> Token) -> (Token,Token) -> Either (Token,Token) Bool
decode ker pi (h,t) =
  if ker h
  then Right False
  else
    let ph = (simplify_token_expression_fix (pi h)) in
    let pt = (simplify_token_expression_fix (pi t)) in
    if token_eq ph pt
    then Right True
    else Left (ph,pt)

   -------------------
   -- Group sampler --
   -------------------

generate_group_rep :: Integer -> (String,String,String,String) -> IO (([Token],[Token]),Integer)
generate_group_rep k s =
  fq (k+1) >>= \(pq,q) -> sl2_fq_rep_sym (pq,1,pq) s >>= \(sl2_rep) ->
  return (sl2_rep,pq)

obfuscate_group :: Integer -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k rep =
  random_tietze rep (\rep -> sample_from_rep_2 k rep) k

construct_group_sampler :: Integer -> IO ((([Token],[Token]), IO Token, IO Token), (Token -> Bool, Token -> Token)) -- TODO: Replace integer with bool!
construct_group_sampler k =
  generate_group_rep k ("u_1","t_1","h2_1","h_1") >>= \(sl2_rep_1,pq1) ->
  generate_group_rep k ("u_2","t_2","h2_2","h_2") >>= \(sl2_rep_2,pq2) ->
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
  let pi1_sim = simplify_token_expression_fix . pi1 . phi in
  let ker = (token_eq IDENTITY) . pi1_sim in
  return ((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi1_sim))

construct_FHE :: Integer -> IO ((Bool -> IO (Token,Token)), ((Token,Token) -> (Token,Token) -> IO (Token,Token), (Token,Token) -> (Token,Token)), ((Token,Token) -> Either (Token,Token) Bool))
construct_FHE k =
  construct_group_sampler k >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi1_sim)) ->
  let enc = (encode sample_G sample_K) in
  let and_op = (token_and_operation sample_G) in
  let not_op = token_not_operation in
  let dec = (decode ker pi1_sim) in
  return ((enc),(and_op,not_op),(dec))

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
    
testEncodeZeroAndOne k =
  construct_group_sampler k >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi)) ->
  sample_K >>= \k ->
  sample_G >>= \g ->
  putStrLn $
  show (ker k) ++ " " ++ show (ker g)

testEncodeDecode k =
  construct_FHE k >>= \((enc),(and_op,not_op),(dec)) ->
  enc False >>= \zero ->
  enc True >>= \one ->
  putStrLn $
  show (dec zero) ++ "\n" ++
  show (dec one)

testEncodeAnd k =
  construct_FHE k >>= \((enc),(and_op,not_op),(dec)) ->
  (enc True) >>= \a ->
  (enc True) >>= \b ->
  (enc False) >>= \c ->
  (enc True) >>= \d ->    
  (enc False) >>= \e ->
  (enc False) >>= \f ->
  and_op a b >>= \ab ->
  and_op c d >>= \cd ->
  and_op e f >>= \ef ->
  putStrLn $
  show (dec a) ++ "\n" ++
  show (dec b) ++ "\n" ++
  show (dec c) ++ "\n" ++
  show (dec d) ++ "\n" ++
  show (dec e) ++ "\n" ++
  show (dec f) ++ "\n" ++
  show (dec ab) ++ "\n" ++
  show (dec cd) ++ "\n" ++
  show (dec ef) ++ "\n"

testEncodeNot k =
  construct_FHE k >>= \((enc),(and_op,not_op),(dec)) ->
  (enc True) >>= \a ->
  (enc False) >>= \b ->
  let na = not_op a in
  let nb = not_op b in
  putStrLn $
  
  show (dec a) ++ "\n" ++
  show (dec b) ++ "\n\n" ++
  
  show (dec na) ++ "\n" ++
  show (dec nb) ++ "\n---"
