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
token_commutator a b =  MULT [a , b , INV a , INV b]

token_and_operation :: IO Token -> (Token,Token) -> (Token,Token) -> IO (Token,Token)
token_and_operation sample (a1,a2) (b1,b2) =
  sample >>= \z ->
  return (token_commutator (MULT [z , a1 , INV z]) b1,
          token_commutator (MULT [z , a2 , INV z]) b2)

token_not_operation :: (Token,Token) -> (Token,Token)
token_not_operation (a1,a2) = (MULT [INV a1 , a2], a2)

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
  return (MULT [ct , h], ct)
  
decode :: (Token -> Either String Bool) -> (Token -> Either String [[Integer]]) -> (Token,Token) -> Either String Bool
decode ker pi_eval (h,t) =
  (ker h) >>= \b ->
  if b
  then Right False
  else 
    pi_eval t >>= \pt ->
    pi_eval h >>= \ph ->
    if ph == pt
    then Right True
    else Left $ show ph ++ " vs " ++ show pt
    
   -------------------
   -- Group sampler --
   -------------------

generate_group_rep :: Integer -> (String,String,String,String) -> IO (([Token],[Token]),Integer,[[[Integer]]])
generate_group_rep k s =
  fq (k+1) >>= \(pq,q) -> sl2_fq_rep (pq,1,pq) s >>= \(sl2_rep,matrix) ->
  return (sl2_rep,pq,matrix)

obfuscate_group :: Integer -> Integer -> [Token] -> ([Token],[Token]) -> IO (([Token],[Token]),[Trace])
obfuscate_group k k2 sample_list rep =
  let sample = (\rev_trace -> cube sample_list >>= return . (calculate_value_from_trace (reverse rev_trace) rep)) in
    random_tietze rep sample k >>= reduce_group_representation

group_commutor [] t = []
group_commutor (a : s) t =
  map (token_commutator a) t ++ group_commutor s t

product_representation (s,r) (t,q) = (s ++ t, r ++ q ++ group_commutor s t)

construct_group_sampler :: Integer -> IO ((([Token],[Token]), IO Token, IO Token), (Token -> Either String Bool, Token -> Either String [[Integer]])) -- TODO: Replace integer with bool!
construct_group_sampler k =  
  let k3 = 4*k + 3 in
  generate_group_rep (k+4) ("u_1","t_1","h2_1","h_1") >>= \(sl2_rep_1,pq1,matrix1) ->
  generate_group_rep (k*2) ("u_2","t_2","h2_2","h_2") >>= \(sl2_rep_2,_,_) ->
  let sl2_rep = product_representation sl2_rep_1 sl2_rep_2 in
  create_sample_list k3 sl2_rep >>= \sample_list ->
  obfuscate_group k k3 sample_list sl2_rep >>= \(sl2_rep_obfuscated,rev_trace) ->  
  let phi = (calculate_value_from_rev_trace rev_trace sl2_rep_obfuscated) in
  let psi = (calculate_value_from_trace (reverse rev_trace) sl2_rep) in
  create_sample_list k3 sl2_rep_1 >>= \sample_list_G ->
  create_sample_list k3 sl2_rep_2 >>= \sample_list_K ->
  let sample_G = (cube sample_list_G) >>= return . knuth_bendix_fix . psi in
  let sample_K = (cube sample_list_K) >>= return . knuth_bendix_fix . psi in
  let pi1 = (replace_name_by_token "u_2" IDENTITY) .
            (replace_name_by_token "t_2" IDENTITY) .
            (replace_name_by_token "h2_2" IDENTITY) .
            (replace_name_by_token "h_2" IDENTITY) in
  let namesList = [NAME "u_1",NAME "t_1",NAME "h2_1",NAME "h_1"] in
  let pi1_eval = (evaluate (zip namesList matrix1) pq1) . knuth_bendix_fix . pi1 . phi . knuth_bendix_fix in
  -- let pi1_eval = (evaluate (zip namesList matrix1) pq1) . normal_form (snd sl2_rep_1) . pi1 . phi . normal_form (snd sl2_rep_obfuscated) in
  let ker = \x -> pi1_eval x >>= \y -> return $ (identity == y) in
    return ((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi1_eval))

construct_FHE :: Integer -> IO ((Bool -> IO (Token,Token)), ((Token,Token) -> (Token,Token) -> IO (Token,Token), (Token,Token) -> (Token,Token)), ((Token,Token) -> Either String Bool))
construct_FHE k =
  construct_group_sampler k >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi)) ->
  let enc = (encode sample_G sample_K) in
  let and_op = (token_and_operation sample_G) in
  let not_op = token_not_operation in
  let dec = (decode ker pi) in
  return ((enc),(and_op,not_op),(dec))

  ------------
  --- TESTS --
  ------------

testEquationSolver =
  putStrLn $
  let val = MULT [(NAME "c") , (NAME "a") , (INV (NAME "a")), (INV (NAME "a")) , (NAME "b")] in
  "Pure: " ++ show val ++ "\n" ++
  "Normal: " ++ show (normal_form [] val) ++ "\n" ++
  "MoveL: " ++ show (move_to_rhs_aux "a" (normal_form [] val) IDENTITY) ++ "\n" ++
  "Flip: " ++ show (normal_form [] $ INV val) ++ "\n" ++
  "MoveR: " ++ show (move_to_rhs_aux "a" (normal_form [] $ INV val) IDENTITY) ++ "\n" ++
  "FlipFlip: " ++ show (normal_form [] $ INV (normal_form [] $ INV val)) ++ "\n" ++
  "Rem?: " ++ show (move_to_rhs [] "a" (normal_form [] val) IDENTITY) ++ "\n" ++
  "Rem: " ++ show (remove_tokens [] "a" (normal_form [] val)) ++ "\n" ++
  "Reduced: " ++ show (reduced "a" (remove_tokens [] "a" (normal_form [] val))) ++ "\n" ++
  "Normal Rem: " ++ show (normal_form [] (remove_tokens [] "a" (normal_form [] val))) ++ "\n" ++
  "Normal Rem: " ++ show (normal_form [] (remove_tokens [] "a" (normal_form [] val))) ++ "\n" ++
  "Solveable: " ++ show (solvable [] "a" val) ++ "\n" ++
  "Solution: " ++ show (solve_for_token [] "a" val) ++ "\n" ++
  "Find generator: " ++ show (find_solution_for_generator [] "a" [val])
    
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
