import GroupRepresentation
import FHE

import System.IO
import Data.List
import System.Random
import Control.Monad

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

testEncodeDecode ((enc),(and_op,not_op),(dec)) =
  enc False >>= \zero ->
  enc True >>= \one ->
  putStrLn $
  "Dec(Enc(False)): " ++ show (dec zero) ++ "\n" ++
  "Dec(Enc(True)): " ++ show (dec one)

testEncodeAnd ((enc),(and_op,not_op),(dec)) =
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
  "A: " ++ show (dec a) ++ "\n" ++
  "B: " ++ show (dec b) ++ "\n" ++
  "C: " ++ show (dec c) ++ "\n" ++
  "D: " ++ show (dec d) ++ "\n" ++
  "E: " ++ show (dec e) ++ "\n" ++
  "F: " ++ show (dec f) ++ "\n" ++
  "A /\\ B: " ++ show (dec ab) ++ "\n" ++
  "C /\\ D: " ++ show (dec cd) ++ "\n" ++
  "E /\\ F: " ++ show (dec ef) ++ "\n"

testEncodeNot ((enc),(and_op,not_op),(dec)) =
  (enc True) >>= \a ->
  (enc False) >>= \b ->
  let na = not_op a in
  let nb = not_op b in
  putStrLn $  
  "A: " ++ show (dec a) ++ "\n" ++
  "B: " ++ show (dec b) ++ "\n\n" ++  
  "not A: " ++ show (dec na) ++ "\n" ++
  "not B: " ++ show (dec nb) ++ "\n"

  -------------------------
  --- Blood Type Example --
  -------------------------

convertToNumber :: String -> (Bool,Bool,Bool)
convertToNumber s = (isInfixOf "A" s,isInfixOf "B" s,isInfixOf "+" s)

fhe_protocol ::((Bool -> IO (Token,Token)), ((Token,Token) -> (Token,Token) -> IO (Token,Token), (Token,Token) -> (Token,Token)), ((Token,Token) -> Either String Bool)) -> (Bool,Bool,Bool) -> (Bool,Bool,Bool) -> IO (Either String Bool)
fhe_protocol ((enc),(and_op,not_op),(dec)) (x0,x1,x2) (y0,y1,y2) =
  -- Alice encrypts her there bits
  enc x0 >>= \cx0 -> 
  enc x1 >>= \cx1 -> 
  enc x2 >>= \cx2 ->
  -- Bob encrypts his input, and compute the function
  enc y0 >>= \cy0 ->
  enc y1 >>= \cy1 ->
  enc y2 >>= \cy2 ->
  -- Compute function
  (and_op cy0 (not_op cx0)) >>= \p0 ->
  (and_op cy1 (not_op cx1)) >>= \p1 ->
  (and_op cy2 (not_op cx2)) >>= \p2 ->
  
  (and_op (not_op p0) (not_op p1) >>= and_op (not_op p2)) >>= \c_res ->
  -- Alice decrypts the result
  return $ dec c_res

blood_type_example scheme = do
  putStrLn "Please enter blood types (AB+,O-,etc.) for X and Y..."
  putStr "X: "
  hFlush stdout
  x <- getLine
  putStr "Y: "
  hFlush stdout
  y <- getLine  
  fhe_protocol scheme (convertToNumber x) (convertToNumber y) >>= \e ->  
    putStrLn $ show $
    e >>= \b ->
    return $
    if b
    then "X can receive blood from Y"
    else "X can not receive blood from Y"

-- A complex computation (long)
call_recursively 0 f x = return x
call_recursively n f x =
  f x >>= \y ->
  do
    putStrLn $ "Iteration " ++ show n
    call_recursively (n-1) f y

complex_computation ((enc),(and_op,not_op),(dec)) =
  enc True >>= \one ->
  enc False >>= \zero ->
  call_recursively 10 (and_op one) one >>= \val ->
  do
    putStrLn "Decrypting"
    putStrLn $ "Dec(1 /\\ 1 /\\ 1 /\\ ...): " ++ show (dec val)

-- Main
main =
  do
    putStrLn "Input security parameter (number of bytes of security): "
    k <- readLn
    construct_FHE (k :: Integer) >>= \scheme ->
      do
        putStrLn "\n\n-------------------------"
        putStrLn "EncodeDecode"
        testEncodeDecode scheme
        putStrLn "-------------------------"
        putStrLn "NOT"
        testEncodeNot scheme
        putStrLn "-------------------------"
        putStrLn "AND"
        testEncodeAnd scheme
        putStrLn "-------------------------"
        putStrLn "Blood Type"
        blood_type_example scheme
        putStrLn "-------------------------"
        putStrLn "Complex computation (1 /\\ 1 /\\ 1 /\\ ...)"
        complex_computation scheme
        putStrLn "-------------------------"
