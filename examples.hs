import GroupRepresentation
import FHE

import System.IO
import Data.List
import System.Random
import Control.Monad

import RenderTokens

convertToNumber :: String -> (Bool,Bool,Bool)
convertToNumber s = (isInfixOf "A" s,isInfixOf "B" s,isInfixOf "+" s)

fhe_protocol :: Integer -> (Bool,Bool,Bool) -> (Bool,Bool,Bool) -> IO (Either String Bool)
fhe_protocol k (x0,x1,x2) (y0,y1,y2) =
  construct_FHE k >>= \((enc),(and_op,not_op),(dec)) ->
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

blood_type_example k = do
  putStrLn "Please enter blood types (AB+,O-,etc.) for X and Y..."
  putStr "X: "
  hFlush stdout
  x <- getLine
  putStr "Y: "
  hFlush stdout
  y <- getLine  
  fhe_protocol k (convertToNumber x) (convertToNumber y) >>= \e ->  
    putStrLn $ show $
    e >>= \b ->
    return $
    if b
    then "X can receive blood from Y"
    else "X can not receive blood from Y"

call_recursively 0 f x = return x
call_recursively n f x =
  f x >>= \y -> call_recursively (n-1) f y

complex_computation k =
  construct_FHE k >>= \((enc),(and_op,not_op),(dec)) ->    
  enc True >>= \one ->
  enc False >>= \zero ->
  call_recursively 10 (and_op one) one >>= \val ->
  putStrLn . show $ (dec val)

loop render 0 =
  do
    render $ "out" ++ show 0 ++ ".png"
    putStrLn $ "out" ++ show 0 ++ ".png"
loop render i =
  do
    render $ "out" ++ show i ++ ".png"
    putStrLn $ "out" ++ show i ++ ".png"
    loop render (i-1)

main =
  -- testEquationSolver
  -- putStrLn . show $ unroll_powers (POW (POW (NAME "s") (3)) (-3))

  -- let k = 10 in
  -- generate_group_rep k ("u_1","t_1","h2_1","h_1") >>= \(sl2_rep,pq1,matrix1) ->
  -- random_tietze sl2_rep (\rep -> sample_from_rep_2 k rep) 40 >>=
  -- putStrLn . foldr (\a b -> a ++ "\n" ++ b) "" . map show . snd
  
    -- group_rep_pos_list 30 >>=
  -- putStrLn . show 

   -- renderTokens $ "out.png"
  -- loop renderTokens 100
  -- loop renderTokensObfuscated 100

  -- (randomIO :: IO Integer) >>= \x ->
  -- do
  --   putStrLn . show $ (abs x)
  --   renderTokensObfuscated $ (show . abs $ x) ++ ".png"
  
  loop renderRandomTokensObfuscated 1000
  
  -- putStrLn $
  -- (show . mult_simplify_fix $ MULT [POW (NAME "a") (-1), MULT [POW (NAME "b") (-1),MULT [POW (NAME "a") (-1), NAME "c"]]]) ++ "\n" ++
  -- foldr (\a b -> (show . simple_form_fix $ a) ++ "\n" ++ b) "" 
  -- [MULT [POW (NAME "a") (-1), POW (MULT [NAME "a",NAME "b"]) (-1), NAME ("c")],
  --  MULT [POW (NAME "a") (-1), MULT [POW (NAME "b") (-1),MULT [POW (NAME "a") (-1), NAME "c"]]],
  --  MULT [POW (NAME "a") (-1), MULT [POW (NAME "a") (-1),MULT [POW (NAME "b") (-1), NAME "c"]]],
  --  MULT [POW (NAME "a") (-1), MULT [NAME "a",NAME "b"], NAME ("c")]]
  
  -- let k = 3 in
  -- let k2 = 80 in
  -- generate_group_rep k ("u_1","t_1","h2_1","h_1") >>= \(sl2_rep,pq,matrix) ->
  -- do
  -- putStrLn $ show "!=0"
  -- random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) [] 0 1 >>= \(sl2_rep,rev_trace) ->
  --   do
  --   putStrLn $ show "!=1"
  --   random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 1 1 >>= \(sl2_rep,rev_trace) ->
  --     do
  --     putStrLn $ show "!=2"
  --     random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 2 1 >>= \(sl2_rep,rev_trace) ->
  --       do
  --       putStrLn $ show "!=3"
  --       random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 3 1 >>= \(sl2_rep,rev_trace) ->
  --         do
  --         putStrLn $ show "!=4"
  --         random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 4 1 >>= \(sl2_rep,rev_trace) ->
  --           do
  --           putStrLn $ show "!=5"
  --           random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 5 1 >>= \(sl2_rep,rev_trace) ->
  --             do
  --             putStrLn $ show "!=6"
  --             random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 6 1 >>= \(sl2_rep,rev_trace) ->
  --               do
  --               putStrLn $ show "!=7"
  --               random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 7 1 >>= \(sl2_rep,rev_trace) ->
  --                 do
  --                 putStrLn $ show "!=8"
  --                 random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 8 1 >>= \(sl2_rep,rev_trace) ->
  --                   do
  --                   putStrLn $ show "!=9"
  --                   random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 9 1 >>= \(sl2_rep,rev_trace) ->
  --                     do
  --                     putStrLn $ show "!=10"
  --                     random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 10 1 >>= \(sl2_rep,rev_trace) ->
  --                       do
  --                       putStrLn $ show "!=11"
  --                       random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 11 1 >>= \(sl2_rep,rev_trace) ->
  --                         do
  --                         putStrLn $ show "!=12"
  --                         random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                           do
  --                           putStrLn $ show "!=13"
  --                           random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                             do
  --                             putStrLn $ show "!=14"
  --                             random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                               do
  --                               putStrLn $ show "!=15"
  --                               random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                 do
  --                                 putStrLn $ show "!=16"
  --                                 random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                   do
  --                                   putStrLn $ show "!=17"
  --                                   random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                     do
  --                                     putStrLn $ show "!=18"
  --                                     random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                       do
  --                                       putStrLn $ show "!=19"
  --                                       random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                         do
  --                                         putStrLn $ show "!=20"
  --                                         random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                           do
  --                                           putStrLn $ show "!=21"
  --                                           random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                             do
  --                                             putStrLn $ show "!=22"
  --                                             random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                               do
  --                                               putStrLn $ show "!=23"
  --                                               random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                                 do
  --                                                 putStrLn $ show "!=24"
  --                                                 random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                                   do
  --                                                   putStrLn $ show "!=25"
  --                                                   random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                                     do
  --                                                     putStrLn $ show "!=26"
  --                                                     random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                                       do
  --                                                       putStrLn $ show "!=27"
  --                                                       random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                                         do
  --                                                         putStrLn $ show "!=28"
  --                                                         random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 12 1 >>= \(sl2_rep,rev_trace) ->
  --                                                           do
  --                                                           putStrLn $ show "!=29"
  --                                                           random_tietze_aux sl2_rep (\rep -> sample_from_rep_2 k2 rep) rev_trace 13 1 >>= \(sl2_rep_obfuscated,rev_trace) ->
  --                                                             do
  --                                                             putStrLn $ show pq ++ "\n"
  --                                                             putStrLn $ foldr (\a b -> show a ++ "\n" ++ b) "" rev_trace
  --                                                             putStrLn $ show $ fst sl2_rep_obfuscated
    
  -- construct_group_sampler 10 >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi1_eval)) ->
  -- putStrLn . show . snd $ sl2_rep_obfuscated

  -- testSimplification
  -- testEncodeDecode 10
  -- testEncodeZeroAndOne 10
  -- testEncodeNot 160
  -- complex_computation 160
  -- testEncodeAnd 160
  -- blood_type_example 10 -- 160
