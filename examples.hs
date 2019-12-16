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
  -- let rel = [MULT [NAME "s",NAME "v"], INV (MULT [NAME "s",NAME "v"])] in
  -- let rel' = (map knuth_bendix rel) in
  --   let x = (MULT [NAME "s",NAME "v"]) in
  --   let y = (INV (MULT [NAME "s",NAME "v"])) in
  --   do
  --     putStrLn . show $ remove_relation rel' rel'
  --     removing_relation_fix (([], rel),[]) >>= putStrLn . show
    
    -- putStrLn . show $ remove_subsection_list (head rel) (tail rel)

    -- putStrLn . show $ remove_relation rel rel

  -- testEquationSolver
  -- testEncodeDecode 30
  testEncodeNot 30
