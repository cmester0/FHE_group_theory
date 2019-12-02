import FHE

import System.IO
import Data.List
import System.Random
import Control.Monad

convertToNumber :: String -> (Integer,Integer,Integer)
convertToNumber s =
  ((if isInfixOf "A" s then 1 else 0),
   (if isInfixOf "B" s then 1 else 0),
   (if isInfixOf "+" s then 1 else 0))


fhe_protocol :: Integer -> (Integer,Integer,Integer) -> (Integer,Integer,Integer) -> IO (Maybe Integer)
fhe_protocol k (x0,x1,x2) (y0,y1,y2) =
  construct_group_sampler k >>= \((sl2_rep_obfuscated,enc),(and_op,not_op),(ker,dec)) ->
  -- Alice encrypts her there bits
  enc x0 >>= \cx0 -> 
  enc x1 >>= \cx1 -> 
  enc x2 >>= \cx2 ->
  -- Bob encrypts his input, and compute the function
  enc y0 >>= \cy0 ->
  enc y1 >>= \cy1 ->
  enc y2 >>= \cy2 ->
  enc 1 >>= \c1 ->
  -- Compute function
  (and_op cy0 (not_op cx0)) >>= \p0 ->
  (and_op cy1 (not_op cx1)) >>= \p1 ->
  (and_op cy2 (not_op cx2)) >>= \p2 ->
  (and_op (not_op p0) (not_op p1) >>= and_op (not_op p2)) >>= \c_res ->
  -- Alice decrypts the result
  return $ dec c_res

show_just_print (Just a) = show $ a
show_just_print Nothing = "A problem occured"

blood_type_example = do
  putStrLn "Please enter blood types (AB+,O-,etc.) for X and Y..."
  putStr "X: "
  hFlush stdout
  x <- getLine
  putStr "Y: "
  hFlush stdout
  y <- getLine  
  fhe_protocol 18 (convertToNumber x) (convertToNumber y) >>= \e ->  
    putStrLn $ show_just_print $
    e >>= \b ->
    return $
    if b == 1
    then "X can receive blood from Y"
    else "X can not receive blood from Y"
  
main =
  testEquationSolver
  -- blood_type_example
