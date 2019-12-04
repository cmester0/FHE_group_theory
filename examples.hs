import GroupRepresentation
import FHE

import System.IO
import Data.List
import System.Random
import Control.Monad

convertToNumber :: String -> (Bool,Bool,Bool)
convertToNumber s = (isInfixOf "A" s,isInfixOf "B" s,isInfixOf "+" s)

fhe_protocol :: Integer -> (Bool,Bool,Bool) -> (Bool,Bool,Bool) -> IO (Either (Token,Token) Bool)
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

-- complex_computation k =
--   construct_FHE k >>= \((enc),(and_op,not_op),(dec)) ->    
--   (enc 1) >>= \one ->
--   (enc 0) >>= \zero ->
--   (((and_op one one >>= and_op one) >>= and_op one) >>= and_op one) >>= \temp ->
--   putStrLn . show $ (dec val)

testSimplification =
  putStrLn $
  foldr (\a b -> show (snd a) ++ " vs " ++ show (simplify_token_expression_fix . fst $ a) ++ "\n" ++ b) ""
  [(MULT (NAME "A") IDENTITY, "A"),
   (MULT IDENTITY (NAME "A"), "A"),

   (MULT (POW (NAME "A") 15) IDENTITY, "A^15"),
   (MULT IDENTITY (POW (NAME "A") 15), "A^15"),

   (MULT (POW (NAME "A") 10) (POW (NAME "A") 5), "A^15"),
   
   (MULT (POW (NAME "A") 10) (MULT (POW (NAME "A") 5) (NAME "B")), "A^15 * B"),
   (MULT (POW IDENTITY 10) (MULT (POW (NAME "A") 5) (NAME "B")), "A^5 * B"),
   (MULT (POW (NAME "A") 10) (MULT (POW IDENTITY 5) (NAME "B")), "A^10 * B"),
   (MULT (POW (NAME "A") 10) (MULT (POW (NAME "A") 5) IDENTITY), "A^15"),
   
   (MULT (MULT (NAME "B") (POW (NAME "A") 5)) (POW (NAME "A") 10), "B * A^15"),
   (MULT (MULT IDENTITY (POW (NAME "B") 5)) (POW (NAME "A") 10), "B^5 * A^10"),
   (MULT (MULT (NAME "B") (POW IDENTITY 5)) (POW (NAME "A") 10), "B * A^10"),
   (MULT (MULT (NAME "B") (POW (NAME "A") 5)) (POW IDENTITY 10), "B * A^5"),
   
   (MULT (MULT (MULT IDENTITY (NAME "A")) (NAME "B")) (NAME "C"), "A * B * C"),
   (MULT (MULT (MULT (NAME "A") IDENTITY) (NAME "B")) (NAME "C"), "A * B * C"),
   (MULT (MULT (MULT (NAME "A") (NAME "B")) IDENTITY) (NAME "C"), "A * B * C"),
   (MULT (MULT (MULT (NAME "A") (NAME "B")) (NAME "C")) IDENTITY, "A * B * C"),

   (MULT (POW (NAME "A") 5) (MULT (POW (NAME "B") 10) IDENTITY) , "A^5 * B^10"),
   
   (MULT (POW (NAME "A") (-1)) (NAME "A"),"I"),

   (MULT (NAME "A") (POW (NAME "B") 1), "A * B"),

   (MULT (POW (NAME "B") (-4)) (POW (NAME "B") 4), "I"),
   (MULT (POW (NAME "B") (-4)) (MULT (POW (NAME "B") 4) (NAME "A")), "A"),
   (MULT (POW (NAME "B") (-4)) (MULT (POW (NAME "B") 4) (POW (NAME "A") 6)), "A^6"),
   (MULT (POW (NAME "A") (-6)) (MULT (POW (NAME "B") (-4)) (MULT (POW (NAME "B") 4) (POW (NAME "A") 6))), "I"),

   (MULT (POW (NAME "A") 2) (MULT (NAME "B") (MULT (POW (NAME "B") (-1)) (POW (NAME "A") (-2)))), "I"),

   (MULT (NAME "C") (MULT (POW (NAME "C") (-1)) (MULT (POW (NAME "B") (-7)) (POW (NAME "A") (-4)))),"B^-7*A^-4"),
   (MULT (POW (NAME "A") 4) (MULT (POW (NAME "B") 7) (MULT (NAME "C") (MULT (POW (NAME "C") (-1)) (MULT (POW (NAME "B") (-7)) (POW (NAME "A") (-4)))))),"I"),
   (MULT (NAME "A") (MULT (POW (NAME "B") 10) (MULT (POW (NAME "B") (-10)) (POW (NAME "A") (-1)))), "I"),
   
   (POW (NAME "A") 1, "A"),
   (POW (NAME "A") 0, "I")]
  
main =
  -- testSimplification
  -- testEncodeDecode 10
  -- testEncodeZeroAndOne 10
  -- testEncodeNot 80
  testEncodeAnd 10
  -- blood_type_example 10 -- 160
