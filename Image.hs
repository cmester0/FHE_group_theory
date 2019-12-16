module RenderTokens where

import Codec.Picture  (generateImage, writePng) -- JuicyPixels
import Codec.Picture.Types

import FHE
import GroupRepresentation

width, height :: Integer
(width, height) = (2^16, 2^16)  -- 10^110

img_width, img_height :: Int
(img_width, img_height) = (100, 100)

pixelRenderer :: [((Integer,Integer),(Integer,Integer))] -> Int -> Int -> PixelRGBA8
pixelRenderer l x y =
  let convert_x = \x -> div ((toInteger x) * width) (toInteger img_width) in
  let convert_y = \y -> div ((toInteger y) * height) (toInteger img_height) in
  if foldr (\((ax0,ax1),(ay0,ay1)) b ->
               ((((convert_x (x-1)) <= ax0 && ax0 <= (convert_x x)) ||
                  (ax0 <= (convert_x x) && (convert_x x) <= ax1) ||
                  ((convert_x x) <= ax0 && ax0 <= (convert_x (x+1))))
                 &&
                 (((convert_y (y-1)) <= ay0 && ay0 <= (convert_y y)) ||
                   (ay0 <= (convert_y y) && (convert_y y) <= ay1) ||
                   ((convert_y y) <= ay0 && ay0 <= (convert_y (y+1)))))
               || b)
     False l
  then PixelRGBA8 (fromIntegral x) (fromIntegral y) 255 16
  else PixelRGBA8 0 0 0 0

token_length :: Token -> Integer
token_length (IDENTITY) = 1
token_length (NAME s) = 1
token_length (MULT l) = foldr (+) 0 $ map token_length l
token_length (INV a) = token_length a

matrix_pos :: [[Integer]] -> ((Integer,Integer),(Integer,Integer))
matrix_pos [[a,b],[c,d]] = ((min a d,max a d),(min b c,max b c))

group_rep_pos_list_obfuscated_random :: Integer -> IO [((Integer,Integer),(Integer,Integer))]
group_rep_pos_list_obfuscated_random k =
  construct_group_sampler k >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi)) ->
  do
    putStrLn "START"
    sequence ([0..3] >>= \_ -> return $ sample_G) >>= \sym ->
      do
        putStrLn "START2"
        let mpi = map pi sym in
          do
            putStrLn $ show mpi
            sequence $ map (\a ->
                              case a of
                                Left x ->
                                  do
                                    putStrLn ("FAIL: " ++ x)
                                    return ((0,width),(0,height))
                                Right x ->
                                  do
                                    putStrLn "Matrix pos?"
                                    let res = matrix_pos x in
                                      do
                                        putStrLn . show $ res
                                        return res) mpi

renderRandomTokensObfuscated :: String -> IO ()
renderRandomTokensObfuscated name =
  group_rep_pos_list_obfuscated_random 3 >>= \l ->
  do
    putStrLn . show $ "START"
    writePng ("output/" ++ name) $ generateImage (pixelRenderer l) img_width img_height
    putStrLn . show $ "DONE"
