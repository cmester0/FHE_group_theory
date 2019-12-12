module RenderTokens where

import Codec.Picture  (generateImage, writePng) -- JuicyPixels
import Codec.Picture.Types

import FHE
import GroupRepresentation

width, height :: Integer
(width, height) = (2^31, 2^31)  -- 10^110

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
token_length (POW a n) = token_length a * (abs n)

unroll_powers :: Token -> Token
unroll_powers (POW a 0) = IDENTITY
unroll_powers (POW a 1) = unroll_powers a
unroll_powers (MULT l) = MULT (map unroll_powers l)
unroll_powers (POW (POW a m) n) = unroll_powers (POW (unroll_powers a) (m+n))
unroll_powers (POW a (-1)) = POW (unroll_powers a) (-1)
unroll_powers (POW (MULT l) n) | n < 0 =
  let inversal = (reverse l >>= \x -> return $ POW (unroll_powers x) (-1)) in
  unroll_powers $
  MULT (concat $ take (fromInteger (-n)) $ repeat inversal)
unroll_powers (POW (MULT l) n) | n > 0 =   
  unroll_powers $
  MULT (concat $ take (fromInteger n) $ repeat l)
unroll_powers (POW a n)
  | n > 0 = MULT (take (fromInteger n) $ repeat $ unroll_powers a)
  | n < 0 = MULT (take (fromInteger (-n)) $ repeat $ POW (unroll_powers a) (-1))
unroll_powers (NAME t) = NAME t
unroll_powers IDENTITY = IDENTITY

matrix_pos :: [[Integer]] -> ((Integer,Integer),(Integer,Integer))
matrix_pos [[a,b],[c,d]] = ((min a d,max a d),(min b c,max b c))

-- group_rep_pos_list :: Integer -> IO [((Integer,Integer),(Integer,Integer))]
-- group_rep_pos_list k =
--   generate_group_rep k ("x","y","z","w") >>= \(sl2_rep,pq,matrix) ->
--   return $ map (\a -> matrix_pos (eval a) ((0,width),(0,height))) (snd sl2_rep)

-- renderTokens :: String -> IO ()
-- renderTokens name =
--   (group_rep_pos_list 160) >>= \l ->
--   writePng ("output/" ++ name) $ generateImage (pixelRenderer l) img_width img_height

-- group_rep_pos_list_obfuscated :: Integer -> IO [((Integer,Integer),(Integer,Integer))]
-- group_rep_pos_list_obfuscated k =
--   construct_group_sampler k >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi)) ->
--   return $ map (\a -> matrix_pos  ((0,width),(0,height))) (map pi (snd sl2_rep_obfuscated))

group_rep_pos_list_obfuscated_random :: Integer -> IO [((Integer,Integer),(Integer,Integer))]
group_rep_pos_list_obfuscated_random k =
  construct_group_sampler k >>= \((sl2_rep_obfuscated,sample_G,sample_K),(ker,pi)) ->
  sequence ([0] >>= \_ -> return $ sample_G) >>= \sym ->
  sequence $ map (\a ->
                  case a of
                    Left x ->
                      do
                        putStrLn x
                        return ((0,width),(0,height))
                    Right x ->
                      let res = matrix_pos x in
                        do
                          putStrLn . show $ res
                          return res) (map pi sym)
  
-- renderTokensObfuscated :: String -> IO ()
-- renderTokensObfuscated name =
--   group_rep_pos_list_obfuscated 160 >>= \l ->
--   do
--     putStrLn . show $ l
--     writePng ("output/" ++ name) $ generateImage (pixelRenderer l) img_width img_height
--     putStrLn . show $ "DONE"

renderRandomTokensObfuscated :: String -> IO ()
renderRandomTokensObfuscated name =
  group_rep_pos_list_obfuscated_random 30 >>= \l ->
  do
    -- putStrLn . show $ l
    putStrLn . show $ "START"
    writePng ("output/" ++ name) $ generateImage (pixelRenderer l) img_width img_height
    putStrLn . show $ "DONE"
