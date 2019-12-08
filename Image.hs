module RenderTokens where

import Codec.Picture  (generateImage, writePng) -- JuicyPixels
import Codec.Picture.Types

import FHE
import GroupRepresentation

width, height :: Int
(width, height) = (400, 200)

pixelRenderer :: [((Int,Int),(Int,Int))] -> Int -> Int -> PixelRGBA8
pixelRenderer l x y =
  if foldr (\((ax0,ax1),(ay0,ay1)) b ->
              ((ax0 <= x && x <= ax1) &&
               (ay0 <= y && y <= ay1))
              || b)
     False l
  then PixelRGBA8 (fromIntegral x) (fromIntegral y) 255 255
  else PixelRGBA8 0 0 0 0

token_length :: Token -> Integer
token_length (IDENTITY) = 1
token_length (NAME s) = 1
token_length (MULT a b) = token_length a + token_length b
token_length (POW a n) = token_length a * (abs n)

unroll_powers :: Token -> Token
unroll_powers (POW a 0) = IDENTITY
unroll_powers (POW a 1) = unroll_powers a
unroll_powers (MULT a b) =
  let ua = unroll_powers a in
  let ub = unroll_powers b in
  MULT ua ub
unroll_powers (POW (POW a m) n) = unroll_powers (POW (unroll_powers a) (m*n))
unroll_powers (POW a (-1)) = POW (unroll_powers a) (-1)
unroll_powers (POW (MULT a b) n) | n < 0 = 
  let ua = unroll_powers a in
  let ub = unroll_powers b in
  MULT
  (MULT (unroll_powers (POW ub (-1))) (unroll_powers (POW ua (-1))))
  (unroll_powers (POW (MULT ua ub) (n+1)))
unroll_powers (POW (NAME s) n) | n < 0 =
  MULT (POW (NAME s) (-1)) (unroll_powers (POW (NAME s) (n+1)))
unroll_powers (POW (MULT a b) n) | n > 0 =   
  let ua = unroll_powers a in
  let ub = unroll_powers a in
  MULT (MULT ua ub) (unroll_powers (POW (MULT ua ub) (n-1)))
unroll_powers (POW a n) | n > 0 =   
  let ua = unroll_powers a in
  MULT ua (unroll_powers (POW  ua (n-1)))
unroll_powers (NAME t) = NAME t
unroll_powers IDENTITY = IDENTITY

token_pos :: Token -> ((Int,Int),(Int,Int)) -> ((Int,Int),(Int,Int))
token_pos (MULT a b) ((x0,x1),(y0,y1)) =
  token_pos b $ token_pos a ((x0,x1),(y0,y1))
token_pos (POW (NAME "x") (-1)) ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0,x1 - x_step * 3),(y0 + y_step,y1))
token_pos (POW (NAME "y") (-1)) ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0 + x_step, x1 - x_step * 2),(y0 + y_step,y1))
token_pos (POW (NAME "z") (-1)) ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0 + x_step * 2, x1 - x_step),(y0 + y_step,y1))
token_pos (POW (NAME "w") (-1)) ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0 + x_step * 3, x1),(y0 + y_step,y1))
token_pos (NAME "x") ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0,x1 - x_step * 3),(y0,y1 - y_step))
token_pos (NAME "y") ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0 + x_step,x1 - x_step * 2),(y0,y1 - y_step))
token_pos (NAME "z") ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0 + x_step*2,x1 - x_step),(y0,y1 - y_step))
token_pos (NAME "w") ((x0,x1),(y0,y1)) =
  let x_step = (div (x1 - x0) 4) in
  let y_step = (div (y1 - y0) 2) in
  ((x0 + x_step*3,x1),(y0,y1 - y_step))
token_pos (POW (MULT a b) n) ranges | n > 0 = token_pos (MULT (POW a n) (POW b n)) ranges
token_pos (POW (MULT a b) n) ranges | n < 0 = token_pos (MULT (POW b n) (POW a n)) ranges
-- token_pos (POW (NAME s) n) ranges | n < 0 = ranges
token_pos (POW (NAME s) n) ranges | n > 0 = token_pos (MULT (NAME s) (POW (NAME s) (n-1))) ranges
token_pos (POW IDENTITY n) ranges = ranges
token_pos (POW a 0) ranges = ranges
token_pos (POW (POW a n) m) ranges = token_pos (POW a (n*m)) ranges
token_pos (IDENTITY) ((x0,x1),(y0,y1)) = ((x0,x1),(y0,y1))

group_rep_pos_list :: Integer -> IO [((Int,Int),(Int,Int))]
group_rep_pos_list k =
  generate_group_rep k ("x","y","z","w") >>= \(sl2_rep,pq,matrix) ->
  let largest = foldr (\a b -> if a > b then a else b) 0 (map token_length (snd sl2_rep)) in
  let val = map (\a -> token_pos (unroll_powers a) ((0,width),(0,height))) (snd sl2_rep) in
  return $ val

renderTokens name =
  (group_rep_pos_list 160) >>= \l ->
  writePng ("output/" ++ name) $ generateImage (pixelRenderer l) width height
  
