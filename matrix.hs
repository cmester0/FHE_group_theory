module Matrix where

import Group

identity = [[1,0],[0,1]]

matrix_inverse order value =
  let r11 = value !! 0 !! 0 in
  let r12 = value !! 0 !! 1 in
  let r21 = value !! 1 !! 0 in
  let r22 = value !! 1 !! 1 in
  let r12_inverse = mod (order - r12) order in
  let r21_inverse = mod (order - r21) order in
  [[r22,r12_inverse],[r21_inverse,r11]]
    
-- 2 x 2 matrix multiplication
matrix_mult :: Integer -> [[Integer]] -> [[Integer]] -> [[Integer]]
matrix_mult order a b =
  let r11 = (a !! 0 !! 0) * (b !! 0 !! 0) + (a !! 0 !! 1) * (b !! 1 !! 0) in
  let r12 = (a !! 0 !! 0) * (b !! 0 !! 1) + (a !! 0 !! 1) * (b !! 1 !! 1) in
  let r21 = (a !! 1 !! 0) * (b !! 0 !! 0) + (a !! 1 !! 1) * (b !! 1 !! 0) in
  let r22 = (a !! 1 !! 0) * (b !! 0 !! 1) + (a !! 1 !! 1) * (b !! 1 !! 1) in
    [[mod r11 order,mod r12 order],
     [mod r21 order,mod r22 order]]

matrix_pow order m 0 = identity
matrix_pow order m 1 = m
matrix_pow order m p | p < 0 = matrix_inverse order (matrix_pow order m (-p))
matrix_pow order m p | p > 0 = matrix_mult order m (matrix_pow order m (p-1))

matrix_scalar order scalar value =
  let r11 = scalar * (value !! 0 !! 0) in
  let r12 = scalar * (value !! 0 !! 1) in
  let r21 = scalar * (value !! 1 !! 0) in
  let r22 = scalar * (value !! 1 !! 1) in
  [[r11,r12],[r21,r22]]    
