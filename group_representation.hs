module GroupRepresentation where

import Data.Maybe
import Data.List
import System.Random

import PrimeNumbers
import Group
import Matrix

-- fq :: Integer -> IO (Integer, Integer, Integer)
-- fq k =
--   randomRIO (1,k) >>= \q ->
--   (large_prime k) >>= \p ->
--   return (p,q,p ^ q)

-- DON'T USE PRIME POWER

fq :: Integer -> IO (Integer,Integer)
fq k = large_prime k


data Token =
  NAME String
  | MULT Token Token
  | POW Token Integer
  | IDENTITY
instance Show Token where
  show (NAME s) = s
  show (MULT a b) = show a ++ "*" ++ "(" ++ show b ++ ")"
  show (POW a n) = "(" ++ show a ++ ")^" ++ "(" ++ show n ++ ")"
  show (IDENTITY) = "I"

base4 :: Integer -> [Integer]
base4 m =
  if m < 4
  then [m]
  else mod m 4 : base4 (div m 4)

sl2_fq_rep_sym :: (Integer,Integer,Integer) -> (String,String,String,String) -> IO (([Token],[Token]),[[[Integer]]])
sl2_fq_rep_sym (p,q,pq) (su,st,sh2,sh) =
  find_generator pq p q 1 >>= \j ->

  let cmm = (\a b -> MULT a b) in
  let cmp = (\a n -> POW a n) in
  let cmi = (\a -> POW a (-1)) in
    
  let e = \cu m ch2 ->
        let b4 = base4 m in
        let cuf = b4 >>= \(m_at_i) ->
              return $
              (cu `cmp` m_at_i) `cmm` (cmi ch2)
        in
          foldr (cmm) IDENTITY (cuf ++ [ch2 `cmp` toInteger (length b4)])
  in

  let u = [[1,1],[0,1]] in
  let t = [[0,1],[-1,0]] in
  let h2 = [[inverse pq 2,0],[0,2]] in
  let h = [[inverse pq j,0],[0,j]] in
    
  let cu = NAME su in
  let ct = NAME st in
  let ch2 = NAME sh2 in
  let ch = NAME sh in

  let ceuj = e cu (j ^ 2) ch2 in 
  let ceinvh2 = e cu (inverse pq 2) ch2 in
  let ceuinvh2 = e cu (inverse pq j) ch2 in
  let ceujh2 = e cu j ch2 in
    
  let r = [e cu p ch2,
           (cmi ch2) `cmm` cu `cmm` ch2 `cmm` (cu `cmp` (-4)),
           (cmi ch) `cmm` cu `cmm` ch `cmm` (cmi (e cu (j ^ 2) ch2)),
           (ct `cmp` 2) `cmm` cu `cmm` (cmi (ct `cmp` 2)) `cmm` (cmi cu),
           (cmi ct) `cmm` ch `cmm` ct `cmm` ch,
           (cmi ct) `cmm` cu `cmm` (cmi ct) `cmm` cu `cmm` ct `cmm` cu,
           (cmi ct) `cmm` (cmi ch2) `cmm` ceinvh2 `cmm` (cmi ct) `cmm` (cu `cmp` 2) `cmm` ct `cmm` ceinvh2,
           (cmi ct) `cmm` (cmi ch) `cmm` (e cu (inverse pq j) ch2) `cmm` (cmi ct) `cmm` (e cu j ch2) `cmm` ct `cmm` (e cu (inverse pq j) ch2)] in
  return $
  (([cu,ct,ch2,ch],r),[u,t,h2,h])

token_eq :: Token -> Token -> Bool
token_eq (MULT a b) (MULT c d) = token_eq a c && token_eq b d
token_eq (POW a b) (POW c d) = token_eq a c && b == d
token_eq (IDENTITY) (IDENTITY) = True
token_eq (NAME a) (NAME b) = a == b
token_eq _ _ = False

lookup_in_list :: Token -> [(Token,a)] -> Maybe a
lookup_in_list a ((b,c):rest) =
  if token_eq a b
  then Just c
  else lookup_in_list a rest
lookup_in_list _ [] = Nothing

evaluate :: [(Token,[[Integer]])] -> Integer -> Token -> Maybe [[Integer]]
evaluate dict pq (MULT a b) =
  (evaluate dict pq a) >>= \ma ->
  (evaluate dict pq b) >>= \mb ->
  return $
  matrix_mult pq ma mb
evaluate dict pq (POW a b) =
  (evaluate dict pq a) >>= \ma ->
  return $
  matrix_pow pq ma b
evaluate _ _ (IDENTITY) = Just identity
evaluate dict pq (NAME s) = lookup_in_list (NAME s) dict

-- SIMPLIFY TOKEN EXPRESSION
-- simplify_token_expression :: Token -> Token

-- simplify_token_expression (POW a 0) = IDENTITY
-- simplify_token_expression (POW IDENTITY n) = IDENTITY
-- simplify_token_expression (POW a 1) = simplify_token_expression a

-- simplify_token_expression (POW (POW a n) m) =
--   let sa = (simplify_token_expression a) in
--   POW sa (n*m)
  
-- simplify_token_expression (MULT IDENTITY a) =
--   simplify_token_expression a
-- simplify_token_expression (MULT a IDENTITY) =
--   simplify_token_expression a

-- simplify_token_expression (POW (MULT a b) n) =
--   let sa = simplify_token_expression a in
--   let sb = simplify_token_expression b in
--     MULT (POW sa n) (POW sb n)

-- simplify_token_expression (MULT a (MULT b c)) =
--   let sa = simplify_token_expression a in
--   let sb = simplify_token_expression b in
--   let sc = simplify_token_expression c in
--   (MULT (MULT sa sb) sc)

-- simplify_token_expression (MULT (MULT a b) c) =
--   let sa = simplify_token_expression a in
--   let sb = simplify_token_expression b in
--   let sc = simplify_token_expression c in
--   (MULT (MULT sa sb) sc)

-- simplify_token_expression (POW a n) = POW (simplify_token_expression a) n
-- simplify_token_expression (MULT a b) =
--   let sa = simplify_token_expression a in
--   let sb = simplify_token_expression b in
--     if token_eq sa sb
--     then POW sa 2
--     else MULT sa sb

-- simplify_token_expression (NAME a) = (NAME a)
-- simplify_token_expression IDENTITY = IDENTITY

-- simplify_token_expression_fix expr =
--   let sexpr = (simplify_token_expression expr) in
--   if token_eq sexpr expr
--   then expr
--   else simplify_token_expression_fix sexpr

left_mult_simplify :: Token -> Token
left_mult_simplify (MULT (MULT a b) c) =
  let ma = left_mult_simplify a in
  let mb = left_mult_simplify b in
  let mc = left_mult_simplify c in
  MULT ma (MULT mb mc)
left_mult_simplify (POW a n) =
  let ma = left_mult_simplify a in
  POW ma n
left_mult_simplify IDENTITY = IDENTITY
left_mult_simplify (NAME s) = NAME s
left_mult_simplify (MULT a b) =
  let ma = left_mult_simplify a in
  let mb = left_mult_simplify b in
  MULT ma mb

right_mult_simplify :: Token -> Token
right_mult_simplify (MULT a (MULT b c)) =
  let ma = right_mult_simplify a in
  let mb = right_mult_simplify b in
  let mc = right_mult_simplify c in
  MULT (MULT ma mb) mc
right_mult_simplify (POW a n) =
  let ma = right_mult_simplify a in
  POW ma n
right_mult_simplify IDENTITY = IDENTITY
right_mult_simplify (NAME s) = NAME s
right_mult_simplify (MULT a b) =
  let ma = right_mult_simplify a in
  let mb = right_mult_simplify b in
  MULT ma mb

unfold_powers :: Token -> Token
unfold_powers (MULT a b) =
  let ua = unfold_powers a in
  let ub = unfold_powers b in
  MULT ua ub
unfold_powers (POW a (-1)) = POW (unfold_powers a) (-1)
unfold_powers (POW a n) | n < 0 = 
  let ua = unfold_powers a in
  MULT (POW ua (-1)) (unfold_powers (POW  ua (n+1)))
unfold_powers (POW a 1) = unfold_powers a
unfold_powers (POW a n) | n > 0 =   
  let ua = unfold_powers a in
  MULT ua (unfold_powers (POW  ua (n-1)))
unfold_powers (POW a 0) = IDENTITY
unfold_powers (NAME t) = NAME t
unfold_powers IDENTITY = IDENTITY

normal_form_left = left_mult_simplify . unfold_powers
normal_form_right = right_mult_simplify . unfold_powers

reduced :: String -> Token -> Bool
reduced s (NAME t) = t == s
reduced s (POW t 1) = reduced s t
reduced s (POW t (-1)) = reduced s t
reduced s a = False

collapse :: Token -> Token
collapse (MULT (NAME a) (NAME b)) =
  if a == b
  then POW (NAME a) 2
  else MULT (NAME a) (NAME b)
collapse (MULT (POW (NAME a) n) (NAME b)) =
  if a == b
  then POW (NAME a) (n+1)
  else MULT (POW (NAME a) n) (NAME b)
collapse (MULT (NAME b) (POW (NAME a) n)) =  
  if a == b
  then POW (NAME a) (n+1)
  else MULT (NAME b) (POW (NAME a) n)
collapse (MULT (POW (NAME a) n) (POW (NAME b) m)) =
  if a == b
  then POW (NAME a) (n+m)
  else MULT (POW (NAME a) n) (POW (NAME b) m)
collapse (MULT a IDENTITY) = collapse a
collapse (MULT IDENTITY b) = collapse b
collapse (MULT a b) = MULT (collapse a) (collapse b)
collapse (POW a n) = POW (collapse a) n
collapse (NAME a) = NAME a
collapse IDENTITY = IDENTITY

collapse_fix a =
  let ca = collapse a in
  if token_eq ca a
  then a
  else collapse_fix ca

move_left_to_rhs :: String -> Token -> Token -> (Token,Token)
move_left_to_rhs s (MULT (NAME t) b) rhs =
  if t == s
  then (MULT (NAME t) b,rhs)
  else move_left_to_rhs s b (MULT (POW (NAME t) (-1)) rhs)
move_left_to_rhs s (NAME t) rhs =
  if s == t
  then (NAME t,rhs)
  else (IDENTITY,rhs)
move_left_to_rhs s (MULT a b) rhs =
  let (ra,rhs') = move_left_to_rhs s a rhs in
  if token_eq ra IDENTITY
  then move_left_to_rhs s b rhs'
  else (MULT ra b,rhs')
move_left_to_rhs s a rhs = (a,rhs)

move_right_to_rhs :: String -> Token -> Token -> (Token,Token)
move_right_to_rhs s (MULT a (NAME t)) rhs =
  if t == s
  then (MULT a (NAME t),rhs)
  else move_right_to_rhs s a (MULT rhs (POW (NAME t) (-1)))
move_right_to_rhs s (NAME t) rhs =
    if s == t
    then (NAME t,rhs)
    else (IDENTITY,rhs)
move_right_to_rhs s (MULT a b) rhs =
  let (rb,rhs') = move_right_to_rhs s b rhs in
  if token_eq rb IDENTITY
  then move_right_to_rhs s a rhs'
  else (MULT a rb,rhs')
move_right_to_rhs s a rhs = (a,rhs)

remove_left :: String -> Token -> Token
remove_left s t = fst $ move_left_to_rhs s t IDENTITY

remove_right :: String -> Token -> Token
remove_right s t = fst $ move_right_to_rhs s t IDENTITY
  
solvable :: String -> Token -> Bool
solvable s = (reduced s) . collapse_fix . (remove_right s) . normal_form_right . (remove_left s) . normal_form_left

solve_for_token :: String -> Token -> Token
solve_for_token s t =
  let (rest,rhs) = move_left_to_rhs s (normal_form_left t) IDENTITY in
  let (rest',rhs') = move_right_to_rhs s (normal_form_right rest) rhs in
    collapse_fix $ rhs'
  
replace_name_by_token :: String -> Token -> Token -> Token
replace_name_by_token s a (NAME t) =
  if s == t
  then a
  else (NAME t)
replace_name_by_token s a (MULT b c) =
  MULT (replace_name_by_token s a b) (replace_name_by_token s a c)
replace_name_by_token s a (POW b n) =
  POW (replace_name_by_token s a b) n
replace_name_by_token s a (IDENTITY) = IDENTITY

replace_token_by_token :: Token -> Token -> Token -> Token
replace_token_by_token (NAME t) a b = replace_name_by_token t a b
  
find_solution_for_generator :: String -> [Token] -> Maybe Token
find_solution_for_generator s (h:sym) =
  if solvable s h
  then Just $ solve_for_token s h
  else find_solution_for_generator s sym
find_solution_for_generator s [] = Nothing

find_solution_for_generator_token :: Token -> [Token] -> Maybe Token
find_solution_for_generator_token (NAME s) a = find_solution_for_generator s a
find_solution_for_generator_token _ _ = Nothing

data Trace =
    ADD_GENERATOR Token Token
  | REMOVE_GENERATOR Token Token
  deriving Show

-- Representation by strings:
-- TODO: ADD TRACE
rep_by_index :: Integer -> ([Token],[Token]) -> IO Token -> Integer -> [Trace] -> IO (([Token],[Token]),[Trace])
rep_by_index 0 (rep,sym) sample_algorithm counter rev_trace =
  sample_algorithm >>= \a ->
  let b = NAME ("gen_" ++ show counter) in
  return $ ((b : rep, MULT (POW b (-1)) a : sym), ADD_GENERATOR b a : rev_trace)
rep_by_index 1 (rep,sym) sample_algorithm _ rev_trace =
  (randomRIO (0,length rep - 1) >>= \i -> return $ (take i rep ++ drop (i+1) rep, rep !! i)) >>= \(rep',gen) ->
  let solution = (find_solution_for_generator_token gen sym) in
    if isJust solution
    then
      let sol = (fromJust solution) in 
      let sym' = map (replace_token_by_token gen sol) sym in
      return $ ((rep',sym'),REMOVE_GENERATOR gen sol : rev_trace)
    else return $ ((rep,sym),rev_trace)
-- rep_by_index 2 (rep,sym) sample_algorithm = TODO ADD RELATION
-- rep_by_index 3 (rep,sym) sample_algorithm = TODO REMOVE RELATION

rep_randomizer :: ([Token],[Token]) -> IO Token -> Integer -> [Trace] -> IO (([Token],[Token]),[Trace])
rep_randomizer (rep,sym) sample_algorithm counter rev_trace =
  randomRIO (0,1) >>= \r -> -- TODO: (0,3)
  rep_by_index r (rep,sym) sample_algorithm counter rev_trace

find_token_index t [] = -1
find_token_index t (h : rep) =
  if token_eq t h
  then 0
  else find_token_index t rep + 1

calculate_value_from_rev_trace :: [Trace] -> ([Token],[Token]) -> Token -> Token
calculate_value_from_rev_trace [] _ value = value
calculate_value_from_rev_trace (ADD_GENERATOR gen sol : rev_trace) (rep,sym) value =
  let sym' = map (replace_token_by_token gen sol) sym in
  let index = find_token_index gen rep in
  let rep' = (take index rep ++ drop (index+1) rep) in
  calculate_value_from_rev_trace rev_trace (rep',sym') (replace_token_by_token gen sol value)    
calculate_value_from_rev_trace (REMOVE_GENERATOR a b : rev_trace) (rep,sym) value =
  calculate_value_from_rev_trace rev_trace (a : rep, b : sym) (value)


calculate_value_from_trace :: [Trace] -> ([Token],[Token]) -> Token -> Token
calculate_value_from_trace [] _ value = value
calculate_value_from_trace (ADD_GENERATOR a b : trace) (rep,sym) value =
  calculate_value_from_trace trace (a : rep, b : sym) (value)
calculate_value_from_trace (REMOVE_GENERATOR gen sol : trace) (rep,sym) value =
  let sym' = map (replace_token_by_token gen sol) sym in
  let index = find_token_index gen rep in
  let rep' = (take index rep ++ drop (index+1) rep) in
  calculate_value_from_trace trace (rep',sym') (replace_token_by_token gen sol value)    

-- Sample random element using a representation: // TODO: is this correct sampling?
sample_from_rep :: ([Token],[Token]) -> Integer -> IO Token
sample_from_rep (rep,sym) pq =
  let list_value = [0..(length rep - 1)] >>= \i ->
        return $
        (randomIO :: IO Bool) >>= \e ->
        if e
        then return $ rep !! i
        else return $ IDENTITY
  in
    (sequence list_value) >>= \l ->
    return $
    (foldr (MULT) IDENTITY l)

sample_from_rep_2 :: Integer -> ([Token],[Token]) -> IO Token
sample_from_rep_2 k (rep,sym) =
  let list_value = [0..(length rep - 1)] >>= \i ->
        return $
        randomRIO (0,k) >>= \p ->
        if p == 0
        then return $ IDENTITY
        else return $ (POW (rep !! i) p)
  in
    (sequence list_value) >>= \l ->
    return $
    (foldr (MULT) IDENTITY l)


apply_n_times :: Integer -> (a -> IO a) -> IO a -> IO a
apply_n_times 0 f v = v
apply_n_times n f v = apply_n_times (n-1) f v >>= f

random_tietze_aux :: ([Token],[Token]) -> (([Token],[Token]) -> IO Token) -> [Trace] -> Integer -> Integer -> IO (([Token],[Token]),[Trace])
random_tietze_aux rep _ rev_trace _ 0 = return (rep,rev_trace)
random_tietze_aux rep sample rev_trace counter i =
  rep_randomizer rep (sample rep) counter rev_trace >>= \(rep,rev_trace) ->
  random_tietze_aux rep sample rev_trace (counter+1) (i-1)

random_tietze :: ([Token],[Token]) -> (([Token],[Token]) -> IO Token) -> Integer -> IO (([Token],[Token]),[Trace])
random_tietze rep sample i =
  random_tietze_aux rep sample [] 0 i
