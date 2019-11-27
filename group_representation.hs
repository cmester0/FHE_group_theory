module GroupRepresentation where

import Data.Maybe
import Data.List
import System.Random

import PrimeNumbers
import Group
import Matrix

fq :: Integer -> IO (Integer, Integer, Integer)
fq k = randomRIO (1,k) >>= \q -> (large_prime k) >>= \p -> return (p,q,p ^ q)

data Token =
  NAME String
  | MULT Token Token
  | POW Token Integer
  | IDENTITY
  deriving Show

base4 :: Integer -> [Integer]
base4 m =
  if m < 4
  then [m]
  else mod m 4 : base4 (div m 4)

sl2_fq_rep_sym :: (Integer,Integer,Integer) -> (String,String,String,String) -> IO ([(Token,[[Integer]])],[Token])
sl2_fq_rep_sym (p,q,pq) (su,st,sh2,sh) =
  find_generator pq p q >>= \j ->

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

  let s = [(cu,u),(ch2,h2),(ch,h),(ct,t)] in  

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
  (s,r)

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

evaluate :: Token -> [(Token,[[Integer]])] -> Integer -> Maybe [[Integer]]
evaluate (MULT a b) dict pq =
  (evaluate a dict pq) >>= \ma ->
  (evaluate b dict pq) >>= \mb ->
  return $
  matrix_mult pq ma mb
evaluate (POW a b) dict pq =
  (evaluate a dict pq) >>= \ma ->
  return $
  matrix_pow pq ma b
evaluate (IDENTITY) _ _ = Just identity
evaluate (NAME s) dict pq = lookup_in_list (NAME s) dict
  
-- evaluate (POW a b) dict = 

-- TODO: FIX s t s^-2 has order 3 not 1 !!

-- SIMPLIFY TOKEN EXPRESSION
simplify_token_expression :: Token -> Token

simplify_token_expression (POW a 0) = IDENTITY
simplify_token_expression (POW IDENTITY n) = IDENTITY
simplify_token_expression (POW a 1) = simplify_token_expression a

simplify_token_expression (POW (POW a n) m) =
  let sa = (simplify_token_expression a) in
  POW sa (n*m)
  
simplify_token_expression (MULT IDENTITY a) =
  simplify_token_expression a
simplify_token_expression (MULT a IDENTITY) =
  simplify_token_expression a

simplify_token_expression (POW (MULT a b) n) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    MULT (POW sa n) (POW sb n)

simplify_token_expression (MULT a (MULT b c)) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in
  (MULT (MULT sa sb) sc)

simplify_token_expression (MULT (MULT a b) c) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in
  (MULT (MULT sa sb) sc)

simplify_token_expression (POW a n) = POW (simplify_token_expression a) n
simplify_token_expression (MULT a b) =
  let sa = (simplify_token_expression a) in
  let sb = (simplify_token_expression b) in
    if token_eq sa sb
    then POW sa 2
    else MULT sa sb

simplify_token_expression (NAME a) = (NAME a)
simplify_token_expression a = a -- TODO FILL OUT ALL CASES

simplify_token_expression_fix expr =
  let sexpr = (simplify_token_expression expr) in
  if token_eq sexpr expr
  then expr
  else simplify_token_expression_fix sexpr

-- ORDER OF NAME IN TOKEN
order_of_name_in_token :: String -> Token -> Integer
order_of_name_in_token s (MULT a (MULT b c)) =
  let oa = order_of_name_in_token s a in
  let ob = order_of_name_in_token s b in
  let oc = order_of_name_in_token s c in
    if ob == 0
    then oa - oc
    else oa + ob + oc    
order_of_name_in_token s (MULT a b) = order_of_name_in_token s a + order_of_name_in_token s b
order_of_name_in_token s (NAME a) =
  if s == a
  then 1
  else 0
order_of_name_in_token s (IDENTITY) = 0
order_of_name_in_token s (POW a b) = order_of_name_in_token s a * b

-- SIMPLE ORDER OF NAME
order_of_name_in_token_simple :: String -> Token -> Integer
order_of_name_in_token_simple s t =
  order_of_name_in_token s t


-- SOLVE FOR TOKEN
solve_for_token :: String -> Token -> Token -> Token  
solve_for_token s (MULT a b) rhs =
  if order_of_name_in_token_simple s b == 0
  then solve_for_token s a (MULT rhs (POW b (-1)))
  else
    if order_of_name_in_token_simple s a == 0
    then solve_for_token s b (MULT (POW a (-1)) rhs)
    else
      let rhs' = solve_for_token s b rhs in
      solve_for_token s a rhs'

solve_for_token s (POW a 0) rhs = rhs
solve_for_token s (POW a b) rhs = 
  if b > 0
  then
    solve_for_token s (MULT a (POW a (b-1))) rhs
  else
    solve_for_token s (POW a (-b)) (POW rhs (-1))
    
solve_for_token s (IDENTITY) rhs = rhs
solve_for_token s (NAME b) rhs = rhs

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
  let s_h_order = order_of_name_in_token s h in
  if s_h_order == 1 || s_h_order == -1
  then Just $ solve_for_token s h IDENTITY
  else find_solution_for_generator s sym
find_solution_for_generator s [] = Nothing

find_solution_for_generator_token :: Token -> [Token] -> Maybe Token
find_solution_for_generator_token (NAME s) a = find_solution_for_generator s a
find_solution_for_generator_token _ _ = Nothing

  -- if s_h_order == 1 || s_h_order == -1
  -- then replace_name_by_token (solve_for_token s h)
  -- else remove_generator s sym

data Trace =
    ADD_GENERATOR (Token,[[Integer]]) Token
  | REMOVE_GENERATOR (Token,[[Integer]]) Token
  deriving Show

-- Representation by strings:
-- TODO: ADD TRACE
rep_by_index :: Integer -> ([(Token,[[Integer]])],[Token]) -> IO (Token,[[Integer]]) -> Integer -> [Trace] -> IO (([(Token,[[Integer]])],[Token]),[Trace])
rep_by_index 0 (rep,sym) sample_algorithm counter rev_trace = sample_algorithm >>= \a ->
  let b = (NAME ("gen_" ++ show counter), snd a) in
  let c = (fst a) in -- simplify_token_expression_fix
  return $ ((b : rep, c : sym), ADD_GENERATOR b c : rev_trace)
rep_by_index 1 (rep,sym) sample_algorithm _ rev_trace =
  (randomRIO (0,length rep - 1) >>= \i -> return $ (take i rep ++ drop (i+1) rep, (rep !! i))) >>= \(rep',gen') ->
  let gen = fst gen' in
  let solution = (find_solution_for_generator_token gen sym) in
    if isJust solution
    then
      let sol = (fromJust solution) in -- simplify_token_expression_fix
      let sym' = map (replace_token_by_token gen sol) sym in
      -- let sym'' = map (simplify_token_expression_fix) sym' in
      return $ ((rep',sym'),REMOVE_GENERATOR gen' sol : rev_trace)
    else return $ ((rep,sym),rev_trace)
-- rep_by_index 2 (rep,sym) sample_algorithm = TODO ADD RELATION
-- rep_by_index 3 (rep,sym) sample_algorithm = TODO REMOVE RELATION

rep_randomizer :: ([(Token,[[Integer]])],[Token]) -> IO (Token,[[Integer]]) -> Integer -> [Trace] -> IO (([(Token,[[Integer]])],[Token]),[Trace])
rep_randomizer (rep,sym) sample_algorithm counter rev_trace =
  randomRIO (0,1) >>= \r -> -- TODO: (0,3)
  rep_by_index r (rep,sym) sample_algorithm counter rev_trace

find_token_index t [] = -1
find_token_index t (h : rep) =
  if token_eq t h
  then 0
  else find_token_index t rep + 1

calculate_value_from_rev_trace :: [Trace] -> ([(Token,[[Integer]])],[Token]) -> Token -> Token
calculate_value_from_rev_trace [] _ value = -- simplify_token_expression_fix
  value
calculate_value_from_rev_trace (ADD_GENERATOR gen sol : rev_trace) (rep,sym) value =
  let sym' = map (replace_token_by_token (fst gen) sol) sym in
  -- let sym'' = map (simplify_token_expression_fix) sym' in
  let index = find_token_index (fst gen) (map fst rep) in
  let rep' = (take index rep ++ drop (index+1) rep) in
  calculate_value_from_rev_trace rev_trace (rep',sym') (-- simplify_token_expression_fix
                                                         (replace_token_by_token (fst gen) sol value))    
calculate_value_from_rev_trace (REMOVE_GENERATOR a b : rev_trace) (rep,sym) value =
  calculate_value_from_rev_trace rev_trace (a : rep, b : sym) (value) -- TODO, (replace_token_by_token b (fst a) value)


-- Sample random element using a representation: // TODO: is this correct sampling?
sample_from_rep :: ([(Token,[[Integer]])],[Token]) -> Integer -> IO (Token,[[Integer]])
sample_from_rep (rep,sym) pq =
  let list_value = [0..(length rep - 1)] >>= \i ->
        return $
        (randomIO :: IO Bool) >>= \e ->
        if e
        then return $ rep !! i
        else return $ (IDENTITY,identity)
  in
    (sequence list_value) >>= \l ->
    return $
    (foldr (\(ca,ma) (cb,mb) -> (MULT ca cb, matrix_mult pq ma mb)) (IDENTITY,identity) l)

sample_from_rep_2 :: Integer -> ([(Token,[[Integer]])],[Token]) -> Integer -> IO (Token,[[Integer]])
sample_from_rep_2 k (rep,sym) pq =
  let list_value = [0..(length rep - 1)] >>= \i ->
        return $
        randomRIO (0,k) >>= \p ->
        let (r1,r2) = rep !! i in
        return $ (-- simplify_token_expression_fix
                  (POW r1 p),matrix_pow pq r2 p)
  in
    (sequence list_value) >>= \l ->
    return $
    (foldr (\(ca,ma) (cb,mb) -> (MULT ca cb, matrix_mult pq ma mb)) (IDENTITY,identity) l)


apply_n_times :: Integer -> (a -> IO a) -> IO a -> IO a
apply_n_times 0 f v = v
apply_n_times n f v = apply_n_times (n-1) f v >>= f

random_tietze_aux :: ([(Token,[[Integer]])],[Token]) -> (([(Token,[[Integer]])],[Token]) -> IO (Token,[[Integer]])) -> [Trace] -> Integer -> Integer -> IO (([(Token,[[Integer]])],[Token]),[Trace])
random_tietze_aux rep _ rev_trace _ 0 = return (rep,rev_trace)
random_tietze_aux rep sample rev_trace counter i =
  rep_randomizer rep (sample rep) counter rev_trace >>= \(rep,rev_trace) ->
  random_tietze_aux rep sample rev_trace (counter+1) (i-1)

random_tietze :: ([(Token,[[Integer]])],[Token]) -> (([(Token,[[Integer]])],[Token]) -> IO (Token,[[Integer]])) -> Integer -> IO (([(Token,[[Integer]])],[Token]),[Trace])
random_tietze rep sample i =
  random_tietze_aux rep sample [] 0 i
