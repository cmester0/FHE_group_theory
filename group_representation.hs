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

-- TODO: DO OR DON'T USE PRIME POWER ?

fq :: Integer -> IO (Integer,Integer)
fq k = large_prime k


data Token =
  NAME String
  | MULT [Token] -- Rewrite to list of tokens! (generalize)
  | INVERSE Token
  | IDENTITY
  -- deriving Show
instance Show Token where
  show (NAME s) = s
  show (MULT []) = "EMPTY"
  show (MULT (x : xr)) = "(" ++ (foldr (\a b -> b ++ "*" ++ show a) (show x) (reverse xr)) ++ ")"
  show (INVERSE a) = show a ++ "^-1"
  show (IDENTITY) = "I"

mult_pow :: Token -> Integer -> [Token]
mult_pow a n | n > 0 = take (fromInteger n) $ repeat a
mult_pow a n | n < 0 = take (fromInteger (-n)) $ repeat (INVERSE a)
mult_pow a 0 = []

pow a 0 = IDENTITY
pow a 1 = a
pow a (-1) = INVERSE a
pow a n = MULT $ mult_pow a n

-- Remove subsection by all other things in symbols:
remove_subsection :: Token -> Token -> Either Token Token
remove_subsection (MULT l) a =
  if token_eq a (MULT l)
  then Right IDENTITY
  else 
    let (change,tokens) = unzip (map (\x -> remove_subsection x a) l >>= \x ->
                                    case x of
                                      Left b -> return (False,b)
                                      Right b -> return (True,b))
    in
      if foldr (||) False change
      then Right $ MULT tokens
      else Left $ MULT tokens
remove_subsection (INVERSE a) b =
  if token_eq (INVERSE a) b
  then Right IDENTITY
  else
    case remove_subsection a b of
      Left c -> Left $ INVERSE c
      Right c -> Right $ INVERSE c
remove_subsection x a =
  if token_eq x a
  then Right IDENTITY
  else Left x

remove_subsection_list :: Token -> [Token] -> Either Token Token
remove_subsection_list x [] = Left x
remove_subsection_list x (y : ys) =
  case remove_subsection x y of
    Right x' ->
      case remove_subsection_list x' ys of
        Right y' -> Right y'
        Left y' -> Right y'
    Left x' -> remove_subsection_list x' ys


remove_x_inv_x a [] = [a]
remove_x_inv_x (INVERSE a) (b : xs) =
  if token_eq a b
  then remove_x_inv_x (head xs) (tail xs)
  else (INVERSE a) : remove_x_inv_x b xs
remove_x_inv_x a (INVERSE b : xs) =
  if token_eq a b
  then remove_x_inv_x (head xs) (tail xs)
  else a : remove_x_inv_x (INVERSE b) xs
remove_x_inv_x a (b : xs) = a : remove_x_inv_x b xs
  
-- Knuth Bendix algorithm
knuth_bendix :: Token -> Token
knuth_bendix (MULT l) =
  let remove_ident = filter (\a -> case a of
                                IDENTITY -> False
                                _ -> True) in
  let remove_inv = \l -> remove_x_inv_x (head l) (tail l) in
    MULT (remove_ident . remove_inv $ l)
knuth_bendix (INVERSE (MULT l)) = MULT . map (INVERSE) . reverse $ l
knuth_bendix (INVERSE (INVERSE a)) = knuth_bendix a
knuth_bendix (INVERSE IDENTITY) = IDENTITY
knuth_bendix t = t

normal_form sym x =
  case remove_subsection_list x sym of
    Left x -> knuth_bendix x
    Right x -> knuth_bendix x

-- Create representation
base4 :: Integer -> [Integer]
base4 m =
  if m < 4
  then [m]
  else mod m 4 : base4 (div m 4)

sl2_fq_rep_sym :: (Integer,Integer,Integer) -> (String,String,String,String) -> IO (([Token],[Token]),[[[Integer]]])
sl2_fq_rep_sym (p,q,pq) (su,st,sh2,sh) =
  find_generator pq p q 1 >>= \j ->
    
  let e = \cu m ch2 ->
        let b4 = base4 m in
        let cuf = b4 >>= \(m_at_i) -> return $ MULT $ cu `mult_pow` m_at_i ++ [INVERSE ch2] in
          cuf ++ ch2 `mult_pow` toInteger (length b4)
  in
  let u = [[1,1],[0,1]] in
  let t = [[0,1],[-1,0]] in
  let h2 = [[inverse pq 2,0],[0,2]] in
  let h = [[inverse pq j,0],[0,j]] in            

  let cu = NAME su in
  let ct = NAME st in
  let ch2 = NAME sh2 in
  let ch = NAME sh in

  let ceinvh2 = e cu (inverse pq 2) ch2 in
  let ceujh2 = e cu j ch2 in
  let ceuinvjh2 = e cu (inverse pq j) ch2 in
    
  let r = [MULT (e cu p ch2),
           MULT $ [INVERSE ch2 , cu , ch2 , INVERSE cu, INVERSE cu, INVERSE cu, INVERSE cu],
           MULT $ [INVERSE ch , cu , ch ] ++ (map (INVERSE) $ reverse $ e cu (j ^ 2) ch2),
           MULT $  [ct , ct  ,  cu  ,  INVERSE ct , INVERSE ct  ,  INVERSE cu],
           MULT $ [INVERSE ct , ch , ct , ch],
           MULT $ [INVERSE ct , cu , INVERSE ct , cu , ct , cu],
           MULT $ [INVERSE ct , INVERSE ch2] ++ ceinvh2 ++ [INVERSE ct , cu , cu , ct ] ++ ceinvh2,
           MULT $ [INVERSE ct , INVERSE ch ] ++ ceuinvjh2 ++ [ INVERSE ct ] ++ ceujh2 ++ [ ct ] ++ ceuinvjh2] in
    
  return (([cu,ct,ch2,ch],r),[u,t,h2,h])

lookup_in_list :: Token -> [(Token,a)] -> Either String a
lookup_in_list a ((b,c):rest) =
  if token_eq a b
  then Right c
  else lookup_in_list a rest
lookup_in_list a [] = Left . show $ a

evaluate :: [(Token,[[Integer]])] -> Integer -> Token -> Either String [[Integer]]
evaluate dict pq (MULT []) = Right identity
evaluate dict pq (MULT (x : xr)) =
  evaluate dict pq x >>= \mx ->
  evaluate dict pq (MULT xr) >>= \mxr ->
  Right $ matrix_mult pq mx mxr
evaluate dict pq (INVERSE a) =
  (evaluate dict pq a) >>= \ma ->
  Right $ matrix_inverse pq ma
evaluate _ _ IDENTITY = Right identity
evaluate dict pq (NAME s) = lookup_in_list (NAME s) dict

token_eq :: Token -> Token -> Bool
token_eq (MULT l0) (MULT l1) =
  foldr (\(a,b) r -> token_eq a b && r) True (zip l0 l1)
token_eq (INVERSE a) (INVERSE b) = token_eq a b
token_eq (IDENTITY) (IDENTITY) = True
token_eq (NAME a) (NAME b) = a == b
token_eq _ _ = False

move_to_rhs_aux :: String -> Token -> Token -> (Token,Token)
move_to_rhs_aux s (MULT ((NAME t) : xr)) rhs =
  if t == s
  then (MULT ((NAME t) : xr), rhs)
  else move_to_rhs_aux s (MULT xr) (MULT [INVERSE (NAME t) , rhs])
move_to_rhs_aux s (NAME t) rhs =
  if s == t
  then (NAME t,rhs)
  else (IDENTITY,MULT [INVERSE (NAME t) , rhs])
move_to_rhs_aux s (MULT (x : xr)) rhs =
  let (ra,rhs') = move_to_rhs_aux s x rhs in
  if token_eq ra IDENTITY
  then move_to_rhs_aux s (MULT xr) rhs'
  else (MULT (ra : xr),rhs')
move_to_rhs_aux s (INVERSE (NAME t)) rhs =
  if t == s
  then (INVERSE (NAME t),rhs)
  else (IDENTITY, MULT [NAME t , rhs])
move_to_rhs_aux s a rhs = (a,rhs)

move_to_rhs :: [Token] -> String -> Token -> Token -> (Token,Token)
move_to_rhs sym s t rhs =
  let (x,rhs') = (move_to_rhs_aux s t rhs) in
  let flip = \v -> normal_form sym (INVERSE v) in 
  let (y,rhs'') = move_to_rhs_aux s (flip x) (flip rhs') in
    (flip y , normal_form sym $ flip rhs'')

remove_tokens :: [Token] -> String -> Token -> Token
remove_tokens sym s t = (normal_form sym) . fst $ move_to_rhs sym s t IDENTITY

reduced s (INVERSE t) = reduced s t
reduced s (NAME t) = s == t
reduced s _ = False
  
solvable :: [Token] -> String -> Token -> Bool
solvable sym s = (reduced s) . (normal_form sym)

solve_for_token :: [Token] -> String -> Token -> Token
solve_for_token sym s t =
  let (rest,rhs) = move_to_rhs sym s (normal_form sym t) IDENTITY in
  if token_eq (normal_form sym rest) (NAME s)
  then normal_form sym $ rhs
  else normal_form sym $ INVERSE rhs
  
replace_name_by_token :: String -> Token -> Token -> Token
replace_name_by_token s a (NAME t) =
  if s == t
  then a
  else (NAME t)
replace_name_by_token s a (MULT l) =
  MULT (map (replace_name_by_token s a) l)
replace_name_by_token s a (INVERSE b) =
  INVERSE (replace_name_by_token s a b)
replace_name_by_token s a (IDENTITY) = IDENTITY

replace_token_by_token :: Token -> Token -> Token -> Token
replace_token_by_token (NAME t) a b = replace_name_by_token t a b
  
find_solution_for_generator :: [Token] -> String -> [Token] -> Maybe Token
find_solution_for_generator sym s (h:hs) =
  if solvable sym s h
  then Just $ solve_for_token sym s h
  else find_solution_for_generator sym s hs
find_solution_for_generator _ _ [] = Nothing

-- TODO: This is the current bottleneck!
-- TODO: Tail recursion
-- TODO: Solve for all equalities (on the right side) / Dynamic!
find_solution_for_generator_token :: Token -> [Token] -> Maybe Token
find_solution_for_generator_token (NAME s) sym = find_solution_for_generator sym s sym
find_solution_for_generator_token _ _ = Nothing

data Trace =
    ADD_GENERATOR Token Token
  | REMOVE_GENERATOR Token Token
  | ADD_RELATION Token
  | REMOVE_RELATION Token
  deriving Show

remove_relation :: [Token] -> [Token] -> Maybe (Token,[Token])
remove_relation [] _ = Nothing
remove_relation (x : sym') sym =
  let symsubx = filter (not . token_eq x) sym in
  case remove_subsection_list x symsubx of
    Left _ -> remove_relation sym' sym
    Right y ->
      if token_eq y IDENTITY
      then Just (x,symsubx)
      else Nothing

-- Representation by strings:
-- TODO: ADD TRACE
rep_by_index :: Integer -> ([Token],[Token]) -> IO Token -> Integer -> [Trace] -> IO (Maybe (([Token],[Token]),[Trace]))
rep_by_index 0 (rep,sym) sample_algorithm counter rev_trace =
  sample_algorithm >>= \a ->
  let a' = normal_form sym a in
  let b = NAME ("gen_" ++ show counter) in
  return $ Just ((b : rep, normal_form sym (MULT [INVERSE b , a']) : sym), ADD_GENERATOR b a' : rev_trace)
rep_by_index 1 (rep,sym) sample_algorithm _ rev_trace =
  (randomRIO (0,length rep - 1) >>= \i -> return $ (take i rep ++ drop (i+1) rep, rep !! i)) >>= \(rep',gen) ->
  do
    putStrLn $ " REP - GEN: " ++ "\n " ++ show rep' ++ "\n " ++ show gen
    return $
      (find_solution_for_generator_token gen sym) >>= \sol ->
      let sym' = map ((normal_form sym) . replace_token_by_token gen sol) sym in
        Just $ ((rep',sym'), REMOVE_GENERATOR gen sol : rev_trace)
rep_by_index 2 (rep,sym) sample_algorithm _ rev_trace =
  randomRIO (0,length sym - 1) >>= \i ->
  randomRIO (1,160) >>= \n -> -- 160?
  let rel = (pow (sym !! i) n) in
  let sym' = rel : sym in
  return $ Just $ ((rep,sym'), ADD_RELATION rel : rev_trace)
rep_by_index 3 (rep,sym) sample_algorithm _ rev_trace =
  do
    putStrLn $ " Length: " ++ show (length sym)
    return $ 
      remove_relation sym sym >>= \(rel,sym') -> Just ((rep,sym'), REMOVE_RELATION rel : rev_trace)  

rep_randomizer :: ([Token],[Token]) -> IO Token -> Integer -> [Trace] -> [Integer] -> IO (([Token],[Token]),[Trace])
rep_randomizer (rep,sym) sample_algorithm counter rev_trace ban =
  randomRIO (0,3) >>= \r ->
  case filter (\x -> r == x) ban of
      [] -> 
        do
          putStrLn $ "Choice: " ++ show r
          rep_by_index r (rep,sym) sample_algorithm counter rev_trace >>= \i ->
            if isJust i
            then return $ fromJust i
            else rep_randomizer (rep,sym) sample_algorithm counter rev_trace (r : ban)
      _ ->
        rep_randomizer (rep,sym) sample_algorithm counter rev_trace ban

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
calculate_value_from_rev_trace (ADD_RELATION rel : trace) (rep,sym) value =
  calculate_value_from_rev_trace trace (rep,filter (not . token_eq rel) sym) value
calculate_value_from_rev_trace (REMOVE_RELATION rel : trace) (rep,sym) value =
  calculate_value_from_rev_trace trace (rep,rel : sym) value

calculate_value_from_trace :: [Trace] -> ([Token],[Token]) -> Token -> Token
calculate_value_from_trace [] _ value = value
calculate_value_from_trace (ADD_GENERATOR a b : trace) (rep,sym) value =
  calculate_value_from_trace trace (a : rep, b : sym) (value)
calculate_value_from_trace (REMOVE_GENERATOR gen sol : trace) (rep,sym) value =
  let sym' = map (replace_token_by_token gen sol) sym in
  let index = find_token_index gen rep in
  let rep' = (take index rep ++ drop (index+1) rep) in
  calculate_value_from_trace trace (rep',sym') (replace_token_by_token gen sol value)    
calculate_value_from_trace (ADD_RELATION rel : trace) (rep,sym) value =
  calculate_value_from_trace trace (rep,rel : sym) value
calculate_value_from_trace (REMOVE_RELATION rel : trace) (rep,sym) value =
  calculate_value_from_trace trace (rep,filter (not . token_eq rel) sym) value

random_order_aux :: [Token] -> [Token] -> IO [Token]
random_order_aux [] l' = return l'
random_order_aux l l' =
  randomRIO (0 , (length l-1)) >>= \i ->
  random_order_aux (take i l ++ drop (i+1) l) (l !! i : l')

random_order :: [Token] -> IO [Token]
random_order l = random_order_aux l []
  
-- Sample random element using a representation: // TODO: is this correct sampling?
sample_from_rep :: ([Token],[Token]) -> IO Token
sample_from_rep (rep,sym) =
  let list_value = [0..(length rep - 1)] >>= \i ->
        return $
        (randomIO :: IO Bool) >>= \e ->
        if e
        then return $ rep !! i
        else return $ IDENTITY
  in
    (sequence list_value) >>= \l ->
    random_order l >>= \l' ->
    return $ normal_form sym $ MULT l'

sample_from_rep_3 :: Integer -> ([Token],[Token]) -> IO Token
sample_from_rep_3 k (rep,sym) =
  sequence ([0 .. 10] >>= \_ -> return $ sample_from_rep (rep,sym)) >>= \l ->
  sample_from_rep ((l ++ rep),sym)

apply_n_times :: Integer -> (a -> IO a) -> IO a -> IO a
apply_n_times 0 f v = v
apply_n_times n f v = apply_n_times (n-1) f v >>= f

random_tietze_aux :: ([Token],[Token]) -> (([Token],[Token]) -> IO Token) -> [Trace] -> Integer -> Integer -> IO (([Token],[Token]),[Trace])
random_tietze_aux rep _ rev_trace _ 0 = return (rep,rev_trace)
random_tietze_aux rep sample rev_trace counter i =
  do
    putStrLn $ "\nITERATION: " ++ show i
    rep_randomizer rep (sample rep) counter rev_trace [] >>= \(rep,rev_trace) -> random_tietze_aux rep sample rev_trace (counter+1) (i-1)

random_tietze :: ([Token],[Token]) -> (([Token],[Token]) -> IO Token) -> Integer -> IO (([Token],[Token]),[Trace])
random_tietze rep sample i =
  random_tietze_aux rep sample [] 0 i
