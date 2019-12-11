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
  | POW Token Integer
  | IDENTITY
  -- deriving Show
instance Show Token where
  show (NAME s) = s
  show (MULT []) = "EMPTY"
  show (MULT (x : xr)) = "(" ++ (foldr (\a b -> b ++ "*" ++ show a) (show x) (reverse xr)) ++ ")"
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
    
  let e = \cu m ch2 ->
        let b4 = base4 m in
        let cuf = b4 >>= \(m_at_i) -> return $ MULT [(cu `POW` m_at_i) , (ch2 `POW` (-1))] in
          MULT (cuf ++ [ch2 `POW` toInteger (length b4)])
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
           MULT [(ch2 `POW` (-1)) , cu , ch2 , (cu `POW` (-4))],
           MULT [(ch `POW` (-1)) , cu , ch , ((e cu (j ^ 2) ch2) `POW` (-1))],
           MULT [(ct `POW` 2)  ,  cu  ,  ((ct `POW` 2)  `POW` (-1))  ,  (cu `POW` (-1))],
           MULT [(ct `POW` (-1)) , ch , ct , ch],
           MULT [(ct `POW` (-1)) , cu , (ct `POW` (-1)) , cu , ct , cu],
           MULT [(ct `POW` (-1)) , (ch2 `POW` (-1)) , ceinvh2 , (ct `POW` (-1)) , (cu `POW` 2) , ct , ceinvh2],
           MULT [(ct `POW` (-1)) , (ch `POW` (-1)) , (e cu (inverse pq j) ch2) , (ct `POW` (-1)) , (e cu j ch2) , ct , (e cu (inverse pq j) ch2)]] in
    
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
evaluate dict pq (POW a b) =
  (evaluate dict pq a) >>= \ma ->
  Right $ matrix_pow pq ma b
evaluate _ _ IDENTITY = Right identity
evaluate dict pq (NAME s) = lookup_in_list (NAME s) dict

token_eq :: Token -> Token -> Bool
token_eq (MULT l0) (MULT l1) =
  foldr (\(a,b) r -> token_eq a b && r) True (zip l0 l1)
token_eq (POW a b) (POW c d) = token_eq a c && b == d
token_eq (IDENTITY) (IDENTITY) = True
token_eq (NAME a) (NAME b) = a == b
token_eq _ _ = False

unfold_powers :: Token -> Token
unfold_powers (MULT l) =
  MULT (map unfold_powers l)
unfold_powers (POW (MULT l) (-1)) = MULT (reverse l >>= \x -> return $ POW x (-1))
unfold_powers (POW (POW a n) m) = unfold_powers $ POW (unfold_powers a) (n * m)
unfold_powers (POW a (-1)) = POW (unfold_powers a) (-1)
unfold_powers (POW a 1) = unfold_powers a
unfold_powers (POW a 0) = IDENTITY
unfold_powers (POW a n)
  | n < 0 = MULT (take (fromInteger (-n)) $ repeat (POW (unfold_powers a) (-1)))
  | n > 0 = MULT (take (fromInteger n) $ repeat (unfold_powers a))
unfold_powers (NAME t) = NAME t
unfold_powers IDENTITY = IDENTITY

-- TODO: Something goes wrong recursively (fixpoint fixes this)
mult_simplify :: Token -> Token
mult_simplify (MULT l) =
  MULT (map mult_simplify l >>= \x ->
           case x of
             MULT k -> map mult_simplify k
             v -> return $ mult_simplify v)
mult_simplify (POW v n) =  POW (mult_simplify v) n
mult_simplify v = v

mult_simplify_fix a =
  let ma = mult_simplify a in
    if token_eq ma a
    then ma
    else mult_simplify_fix ma

remove_identity (MULT l) =
  MULT (map remove_identity (filter (not . token_eq IDENTITY) l))
remove_identity (POW IDENTITY n) = IDENTITY
remove_identity (POW a 0) = IDENTITY
remove_identity (POW a n) = POW (remove_identity a) n
remove_identity t = t

remove_identity_fix a =
  let ra = remove_identity a in
    if token_eq ra a
    then ra
    else remove_identity_fix ra

normal_form_aux = remove_identity_fix . mult_simplify_fix . unfold_powers
normal_form a =
  let na = normal_form_aux a in
    if token_eq na a
    then na
    else normal_form na

reduced :: String -> Token -> Bool
reduced s (NAME t) = t == s
reduced s (POW t 1) = reduced s t
reduced s (POW t (-1)) = reduced s t
reduced s a = False

collapse :: Token -> Token
collapse (MULT (NAME s : NAME t : xr)) | s == t =
  collapse $ MULT $ POW (NAME s) 2 : xr
collapse (MULT (POW (NAME s) n : NAME t : xr)) | s == t =
  collapse $ MULT $ POW (NAME s) (n+1) : xr
collapse (MULT (NAME s : POW (NAME t) m : xr)) | s == t =
  collapse $ MULT $ POW (NAME s) (m+1) : xr
collapse (MULT (POW (NAME s) n : POW (NAME t) m : xr)) | s == t =
  collapse $ MULT $ POW (NAME s) (n+m) : xr
collapse (MULT (a : b : xr)) =
  MULT [collapse a, collapse $ MULT $ b : xr]
collapse (MULT [x]) = collapse x
collapse (MULT []) = IDENTITY
collapse (POW a 0) = IDENTITY
collapse (POW a n) = POW (collapse a) n
collapse (NAME a) = NAME a
collapse IDENTITY = IDENTITY

collapse_fix a =
  let ca = collapse a in
  if token_eq ca a
  then a
  else collapse_fix ca

simple_form =
  -- mult_simplify_fix . collapse_fix . 
  remove_identity_fix . mult_simplify_fix

simple_form_fix a =
  let sa = simple_form a in
  if token_eq sa a
  then a
  else simple_form_fix sa


move_to_rhs_aux :: String -> Token -> Token -> (Token,Token)
move_to_rhs_aux s (MULT ((NAME t) : xr)) rhs =
  if t == s
  then (MULT ((NAME t) : xr), rhs)
  else move_to_rhs_aux s (MULT xr) (MULT [(POW (NAME t) (-1)) , rhs])
move_to_rhs_aux s (NAME t) rhs =
  if s == t
  then (NAME t,rhs)
  else (IDENTITY,MULT [POW (NAME t) (-1) , rhs])
move_to_rhs_aux s (MULT (x : xr)) rhs =
  let (ra,rhs') = move_to_rhs_aux s x rhs in
  if token_eq ra IDENTITY
  then move_to_rhs_aux s (MULT xr) rhs'
  else (MULT (ra : xr),rhs')
move_to_rhs_aux s (POW (NAME t) n) rhs =
  if t == s
  then (POW (NAME t) n,rhs)
  else (IDENTITY, MULT [POW (NAME t) (-n) , rhs])
move_to_rhs_aux s a rhs = (a,rhs)

move_to_rhs :: String -> Token -> Token -> (Token,Token)
move_to_rhs s t rhs =
  let (x,rhs') = (move_to_rhs_aux s t rhs) in
  let flip = \v -> normal_form (POW v (-1)) in 
  let (y,rhs'') = move_to_rhs_aux s (flip x) (flip rhs') in
    (flip y , normal_form $ flip rhs'')

remove_tokens :: String -> Token -> Token
remove_tokens s t = normal_form . fst $ move_to_rhs s t IDENTITY
  
solvable :: String -> Token -> Bool
solvable s = (reduced s) . collapse_fix . (remove_tokens s) . normal_form

solve_for_token :: String -> Token -> Token
solve_for_token s t =
  let (rest,rhs) = move_to_rhs s (normal_form t) IDENTITY in
  if token_eq (collapse_fix rest) (NAME s)
  then collapse_fix $ rhs
  else collapse_fix $ POW rhs (-1)
  
replace_name_by_token :: String -> Token -> Token -> Token
replace_name_by_token s a (NAME t) =
  if s == t
  then a
  else (NAME t)
replace_name_by_token s a (MULT l) =
  MULT (map (replace_name_by_token s a) l)
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

-- TODO: This is the current bottleneck!
-- TODO: Tail recursion
-- TODO: Solve for all equalities (on the right side) / Dynamic!
find_solution_for_generator_token :: Token -> [Token] -> Maybe Token
find_solution_for_generator_token (NAME s) a = find_solution_for_generator s a
find_solution_for_generator_token _ _ = Nothing

data Trace =
    ADD_GENERATOR Token Token
  | REMOVE_GENERATOR Token Token
  | ADD_RELATION Token
  | REMOVE_RELATION Token
  deriving Show

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
remove_subsection (POW a n) b =
  if token_eq (POW a n) b
  then Right IDENTITY
  else
    case remove_subsection a b of
      Left c -> Left $ POW c n
      Right c -> Right $ POW c n
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
  let a' = simple_form_fix a in
  let b = NAME ("gen_" ++ show counter) in
  return $ Just ((b : rep, simple_form_fix (MULT [(POW b (-1)) , a']) : sym), ADD_GENERATOR b a' : rev_trace)
rep_by_index 1 (rep,sym) sample_algorithm _ rev_trace =
  (randomRIO (0,length rep - 1) >>= \i -> return $ (take i rep ++ drop (i+1) rep, rep !! i)) >>= \(rep',gen) ->
  do
    putStrLn $ " REP - GEN: " ++ "\n " ++ show rep' ++ "\n " ++ show gen
    return $
      (find_solution_for_generator_token gen sym) >>= \sol ->
      let sym' = map (simple_form . replace_token_by_token gen sol) sym in
        Just $ ((rep',sym'), REMOVE_GENERATOR gen sol : rev_trace)
rep_by_index 2 (rep,sym) sample_algorithm _ rev_trace =
  randomRIO (0,length sym - 1) >>= \i ->
  randomRIO (1,160) >>= \n -> -- 160?
  let rel = (POW (sym !! i) n) in
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
    return $ remove_identity $ MULT l'

-- sample_from_rep_2 :: Integer -> ([Token],[Token]) -> IO Token
-- sample_from_rep_2 k (rep,sym) =
--   let list_value = [0..(length rep - 1)] >>= \i ->
--         return $
--         (randomIO :: IO Bool) >>= \b ->
--         if b
--         then randomRIO (1,k) >>= \p -> return $ (POW (rep !! i) p)
--         else return $ IDENTITY
--   in
--     (sequence list_value) >>= \l ->
--     return $ simple_form $ MULT l

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
