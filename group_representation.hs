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
  | INV Token
  | IDENTITY
  -- deriving Show
instance Show Token where
  show (NAME s) = s
  show (MULT []) = "EMPTY"
  show (MULT (x : xr)) = "(" ++ (foldr (\a b -> b ++ "*" ++ show a) (show x) (reverse xr)) ++ ")"
  show (INV a) = show a ++ "^-1"
  show (IDENTITY) = "I"

mult_pow :: Token -> Integer -> [Token]
mult_pow a n | n > 0 = take (fromInteger n) $ repeat a
mult_pow a n | n < 0 = take (fromInteger (-n)) $ repeat (INV a)
mult_pow a 0 = []

pow a 0 = IDENTITY
pow a 1 = a
pow a (-1) = INV a
pow a n = MULT $ mult_pow a n

-- Remove subsection by all other things in symbols:
remove_subsection_aux :: Token -> Token -> Either Token Token
remove_subsection_aux (MULT l) a =
  if token_eq a (MULT l)
  then Right IDENTITY
  else 
    let (change,tokens) = unzip (map (\x -> remove_subsection_aux x a) l >>= \x ->
                                    case x of
                                      Left b -> return (False,b)
                                      Right b -> return (True,b))
    in
      if foldr (||) False change
      then Right $ MULT tokens
      else Left $ MULT tokens
remove_subsection_aux (INV a) b =
  if token_eq (INV a) b
  then Right IDENTITY
  else
    case remove_subsection_aux a b of
      Left c -> Left $ INV c
      Right c -> Right $ INV c
remove_subsection_aux x a =
  if token_eq x a
  then Right IDENTITY
  else Left x

remove_subsection a b = remove_subsection_aux (knuth_bendix_fix a) (knuth_bendix_fix b)

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
remove_x_inv_x (INV a) (b : xs) =
  if token_eq a b
  then
    case xs of
      [] -> []
      (c : cs) -> remove_x_inv_x c cs
  else (INV a) : remove_x_inv_x b xs
remove_x_inv_x a (INV b : xs) =
  if token_eq a b
  then
    case xs of
      [] -> []
      (c : cs) -> remove_x_inv_x c cs
  else a : remove_x_inv_x (INV b) xs
remove_x_inv_x a (b : xs) = a : remove_x_inv_x b xs

list_flat_list :: [Token] -> [Token]
list_flat_list (MULT l : xs) = list_flat_list l ++ list_flat_list xs
list_flat_list (INV a : xs) = map (INV) (reverse (list_flat_list [a])) ++ list_flat_list xs
list_flat_list (NAME s : xs) = NAME s : (list_flat_list xs)
list_flat_list (IDENTITY : xs) = list_flat_list xs
list_flat_list [] = []

flatten_mult :: Token -> Token
flatten_mult (MULT l) = MULT (list_flat_list l)
flatten_mult (INV (MULT l)) = flatten_mult $ MULT (map (INV) (reverse l))
flatten_mult (INV a) = INV (flatten_mult a)
flatten_mult (NAME s) = NAME s
flatten_mult IDENTITY = IDENTITY

fix :: (Token -> Token) -> Token -> Token
fix f x =
  let fx = f x in
    if token_eq fx x
    then fx
    else fix f fx

remove_identity :: Token -> Token
remove_identity (MULT l) =
  MULT (l >>= \a ->
           case a of
             IDENTITY -> []
             x -> return (remove_identity x))
remove_identity (INV IDENTITY) = IDENTITY
remove_identity (INV a) = INV (remove_identity a)
remove_identity (NAME s) = (NAME s)
remove_identity IDENTITY = IDENTITY

remove_inverse :: Token -> Token
remove_inverse (MULT l) =
  case l of
    [] -> MULT []
    (c : cs) -> MULT (remove_x_inv_x c cs)
remove_inverse (INV a) = INV (remove_inverse a)
remove_inverse a = a

-- Knuth Bendix algorithm
knuth_bendix :: Token -> Token
knuth_bendix (MULT l) =
  case map knuth_bendix l of
    [] -> IDENTITY
    [x] -> x
    l' -> MULT l'
  -- Other case should never happen

knuth_bendix (INV (MULT l)) = knuth_bendix $ MULT . map (INV) . reverse $ l
knuth_bendix (INV (INV a)) = knuth_bendix a
knuth_bendix (INV IDENTITY) = IDENTITY
knuth_bendix (INV (NAME s)) = INV (NAME s)

knuth_bendix (NAME s) = NAME s
knuth_bendix IDENTITY = IDENTITY

knuth_bendix_fix x =  
  let kx = knuth_bendix . remove_identity . remove_inverse . remove_identity . flatten_mult . remove_identity $ x in
    if token_eq kx x
    then kx
    else knuth_bendix_fix kx

normal_form sym x =
  case remove_subsection_list x sym of
    Left x -> knuth_bendix_fix $ x
    Right x -> knuth_bendix_fix $ x

-- Create representation
base4 :: Integer -> [Integer]
base4 m =
  if m < 4
  then [m]
  else mod m 4 : base4 (div m 4)

sl2_fq_rep :: (Integer,Integer,Integer) -> (String,String,String,String) -> IO (([Token],[Token]),[[[Integer]]])
sl2_fq_rep (p,q,pq) (su,st,sh2,sh) =
  find_generator pq p q 1 >>= \j ->
    
  let e = \cu m ch2 ->
        let b4 = base4 m in
        let cuf = b4 >>= \(m_at_i) -> return $ MULT $ cu `mult_pow` m_at_i ++ [INV ch2] in
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
           MULT $ [INV ch2 , cu , ch2 , INV cu, INV cu, INV cu, INV cu],
           MULT $ [INV ch , cu , ch ] ++ (map (INV) $ reverse $ e cu (j ^ 2) ch2),
           MULT $  [ct , ct  ,  cu  ,  INV ct , INV ct  ,  INV cu],
           MULT $ [INV ct , ch , ct , ch],
           MULT $ [INV ct , cu , INV ct , cu , ct , cu],
           MULT $ [INV ct , INV ch2] ++ ceinvh2 ++ [INV ct , cu , cu , ct ] ++ ceinvh2,
           MULT $ [INV ct , INV ch ] ++ ceuinvjh2 ++ [ INV ct ] ++ ceujh2 ++ [ ct ] ++ ceuinvjh2] in
    
  return (([cu,ct,ch2,ch],r),[u,t,h2,h])

lookup_in_list :: Token -> [(Token,a)] -> Either String a
lookup_in_list a ((b,c):rest) =
  if token_eq a b
  then Right c
  else lookup_in_list a rest
lookup_in_list a [] = Left . show $ a

evaluate :: [(Token,[[Integer]])] -> Integer -> Token -> Either String [[Integer]]
evaluate dict pq (INV a) =
  evaluate dict pq a >>= \mx ->
  Right $ matrix_inverse pq mx
evaluate _ _ IDENTITY = Right identity
evaluate dict _ (NAME s) = lookup_in_list (NAME s) dict
evaluate dict pq (MULT l) = 
  foldl (\b a -> evaluate dict pq a >>= \x ->  b >>= \y -> Right $ matrix_mult pq y x) (Right identity) l
  -- foldr (\a b -> evaluate dict pq a >>= \x -> b >>= \y ->Right $ matrix_mult pq y x) (Right identity) l

token_eq :: Token -> Token -> Bool
token_eq (MULT l0) (MULT l1) =
  foldr (\(a,b) r -> token_eq a b && r) True (zip l0 l1)
token_eq (INV a) (INV b) = token_eq a b
token_eq (IDENTITY) (IDENTITY) = True
token_eq (NAME a) (NAME b) = a == b
token_eq _ _ = False

move_to_rhs_aux :: String -> Token -> Token -> (Token,Token)
move_to_rhs_aux s (MULT ((NAME t) : xr)) rhs =
  if t == s
  then (MULT ((NAME t) : xr), rhs)
  else move_to_rhs_aux s (MULT xr) (MULT [INV (NAME t) , rhs])
move_to_rhs_aux s (NAME t) rhs =
  if s == t
  then (NAME t,rhs)
  else (IDENTITY,MULT [INV (NAME t) , rhs])
move_to_rhs_aux s (MULT (x : xr)) rhs =
  let (ra,rhs') = move_to_rhs_aux s x rhs in
  if token_eq ra IDENTITY
  then move_to_rhs_aux s (MULT xr) rhs'
  else (MULT (ra : xr),rhs')
move_to_rhs_aux s (INV (NAME t)) rhs =
  if t == s
  then (INV (NAME t),rhs)
  else (IDENTITY, MULT [NAME t , rhs])
move_to_rhs_aux s a rhs = (a,rhs)

move_to_rhs :: [Token] -> String -> Token -> Token -> (Token,Token)
move_to_rhs sym s t rhs =
  let (x,rhs') = (move_to_rhs_aux s t rhs) in
  let flip = \v -> normal_form sym (INV v) in
  let (y,rhs'') = move_to_rhs_aux s (flip x) (flip rhs') in
    (flip y , normal_form sym $ flip rhs'')

remove_tokens :: [Token] -> String -> Token -> Token
remove_tokens sym s t = (normal_form sym) . fst $ move_to_rhs sym s t IDENTITY

reduced s (INV t) = reduced s t
reduced s (NAME t) = s == t
reduced s _ = False
  
solvable :: [Token] -> String -> Token -> Bool
solvable sym s = (reduced s) . (remove_tokens sym s) . (normal_form sym)

solve_for_token :: [Token] -> String -> Token -> Token
solve_for_token sym s t =
  let (rest,rhs) = move_to_rhs sym s (normal_form sym t) IDENTITY in
  if token_eq (normal_form sym rest) (NAME s)
  then normal_form sym $ rhs
  else normal_form sym $ INV rhs
  
replace_name_by_token :: String -> Token -> Token -> Token
replace_name_by_token s a (NAME t) =
  if s == t
  then a
  else (NAME t)
replace_name_by_token s a (MULT l) =
  MULT (map (replace_name_by_token s a) l)
replace_name_by_token s a (INV b) =
  INV (replace_name_by_token s a b)
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

-- Assumption knuth_bendix normal form
remove_relation :: [Token] -> [Token] -> Maybe (Token,[Token])
remove_relation [] _ = Nothing
remove_relation (x : sym') sym =
  let symsubx = filter (not . token_eq x) sym in
  let symsubxinv = map (knuth_bendix_fix . INV) symsubx in
  case remove_subsection_list x (symsubx ++ symsubxinv) of
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
  let b = NAME ("gen_" ++ show counter) in
  return $ Just ((b : rep, knuth_bendix_fix (MULT [INV b , a]) : sym), ADD_GENERATOR b (knuth_bendix_fix a) : rev_trace)
rep_by_index 1 (rep,sym) _ _ rev_trace =
  (randomRIO (0,length rep - 1) >>= \i -> return $ (take i rep ++ drop (i+1) rep, rep !! i)) >>= \(rep',gen) ->
  do
    putStrLn $ " REP - GEN: " ++ "\n " ++ show rep' ++ "\n " ++ show gen
    return $
      (find_solution_for_generator_token gen sym) >>= \sol ->
      let sym' = map (knuth_bendix_fix . replace_token_by_token gen sol) sym in
        Just $ ((rep',sym'), REMOVE_GENERATOR gen sol : rev_trace)
rep_by_index 2 (rep,sym) sample_algorithm _ rev_trace =
  sequence ([0..10] >>= \_ -> return $
          randomRIO (0,length sym - 1) >>= \i ->
          (randomIO :: IO Bool) >>= \b ->
            return $
            if b
            then (sym !! i)
            else IDENTITY) >>= \l ->
  let rel = knuth_bendix_fix $ MULT l in
  let sym' = rel : sym in
  return $ Just $ ((rep,sym'), ADD_RELATION rel : rev_trace)
rep_by_index 3 (rep,sym) sample_algorithm _ rev_trace =
  do
    putStrLn $ " Length: " ++ show (length sym)
    return $ remove_relation sym sym >>= \(rel,sym') -> Just ((rep,sym'), REMOVE_RELATION rel : rev_trace)  

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
cube :: [Token] -> IO Token
cube rep =
  let list_value = rep >>= \x ->
        return $
        (randomIO :: IO Bool) >>= \e ->
        if e
        then return $ x
        else return $ IDENTITY
  in
    (sequence list_value) >>= \l ->
    random_order l >>= \l' ->
    return $ MULT (filter (not . token_eq IDENTITY) l')

create_sample_list m (rep,sym) =
  let fm = \m -> 
        create_sample_list (m-1) (rep,sym) >>= \sample_list ->
        cube sample_list >>= \ym -> 
        cube sample_list >>= \zm ->
        return $ MULT [INV ym, zm]
  in
    foldr (\a b -> fm a >>= \x -> b >>= \y -> return $ y ++ [x]) (return rep) [(toInteger (length rep)) .. m]
    
  -- sequence ([0 .. 10] >>= \_ -> return $ sample_from_rep (rep,sym)) >>= \l ->
  -- sample_from_rep ((l ++ rep),sym)

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

reduce_group_representation_generators_aux :: ([Token],[Token]) -> [Trace] -> IO (([Token],[Token]),[Trace])
reduce_group_representation_generators_aux ([],rel) rev_trace = return (([],rel),rev_trace)
reduce_group_representation_generators_aux (g : gen,rel) rev_trace =
  maybe (reduce_group_representation_generators_aux (gen,rel) rev_trace >>=
         return . (\rep' -> ((g : fst (fst rep'), snd (fst rep')), snd rep')))
    (\sol -> return $
      maybe ((g:gen,rel),rev_trace) (\sol ->
        let rel' = map (knuth_bendix_fix . replace_token_by_token g sol) rel in
          ((g : gen,rel'), REMOVE_GENERATOR g sol : rev_trace)) (find_solution_for_generator_token g rel))
    (find_solution_for_generator_token g rel)

reduce_group_representation_generators :: ([Token],[Token]) -> [Trace] -> IO (([Token],[Token]),[Trace])
reduce_group_representation_generators rep rev_trace =
  random_order (fst rep) >>= \fs -> reduce_group_representation_generators_aux (fs, snd rep) rev_trace

removing_relation_fix :: (([Token],[Token]),[Trace]) -> IO (([Token],[Token]),[Trace])
removing_relation_fix ((gen,rel),rev_trace) =
  do
    putStrLn ("ITER " ++ show (length rel))
    maybe (return ((gen,map knuth_bendix_fix rel),rev_trace)) (\(r,rel') -> removing_relation_fix ((gen,rel'), REMOVE_RELATION r : rev_trace)) (remove_relation rel rel)
                                    
reduce_group_representation :: (([Token],[Token]) -> IO Token) -> Integer -> (([Token],[Token]),[Trace]) -> IO (([Token],[Token]),[Trace])
reduce_group_representation sample threshold (rep,rev_trace) =
  reduce_group_representation_generators rep rev_trace >>= \x ->
  do
    putStrLn . show . fst . fst $ x
    removing_relation_fix x
