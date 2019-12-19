module GroupRepresentation where

import Data.Maybe
import Data.List
import System.Random

import PrimeNumbers
import Group
import Matrix

fq :: Integer -> IO (Integer,Integer)
fq k = large_prime k

data Token =
  NAME String
  | MULT [Token]
  | INV Token
  | IDENTITY
  -- deriving Show
instance Show Token where
  show (NAME s) = s
  show (MULT []) = "EMPTY"
  show (MULT (x : xr)) = "(" ++ (foldr (\a b -> b ++ "*" ++ show a) (show x) (reverse xr)) ++ ")"
  show (INV a) = show a ++ "^-1"
  show (IDENTITY) = "I"

remove_identity :: Token -> Token
remove_identity (MULT l) =
  let l' = (l >>= \a ->
           case a of
             IDENTITY -> []
             x -> return (remove_identity x)) in
  case l' of
    [] -> IDENTITY
    _ -> MULT l'
remove_identity (INV IDENTITY) = IDENTITY
remove_identity (INV a) = INV (remove_identity a)
remove_identity (NAME s) = (NAME s)
remove_identity IDENTITY = IDENTITY

-- Equality for tokens
token_eq_aux :: Token -> Token -> Bool
token_eq_aux (MULT l0) (MULT l1) = foldr (\(a,b) r -> token_eq_aux a b && r) True (zip l0 l1)
token_eq_aux (INV a) (INV b) = token_eq_aux a b
token_eq_aux (IDENTITY) (IDENTITY) = True
token_eq_aux (NAME a) (NAME b) = a == b
token_eq_aux _ _ = False

token_eq a b = token_eq_aux (remove_identity a) (remove_identity b)

-- Knuth Bendix algorithm
knuth_bendix :: Token -> Token
knuth_bendix (MULT l) =
  case map knuth_bendix l of
    [] -> IDENTITY
    [x] -> x
    l' -> MULT l'

knuth_bendix (INV (MULT l)) = knuth_bendix $ MULT . map (INV) . reverse $ l
knuth_bendix (INV (INV a)) = knuth_bendix a
knuth_bendix (INV IDENTITY) = IDENTITY
knuth_bendix (INV (NAME s)) = INV (NAME s)

knuth_bendix (NAME s) = NAME s
knuth_bendix IDENTITY = IDENTITY

-- Flatten multiplication
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

-- Remove inverse
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

remove_inverse :: Token -> Token
remove_inverse (MULT l) =
  case l of
    [] -> MULT []
    (c : cs) -> MULT (remove_x_inv_x c cs)
remove_inverse (INV a) = INV (remove_inverse a)
remove_inverse a = a

-- Knuth_bendix normal form (fixpoint)
knuth_bendix_fix x =  
  let kx = knuth_bendix . remove_identity . remove_inverse . remove_identity . flatten_mult . remove_identity $ x in
    if token_eq kx x
    then kx
    else knuth_bendix_fix kx

-- Definition of power
mult_pow :: Token -> Integer -> [Token]
mult_pow a n | n > 0 = take (fromInteger n) $ repeat a
mult_pow a n | n < 0 = take (fromInteger (-n)) $ repeat (INV a)
mult_pow a 0 = []

pow a 0 = IDENTITY
pow a 1 = a
pow a (-1) = INV a
pow a n = MULT $ mult_pow a n

-- Subsection removal helper functions
remove_while_not_eq [] _ = ([],[])
remove_while_not_eq (x : xs) h =
  if token_eq x h
  then ([], x : xs)
  else
    let (f,b) = remove_while_not_eq xs h in
      (x : f, b)

find_seq :: [Token] -> [Token] -> [Token]
find_seq l l' =
  let (t',b') = remove_while_not_eq l (head l') in
    if foldr (&&) True $ map (\(a,b) -> token_eq a b) (zip b' l')
    then t' ++ drop (length l') b'
    else t' ++ (head b') : find_seq (tail b') l'

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
      case a of
        MULT l' ->
          Right . MULT $ find_seq tokens l'
        _ ->
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

remove_subsection a b =
  case remove_subsection_aux (knuth_bendix_fix a) (knuth_bendix_fix b) of
    Right x -> Right (knuth_bendix_fix x)
    Left x -> Left x

remove_subsection_list :: Token -> [Token] -> Either Token Token
remove_subsection_list x [] = Left x
remove_subsection_list x (y : ys) =
  case remove_subsection x y of
    Right x' ->
      case remove_subsection_list x' ys of
        Right y' -> Right y'
        Left y' -> Right y'
    Left x' ->
      remove_subsection_list x' ys

-- Normal form, reduce everything to a normal form (TODO: broken?)
normal_form :: [Token] -> Token -> Token
normal_form rel x = 
  let relinv = map INV rel in
    case remove_subsection_list (knuth_bendix_fix x) (map knuth_bendix_fix (rel ++ relinv)) of
      Left y -> knuth_bendix_fix $ y
      Right y -> knuth_bendix_fix $ y



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


-- Evaluation
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
  -- foldl (\b a -> evaluate dict pq a >>= \x ->  b >>= \y -> Right $ matrix_mult pq y x) (Right identity) l
  foldr (\a b -> evaluate dict pq a >>= \x -> b >>= \y ->Right $ matrix_mult pq y x) (Right identity) l

-- Random permutation of list
random_order_aux :: [Token] -> [Token] -> IO [Token]
random_order_aux [] l' = return l'
random_order_aux l l' =
  randomRIO (0 , (length l-1)) >>= \i ->
  random_order_aux (take i l ++ drop (i+1) l) (l !! i : l')

random_order :: [Token] -> IO [Token]
random_order l = random_order_aux l []
  
-- Create a sample list, and a sample algorithm for uniform sampling over a presentation
cube :: [Token] -> IO Token
cube gen =
  let list_value = gen >>= \x ->
        return $
        (randomIO :: IO Bool) >>= \e ->
        if e
        then return $ x
        else return $ IDENTITY
  in
    (sequence list_value) >>= \l ->
    random_order l >>= \l' ->
    return $ MULT (filter (not . token_eq IDENTITY) l')

create_sample_list_aux :: Int -> ([Token],[Token]) -> IO [[Token]]
create_sample_list_aux m (gen,sym) | m < length gen = return [gen]
create_sample_list_aux m (gen,sym) =
  create_sample_list_aux (m-1) (gen,sym) >>= \sample_lists ->
  let sl = sample_lists !! (m-length gen) in
  cube sl >>= \ym ->
  cube sl >>= \zm ->
  return ((MULT [INV ym, zm] : sl) : sample_lists)

create_sample_list :: Integer -> ([Token],[Token]) -> IO [Token]
create_sample_list m (gen,sym) =
  create_sample_list_aux (fromInteger m) (gen,sym) >>= \sample_lists ->
  return $ sample_lists !! (fromInteger m-length gen)

-- Solve relation for generator
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
move_to_rhs rel s t rhs =
  let (x,rhs') = (move_to_rhs_aux s t rhs) in
  let flip = \v -> normal_form rel (INV v) in
  let (y,rhs'') = move_to_rhs_aux s (flip x) (flip rhs') in
    (flip y , normal_form rel $ flip rhs'')

remove_tokens :: [Token] -> String -> Token -> Token
remove_tokens rel s t = (normal_form rel) . fst $ move_to_rhs rel s t IDENTITY

reduced s (INV t) = reduced s t
reduced s (NAME t) = s == t
reduced s _ = False
  
solvable :: [Token] -> String -> Token -> Bool
solvable rel s = (reduced s) . (remove_tokens rel s) . (normal_form rel)

solve_for_token :: [Token] -> String -> Token -> Token
solve_for_token rel s t =
  let (rest,rhs) = move_to_rhs rel s (normal_form rel t) IDENTITY in
  if token_eq (normal_form rel rest) (NAME s)
  then normal_form rel $ rhs
  else normal_form rel $ INV rhs

find_solution_for_generator :: [Token] -> String -> [Token] -> Maybe Token
find_solution_for_generator rel s (h:hs) =
  let relsubh = filter (not . token_eq h) rel in
  if solvable [] s h
  then Just $ solve_for_token [] s h
  else find_solution_for_generator rel s hs
find_solution_for_generator _ _ [] = Nothing

-- Replace token by token
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

find_solution_for_generator_token :: Token -> [Token] -> Maybe Token
find_solution_for_generator_token (NAME s) rel = find_solution_for_generator rel s rel
find_solution_for_generator_token _ _ = Nothing

-- Assumption knuth_bendix normal form
remove_relation :: [Token] -> [Token] -> Maybe (Token,[Token])
remove_relation [] _ = Nothing
remove_relation (x : rel') rel =
  let x' = knuth_bendix_fix x in
  let relsubx = filter (not . token_eq x) rel in
  let relsubxinv = map INV relsubx in
  case remove_subsection_list x' (map knuth_bendix_fix (relsubx ++ relsubxinv)) of
    Left _ -> remove_relation rel' rel
    Right y ->
      if token_eq y IDENTITY
      then Just (x',relsubx)
      else Nothing

-- Data structure for Trace of Tietze transformation
data Trace =
    ADD_GENERATOR Token Token
  | REMOVE_GENERATOR Token Token
  | ADD_RELATION Token
  | REMOVE_RELATION Token
  deriving Show

-- Tietze transformations
rep_by_index :: Integer -> ([Token],[Token]) -> IO Token -> Integer -> [Trace] -> IO (Maybe (([Token],[Token]),[Trace]))
rep_by_index 0 (gen,sym) sample_algorithm counter rev_trace =
  sample_algorithm >>= \a ->
  let b = NAME ("gen_" ++ show counter) in
  return $ Just ((b : gen, knuth_bendix_fix (MULT [INV b , a]) : sym), ADD_GENERATOR b (knuth_bendix_fix a) : rev_trace)
rep_by_index 1 (gen,sym) _ _ rev_trace =
  (randomRIO (0,length gen - 1) >>= \i -> return $ (take i gen ++ drop (i+1) gen, gen !! i)) >>= \(gen',gen) ->
  do
    putStrLn $ " REP - GEN: " ++ "\n " ++ show gen' ++ "\n " ++ show gen
    return $
      (find_solution_for_generator_token gen sym) >>= \sol ->
      let sym' = map (knuth_bendix_fix . replace_token_by_token gen sol) sym in
        Just $ ((gen',sym'), REMOVE_GENERATOR gen sol : rev_trace)
rep_by_index 2 (gen,sym) sample_algorithm _ rev_trace =
  (random_order sym >>= cube . (take 3)) >>= \l -> -- Size here should vary!
  let rel = knuth_bendix_fix l in
  let sym' = rel : sym in
    return $ Just $ ((gen,sym'), ADD_RELATION rel : rev_trace)
rep_by_index 3 (gen,sym) sample_algorithm counter rev_trace =
  do
    putStrLn $ " Length: " ++ show (length sym)
    randomRIO (0,length sym-1) >>= \i ->
      return $ remove_relation [sym !! i] sym >>= \(rel,sym') ->
      Just ((gen,sym'), REMOVE_RELATION rel : rev_trace)  

-- Do random Tietze transformations
rep_randomizer :: ([Token],[Token]) -> IO Token -> Integer -> [Trace] -> [Integer] -> IO (([Token],[Token]),[Trace])
rep_randomizer (gen,sym) sample_algorithm counter rev_trace ban =
  randomRIO (0,3) >>= \r ->
  case filter (\x -> r == x) ban of
      [] -> 
        do
          putStrLn $ "Choice: " ++ show r
          rep_by_index r (gen,sym) sample_algorithm counter rev_trace >>= \i ->
            if isJust i
            then return $ fromJust i
            else rep_randomizer (gen,sym) sample_algorithm counter rev_trace (r : ban)
      _ ->
        rep_randomizer (gen,sym) sample_algorithm counter rev_trace ban

random_tietze_aux :: ([Token],[Token]) -> ([Trace] -> IO Token) -> [Trace] -> Integer -> Integer -> IO (([Token],[Token]),[Trace])
random_tietze_aux rep _ rev_trace _ 0 = return (rep,rev_trace)
random_tietze_aux rep sample rev_trace counter i =
  do
    putStrLn $ "\nTietze Iteration: " ++ show i
    rep_randomizer rep (sample rev_trace) counter rev_trace [] >>= \(rep,rev_trace) -> random_tietze_aux rep sample rev_trace (counter+1) (i-1)

random_tietze :: ([Token],[Token]) -> ([Trace] -> IO Token) -> Integer -> IO (([Token],[Token]),[Trace])
random_tietze rep sample i =
  do
    putStrLn "Start of Tietze obfuscation"
    random_tietze_aux rep sample [] 0 i


-- Reduce group structure by removing generators and relations.
reduce_group_representation_generators_aux :: ([Token],[Token]) -> [Trace] -> IO (([Token],[Token]),[Trace])
reduce_group_representation_generators_aux ([],rel) rev_trace = return (([],rel),rev_trace)
reduce_group_representation_generators_aux (g : gen,rel) rev_trace =
  maybe (reduce_group_representation_generators_aux (gen,rel) rev_trace >>= \rep ->
         do
           putStrLn ("GEN ITER " ++ show g ++ " FAIL")
           return $ ((g : fst (fst rep), snd (fst rep)), snd rep))
  (\sol ->
     let rel' = filter (not . token_eq IDENTITY) $ map (knuth_bendix_fix . replace_token_by_token g (knuth_bendix_fix sol)) rel in
      do
        putStrLn ("GEN ITER " ++ show g ++ " SUCC")
        reduce_group_representation_generators_aux (gen,rel') (REMOVE_GENERATOR g sol : rev_trace))
  (find_solution_for_generator_token g (map knuth_bendix_fix rel))

reduce_group_representation_generators :: ([Token],[Token]) -> [Trace] -> IO (([Token],[Token]),[Trace])
reduce_group_representation_generators rep rev_trace =
  random_order (fst rep) >>= \fs -> reduce_group_representation_generators_aux (fs, snd rep) rev_trace

removing_relation_fix :: (([Token],[Token]),[Trace]) -> IO (([Token],[Token]),[Trace])
removing_relation_fix ((gen,rel),rev_trace) =
  let rel' = map knuth_bendix_fix rel in
    maybe
      (do
          putStrLn ("REL ITER " ++ show (length rel) ++ " FAIL")
          return ((gen,rel'),rev_trace))
      (\(r,rel'') ->
           do
             putStrLn ("REL ITER " ++ show (length rel) ++ " SUCC")
             removing_relation_fix ((gen,rel''), REMOVE_RELATION r : rev_trace))
      (remove_relation rel' rel')
                                    
reduce_group_representation :: (([Token],[Token]),[Trace]) -> IO (([Token],[Token]),[Trace])
reduce_group_representation (rep,rev_trace) =
  do
    putStrLn "Start of reduction"
    reduce_group_representation_generators rep rev_trace >>= removing_relation_fix

-- lookup algorithm
find_token_index t [] = -1
find_token_index t (h : rep) =
  if token_eq t h
  then 0
  else find_token_index t rep + 1

-- Calculate isomorphism and its inverse from (rev_)trace.
calculate_value_from_rev_trace :: [Trace] -> ([Token],[Token]) -> Token -> Token
calculate_value_from_rev_trace [] _ value = value
calculate_value_from_rev_trace (ADD_GENERATOR g sol : rev_trace) (gen,sym) value =
  let sym' = map (replace_token_by_token g sol) sym in
  let index = find_token_index g gen in
  let gen' = (take index gen ++ drop (index+1) gen) in
  calculate_value_from_rev_trace rev_trace (gen',sym') (replace_token_by_token g sol value)    
calculate_value_from_rev_trace (REMOVE_GENERATOR a b : rev_trace) (gen,sym) value =
  calculate_value_from_rev_trace rev_trace (a : gen, b : sym) (value)
calculate_value_from_rev_trace (ADD_RELATION rel : trace) (gen,sym) value =
  calculate_value_from_rev_trace trace (gen,filter (not . token_eq rel) sym) value
calculate_value_from_rev_trace (REMOVE_RELATION rel : trace) (gen,sym) value =
  calculate_value_from_rev_trace trace (gen,rel : sym) value

-- Inverse isomorphism
calculate_value_from_trace :: [Trace] -> ([Token],[Token]) -> Token -> Token
calculate_value_from_trace [] _ value = value
calculate_value_from_trace (ADD_GENERATOR a b : trace) (gen,sym) value =
  calculate_value_from_trace trace (a : gen, b : sym) (value)
calculate_value_from_trace (REMOVE_GENERATOR g sol : trace) (gen,sym) value =
  let sym' = map (replace_token_by_token g sol) sym in
  let index = find_token_index g gen in
  let gen' = (take index gen ++ drop (index+1) gen) in
  calculate_value_from_trace trace (gen',sym') (replace_token_by_token g sol value)    
calculate_value_from_trace (ADD_RELATION rel : trace) (gen,sym) value =
  calculate_value_from_trace trace (gen,rel : sym) value
calculate_value_from_trace (REMOVE_RELATION rel : trace) (gen,sym) value =
  calculate_value_from_trace trace (gen,filter (not . token_eq rel) sym) value

