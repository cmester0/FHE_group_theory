module TokenSimplification where

import GroupRepresentation
-- SIMPLIFY TOKEN EXPRESSION
simplify_token_expression :: Token -> Token

-- POW
simplify_token_expression (POW a 0) = IDENTITY
simplify_token_expression (POW IDENTITY n) = IDENTITY
simplify_token_expression (POW a 1) = simplify_token_expression a
simplify_token_expression (POW (POW a n) m) =
  let sa = (simplify_token_expression a) in
  POW sa (n*m)
simplify_token_expression (POW (MULT a b) n) | n > 0 =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    MULT (POW sa n) (POW sb n)
simplify_token_expression (POW (MULT a b) n) | n < 0 =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    MULT (POW sb n) (POW sa n)
  
-- MULT
simplify_token_expression (MULT IDENTITY a) = simplify_token_expression a
simplify_token_expression (MULT a IDENTITY) = simplify_token_expression a
simplify_token_expression (MULT (POW IDENTITY n) (POW b m)) = POW b m
simplify_token_expression (MULT (POW a n) (POW IDENTITY m)) = POW a n
simplify_token_expression (MULT (POW a n) (POW b m)) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    if token_eq sa sb
    then POW sa (n+m)
    else
      let smsa = simplify_token_expression (POW sa n) in
      let smsb = simplify_token_expression (POW sb m) in      
      MULT smsa smsb

simplify_token_expression (MULT (POW a n) (MULT (POW IDENTITY m) c)) = MULT (POW a n) c
simplify_token_expression (MULT (POW IDENTITY n) (MULT (POW b m) c)) = MULT (POW b m) c
simplify_token_expression (MULT (POW a n) (MULT (POW b m) IDENTITY)) = MULT (POW a n) (POW b m)
simplify_token_expression (MULT (POW a n) (MULT (POW b m) c)) = 
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in
    if token_eq sa sb
    then MULT (POW sb (n+m)) sc
    else
      let spsa = simplify_token_expression (POW sa n) in
      if token_eq sb sc
      then MULT spsa (POW sb (m+1))
      else
        let smsbsc = simplify_token_expression (MULT (POW sb m) sc) in
        MULT spsa smsbsc

simplify_token_expression (MULT a (MULT (POW IDENTITY n) (POW c m))) = MULT a (POW c m)
simplify_token_expression (MULT a (MULT (POW b n) (POW IDENTITY m))) = MULT a (POW b n)
simplify_token_expression (MULT a (MULT (POW b n) (POW c m))) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in      
    if token_eq sb sc
    then MULT sa (POW sb (n+m))
    else
      let spsc = simplify_token_expression (POW sc m) in
      if token_eq sa sb
      then MULT (POW sb (n+1)) spsc
      else
        let spsb = simplify_token_expression (POW sb n) in
        MULT sa (MULT spsb spsc)  
           
simplify_token_expression (MULT a (MULT IDENTITY c)) = MULT a c
simplify_token_expression (MULT a (MULT b IDENTITY)) = MULT a b
simplify_token_expression (MULT (POW a n) (MULT b c)) = 
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in
    if token_eq sa sb
    then MULT (POW sb (n+1)) sc
    else
      if token_eq sb sc
      then MULT sa (POW sb 2)
      else
        let spa = simplify_token_expression (POW a n) in
        let smsbsc = simplify_token_expression (MULT sb sc) in
        MULT spa smsbsc      

simplify_token_expression (MULT (POW a n) b) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    if token_eq sa sb
    then POW sa (n+1)
    else
      let spsa = simplify_token_expression (POW sa n) in
      MULT spsa sb
simplify_token_expression (MULT a (MULT (POW b m) c)) =
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in
    if token_eq sa sb
    then MULT (POW sa (m+1)) sc
    else
      if token_eq sb sc
      then MULT sa (POW sb (m+1))
      else
        let smsbsc = simplify_token_expression (MULT (POW sb m) sc) in
        MULT sa smsbsc
      
simplify_token_expression (MULT a (MULT b c)) = 
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
  let sc = simplify_token_expression c in
    if token_eq sa sb
    then MULT (POW sb 2) sc
    else
      if token_eq sb sc
      then MULT sa (POW sb 2)
      else
        let smsbsc = simplify_token_expression (MULT sb sc) in
        MULT sa smsbsc      

simplify_token_expression (MULT a (POW b m)) = 
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    if token_eq sa sb
    then POW sb (m+1)
    else
      let spsb = simplify_token_expression (POW sb m) in
      MULT sa spsb

-- Recurse cases:
simplify_token_expression (POW a n) = POW (simplify_token_expression a) n
simplify_token_expression (MULT a b) = 
  let sa = simplify_token_expression a in
  let sb = simplify_token_expression b in
    if token_eq sa sb
    then POW sa 2
    else MULT sa sb
simplify_token_expression (NAME a) = (NAME a)
simplify_token_expression IDENTITY = IDENTITY

simplify_token_expression_fix expr =
  let sexpr = left_mult_simplify (simplify_token_expression expr) in
  if token_eq sexpr expr
  then expr
  else simplify_token_expression_fix sexpr
