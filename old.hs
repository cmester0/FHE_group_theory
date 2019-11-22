sl2_fq_rep :: (Integer,Integer,Integer) -> IO ([(String,[[Integer]])],[(String,[[Integer]])])
sl2_fq_rep (p,q,pq) =
  find_generator pq p q >>= \j ->

  let mm = (matrix_mult pq) in
  let mi = (matrix_inverse pq) in
  let mp = (matrix_pow pq) in

  let cmm = (\a b -> a ++ "*" ++ b) in
  let cmp = (\a n -> "("++a++"^("++n++"))") in
  let cmi = (\a -> cmp a "-1") in
    
  let e = \(cu,u) m (ch2,h2) ->
        let b4 = base4 m in
        let uf = b4 >>= \(m_at_i) ->
              return $
              (u `mp` m_at_i) `mm` (h2 `mp` (-1))
        in
        let uf' = foldr (mm) [[1,0],[0,1]] (uf ++ [h2 `mp` toInteger (length b4)]) in
        let cuf = b4 >>= \(m_at_i) ->
              return $
              cu `cmp` show m_at_i `cmm` (cmi ch2)
        in
        let cuf' = foldr (cmm) "" (cuf ++ [ch2 `cmp` show (length b4)]) in
          (cuf',uf')
  in
    
  let u = [[1,1],[0,1]] in
  let t = [[0,1],[-1,0]] in
  let h2 = [[inverse pq 2,0],[0,2]] in
  let h = [[inverse pq j,0],[0,j]] in

  let u_inverse = mi u in
  let u_inverse_2 = u_inverse `mm` u_inverse in
  let u_inverse_4 = u_inverse_2 `mm` u_inverse_2 in

  let cu = "u" in
  let ct = "t" in
  let ch2 = "h2" in
  let ch = "h" in

  let s = [(cu,u),(ch2,h2),(ch,h),(ct,t)] in  

  let (ceuj,euj) = e (cu,u) (j ^ 2) (ch2,h2) in 
  let (ceinvh2,einvh2) = e (cu,u) (inverse pq 2) (ch2,h2) in
  let (ceuinvh2,euinvh2) = e (cu,u) (inverse pq j) (ch2,h2) in
  let (ceujh2,eujh2) = e (cu,u) j (ch2,h2) in
    
  let r = [e (cu,u) p (ch2,h2),
           
           ((cmi ch2) `cmm` cu `cmm` ch2 `cmm` (cmp cu "-4"),
            (mi h2) `mm` u `mm` h2 `mm` u_inverse_4),
            
           ((cmi ch) `cmm` cu `cmm` ch `cmm` (cmi ceuj),
            (mi h) `mm` u `mm` h `mm` (mi euj)),
            
           ((ct `cmp` "2" `cmm` cu `cmm` (cmi (ct `cmp` "2")) `cmm` (cmi cu)),
            (t `mp` 2) `mm` u `mm` (mi (t `mp` 2)) `mm` (mi u)),
            
           ((cmi ct) `cmm` ch `cmm` ct `cmm` ch,
             (mi t) `mm` h `mm` t `mm` h),

           ((cmi ct) `cmm` cu `cmm` (cmi ct) `cmm` cu `cmm` ct `cmm` cu,
            (mi t) `mm` u `mm` (mi t) `mm` u `mm` t `mm` u),

            ((cmi ct) `cmm` (cmi ch2) `cmm` ceinvh2 `cmm` (cmi ct) `cmm` (cu `cmp` "2") `cmm` ct `cmm` ceinvh2,
             (mi t) `mm` (mi h2) `mm` einvh2 `mm` (mi t) `mm` (u `mp` 2) `mm` t `mm` einvh2),
            
           ((cmi ct) `cmm` (cmi ch) `cmm` ceuinvh2 `cmm` (cmi ct) `cmm` ceujh2 `cmm` ct `cmm` ceuinvh2,
            (mi t) `mm` (mi h) `mm` euinvh2 `mm` (mi t) `mm` eujh2 `mm` t `mm` euinvh2)
          ] in
  return $
  (s,r)
