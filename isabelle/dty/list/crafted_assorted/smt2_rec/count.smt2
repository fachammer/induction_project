(set-info :smt-lib-version 2.6)
(set-logic UFDT)
(set-info :category "crafted")
(declare-datatypes ((nat 0) (lst 0)) (((s (s0 nat)) (zero)) ((nil) (cons (cons0 nat) (cons1 lst)))))
(define-fun-rec cnt
  ((x nat) (xs lst)) nat
  (match xs
    ((nil zero)
     ((cons y ys) (ite (= x y) 
                    (s (cnt x ys)) 
                    (cnt x ys))))))

(define-fun-rec len
  ((xs lst)) nat
  (match xs
    ((nil zero)
     ((cons y ys) (s (len ys))))))

(define-fun-rec leq
  ((n nat) (m nat)) Bool
  (match n
    ((zero true)
     ((s x) (match m
             ((zero false)
              ((s y) (leq x y))))))))

(assert (forall ((n nat) (m nat)) (=> (leq n m) (leq n (s m)))))
; (assert (forall ((n nat) (m nat)) (= (leq n m) (or (exists ((n0 nat)) (and (= n zero) (= m n0))) (exists ((n0 nat) (m0 nat)) (and (= n (s n0)) (= m (s m0)) (leq n0 m0)))))))

(assert (not (forall ((n nat) (xs lst)) (leq (cnt n xs) (len xs)))))
(check-sat)