(set-info :smt-lib-version 2.6)
(set-logic UFDT)
(set-info :category "crafted")
(declare-datatypes ((nat 0) (lst 0)) (((s (s0 nat)) (zero)) ((nil) (cons (cons0 nat) (cons1 lst)))))

(declare-fun p (nat) Bool)

(define-fun-rec cnt
  ((xs lst)) nat
  (match xs
    ((nil zero)
     ((cons y ys) (ite (p y)
                    (s (cnt ys))
                    (cnt ys))))))

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

; (assert (forall ((n nat) (m nat)) (=> (leq n m) (leq n (s m)))))

; (assert (forall ((y nat)) (or (p y) (not (p y)))))
(assert (not (forall ((xs lst)) (leq (cnt xs) (len xs))))) 
;(assert (not (forall ((ys lst) (y nat)) (=> (leq (cnt ys) (len ys)) (and (=> (not (p y)) (leq (cnt (cons y ys)) (len (cons y ys))))
 ;                                                                        (=> (p y) (leq (cnt (cons y ys)) (len (cons y ys)))))))))
;(assert (not (forall ((ys lst) (y nat)) (=> (leq (cnt ys) (len ys)) (not (p y)) (leq (cnt ys) (s (len ys)))))))

(check-sat)