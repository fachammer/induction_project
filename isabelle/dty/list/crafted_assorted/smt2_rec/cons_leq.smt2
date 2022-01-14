(set-info :smt-lib-version 2.6)
(set-logic UFDT)
(set-info :category "crafted")
(declare-datatypes ((nat 0) (lst 0)) (((s (s0 nat)) (zero)) ((nil) (cons (cons0 nat) (cons1 lst)))))

(declare-fun p (nat) Bool)

(define-fun-rec list-half
  ((xs lst)) lst
  (match xs
    ((nil nil)
     ((cons y ys) (match ys 
                     ((nil nil)
                      ((cons z zs) (cons y (list-half zs)))))))))

(define-fun-rec length
  ((xs lst)) nat
  (match xs
    ((nil zero)
     ((cons y ys) (s (length ys))))))

(define-fun-rec leq
  ((n nat) (m nat)) Bool
  (match n
    ((zero true)
     ((s x) (match m
             ((zero false)
              ((s y) (leq x y))))))))

(assert (not (forall ((xs lst) (x nat)) (leq (length xs) (length (cons x xs))))))

(check-sat)