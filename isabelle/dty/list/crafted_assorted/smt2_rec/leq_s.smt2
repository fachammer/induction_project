(set-info :smt-lib-version 2.6)
(set-logic UFDT)
(set-info :category "crafted")
(declare-datatypes ((nat 0)) (((s (s0 nat)) (zero))))

(define-fun-rec leq
  ((n nat) (m nat)) Bool
  (match n
    ((zero true)
     ((s x) (match m
             ((zero false)
              ((s y) (leq x y))))))))

(assert (not (forall ((n nat) (m nat)) (=> (leq n m) (leq n (s m))))))

(check-sat)