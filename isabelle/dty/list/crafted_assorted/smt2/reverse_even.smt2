(set-info :smt-lib-version 2.6)
(set-logic UFDT)
(set-info :category "crafted")
(declare-datatypes ((nat 0) (lst 0)) (((s (s0 nat)) (zero)) ((nil) (cons (cons0 nat) (cons1 lst)))))
(declare-fun snoc (lst nat) lst)
(declare-fun rev (lst) lst)
(declare-fun even (nat) Bool)
(declare-fun rev_n (nat lst) lst)
(assert (forall ((x nat)) (= (snoc nil x) (cons x nil))))
(assert (forall ((xs lst) (x nat) (y nat) ) (= (snoc (cons x xs) y) (cons x (snoc xs y)))))
(assert (= (rev nil) nil))
(assert (forall ((xs lst) (x nat) ) (= (rev (cons x xs)) (snoc (rev xs) x))))
(assert (forall ((xs lst)) (= (rev_n zero xs) xs)))
(assert (forall ((n nat) (xs lst)) (= (rev_n (s n) xs) (rev (rev_n n xs)))))
(assert (= true (even zero)))
(assert (forall ((n nat)) (=> (even n) (even (s (s n))))))

; lemmas
;(assert (forall ((xs lst) (x nat)) (= (rev (snoc xs x)) (cons x (rev xs)))))
;(assert (not (forall ((xs lst) (x nat)) (= (rev (snoc xs x)) (cons x (rev xs))))))

;(assert (forall ((xs lst)) (= xs (rev (rev xs)))))
;(assert (not (forall ((xs lst)) (= xs (rev (rev xs))))))

; goal
(assert (not (forall ((n nat) (xs lst)) (=> (even n) (= (rev_n n xs) xs)))))
(check-sat)