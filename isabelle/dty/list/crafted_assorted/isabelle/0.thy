theory 0
  imports Main
begin

datatype nat = zero | s nat
datatype lst = nil | cons nat lst

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add zero y = y" |
"add (s x) y = s (add x y)"

fun app :: "lst \<Rightarrow> lst \<Rightarrow> lst" where
"app nil r = r" |
"app (cons a l) r = cons a (app l r)"

notepad
begin
assume app_assoc_induction_rule:
  "\<forall>sK1.
    (app nil (app sK1 sK1) = app (app nil sK1) sK1
     \<longrightarrow> (\<forall>x1.\<forall>x0. (app x1 (app sK1 sK1) = app (app x1 sK1) sK1
        \<longrightarrow> app (cons x0 x1) (app sK1 sK1) = app (app (cons x0 x1) sK1) sK1) )
     \<longrightarrow> (\<forall>x2. app x2 (app sK1 sK1) = app (app x2 sK1) sK1))"

assume add_s_induction_rule:
  "\<forall>sK0.\<forall>sK1.
    (add zero (s sK0) = s (add zero sK0)
     \<longrightarrow> (\<forall>x0. add x0 (s sK0) = s (add x0 sK0)
        \<longrightarrow> add (s x0) (s sK0) = s (add (s x0) sK0))
     \<longrightarrow> (\<forall>x1. add x1 (s sK0) = s (add x1 sK0)))"

have "\<forall>n. \<forall>x. app (cons (add n (s n)) x) (app x x) = app (app (cons (add (s n) n) x) x) x"
using app_assoc_induction_rule add_s_induction_rule
by simp

end

end
