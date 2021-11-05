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

lemma add_successor [simp]: "add x (s y) = s (add x y)"
  apply(induction x)
  by auto

lemma app_assoc [simp]: "app x (app y z) = app (app x y) z"
  apply(induction x)
  by auto

lemma "app (cons (add n (s n)) x) (app x x) = app (app (cons (add (s n) n) x) x) x"
  by auto

end