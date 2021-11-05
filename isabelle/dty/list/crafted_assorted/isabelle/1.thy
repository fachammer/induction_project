theory 1
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

fun len :: "lst \<Rightarrow> nat" where
"len nil = zero" |
"len (cons e l) = s (len l)"

lemma "add (len x) (len y) = len (app x y)"
  apply(induction x)
   apply(auto)
  done

end