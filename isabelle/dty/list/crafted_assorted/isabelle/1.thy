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

notepad
begin
(*
have "\<forall>x. \<forall>y. add (len x) (len y) = len (app x y)"
proof
fix x
show "\<forall>y. add (len x) (len y) = len (app x y)"
proof(induct x)
case nil
then show ?case by simp
next
case (cons x1 x)
then show ?case using cons.hyps by simp
qed
qed
*)

fix sK0
fix sK1
assume induction_formula: "(\<And>x1. \<And>x0. (len (app nil sK0) = add (len nil) (len sK0)
              \<Longrightarrow> len (app x1 sK0) = add (len x1) (len sK0)
              \<Longrightarrow> len (app (cons x0 x1) sK0) = add (len (cons x0 x1)) (len sK0)))
              \<Longrightarrow> (\<And>x2. (len (app x2 sK0) = add (len x2) (len sK0)))"

and goal_negated_skolemised: "len (app sK1 sK0) \<noteq> add (len sK1) (len sK0)"
then have "False"
by simp

end

end