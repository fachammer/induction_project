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

assume "\<not>(\<forall>xs.\<forall>ys. len (app xs ys) = add (len xs) (len ys))"
then have "\<exists>xs. \<exists>ys. len (app xs ys) \<noteq> add (len xs) (len ys)" by blast
then obtain sK1 where "\<exists>ys. len (app sK1 ys) \<noteq> add (len sK1) (len ys)" ..
then obtain sK0 where skolemised_negated_goal: "len (app sK1 sK0) \<noteq> add (len sK1) (len sK0)" ..
then have induction_base: "len (app nil sK0) = add (len nil) (len sK0)" by simp
then have induction_step: "(\<And>x0.\<And>x1. (len (app x1 sK0) = add (len x1) (len sK0) \<Longrightarrow> len (app (cons x0 x1) sK0) = add (len (cons x0 x1)) (len sK0)))" by simp

assume induction_formula: "(len (app nil sK0) = add (len nil) (len sK0))
              \<Longrightarrow> (\<And>x0.\<And>x1. (len (app x1 sK0) = add (len x1) (len sK0)
              \<Longrightarrow> len (app (cons x0 x1) sK0) = add (len (cons x0 x1)) (len sK0)))
              \<Longrightarrow> (\<And>x2. (len (app x2 sK0) = add (len x2) (len sK0)))"
then have "False"
using skolemised_negated_goal
by simp

end

end