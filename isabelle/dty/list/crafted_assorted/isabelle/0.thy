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

assume "\<not>(\<forall>n.\<forall>xs. app (cons (add n (s n)) xs) (app xs xs) = app (app (cons (add (s n) n) xs) xs) xs)"
then have "\<exists>n.\<exists>xs. app (cons (add n (s n)) xs) (app xs xs) \<noteq> app (app (cons (add (s n) n) xs) xs) xs" by blast
then obtain sK0 where "\<exists>xs. app (cons (add sK0 (s sK0)) xs) (app xs xs) \<noteq> app (app (cons (add (s sK0) sK0) xs) xs) xs" ..
then obtain sK1 where skolemised_negated_goal: "app (cons (add sK0 (s sK0)) sK1) (app sK1 sK1) \<noteq> app (app (cons (add (s sK0) sK0) sK1) sK1) sK1" ..
assume app_assoc_induction_rule:
"(app nil (app sK1 sK1) = app (app nil sK1) sK1
     \<Longrightarrow> (\<And>x1.\<And>x0. (app x1 (app sK1 sK1) = app (app x1 sK1) sK1
        \<Longrightarrow> app (cons x0 x1) (app sK1 sK1) = app (app (cons x0 x1) sK1) sK1) )
     \<Longrightarrow> (\<And>x2. app x2 (app sK1 sK1) = app (app x2 sK1) sK1))"

and add_s_induction_rule:
"(add zero (s sK0) = s (add zero sK0)
     \<Longrightarrow> (\<And>x0. add x0 (s sK0) = s (add x0 sK0)
          \<Longrightarrow> add (s x0) (s sK0) = s (add (s x0) sK0))
     \<Longrightarrow> (\<And>x1. add x1 (s sK0) = s (add x1 sK0)))"
     
then have "False" using skolemised_negated_goal by simp

end

end
