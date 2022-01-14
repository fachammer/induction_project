theory count
imports Main
begin

datatype nat = zero | s nat
datatype lst = nil | cons nat lst

inductive leq :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
zero: "leq zero n" |
step: "leq n m \<Longrightarrow> leq (s n) (s m)"

fun leq_fn :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"leq_fn zero n = True" |
"leq_fn (s m) zero = False" |
"leq_fn (s m) (s n) = leq_fn m n"

declare leq.intros[simp,intro]

fun length :: "lst \<Rightarrow> nat" where
"length nil = zero" |
"length (cons x xs) = s (length xs)"

fun count :: "(nat \<Rightarrow> bool) \<Rightarrow> lst \<Rightarrow> nat" where
"count p nil = zero" |
"count p (cons y ys) = (if (p y) then s (count p ys) else count p ys)"

lemma leq_s_right: "\<And>n. \<And>m. leq n m \<Longrightarrow> leq n (s m)"
proof -
fix n
show "\<And>m. leq n m \<Longrightarrow> leq n (s m)" proof(induct n)
case zero
then show ?case by simp
next
case (s n)
then show ?case by (metis nat.inject leq.simps)
qed
qed

lemma leq_fn_s_right: "\<And>n. \<And>m. leq_fn n m \<Longrightarrow> leq_fn n (s m)"
proof -
fix n
show "\<And>m. leq_fn n m \<Longrightarrow> leq_fn n (s m)" proof(induct n)
case zero
then show ?case by simp
next
case (s n)
then show ?case by (metis leq_fn.elims(2) leq_fn.simps(1) leq_fn.simps(3))
qed
qed

theorem "\<And>p. \<And>xs. leq (count p xs) (length xs)" proof -
fix xs
show "\<And>p. leq (count p xs) (length xs)" proof(induct xs)
case nil
then show ?case by simp
next
case (cons y ys)
then show ?case by (simp add: leq_s_right)
qed
qed

theorem "\<And>xs. \<And>x. leq_fn (count x xs) (length xs)" proof -
fix xs
show "\<And>x. leq_fn (count x xs) (length xs)" proof(induct xs)
case nil
then show ?case by simp
next
case (cons y ys)
then show ?case by (simp add: leq_fn_s_right)
qed
qed

end