theory count
imports Main
begin

datatype nat = zero | s nat
datatype lst = nil | cons nat lst

inductive leq :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
zero: "leq zero n" |
step: "leq n m \<Longrightarrow> leq (s n) (s m)"

declare leq.intros[simp,intro]

fun length :: "lst \<Rightarrow> nat" where
"length nil = zero" |
"length (cons x xs) = s (length xs)"

fun count :: "nat \<Rightarrow> lst \<Rightarrow> nat" where
"count x nil = zero" |
"count x (cons y ys) = (if x=y then s (count x ys) else count x ys)"

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

theorem "\<And>xs. \<And>x. leq (count x xs) (length xs)" proof -
fix xs
show "\<And>x. leq (count x xs) (length xs)" proof(induct xs)
case nil
then show ?case by simp
next
case (cons x1 xs)
then show ?case by (simp add: leq_s_right)
qed
qed

end