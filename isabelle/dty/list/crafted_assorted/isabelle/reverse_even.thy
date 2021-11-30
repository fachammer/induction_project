theory reverse_even
imports Main
begin
datatype nat = zero | s nat
datatype lst = nil | cons nat lst

fun snoc :: "lst \<Rightarrow> nat \<Rightarrow> lst" where
"snoc nil x = cons x nil" |
"snoc (cons x xs) y = cons x (snoc xs y)"

fun reverse :: "lst \<Rightarrow> lst" where
"reverse nil = nil" |
"reverse (cons x xs) = snoc (reverse xs) x"

fun reverse_n :: "nat \<Rightarrow> lst \<Rightarrow> lst" where
"reverse_n zero xs = xs" |
"reverse_n (s n) xs = reverse (reverse_n n xs)"
 
fun even_fn :: "nat \<Rightarrow> bool" where
"even_fn zero = True" |
"even_fn (s zero) = False" |
"even_fn (s (s n)) = even_fn n"

inductive even :: "nat \<Rightarrow> bool" where
"even zero" |
"even n \<Longrightarrow> even (s (s n))"

lemma reverse_snoc: "reverse (snoc xs x) = cons x (reverse xs)" proof(induct xs)
case nil
then show ?case by simp
next
case (cons x1 xs)
then show ?case by simp
qed

lemma reverse_involution: "\<And>xs. reverse (reverse xs) = xs" proof -
fix xs
show "reverse (reverse xs) = xs" proof(induct xs)
case nil
then show ?case by simp
next
case (cons x1 xs)
then show ?case by (simp add: reverse_snoc)
qed
qed

lemma "\<And>n xs. (even n \<Longrightarrow> reverse_n n xs = xs)" proof (rule even.induct)
show "\<And>n xs. reverse_even.even n \<Longrightarrow> reverse_even.even n" by simp
next
show "\<And>n xs. reverse_even.even n \<Longrightarrow> reverse_n zero xs = xs" by simp
next
show 
"\<And>n xs na. 
reverse_even.even n
\<Longrightarrow> reverse_even.even na 
\<Longrightarrow> reverse_n na xs = xs 
\<Longrightarrow> reverse_n (s (s na)) xs = xs" by (simp add: reverse_involution)
qed

lemma "\<And>n xs. (even_fn n \<longrightarrow> reverse_n n xs = xs)" proof (rule even_fn.induct)
show "\<And>n xs. even_fn n \<longrightarrow> reverse_n zero xs = xs" by simp
next
show "\<And>n xs. even_fn (s zero) \<longrightarrow> reverse_n (s zero) xs = xs" by simp
next
show "\<And>n xs na. even_fn na \<longrightarrow> reverse_n na xs = xs \<Longrightarrow> even_fn (s (s na)) \<longrightarrow> reverse_n (s (s na)) xs = xs" by (simp add: reverse_involution)
qed

end