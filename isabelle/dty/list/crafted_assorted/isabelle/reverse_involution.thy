theory reverse_involution
imports Main
begin
datatype nat = zero | s nat
datatype lst = nil | cons nat lst

fun app :: "lst \<Rightarrow> lst \<Rightarrow> lst" where
"app nil xs = xs" |
"app (cons x xs) ys = cons x (app xs ys)"

fun rev :: "lst \<Rightarrow> lst" where
"rev nil = nil" |
"rev (cons x xs) = app (rev xs) (cons x nil)"

lemma app_nil: "app xs nil = xs"
proof(induct xs)
case nil
then show ?case by simp
next
case (cons x1 xs)
then show ?case by simp
qed

lemma app_assoc: "app (app xs ys) zs = app xs (app ys zs)"
proof(induct xs)
case nil
then show ?case by simp
next
case (cons x1 xs)
then show ?case by simp
qed

lemma rev_app: "rev (app xs ys) = app (rev ys) (rev xs)"
proof(induct xs)
case nil
then show ?case using app_nil by simp
next
case (cons x1 xs)
then show ?case using app_assoc by simp
qed

theorem "rev (rev xs) = xs"
proof(induct xs)
case nil
then show ?case by simp
next
  case (cons x1 xs)
  then show ?case using rev_app by simp
qed

end