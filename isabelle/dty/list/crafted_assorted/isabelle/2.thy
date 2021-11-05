theory 2
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

fun leq :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"leq zero x = True" |
"leq (s x) zero = False" |
"leq (s x) (s y) = leq x y"

fun less :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"less x y = leq (s x) y"

fun cnt :: "lst \<Rightarrow> nat \<Rightarrow> nat" where
"cnt nil x = zero" |
"cnt (cons x tail) e = (if (\<not>(x=e)) then (cnt tail e) else (s (cnt tail e)))"

fun outOfBounds :: "nat \<Rightarrow> nat" where
"outOfBounds i = i"

fun get :: "lst \<Rightarrow> nat \<Rightarrow> nat" where
"get nil i = outOfBounds i" |
"get (cons x tail) zero = x" |
"get (cons x tail) (s i) = get tail i"

lemma "less i (len x) \<and> get x i = e \<Longrightarrow> less zero (cnt l e)"