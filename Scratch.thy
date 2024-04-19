theory Scratch
imports Main Complex_Main
begin
fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02: "add m 0 = m"
  apply (induction m)
  apply (auto)
  done

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys"  |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"
value "rev (Cons a (Cons b Nil))"

lemma app_Nil2 [simp] : "app xs Nil = xs"
  apply (induction xs)
  apply (auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply (auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
  apply (auto)
  done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply (induction xs)
  apply (auto)
  done

(* Exercises 2.1-2.5  *)
value "1 + (2::nat)" (* 3::nat *)
value "1 + (2::int)" (* 3::int *)
value "1 - (2::nat)" (* 0::nat *)
value "1 - (2::int)" (* -1::int *)

theorem add_assoc [simp]: "add x (add y z) = add (add x y) z"
  apply (induction x)
  apply (auto)
  done

lemma add_zero_2[simp]: "add x 0 = x"
  apply (induction x)
  apply (auto)
  done

lemma add_suc_2 [simp]: "add x (Suc y)=Suc (add x y)"
  apply (induction x)
  apply (auto)
  done

theorem add_comm [simp]: "add x y = add y x"
  apply (induction x)
  apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

theorem double_add [simp]: "double m = add m m" 
  apply (induction m)
  apply (auto)
  done

type_synonym string = "char list"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l m r) = Node (mirror r) m (mirror l)"

lemma "mirror (mirror t) = t"
  apply (induction t)
  apply (auto)
  done

definition sq :: "nat \<Rightarrow> nat" where
"sq x = x * x"

abbreviation sq':: "nat \<Rightarrow> nat" where
"sq' x \<equiv> x * x"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"

lemma "div2 n = n div 2"
  apply (induction n rule: div2.induct)
  apply (auto)
  done

fun contents:: "'a tree \<Rightarrow> 'a List.list" where
"contents Tip = []" |
"contents (Node l a r) = a # (contents l) @ (contents r)"

fun sum_tree:: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

fun sum_list :: "nat List.list \<Rightarrow> nat" where
"sum_list [] = 0" |
"sum_list (x # xs) = x + (sum_list xs)"

lemma sum_list_add [simp]: "sum_list (xs @ ys) = sum_list xs + sum_list ys"
  apply (induction xs)
  apply (auto)
  done

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply (auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a List.list \<Rightarrow> 'a List.list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x # y # xs) = x # a # y # (intersperse a xs)"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule:intersperse.induct)
  apply (auto)
  done

fun itrev:: "'a List.list \<Rightarrow> 'a List.list \<Rightarrow> 'a List.list" where
"itrev [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma itrev_app[simp]: "itrev xs ys = List.rev xs @ ys"
  apply (induction xs arbitrary: ys)
  apply (auto)
  done

lemma "itrev xs [] = List.rev xs"
  apply(auto)
  done

fun itadd:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 acc = acc" |
"itadd (Suc n) acc = itadd n (Suc acc)"


lemma "itadd m n = add m n"
  apply (induction m arbitrary:n)
  apply (auto)
  done

datatype tree0 = Tip0 | Node0 tree0 tree0
fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip0 = 0" |
"nodes (Node0 l r) = nodes l + nodes r + 1"

fun explode:: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node0 t t)"

definition num_explode :: "nat \<Rightarrow> tree0 \<Rightarrow> nat" where
"num_explode n t = 2^n * (nodes t + 1)- 1"

lemma " nodes (explode n t) = num_explode n t " 
  apply (induction n arbitrary:t)
  apply (simp_all add:num_explode_def algebra_simps)
  done

datatype exp = Var | Const int | Add exp exp | Mult exp exp
fun eval:: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const n) _ = n" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp:: "int List.list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] _ = 0" |
"evalp (h # t) x = h + (evalp t x) * x"

fun add_list:: "int List.list \<Rightarrow> int List.list \<Rightarrow> int List.list" where
"add_list [] ys = ys" |
"add_list (h1#t1) [] = (h1#t1)" |
"add_list (h1#t1) (h2#t2) = (h1 + h2) # (add_list t1 t2)"

fun mult_list_scalar :: "int \<Rightarrow> int List.list \<Rightarrow> int List.list" where
"mult_list_scalar n [] = []" |
"mult_list_scalar n (h # t) = (n * h) # (mult_list_scalar n t)"

fun mult_coeffs :: "int List.list \<Rightarrow> int List.list \<Rightarrow> int List.list" where
"mult_coeffs [] _ = []" |
"mult_coeffs (h1#t1) l = 
  (let h1_l = (mult_list_scalar h1 l) in 
  (let t1_l_shift = 0#(mult_coeffs t1 l) in 
  add_list h1_l t1_l_shift ))"

fun coeffs:: "exp \<Rightarrow> int List.list" where
"coeffs Var = [0,1]" |
"coeffs (Const n) = [n]" |
"coeffs (Add e1 e2) = add_list (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = mult_coeffs (coeffs e1) (coeffs e2)"

lemma addlist_nil [simp]: "add_list ys [] = ys"
  apply (induction ys)
  apply (auto)
  done
lemma evalp_addlist [simp]: "evalp (add_list l1 l2) x = evalp l1 x + evalp l2 x"
  apply (induction l1 rule:add_list.induct)
    apply (auto)
  apply (simp add:algebra_simps)
  done

lemma evalp_mult_coeffs_0 [simp]: "evalp (mult_coeffs l []) x = 0"
  apply (induction l)
   apply (auto)
  done

lemma evalp_mult_coeffs_1 [simp]: "evalp (mult_list_scalar a l) x = a * evalp l x"
  apply (induction l)
   apply (auto)
  apply (simp add:algebra_simps)
  done

lemma evalp_mult_coeffs [simp]: "evalp (mult_coeffs l1 l2) x = evalp l1 x * evalp l2 x"
  apply (induction l1 arbitrary:l2)
   apply (auto)
  apply (simp add:algebra_simps)
  done

theorem "evalp (coeffs e) x = eval e x"
  apply (induction e)
  apply (simp)
  apply (simp)
   apply (simp)
  apply (simp add:algebra_simps)
  done

end