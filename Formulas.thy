theory Formulas
imports Main HOL.Set
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l m r) = {m} \<union> (set l) \<union> (set r)"

fun treetop :: "int tree \<Rightarrow> int option" where
"treetop Tip = None" |
"treetop (Node l m r) = Some m"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node Tip m Tip) = True" |
"ord (Node (Node _ l _) m Tip) = (l \<le> m)" |
"ord (Node Tip m (Node _ r _)) = (m \<le> r)" |
"ord (Node (Node _ l _) m (Node _ r _)) = (l \<le> m \<and> m \<le> r)" 


fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l m r) = 
  (if x=m then Node l m r 
  else if x < m then Node (ins x l) m r
  else Node l m (ins x r))"

theorem "set (ins x t) = {x} \<union> set t"
  apply (induction t)
  by auto

theorem "ord t \<Longrightarrow> ord (ins x t)"
  apply (induction t arbitrary:x rule:ord.induct)
      apply (auto)
  done

lemma "\<forall>x. \<exists>y. x=y "
  by auto

lemma "\<lbrakk> \<forall> xs \<in> A. \<exists> ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists> n. length us = n+n"
  by fastforce
  

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (metis append_eq_conv_conj)

lemma "\<lbrakk> (a::nat) \<le> b; b \<le> c; c \<le> d; d \<le> e \<rbrakk> \<Longrightarrow> a \<le> e"
  by (blast intro: le_trans)

thm conjI [OF refl[of "a"] refl[of "b"]]

lemma "Suc (Suc(Suc a)) \<le> b \<Longrightarrow> a \<le> b"
  by (blast dest:Suc_leD)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc(n)))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"
declare ev.intros[simp, intro]

lemma "ev (Suc(Suc(Suc(Suc 0))))"
  apply (rule evSS)
  apply (rule evSS)
  apply (rule ev0)
  done

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule:ev.induct)
  by (simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
  by (simp_all add: ev0 evSS)

  
inductive star :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a\<Rightarrow>'a\<Rightarrow>bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule:star.induct)
  apply(assumption)
  apply (metis step)
  done

inductive palindrome :: "'a list \<Rightarrow> bool" where
  pal_nil: "palindrome []" |
  pal_cons: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

theorem "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct)
  apply simp
  apply simp
  done

inductive star' :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a\<Rightarrow>'a\<Rightarrow>bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_refl: "star r x y \<Longrightarrow> star r y x"
  apply (induction rule: star.induct)
  apply (auto simp add: refl step star_trans)


lemma "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule:star'.induct)
  apply (simp add:refl)
  apply (simp add:step step')
  
end