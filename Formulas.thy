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


end