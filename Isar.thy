theory Isar
  imports Main "HOL-IMPP.EvenOdd"
begin
lemma "\<not>surj(f:: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall> A. \<exists>a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma "\<not>surj(f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from this show "False" by blast
qed

lemma "\<not>surj(f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
  hence "\<exists>a. {x. x \<notin> f x} = f a" by blast
  thus "False" by blast
qed

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof-
  have "\<exists>a. {x. x \<notin> f x} = f a" using s
    by (auto simp: surj_def)
  thus "False" by blast
qed

lemma "\<not>surj(f:: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by (auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
  thus "False" by blast
qed

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  have "\<exists>k'. a = b*k'" if asm: "a+b = b*k" for k
  proof
    show "a = b*(k-1)" using asm by (simp add: algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and A_x_y:"A x y"
  shows "T x y"
proof -
  have "T x y \<or> T y x" using assms by blast
  then show "T x y"
  proof
    assume "T x y"
    then show "T x y" by (auto)
  next
    assume "T y x"
    then have "A y x" using TA by blast
    then have "x = y" using assms by blast
    then show "T x y" using assms by blast
  qed
qed

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  let ?n = "(length xs + 1) div 2"
  let ?f = "take ?n xs" and ?b = "drop ?n xs"
  have "xs = ?f @ ?b" by simp 
  moreover have "?n = (length xs - ?n) \<or> ?n = Suc (length xs - ?n)" by fastforce
  ultimately show ?thesis by (smt (verit, ccfv_threshold) Suc_diff_Suc Suc_eq_plus1 add_diff_cancel_right' diff_less drop.simps(1) length_append length_drop length_greater_0_conv zero_less_Suc)
qed   

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof-
  let ?n = "(length xs + 1) div 2"
  let ?f = "take ?n xs" and ?b = "drop ?n xs"
  have app: "xs = ?f @ ?b" by simp
  then show ?thesis
  proof cases
    assume even: "2 dvd (length xs)"
    then have "length xs = ?n + ?n" using even by fastforce
    then show ?thesis
      by (metis \<open>xs = ?f @ ?b\<close> add_diff_cancel_right' length_append length_drop) 
  next
    assume odd: "\<not> (2 dvd (length xs))"
    then have "length xs = ?n + (?n-1)" by arith
    moreover have "length ?f = ?n" by fastforce
    then show ?thesis using app
      by (metis add.commute add_diff_cancel_right' calculation length_drop odd odd_succ_div_two) 
  qed
qed

lemma "length (tl xs) = length xs - 1"  
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  show "?P 0" by simp
next
  fix n assume "?P n"
  thus "?P (Suc n)" by simp
qed

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True"|
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
  case ev0
  show ?case by simp
next
  case (evSS m)
  have "evn (Suc (Suc m)) = evn m" by simp
  thus ?case using `evn m` by simp
qed

lemma "ev n \<Longrightarrow> ev (n-2)"
proof-
  assume "ev n"
  from this show "ev (n-2)"
  proof cases
    case ev0 thus "ev (n-2)" by (simp add:ev.ev0)
  next
    case (evSS k) thus "ev(n-2)" by simp
  qed
qed

lemma "\<not> ev(Suc 0)"
proof 
  assume "ev (Suc 0)" then show False by cases
qed

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))" then show False
  proof cases 
    case evSS thus "False" by cases
  qed
qed
(* ev n \<Longrightarrow> forall m, (n = Suc m \<Longrightarrow> \<not>ev m)
  ev n' \<Longrightarrow> (all m, n' = Suc m \<Longrightarrow> \<not>ev m) 
\<Longrightarrow> Suc Suc n' = Suc m \<Longrightarrow> \<not>ev Suc Suc n'
*)

lemma "ev (Suc m) ==> \<not>ev m"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m'. n = Suc m' \<Longrightarrow> \<not> ev m'" (* n = (Suc m - 2) *)
  show "\<not>ev (Suc n)" 
  proof 
    assume "ev (Suc n)"
    thus False
    proof cases
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

lemma
  assumes a: "ev (Suc (Suc n))"
  shows "ev n"
proof- 
  from a show ?thesis
  proof (induction "Suc (Suc n)" arbitrary: n rule: ev.induct)
    case (evSS n)
    then show ?case by simp
  qed
qed

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))" thus "False"
  proof (induction "(Suc (Suc (Suc 0)))" rule: ev.induct)
    case (evSS) thus "False"
    proof (induction "Suc 0" rule: ev.induct)
    qed
  qed
qed


inductive iter :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> nat \<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>bool)" for r where
irefl: "iter r 0 x x" |
istep: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"


inductive star :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a\<Rightarrow>'a\<Rightarrow>bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

theorem "iter r n x y \<Longrightarrow> star r x y"
proof (induction arbitrary: n rule:iter.induct)
  case (irefl x) thus ?case by (auto simp: star.refl)
next
  case (istep x y n z) thus ?case by (auto simp:star.step) 
qed

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (h#t) = {h} \<union> (elems t)"

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil thus ?case by auto
next
  case (Cons h xs) thus ?case
  proof cases
    assume "h = x"
    then show ?case by fastforce
  next
    assume "\<not> h=x"
    hence "x \<in> elems xs" using Cons.prems by auto (*Cons.prems: the name of IH*)
    hence "\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" using Cons by auto
    then obtain ys zs where "xs = ys @ x # zs \<and> x \<notin> elems ys" by auto
    hence " h # xs = h # ys @ x # zs \<and> x \<notin> elems (h # ys)" using `\<not> h=x` by auto
    thus ?thesis
      by (metis append_Cons)
  qed
qed


datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S_nil: "S []" |
S_ab: "S w \<Longrightarrow> S (a # w @ [b])" |
S_S: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_nil: "T []" |
T_ab: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ a # w2 @ [b])"



theorem T_to_S: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  apply (simp add:S_nil)
  apply (simp add: S_S S_ab)
  done

lemma T_app: "T w2 \<Longrightarrow> T w1 \<Longrightarrow> T (w1 @ w2)"
  apply (induction rule: T.induct)
   apply simp
  apply (simp add:T_ab)
  by (metis T_ab append.assoc)

theorem S_to_T: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
    apply (simp add: T_nil)
   apply (metis T_ab T_nil append_Nil)
  apply (rule T_app, auto)
  done

theorem S_interl: "S (w1 @ w2) \<Longrightarrow> S (w1 @ a # b # w2)"
proof (induction "w1 @ w2" arbitrary: w1 w2 rule:S.induct)
  case (S_nil) 
  thus ?case using S_nil S_ab using S.S_nil by fastforce 
next
  case (S_ab w) thus ?case
  proof (cases w1)
    case Nil
    hence "a # w @ [b] = w2" using S_ab by auto
    hence "S w2" using `S w` S.S_ab by blast
    hence "S (w1 @ a # b # w2)" using S.S_S S.S_ab S_nil Nil by force
    thus ?thesis by auto
  next
    case IH_w1:(Cons x w1') thus ?thesis
    proof (cases w2)
      case Nil thus ?thesis
        by (metis S.S_ab S_S S_ab.hyps(1) S_ab.hyps(3) S_nil append.right_neutral append_Nil)
    next
      case (Cons y w2')
      then obtain w2'' where p_w2:"w2 = w2'' @ [b]"
        by (metis S_ab.hyps(3) append_butlast_last_id append_is_Nil_conv last_ConsR last_appendR last_snoc list.discI)
      then have "w = w1' @ w2''" using IH_w1 S_ab.hyps(3) by auto
      hence "S(w1' @ a # b # w2'')" by (simp add: S_ab.hyps(2))
      moreover have "x=a"
        using IH_w1 S_ab.hyps(3) by auto
      ultimately show ?thesis
        using IH_w1 S.S_ab p_w2 by force
    qed
  qed
next
  case (S_S w1' w2')
  then obtain r where "(w1' @ r = w1 \<and> w2' = r @ w2) \<or> (w1' = w1 @ r \<and> r @ w2' = w2)" (is "?A \<or> ?B")
    by (meson append_eq_append_conv2) 
  thus "S (w1 @ a # b # w2)"
  proof 
    assume A: "(w1' @ r = w1 \<and> w2' = r @ w2)"
    hence "S (r @ a # b # w2)" using S_S by simp
    thus "S (w1 @ a # b # w2)" using S.S_S A S_S by force
  next
    assume B: "(w1' = w1 @ r \<and> r @ w2' = w2)"
    hence "S (w1 @ a # b # r)" using S_S by simp
    thus "S (w1 @ a # b # w2)" using S.S_S B S_S by force
  qed
qed

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0 (b#w) = False" |
"balanced 0 [] = True" |
"balanced (Suc n) [] = False" |
"balanced n (a#w) = balanced (n+1) w" |
"balanced (Suc n) (b#w) = balanced n w"

lemma balanced_ab: "balanced n w \<Longrightarrow> balanced n (a # w @ [b])"
  apply (induction n w rule:balanced.induct)
  by auto

lemma balanced_app: "balanced n w1 \<Longrightarrow> balanced 0 w2 \<Longrightarrow> balanced n (w1 @ w2)"
  apply (induction n w1 arbitrary: w2 rule: balanced.induct) 
  by auto

theorem "balanced n w = S (replicate n a @ w)"
proof
  assume "balanced n w" thus "S (replicate n a @ w)"
  proof (induction w arbitrary:n)
    case Nil
    hence "n=0" using balanced.elims by blast
    thus ?case using "S.S_nil" by simp
  next
    case (Cons x w) thus ?case
    proof (cases x)
      case a
      hence "balanced (n+1) w" using Cons by simp
      hence "S (replicate (n+1) a @ w)" using Cons by blast
      then show ?thesis
        by (simp add: a replicate_app_Cons_same)
    next
      case b
      then obtain m where p_m:"n = Suc m \<and> balanced m w" using Cons balanced.elims(2) by blast
      hence "S (replicate m a @ w)" using Cons by auto
      hence "S (replicate m a @ a # x # w)" using b S_interl by simp
      thus ?thesis using p_m
        by (simp add: replicate_app_Cons_same)
    qed
  qed
next
  assume "S (replicate n a @ w)" thus "balanced n w"
  proof (induction "replicate n a @ w" arbitrary: n w rule:S.induct)
    case S_nil thus ?case by auto
  next
    case (S_ab w') thus ?case
    proof (induction n arbitrary: w' w) 
      case 0 
      hence "w = a # w' @ [b]" by simp
      moreover have "balanced 0 w'" by (simp add: "0.prems"(2))
      ultimately show ?case
        using balanced_ab by auto
    next
      case (Suc n) 
      then obtain w'' where p_w'':"w' = replicate n a @ w'' \<and> w = w'' @ [b]"
        by (smt (verit) Cons_replicate_eq add_diff_cancel_left' alpha.distinct(1) append_butlast_last_id append_eq_Cons_conv append_is_Nil_conv butlast_append butlast_snoc empty_replicate last_append last_replicate last_snoc nat.simps(3) plus_1_eq_Suc)
      from Suc this have "balanced n w''" by auto
      thus ?case using p_w'' Suc balanced_ab by force
    qed
  next
    case (S_S w1 w2) (*w1 @ w2 = replicate n a @ w*)
      then obtain r where "(w1 @ r = replicate n a \<and> w2 = r @ w) \<or> (w1 = replicate n a @ r \<and> r @ w2 = w)"
        by (meson append_eq_append_conv2)
      thus ?case
      proof
        assume A:"(w1 @ r = replicate n a \<and> w2 = r @ w)"
        then have "\<exists>m. w1 = replicate m a"
          by (metis append_eq_conv_conj take_replicate)
        then have "w1 = []" using `S w1`
          by (metis S_S.hyps(2) Suc_pred append.right_neutral balanced.simps(3) length_greater_0_conv length_replicate)
        then have "r = replicate n a" using A by auto
        thus ?case
          by (simp add: A S_S.hyps(4))
      next
        assume B: "(w1 = replicate n a @ r \<and> r @ w2 = w)"
        from this S_S have "balanced n r" by auto
        moreover have "balanced 0 w2" using B S_S by auto
        ultimately show "balanced n w" using B S_S
          using balanced_app by blast
      qed
  qed
qed  

end