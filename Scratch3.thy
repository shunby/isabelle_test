theory Scratch3
  imports Main
begin 
locale partial_order =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym [intro]: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
print_locale! partial_order
thm partial_order_def
thm partial_order.trans

definition (in partial_order)
  less:: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
  where "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"

thm partial_order.less_def

lemma (in partial_order) less_le_trans [trans]:
  "\<lbrakk>x \<sqsubset> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubset> z"
  unfolding less_def by (blast intro:trans)
notepad begin
end

context partial_order
begin

definition
  is_inf where "is_inf x y i =
    (i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i))"

definition
  is_sup where "is_sup x y s =
    (x \<sqsubseteq> s \<and> y \<sqsubseteq> s \<and> (\<forall>z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> s \<sqsubseteq> z))"

theorem is_inf_uniq: "\<lbrakk>is_inf x y i; is_inf x y i'\<rbrakk> \<Longrightarrow> i = i'"
proof (rule anti_sym[of i i'])
  assume "is_inf x y i"
    and  "is_inf x y i'"  
  thus "i \<sqsubseteq> i'"
    unfolding is_inf_def by auto
next
  assume "is_inf x y i"
    and  "is_inf x y i'"  
  thus "i' \<sqsubseteq> i" unfolding is_inf_def by auto
qed

theorem is_sup_uniq: "\<lbrakk>is_sup x y s; is_sup x y s'\<rbrakk> \<Longrightarrow> s=s'"
  unfolding is_sup_def by auto
end

locale lattice = partial_order +
  assumes ex_inf: "\<exists> inf. is_inf x y inf"
    and ex_sup: "\<exists> sup. is_sup x y sup"
begin
definition 
  meet (infixl "\<sqinter>" 70) where "x \<sqinter> y = (THE inf. is_inf x y inf)"
definition
  join (infixl "\<squnion>" 70) where "x \<squnion> y = (THE sup. is_sup x y sup)"

lemma meet_is_inf: "is_inf x y (x \<sqinter> y)"
  unfolding meet_def
proof -
  obtain inf where p_inf:"is_inf x y inf" using ex_inf by auto
  then show "is_inf x y (The (is_inf x y))" 
  proof (rule theI)
    show " \<And>xa. is_inf x y xa \<Longrightarrow> xa = inf" using is_inf_uniq p_inf by auto
  qed
qed


lemma join_is_sup: "is_sup x y (x \<squnion> y)"
  unfolding join_def
proof -
  obtain sup where p_sup:"is_sup x y sup" using ex_sup by auto
  then show "is_sup x y (The (is_sup x y))" 
  proof (rule theI)
    show " \<And>xa. is_sup x y xa \<Longrightarrow> xa = sup" using is_sup_uniq p_sup by auto
  qed
qed


lemma meet_left: "x \<sqinter> y \<sqsubseteq> x"
  using is_inf_def meet_is_inf by auto

lemma meet_symm: "x \<sqinter> y = y \<sqinter> x"
  using is_inf_def meet_is_inf by auto

lemma meet_right: "x \<sqinter> y \<sqsubseteq> y"
  using meet_left meet_symm by fastforce

lemma join_left: "x \<sqsubseteq> x \<squnion> y"
  using is_sup_def join_is_sup by auto

lemma join_right: "y \<sqsubseteq> x \<squnion> y"
  using is_sup_def join_is_sup by auto

lemma join_symm: "x \<squnion> y = y \<squnion> x"
  using is_sup_def join_is_sup by auto

lemma join_assoc: "\<And>x y z. x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
proof
  fix x y z
  have "y \<sqsubseteq> (x \<squnion> y) \<squnion> z" and "z \<sqsubseteq> (x \<squnion> y) \<squnion> z"
    using join_left join_right local.trans apply blast
    using join_right by auto
  hence "y \<squnion> z \<sqsubseteq> (x \<squnion> y) \<squnion> z" using is_sup_def join_is_sup by auto 
  thus p:"\<And>x y z. x \<squnion> (y \<squnion> z) \<sqsubseteq> (x \<squnion> y) \<squnion> z" by (meson is_sup_def join_is_sup local.trans)
  thus " (x \<squnion> y) \<squnion> z \<sqsubseteq> x \<squnion> (y \<squnion> z)" by (metis join_symm) 
qed

lemma absorption_meet [simp]: "x \<sqinter> (x \<squnion> y) = x"
proof
  show "x \<sqinter> (x \<squnion> y) \<sqsubseteq> x" using meet_left by auto
  have "x \<sqsubseteq> x" and  "x \<sqsubseteq>(x \<squnion> y)" using refl join_left by auto
  thus "x \<sqsubseteq> x \<sqinter> (x \<squnion> y)" using is_inf_def meet_is_inf by auto
qed

lemma absorption_join [simp]: "x \<squnion> (x \<sqinter> y) = x"
proof
  show "x \<sqsubseteq> x \<squnion> (x \<sqinter> y)" using join_left by auto
  have "x \<sqsubseteq> x" and  "(x \<sqinter> y \<sqsubseteq> x)" using refl meet_left by auto
  thus "x \<squnion> (x \<sqinter> y) \<sqsubseteq> x" using is_sup_def join_is_sup by auto
qed


end
                                       
locale total_order = partial_order +
  assumes total: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

lemma (in total_order) less_total: "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
proof -
  from total[of x y] show ?thesis
    unfolding less_def 
    by auto
qed

locale distrib_lattice = lattice +
  assumes meet_distr: "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"

lemma (in distrib_lattice) join_distr: 
  "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof-
  have "(x \<squnion> y) \<sqinter> (x \<squnion> z) = ((x\<squnion>z)\<sqinter>x) \<squnion> ((x \<squnion> z)\<sqinter>y)" using meet_distr meet_symm by metis
  also have "... = ((x\<squnion>z)\<sqinter>x) \<squnion> ((x\<sqinter>y) \<squnion> (z\<sqinter>y))" using meet_distr meet_symm by metis
  finally have "(x \<squnion> y) \<sqinter> (x \<squnion> z) = x \<squnion> (y\<sqinter>z)" using meet_symm join_assoc by auto
  thus ?thesis by auto
qed

sublocale total_order \<subseteq> lattice
proof unfold_locales
  fix x y
  from total have "is_inf x y (if x \<sqsubseteq> y then x else y)"
    by (auto simp: is_inf_def)
  thus "\<exists> inf. is_inf x y inf" ..
  
  from total have "is_sup x y (if x \<sqsubseteq> y then y else x)"
    by (auto simp: is_sup_def)
  thus "\<exists> sup. is_sup x y sup" ..
qed

sublocale total_order \<subseteq> distrib_lattice
proof
  have tot_meet: "\<And>x y. x \<sqinter> y = (if x \<sqsubseteq> y then x else y)" 
    using is_inf_def meet_is_inf total anti_sym by fastforce 
  moreover have tot_join: "\<And>x y. x \<squnion> y = (if x \<sqsubseteq> y then y else x)" 
    using is_sup_def join_is_sup total anti_sym by fastforce 
  ultimately show "\<And>x y z. x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> (x \<sqinter> z)"
    by (metis local.trans meet_left)
qed


(* first version

interpretation int: partial_order "(\<le>):: int \<Rightarrow> int \<Rightarrow> bool"
  by unfold_locales auto

thm int.trans
thm int.less_le_trans (*\<rightarrow> int.less ?x ?y \<Longrightarrow> ?y \<le> ?z \<Longrightarrow> int.less ?x ?z  *)

*)

interpretation int: partial_order "(\<le>):: int \<Rightarrow> int \<Rightarrow> bool"
  rewrites "int.less x y = (x < y)"
proof -
  show "partial_order ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
    by unfold_locales auto
  then interpret int: partial_order "(\<le>) :: [int, int] \<Rightarrow> bool".
  show "int.less x y = (x < y)"
    unfolding int.less_def by auto
qed

thm int.less_def (*\<rightarrow> (?x < ?y) = (?x \<le> ?y \<and> ?x \<noteq> ?y)*)

interpretation int: lattice "(\<le>):: int\<Rightarrow>int\<Rightarrow>bool"
  rewrites int_min_eq: "int.meet x y = min x y"
    and int_max_eq: "int.join x y = max x y"
proof -
  show "lattice ((\<le>)::int\<Rightarrow>int\<Rightarrow>bool)" 
    apply unfold_locales
     apply (unfold int.is_inf_def int.is_sup_def)
    by arith+
  then interpret int: lattice "(\<le>) :: int\<Rightarrow>int\<Rightarrow>bool".
  show "int.meet x y = min x y"
    using int.is_inf_def int.meet_is_inf by auto
  show "int.join x y = max x y"
    by (bestsimp simp: int.is_sup_def int.join_def)
qed

interpretation int: total_order "(\<le>) :: int\<Rightarrow>int\<Rightarrow>bool"
  by unfold_locales arith

thm int.less_total

print_interps partial_order

locale order_preserving =
  le: partial_order le + le': partial_order le'
    for le (infixl "\<sqsubseteq>" 50) and le' (infixl "\<preceq>" 50) +
    fixes \<phi>
    assumes hom_le: "x \<sqsubseteq> y \<Longrightarrow> \<phi> x \<preceq> \<phi> y"
begin
notation le'.less (infixl "\<prec>" 50)
thm le'.less_le_trans
thm le.less_le_trans
end

locale fun_partial_order = partial_order
sublocale fun_partial_order \<subseteq> f: partial_order "\<lambda>f g. \<forall>x. le (f x) (g x)"
proof unfold_locales
  show "\<And>x. \<forall>xa. x xa \<sqsubseteq> x xa" by auto
  show "\<And>x y. \<forall>xa. x xa \<sqsubseteq> y xa \<Longrightarrow> \<forall>xa. y xa \<sqsubseteq> x xa \<Longrightarrow> x = y" by auto
  show "\<And>x y z. \<forall>xa. x xa \<sqsubseteq> y xa \<Longrightarrow> \<forall>x. y x \<sqsubseteq> z x \<Longrightarrow> \<forall>xa. x xa \<sqsubseteq> z xa" 
    using trans by blast
qed


end