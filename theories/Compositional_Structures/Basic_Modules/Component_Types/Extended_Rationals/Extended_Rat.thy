theory Extended_Rat
imports 
    "HOL-Algebra.Congruence"
    "HOL-Library.Extended_Nat"
    "HOL-Library.Disjoint_Sets"
    "HOL.Finite_Set"

begin


subsection \<open>General Extended Rationals\<close>

(* Rational Numbers as a codatatype sounds... questionable

erat as codatatype: codatatype erat = EZero | ESucc erat 
*)

subsection \<open>Type definition\<close>

text \<open>
  We extend the standard natural numbers by a special value indicating
  infinity.
\<close>

datatype erat = erat rat | PInfty | MInfty

lemma erat_cong: "x = y \<Longrightarrow> erat x = erat y" by simp

fun erat_of :: "nat \<Rightarrow> erat" where
"erat_of n = erat (Fract n 1)"

instantiation erat :: uminus
begin

fun uminus_erat where
  "- (erat r) = erat (- r)"
| "- PInfty = MInfty"
| "- MInfty = PInfty"

instance ..

end

lemma erat_uminus_uminus[simp]:
  fixes a :: erat
  shows "- (- a) = a"
  by (cases a) simp_all

subsection \<open>Dealing with Infinity\<close>

instantiation erat :: infinity
begin

definition "(\<infinity>::erat) = PInfty"
instance ..

end

lemma
  shows PInfty_eq_infinity[simp]: "PInfty = \<infinity>"
    and MInfty_eq_minfinity[simp]: "MInfty = - \<infinity>"
    and MInfty_neq_PInfty[simp]: "\<infinity> \<noteq> - (\<infinity>::erat)" "- \<infinity> \<noteq> (\<infinity>::erat)"
    and MInfty_neq_erat[simp]: "erat r \<noteq> - \<infinity>" "- \<infinity> \<noteq> erat r"
    and PInfty_neq_erat[simp]: "erat r \<noteq> \<infinity>" "\<infinity> \<noteq> erat r"
    and PInfty_cases[simp]: "(case \<infinity> of erat r \<Rightarrow> f r | PInfty \<Rightarrow> y | MInfty \<Rightarrow> z) = y"
    and MInfty_cases[simp]: "(case - \<infinity> of erat r \<Rightarrow> f r | PInfty \<Rightarrow> y | MInfty \<Rightarrow> z) = z"
  by (simp_all add: infinity_erat_def)

lemma not_infinity_eq [iff]: "(x \<noteq> \<infinity> \<and> x \<noteq> - \<infinity>) = (\<exists>i. x = erat i)"
proof (cases x)
  case (erat y)
  thus ?thesis using erat by simp
next
  case (PInfty)
  thus ?thesis by simp
next
  case (MInfty)
  thus ?thesis by simp
qed

lemma not_erat_eq [iff]: "(\<forall>y. x \<noteq> erat y) = (x = \<infinity> \<or> x = -\<infinity>)" 
  by (meson not_infinity_eq)

declare
  PInfty_eq_infinity[code_post]
  MInfty_eq_minfinity[code_post]

lemma [code_unfold]:
  "\<infinity> = PInfty"
  "- PInfty = MInfty"
  by simp_all

subsection \<open>Proof Methods on Extended Rationals\<close>

lemma inj_erat[simp]: "inj_on erat A"
  unfolding inj_on_def by auto

lemma erat_cases[cases type: erat]:
  obtains (rat) r where "x = erat r"
    | (PInf) "x = \<infinity>"
    | (MInf) "x = -\<infinity>"
  by (cases x) auto

lemmas erat2_cases = erat_cases[case_product erat_cases]
lemmas erat3_cases = erat2_cases[case_product erat_cases]

declare [[coercion "erat :: rat \<Rightarrow> erat"]]

lemma erat_all_split: "\<And>P. (\<forall>x::erat. P x) \<longleftrightarrow> P \<infinity> \<and> (\<forall>x. P (erat x)) \<and> P (-\<infinity>)"
  by (metis erat_cases)

lemma erat_ex_split: "\<And>P. (\<exists>x::erat. P x) \<longleftrightarrow> P \<infinity> \<or> (\<exists>x. P (erat x)) \<or> P (-\<infinity>)"
  by (metis erat_cases)

lemma erat_uminus_eq_iff[simp]:
  fixes a b :: erat
  shows "-a = -b \<longleftrightarrow> a = b"
  by (cases rule: erat2_cases[of a b]) simp_all


subsection \<open>Basic Properties\<close>

function rat_of_erat :: "erat \<Rightarrow> rat" where
  "rat_of_erat (erat r) = r"
| "rat_of_erat \<infinity> = 0"
| "rat_of_erat (-\<infinity>) = 0"
  by (auto intro: erat_cases)
termination by standard (rule wf_empty)

lemma rat_of_erat[simp]:
  "rat_of_erat (- x :: erat) = - (rat_of_erat x)"
  by (cases x) simp_all

lemma range_erat[simp]: "range erat = UNIV - {\<infinity>, -\<infinity>}"
proof safe
  fix x
  assume "x \<notin> range erat" "x \<noteq> \<infinity>"
  then show "x = -\<infinity>"
    by (cases x) auto
qed auto

lemma erat_range_uminus[simp]: "range uminus = (UNIV::erat set)"
proof safe
  fix x :: erat
  show "x \<in> range uminus"
    by (intro image_eqI[of _ _ "-x"]) auto
qed auto

instantiation erat :: abs
begin

function abs_erat where
  "\<bar>erat r\<bar> = erat \<bar>r\<bar>"
| "\<bar>-\<infinity>\<bar> = (\<infinity>::erat)"
| "\<bar>\<infinity>\<bar> = (\<infinity>::erat)"
by (auto intro: erat_cases)
termination proof qed (rule wf_empty)

instance ..

end

lemma abs_eq_infinity_cases[elim!]:
  fixes x :: erat
  assumes "\<bar>x\<bar> = \<infinity>"
  obtains "x = \<infinity>" | "x = -\<infinity>"
  using assms by (cases x) auto

lemma abs_neq_infinity_cases[elim!]:
  fixes x :: erat
  assumes "\<bar>x\<bar> \<noteq> \<infinity>"
  obtains r where "x = erat r"
  using assms by (cases x) auto

lemma abs_erat_uminus[simp]:
  fixes x :: erat
  shows "\<bar>- x\<bar> = \<bar>x\<bar>"
  by (cases x) auto

lemma erat_infinity_cases:
  fixes a :: erat
  shows "a \<noteq> \<infinity> \<Longrightarrow> a \<noteq> -\<infinity> \<Longrightarrow> \<bar>a\<bar> \<noteq> \<infinity>"
  by auto

subsection \<open>Basic Operations\<close>

subsubsection "Addition"

instantiation erat :: "{one,comm_monoid_add,zero_neq_one}"
begin

definition "0 = erat 0"
definition "1 = erat 1"

function plus_erat where
  "erat r + erat p = erat (r + p)"
| "\<infinity> + a = (\<infinity>::erat)"
| "a + \<infinity> = (\<infinity>::erat)"
| "erat r + -\<infinity> = - \<infinity>"
| "-\<infinity> + erat p = -(\<infinity>::erat)"
| "-\<infinity> + -\<infinity> = -(\<infinity>::erat)"
proof goal_cases
  case prems: (1 P x)
  then obtain a b where "x = (a, b)"
    by (cases x) auto
  with prems show P
   by (cases rule: erat2_cases[of a b]) auto
qed auto
termination by standard (rule wf_empty)

lemma Infty_neq_0[simp]:
  "(\<infinity>::erat) \<noteq> 0" "0 \<noteq> (\<infinity>::erat)"
  "-(\<infinity>::erat) \<noteq> 0" "0 \<noteq> -(\<infinity>::erat)"
  by (simp_all add: zero_erat_def)

lemma erat_eq_0[simp]:
  "erat r = 0 \<longleftrightarrow> r = 0"
  "0 = erat r \<longleftrightarrow> r = 0"
  unfolding zero_erat_def by simp_all

lemma erat_eq_1[simp]:
  "erat r = 1 \<longleftrightarrow> r = 1"
  "1 = erat r \<longleftrightarrow> r = 1"
  unfolding one_erat_def by simp_all

instance
proof
  fix a b c :: erat
  show "0 + a = a"
    by (cases a) (simp_all add: zero_erat_def)
  show "a + b = b + a"
    by (cases rule: erat2_cases[of a b]) simp_all
  show "a + b + c = a + (b + c)"
    by (cases rule: erat3_cases[of a b c]) simp_all
  show "0 \<noteq> (1::erat)"
    by (simp add: one_erat_def zero_erat_def)
qed

end

lemma erat_0_plus [simp]: "erat 0 + x = x"
  and plus_erat_0 [simp]: "x + erat 0 = x"
by(simp_all flip: zero_erat_def)

instance erat :: numeral ..

lemma rat_of_erat_0[simp]: "rat_of_erat (0::erat) = 0"
  unfolding zero_erat_def by simp

lemma abs_erat_zero[simp]: "\<bar>0\<bar> = (0::erat)"
  unfolding zero_erat_def abs_erat.simps by simp

lemma erat_uminus_zero[simp]: "- 0 = (0::erat)"
  by (simp add: zero_erat_def)

lemma erat_uminus_zero_iff[simp]:
  fixes a :: erat
  shows "-a = 0 \<longleftrightarrow> a = 0"
  by (cases a) simp_all

lemma erat_plus_eq_PInfty[simp]:
  fixes a b :: erat
  shows "a + b = \<infinity> \<longleftrightarrow> a = \<infinity> \<or> b = \<infinity>"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_plus_eq_MInfty[simp]:
  fixes a b :: erat
  shows "a + b = -\<infinity> \<longleftrightarrow> (a = -\<infinity> \<or> b = -\<infinity>) \<and> a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_add_cancel_left:
  fixes a b :: erat
  assumes "a \<noteq> -\<infinity>"
  shows "a + b = a + c \<longleftrightarrow> a = \<infinity> \<or> b = c"
  using assms by (cases rule: erat3_cases[of a b c]) auto

lemma erat_add_cancel_right:
  fixes a b :: erat
  assumes "a \<noteq> -\<infinity>"
  shows "b + a = c + a \<longleftrightarrow> a = \<infinity> \<or> b = c"
  using assms by (cases rule: erat3_cases[of a b c]) auto

lemma erat_rat: "erat (rat_of_erat x) = (if \<bar>x\<bar> = \<infinity> then 0 else x)"
  by (cases x) simp_all

lemma rat_of_erat_add:
  fixes a b :: erat
  shows "rat_of_erat (a + b) =
    (if (\<bar>a\<bar> = \<infinity>) \<and> (\<bar>b\<bar> = \<infinity>) \<or> (\<bar>a\<bar> \<noteq> \<infinity>) \<and> (\<bar>b\<bar> \<noteq> \<infinity>) then rat_of_erat a + rat_of_erat b else 0)"
  by (cases rule: erat2_cases[of a b]) auto


subsubsection "Linear order on \<^typ>\<open>erat\<close>"

instantiation erat :: linorder
begin

function less_erat
where
  "   erat x < erat y     \<longleftrightarrow> x < y"
| "(\<infinity>::erat) < a           \<longleftrightarrow> False"
| "         a < -(\<infinity>::erat) \<longleftrightarrow> False"
| "erat x    < \<infinity>           \<longleftrightarrow> True"
| "        -\<infinity> < erat r     \<longleftrightarrow> True"
| "        -\<infinity> < (\<infinity>::erat) \<longleftrightarrow> True"
proof goal_cases
  case prems: (1 P x)
  then obtain a b where "x = (a,b)" by (cases x) auto
  with prems show P by (cases rule: erat2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

definition "x \<le> (y::erat) \<longleftrightarrow> x < y \<or> x = y"

lemma erat_infty_less[simp]:
  fixes x :: erat
  shows "x < \<infinity> \<longleftrightarrow> (x \<noteq> \<infinity>)"
    "-\<infinity> < x \<longleftrightarrow> (x \<noteq> -\<infinity>)"
  by (cases x, simp_all) (cases x, simp_all)

lemma erat_infty_less_eq[simp]:
  fixes x :: erat
  shows "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
    and "x \<le> -\<infinity> \<longleftrightarrow> x = -\<infinity>"
  by (auto simp add: less_eq_erat_def)

lemma erat_less[simp]:
  "erat r < 0 \<longleftrightarrow> (r < 0)"
  "0 < erat r \<longleftrightarrow> (0 < r)"
  "erat r < 1 \<longleftrightarrow> (r < 1)"
  "1 < erat r \<longleftrightarrow> (1 < r)"
  "0 < (\<infinity>::erat)"
  "-(\<infinity>::erat) < 0"
  by (simp_all add: zero_erat_def one_erat_def)

lemma erat_less_eq[simp]:
  "x \<le> (\<infinity>::erat)"
  "-(\<infinity>::erat) \<le> x"
  "erat r \<le> erat p \<longleftrightarrow> r \<le> p"
  "erat r \<le> 0 \<longleftrightarrow> r \<le> 0"
  "0 \<le> erat r \<longleftrightarrow> 0 \<le> r"
  "erat r \<le> 1 \<longleftrightarrow> r \<le> 1"
  "1 \<le> erat r \<longleftrightarrow> 1 \<le> r"
  by (auto simp add: less_eq_erat_def zero_erat_def one_erat_def)

lemma erat_infty_less_eq2:
  "a \<le> b \<Longrightarrow> a = \<infinity> \<Longrightarrow> b = (\<infinity>::erat)"
  "a \<le> b \<Longrightarrow> b = -\<infinity> \<Longrightarrow> a = -(\<infinity>::erat)"
  by simp_all

instance
proof
  fix x y z :: erat
  show "x \<le> x"
    by (cases x) simp_all
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (cases rule: erat2_cases[of x y]) auto
  show "x \<le> y \<or> y \<le> x "
    by (cases rule: erat2_cases[of x y]) auto
  {
    assume "x \<le> y" "y \<le> x"
    then show "x = y"
      by (cases rule: erat2_cases[of x y]) auto
  }
  {
    assume "x \<le> y" "y \<le> z"
    then show "x \<le> z"
      by (cases rule: erat3_cases[of x y z]) auto
  }
qed

end

lemma erat_dense2: "x < y \<Longrightarrow> \<exists>z. x < erat z \<and> erat z < y"
  using lt_ex gt_ex dense by (cases x y rule: erat2_cases) auto

instance erat :: dense_linorder
  by standard (blast dest: erat_dense2)

instance erat :: ordered_comm_monoid_add
proof
  fix a b c :: erat
  assume "a \<le> b"
  then show "c + a \<le> c + b"
    by (cases rule: erat3_cases[of a b c]) auto
qed

lemma erat_one_not_less_zero_erat[simp]: "\<not> 1 < (0::erat)"
  by (simp add: zero_erat_def)

lemma rat_of_erat_positive_mono:
  fixes x y :: erat
  shows "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> rat_of_erat x \<le> rat_of_erat y"
  by (cases rule: erat2_cases[of x y]) auto

lemma erat_MInfty_lessI[intro, simp]:
  fixes a :: erat
  shows "a \<noteq> -\<infinity> \<Longrightarrow> -\<infinity> < a"
  by (cases a) auto

lemma erat_less_PInfty[intro, simp]:
  fixes a :: erat
  shows "a \<noteq> \<infinity> \<Longrightarrow> a < \<infinity>"
  by (cases a) auto

lemma erat_less_erat_Ex:
  fixes a b :: erat
  shows "x < erat r \<longleftrightarrow> x = -\<infinity> \<or> (\<exists>p. p < r \<and> x = erat p)"
  by (cases x) auto

lemma less_PInf_Ex_of_nat: "x \<noteq> \<infinity> \<longleftrightarrow> (\<exists>n::nat. x < erat (Fract n 1))"
proof (cases x)
  case (rat r)
  have "\<exists> p :: nat. r < (Fract p 1)" by (metis of_nat_rat reals_Archimedean2)
  then show ?thesis by (simp add: rat)
qed simp_all

lemma erat_add_strict_mono2:
  fixes a b c d :: erat
  assumes "a < b" and "c < d"
  shows "a + c < b + d"
  using assms
  by (cases a; force simp add: elim: less_erat.elims)

lemma erat_minus_le_minus[simp]:
  fixes a b :: erat
  shows "- a \<le> - b \<longleftrightarrow> b \<le> a"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_minus_less_minus[simp]:
  fixes a b :: erat
  shows "- a < - b \<longleftrightarrow> b < a"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_le_rat_iff:
  "x \<le> rat_of_erat y \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> erat x \<le> y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x \<le> 0)"
  by (cases y) auto

lemma rat_le_erat_iff:
  "rat_of_erat y \<le> x \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y \<le> erat x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 \<le> x)"
  by (cases y) auto

lemma erat_less_rat_iff:
  "x < rat_of_erat y \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> erat x < y) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> x < 0)"
  by (cases y) auto

lemma rat_less_erat_iff:
  "rat_of_erat y < x \<longleftrightarrow> (\<bar>y\<bar> \<noteq> \<infinity> \<longrightarrow> y < erat x) \<and> (\<bar>y\<bar> = \<infinity> \<longrightarrow> 0 < x)"
  by (cases y) auto

text \<open>
  To help with inferences like \<^prop>\<open>a < erat x \<Longrightarrow> x < y \<Longrightarrow> a < erat y\<close>,
  where x and y are rat.
\<close>

lemma le_erat_le: "a \<le> erat x \<Longrightarrow> x \<le> y \<Longrightarrow> a \<le> erat y"
  using erat_less_eq(3) order.trans by blast

lemma le_erat_less: "a \<le> erat x \<Longrightarrow> x < y \<Longrightarrow> a < erat y"
  by (simp add: le_less_trans)

lemma less_erat_le: "a < erat x \<Longrightarrow> x \<le> y \<Longrightarrow> a < erat y"
  using erat_less_erat_Ex by auto

lemma erat_le_le: "erat y \<le> a \<Longrightarrow> x \<le> y \<Longrightarrow> erat x \<le> a"
  by (simp add: order_subst2)

lemma erat_le_less: "erat y \<le> a \<Longrightarrow> x < y \<Longrightarrow> erat x < a"
  by (simp add: dual_order.strict_trans1)

lemma erat_less_le: "erat y < a \<Longrightarrow> x \<le> y \<Longrightarrow> erat x < a"
  using erat_less_eq(3) le_less_trans by blast

lemma rat_of_erat_pos:
  fixes x :: erat
  shows "0 \<le> x \<Longrightarrow> 0 \<le> rat_of_erat x" by (cases x) auto

lemmas rat_of_erat_ord_simps =
  erat_le_rat_iff rat_le_erat_iff erat_less_rat_iff rat_less_erat_iff

lemma abs_erat_ge0[simp]: "0 \<le> x \<Longrightarrow> \<bar>x :: erat\<bar> = x"
  by (cases x) auto

lemma abs_erat_less0[simp]: "x < 0 \<Longrightarrow> \<bar>x :: erat\<bar> = -x"
  by (cases x) auto

lemma abs_erat_pos[simp]: "0 \<le> \<bar>x :: erat\<bar>"
  by (cases x) auto

lemma erat_abs_leI:
  fixes x y :: erat
  shows "\<lbrakk> x \<le> y; -x \<le> y \<rbrakk> \<Longrightarrow> \<bar>x\<bar> \<le> y"
by(cases x y rule: erat2_cases)(simp_all)

lemma erat_abs_add:
  fixes a b::erat
  shows "abs(a+b) \<le> abs a + abs b"
by (cases rule: erat2_cases[of a b]) (auto)

lemma rat_of_erat_le_0[simp]: "rat_of_erat (x :: erat) \<le> 0 \<longleftrightarrow> x \<le> 0 \<or> x = \<infinity>"
  by (cases x) auto

lemma abs_rat_of_erat[simp]: "\<bar>rat_of_erat (x :: erat)\<bar> = rat_of_erat \<bar>x\<bar>"
  by (cases x) auto

lemma zero_less_rat_of_erat:
  fixes x :: erat
  shows "0 < rat_of_erat x \<longleftrightarrow> 0 < x \<and> x \<noteq> \<infinity>"
  by (cases x) auto

lemma erat_0_le_uminus_iff[simp]:
  fixes a :: erat
  shows "0 \<le> - a \<longleftrightarrow> a \<le> 0"
  by (cases rule: erat2_cases[of a]) auto

lemma erat_uminus_le_0_iff[simp]:
  fixes a :: erat
  shows "- a \<le> 0 \<longleftrightarrow> 0 \<le> a"
  by (cases rule: erat2_cases[of a]) auto

lemma erat_add_strict_mono:
  fixes a b c d :: erat
  assumes "a \<le> b"
    and "0 \<le> a"
    and "a \<noteq> \<infinity>"
    and "c < d"
  shows "a + c < b + d"
  using assms
  by (cases rule: erat3_cases[case_product erat_cases, of a b c d]) auto

lemma erat_less_add:
  fixes a b c :: erat
  shows "\<bar>a\<bar> \<noteq> \<infinity> \<Longrightarrow> c < b \<Longrightarrow> a + c < a + b"
  by (cases rule: erat2_cases[of b c]) auto

lemma erat_add_nonneg_eq_0_iff:
  fixes a b :: erat
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (cases a b rule: erat2_cases) auto

lemma erat_uminus_eq_reorder: "- a = b \<longleftrightarrow> a = (-b::erat)"
  by auto

lemma erat_uminus_less_reorder: "- a < b \<longleftrightarrow> -b < (a::erat)"
  by (subst (3) erat_uminus_uminus[symmetric]) (simp only: erat_minus_less_minus)

lemma erat_less_uminus_reorder: "a < - b \<longleftrightarrow> b < - (a::erat)"
  by (subst (3) erat_uminus_uminus[symmetric]) (simp only: erat_minus_less_minus)

lemma erat_uminus_le_reorder: "- a \<le> b \<longleftrightarrow> -b \<le> (a::erat)"
  by (subst (3) erat_uminus_uminus[symmetric]) (simp only: erat_minus_le_minus)

lemmas erat_uminus_reorder =
  erat_uminus_eq_reorder erat_uminus_less_reorder erat_uminus_le_reorder

lemma erat_bot:
  fixes x :: erat
  assumes "\<And>B. x \<le> erat B"
  shows "x = - \<infinity>"
proof (cases x)
  case (rat r)
  with assms[of "r - 1"] show ?thesis
    by auto
next
  case PInf
  with assms[of 0] show ?thesis
    by auto
next
  case MInf
  then show ?thesis
    by simp
qed

lemma erat_top:
  fixes x :: erat
  assumes "\<And>B. x \<ge> erat B"
  shows "x = \<infinity>"
proof (cases x)
  case (rat r)
  with assms[of "r + 1"] show ?thesis
    by auto
next
  case MInf
  with assms[of 0] show ?thesis
    by auto
next
  case PInf
  then show ?thesis
    by simp
qed

lemma
  shows erat_max[simp]: "erat (max x y) = max (erat x) (erat y)"
    and erat_min[simp]: "erat (min x y) = min (erat x) (erat y)"
  by (simp_all add: min_def max_def)

lemma erat_max_0: "max 0 (erat r) = erat (max 0 r)"
  by (auto simp: zero_erat_def)

lemma
  fixes f :: "nat \<Rightarrow> erat"
  shows erat_incseq_uminus[simp]: "incseq (\<lambda>x. - f x) \<longleftrightarrow> decseq f"
    and erat_decseq_uminus[simp]: "decseq (\<lambda>x. - f x) \<longleftrightarrow> incseq f"
  unfolding decseq_def incseq_def by auto

lemma incseq_erat: "incseq f \<Longrightarrow> incseq (\<lambda>x. erat (f x))"
  unfolding incseq_def by auto

lemma sum_erat[simp]: "(\<Sum>x\<in>A. erat (f x)) = erat (\<Sum>x\<in>A. f x)"
proof (cases "finite A")
  case True
  then show ?thesis by induct auto
next
  case False
  then show ?thesis by simp
qed

lemma sum_list_erat [simp]: "sum_list (map (\<lambda>x. erat (f x)) xs) = erat (sum_list (map f xs))"
  by (induction xs) simp_all

lemma sum_Pinfty:
  fixes f :: "'a \<Rightarrow> erat"
  shows "(\<Sum>x\<in>P. f x) = \<infinity> \<longleftrightarrow> finite P \<and> (\<exists>i\<in>P. f i = \<infinity>)"
proof safe
  assume *: "sum f P = \<infinity>"
  show "finite P"
  proof (rule ccontr)
    assume "\<not> finite P"
    with * show False
      by auto
  qed
  show "\<exists>i\<in>P. f i = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<And>i. i \<in> P \<Longrightarrow> f i \<noteq> \<infinity>"
      by auto
    with \<open>finite P\<close> have "sum f P \<noteq> \<infinity>"
      by induct auto
    with * show False
      by auto
  qed
next
  fix i
  assume "finite P" and "i \<in> P" and "f i = \<infinity>"
  then show "sum f P = \<infinity>"
  proof induct
    case (insert x A)
    show ?case using insert by (cases "x = i") auto
  qed simp
qed

lemma sum_Inf:
  fixes f :: "'a \<Rightarrow> erat"
  shows "\<bar>sum f A\<bar> = \<infinity> \<longleftrightarrow> finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
proof
  assume *: "\<bar>sum f A\<bar> = \<infinity>"
  have "finite A"
    by (rule ccontr) (insert *, auto)
  moreover have "\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<forall>i\<in>A. \<exists>r. f i = erat r"
      by auto
    from bchoice[OF this] obtain r where "\<forall>x\<in>A. f x = erat (r x)" ..
    with * show False
      by auto
  qed
  ultimately show "finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
    by auto
next
  assume "finite A \<and> (\<exists>i\<in>A. \<bar>f i\<bar> = \<infinity>)"
  then obtain i where "finite A" "i \<in> A" and "\<bar>f i\<bar> = \<infinity>"
    by auto
  then show "\<bar>sum f A\<bar> = \<infinity>"
  proof induct
    case (insert j A)
    then show ?case
      by (cases rule: erat3_cases[of "f i" "f j" "sum f A"]) auto
  qed simp
qed

lemma sum_rat_of_erat:
  fixes f :: "'i \<Rightarrow> erat"
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<noteq> \<infinity>"
  shows "(\<Sum>x\<in>S. rat_of_erat (f x)) = rat_of_erat (sum f S)"
proof -
  have "\<forall>x\<in>S. \<exists>r. f x = erat r"
  proof
    fix x
    assume "x \<in> S"
    from assms[OF this] show "\<exists>r. f x = erat r"
      by (cases "f x") auto
  qed
  from bchoice[OF this] obtain r where "\<forall>x\<in>S. f x = erat (r x)" ..
  then show ?thesis
    by simp
qed

lemma sum_erat_0:
  fixes f :: "'a \<Rightarrow> erat"
  assumes "finite A"
    and "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i"
  shows "(\<Sum>x\<in>A. f x) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
proof
  assume "sum f A = 0" with assms show "\<forall>i\<in>A. f i = 0"
  proof (induction A)
    case (insert a A)
    then have "f a = 0 \<and> (\<Sum>a\<in>A. f a) = 0"
      by (subst erat_add_nonneg_eq_0_iff[symmetric]) (simp_all add: sum_nonneg)
    with insert show ?case
      by simp
  qed simp
qed auto

subsubsection "Multiplication"

instantiation erat :: "{comm_monoid_mult,sgn}"
begin

function sgn_erat :: "erat \<Rightarrow> erat" where
  "sgn (erat r) = erat (sgn r)"
| "sgn (\<infinity>::erat) = 1"
| "sgn (-\<infinity>::erat) = -1"
by (auto intro: erat_cases)
termination by standard (rule wf_empty)

function times_erat where
  "erat r * erat p = erat (r * p)"
| "erat r * \<infinity> = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)"
| "\<infinity> * erat r = (if r = 0 then 0 else if r > 0 then \<infinity> else -\<infinity>)"
| "erat r * -\<infinity> = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)"
| "-\<infinity> * erat r = (if r = 0 then 0 else if r > 0 then -\<infinity> else \<infinity>)"
| "(\<infinity>::erat) * \<infinity> = \<infinity>"
| "-(\<infinity>::erat) * \<infinity> = -\<infinity>"
| "(\<infinity>::erat) * -\<infinity> = -\<infinity>"
| "-(\<infinity>::erat) * -\<infinity> = \<infinity>"
proof goal_cases
  case prems: (1 P x)
  then obtain a b where "x = (a, b)"
    by (cases x) auto
  with prems show P
    by (cases rule: erat2_cases[of a b]) auto
qed simp_all
termination by (relation "{}") simp

instance
proof
  fix a b c :: erat
  show "1 * a = a"
    by (cases a) (simp_all add: one_erat_def)
  show "a * b = b * a"
    by (cases rule: erat2_cases[of a b]) simp_all
  show "a * b * c = a * (b * c)"
    by (cases rule: erat3_cases[of a b c])
       (simp_all add: zero_erat_def zero_less_mult_iff)
qed

end

lemma [simp]:
  shows erat_1_times: "erat 1 * x = x"
  and times_erat_1: "x * erat 1 = x"
by(simp_all flip: one_erat_def)

lemma one_not_le_zero_erat[simp]: "\<not> (1 \<le> (0::erat))"
  by (simp add: one_erat_def zero_erat_def)

lemma rat_erat_1[simp]: "rat_of_erat (1::erat) = 1"
  unfolding one_erat_def by simp

lemma rat_of_erat_le_1:
  fixes a :: erat
  shows "a \<le> 1 \<Longrightarrow> rat_of_erat a \<le> 1"
  by (cases a) (auto simp: one_erat_def)

lemma abs_erat_one[simp]: "\<bar>1\<bar> = (1::erat)"
  unfolding one_erat_def by simp

lemma erat_mult_zero[simp]:
  fixes a :: erat
  shows "a * 0 = 0"
  by (cases a) (simp_all add: zero_erat_def)

lemma erat_zero_mult[simp]:
  fixes a :: erat
  shows "0 * a = 0"
  by (cases a) (simp_all add: zero_erat_def)

lemma erat_m1_less_0[simp]: "-(1::erat) < 0"
  by (simp add: zero_erat_def one_erat_def)

lemma erat_times[simp]:
  "1 \<noteq> (\<infinity>::erat)" "(\<infinity>::erat) \<noteq> 1"
  "1 \<noteq> -(\<infinity>::erat)" "-(\<infinity>::erat) \<noteq> 1"
  by (auto simp: one_erat_def)

lemma erat_plus_1[simp]:
  "1 + erat r = erat (r + 1)"
  "erat r + 1 = erat (r + 1)"
  "1 + -(\<infinity>::erat) = -\<infinity>"
  "-(\<infinity>::erat) + 1 = -\<infinity>"
  unfolding one_erat_def by auto

lemma erat_zero_times[simp]:
  fixes a b :: erat
  shows "a * b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_mult_eq_PInfty[simp]:
  "a * b = (\<infinity>::erat) \<longleftrightarrow>
    (a = \<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = -\<infinity>)"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_mult_eq_MInfty[simp]:
  "a * b = -(\<infinity>::erat) \<longleftrightarrow>
    (a = \<infinity> \<and> b < 0) \<or> (a < 0 \<and> b = \<infinity>) \<or> (a = -\<infinity> \<and> b > 0) \<or> (a > 0 \<and> b = -\<infinity>)"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_abs_mult: "\<bar>x * y :: erat\<bar> = \<bar>x\<bar> * \<bar>y\<bar>"
  by (cases x y rule: erat2_cases) (auto simp: abs_mult)

lemma erat_0_less_1[simp]: "0 < (1::erat)"
  by (simp_all add: zero_erat_def one_erat_def)

lemma erat_mult_minus_left[simp]:
  fixes a b :: erat
  shows "-a * b = - (a * b)"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_mult_minus_right[simp]:
  fixes a b :: erat
  shows "a * -b = - (a * b)"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_mult_infty[simp]:
  "a * (\<infinity>::erat) = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma erat_infty_mult[simp]:
  "(\<infinity>::erat) * a = (if a = 0 then 0 else if 0 < a then \<infinity> else - \<infinity>)"
  by (cases a) auto

lemma erat_mult_strict_right_mono:
  assumes "a < b"
    and "0 < c"
    and "c < (\<infinity>::erat)"
  shows "a * c < b * c"
  using assms
  by (cases rule: erat3_cases[of a b c]) (auto simp: zero_le_mult_iff)

lemma erat_mult_strict_left_mono:
  "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c < (\<infinity>::erat) \<Longrightarrow> c * a < c * b"
  using erat_mult_strict_right_mono
  by (simp add: mult.commute[of c])

lemma erat_mult_right_mono:
  fixes a b c :: erat
  assumes "a \<le> b" "0 \<le> c"
  shows "a * c \<le> b * c"
proof (cases "c = 0")
  case False
  with assms show ?thesis
    by (cases rule: erat3_cases[of a b c]) auto
qed auto

lemma erat_mult_left_mono:
  fixes a b c :: erat
  shows "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  using erat_mult_right_mono
  by (simp add: mult.commute[of c])

lemma erat_mult_mono:
  fixes a b c d::erat
  assumes "b \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis erat_mult_right_mono mult.commute order_trans assms)

lemma erat_mult_mono':
  fixes a b c d::erat
  assumes "a \<ge> 0" "c \<ge> 0" "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
by (metis erat_mult_right_mono mult.commute order_trans assms)

lemma erat_mult_mono_strict:
  fixes a b c d::erat
  assumes "b > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
proof -
  have "c < \<infinity>" using \<open>c < d\<close> by auto
  then have "a * c < b * c" by (metis erat_mult_strict_left_mono[OF assms(3) assms(2)] mult.commute)
  moreover have "b * c \<le> b * d" using assms(2) assms(4) by (simp add: assms(1) erat_mult_left_mono less_imp_le)
  ultimately show ?thesis by simp
qed

lemma erat_mult_mono_strict':
  fixes a b c d::erat
  assumes "a > 0" "c > 0" "a < b" "c < d"
  shows "a * c < b * d"
  using assms erat_mult_mono_strict by auto

lemma zero_less_one_erat[simp]: "0 \<le> (1::erat)"
  by (simp add: one_erat_def zero_erat_def)

lemma erat_0_le_mult[simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a * (b :: erat)"
  by (cases rule: erat2_cases[of a b]) auto

lemma erat_right_distrib:
  fixes r a b :: erat
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> r * (a + b) = r * a + r * b"
  by (cases rule: erat3_cases[of r a b]) (simp_all add: field_simps)

lemma erat_left_distrib:
  fixes r a b :: erat
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a + b) * r = a * r + b * r"
  by (cases rule: erat3_cases[of r a b]) (simp_all add: field_simps)

lemma erat_mult_le_0_iff:
  fixes a b :: erat
  shows "a * b \<le> 0 \<longleftrightarrow> (0 \<le> a \<and> b \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> b)"
  by (cases rule: erat2_cases[of a b]) (simp_all add: mult_le_0_iff)

lemma erat_zero_le_0_iff:
  fixes a b :: erat
  shows "0 \<le> a * b \<longleftrightarrow> (0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0)"
  by (cases rule: erat2_cases[of a b]) (simp_all add: zero_le_mult_iff)

lemma erat_mult_less_0_iff:
  fixes a b :: erat
  shows "a * b < 0 \<longleftrightarrow> (0 < a \<and> b < 0) \<or> (a < 0 \<and> 0 < b)"
  by (cases rule: erat2_cases[of a b]) (simp_all add: mult_less_0_iff)

lemma erat_zero_less_0_iff:
  fixes a b :: erat
  shows "0 < a * b \<longleftrightarrow> (0 < a \<and> 0 < b) \<or> (a < 0 \<and> b < 0)"
  by (cases rule: erat2_cases[of a b]) (simp_all add: zero_less_mult_iff)

lemma erat_left_mult_cong:
  fixes a b c :: erat
  shows  "c = d \<Longrightarrow> (d \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> a * c = b * d"
  by (cases "c = 0") simp_all

lemma erat_right_mult_cong:
  fixes a b c :: erat
  shows "c = d \<Longrightarrow> (d \<noteq> 0 \<Longrightarrow> a = b) \<Longrightarrow> c * a = d * b"
  by (cases "c = 0") simp_all

lemma erat_distrib:
  fixes a b c :: erat
  assumes "a \<noteq> \<infinity> \<or> b \<noteq> -\<infinity>"
    and "a \<noteq> -\<infinity> \<or> b \<noteq> \<infinity>"
    and "\<bar>c\<bar> \<noteq> \<infinity>"
  shows "(a + b) * c = a * c + b * c"
  using assms
  by (cases rule: erat3_cases[of a b c]) (simp_all add: field_simps)

lemma numeral_eq_erat [simp]: "numeral w = erat (numeral w)"
proof (induct w rule: num_induct)
  case One
  then show ?case
    by simp
next
  case (inc x)
  then show ?case
    by (simp add: inc numeral_inc)
qed

lemma distrib_left_erat_nn:
  "c \<ge> 0 \<Longrightarrow> (x + y) * erat c = x * erat c + y * erat c"
  by(cases x y rule: erat2_cases)(simp_all add: ring_distribs)

lemma sum_erat_right_distrib:
  fixes f :: "'a \<Rightarrow> erat"
  shows "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> r * sum f A = (\<Sum>n\<in>A. r * f n)"
  by (induct A rule: infinite_finite_induct)  (auto simp: erat_right_distrib sum_nonneg)

lemma sum_erat_left_distrib:
  "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> sum f A * r = (\<Sum>n\<in>A. f n * r :: erat)"
  using sum_erat_right_distrib[of A f r] by (simp add: mult_ac)

lemma sum_distrib_right_erat:
  "c \<ge> 0 \<Longrightarrow> sum f A * erat c = (\<Sum>x\<in>A. f x * c :: erat)"
by(subst sum_comp_morphism[where h="\<lambda>x. x * erat c", symmetric])(simp_all add: distrib_left_erat_nn)

lemma erat_le_epsilon:
  fixes x y :: erat
  assumes "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (cases "x = -\<infinity> \<or> x = \<infinity> \<or> y = -\<infinity> \<or> y = \<infinity>")
  case True
  then show ?thesis
    using assms[of 1] by auto
next
  case False
  then obtain p q where "x = erat p" "y = erat q"
    by (metis MInfty_eq_minfinity erat.distinct(3) uminus_erat.elims)
  then show ?thesis 
    by (metis assms field_le_epsilon erat_less(2) erat_less_eq(3) plus_erat.simps(1))
qed

lemma erat_le_epsilon2:
  fixes x y :: erat
  assumes "\<And>e::rat. 0 < e \<Longrightarrow> x \<le> y + erat e"
  shows "x \<le> y"
proof (rule erat_le_epsilon)
  show "\<And>\<epsilon>::erat. 0 < \<epsilon> \<Longrightarrow> x \<le> y + \<epsilon>"
  using assms less_erat.elims(2) zero_less_rat_of_erat by fastforce
qed

lemma erat_le_rat:
  fixes x y :: erat
  assumes "\<And>z. x \<le> erat z \<Longrightarrow> y \<le> erat z"
  shows "y \<le> x"
  by (metis assms erat_bot erat_cases erat_infty_less_eq(2) erat_less_eq(1) linorder_le_cases)

lemma prod_erat_0:
  fixes f :: "'a \<Rightarrow> erat"
  shows "(\<Prod>i\<in>A. f i) = 0 \<longleftrightarrow> finite A \<and> (\<exists>i\<in>A. f i = 0)"
proof (cases "finite A")
  case True
  then show ?thesis by (induct A) auto
qed auto

lemma prod_erat_pos:
  fixes f :: "'a \<Rightarrow> erat"
  assumes pos: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "0 \<le> (\<Prod>i\<in>I. f i)"
proof (cases "finite I")
  case True
  from this pos show ?thesis
    by induct auto
qed auto

lemma prod_PInf:
  fixes f :: "'a \<Rightarrow> erat"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "(\<Prod>i\<in>I. f i) = \<infinity> \<longleftrightarrow> finite I \<and> (\<exists>i\<in>I. f i = \<infinity>) \<and> (\<forall>i\<in>I. f i \<noteq> 0)"
proof (cases "finite I")
  case True
  from this assms show ?thesis
  proof (induct I)
    case (insert i I)
    then have pos: "0 \<le> f i" "0 \<le> prod f I"
      by (auto intro!: prod_erat_pos)
    from insert have "(\<Prod>j\<in>insert i I. f j) = \<infinity> \<longleftrightarrow> prod f I * f i = \<infinity>"
      by auto
    also have "\<dots> \<longleftrightarrow> (prod f I = \<infinity> \<or> f i = \<infinity>) \<and> f i \<noteq> 0 \<and> prod f I \<noteq> 0"
      using prod_erat_pos[of I f] pos
      by (cases rule: erat2_cases[of "f i" "prod f I"]) auto
    also have "\<dots> \<longleftrightarrow> finite (insert i I) \<and> (\<exists>j\<in>insert i I. f j = \<infinity>) \<and> (\<forall>j\<in>insert i I. f j \<noteq> 0)"
      using insert by (auto simp: prod_erat_0)
    finally show ?case .
  qed simp
qed auto

lemma prod_erat: "(\<Prod>i\<in>A. erat (f i)) = erat (prod f A)"
proof (cases "finite A")
  case True
  then show ?thesis
    by induct (auto simp: one_erat_def)
next
  case False
  then show ?thesis
    by (simp add: one_erat_def)
qed


subsubsection "Disjoint Sums"

lemma erat_of_sum:
  fixes
    X :: "'a set" and
    f :: "'a \<Rightarrow> nat"
  shows "(\<Sum>x\<in>X. (erat_of (f x))) = erat_of (\<Sum>x\<in>X. (f x))"
proof (unfold erat_of.simps, simp)
  have "\<forall>x\<in>X. Fract (int (f x)) 1 = f x" by (simp add: of_rat_rat)
  hence *: "(\<Sum>x\<in>X. Fract (int (f x)) 1) = (\<Sum>x\<in>X. f x)"
    by (metis (mono_tags, lifting) Fract_of_nat_eq of_nat_sum of_rat_of_nat_eq sum.cong)
  have "Fract (\<Sum>x\<in>X. int (f x)) 1 = (\<Sum>x\<in>X. f x)"
    by (metis of_int_of_nat_eq of_int_rat of_nat_sum of_rat_of_int_eq)
  thus "(\<Sum>x\<in>X. Fract (int (f x)) 1) = Fract (\<Sum>x\<in>X. int (f x)) 1" using *
    by (metis of_rat_eq_iff)
qed


lemma erat_of_leq: "(x \<le> y) \<longleftrightarrow> (erat_of x \<le> erat_of y)"
proof
  assume "x \<le> y"
  thus "erat_of x \<le> erat_of y" by simp
next
  assume "erat_of x \<le> erat_of y"
  hence "Fract x 1 \<le> Fract y 1" using erat_of.simps by simp
  thus "x \<le> y" by simp
qed


lemma rat_erat_simp: 
fixes e :: erat
assumes rational: "\<bar>e\<bar> \<noteq> \<infinity>"
shows "e = erat (rat_of_erat e)"
using assms 
by auto

lemma disjoint_erat_sum:
fixes 
  P :: "'x set set" and
  f :: "'x \<Rightarrow> erat"
assumes 
  fin: "finite P" and
  disj: "disjoint P" and
  all_fin: "\<forall>p \<in> P. finite p"
shows "sum f (\<Union> P) = sum (sum f) P"
using assms
proof (induct P arbitrary: f  rule: finite_induct)
case empty
then show ?case by simp
next
case (insert p X)
fix
  p :: "'x set" and
  X :: "'x set set"
assume 
  fin: "finite X" and
  new: "p \<notin> X" and
  disj_ins: "disjoint (insert p X)" and
  elems_fin: "Ball (insert p X) finite"
show "sum f (\<Union> (insert p X)) = sum (sum f) (insert p X)"
  proof -
  have disj_u: "p \<inter> \<Union> X = {}" 
    using disj_ins insert.hyps(2) insert_partition
    by (metis disjoint_def new)
  have fin_p: "finite p" 
    using elems_fin insert.prems(2) 
    by simp
  have fin_u: "finite (\<Union> X)" 
    using fin finite_Union elems_fin 
    by simp
  have sum_u: "sum f (\<Union> (insert p X)) = sum f (p \<union> \<Union> X)" by simp
  moreover have "... = sum f p + sum f (\<Union> X)"
    using disj_u fin_u fin_p sum.union_disjoint sum_Un 
    by blast
  moreover have "... = sum (sum f) (insert p X)"
    using Sup_insert disjoint_def disjoint_sum disj_ins fin fin_p fin_u
    by (metis calculation finite.insertI finite_UnI partitionI)
  ultimately show ?thesis by simp
  qed
qed

lemma erat_sum_distrib_left:
fixes 
  X :: "'x set" and
  y :: erat and
  f :: "'x \<Rightarrow> erat"
assumes 
  rational: "\<bar>y\<bar> \<noteq> \<infinity>" and 
  set_rational: "\<forall>x \<in> X. (\<bar>f x\<bar> \<noteq> \<infinity>)"
shows "y * sum f X = (\<Sum>x\<in>X. y * f x)"
using assms
proof (induct X rule: infinite_finite_induct)
case (infinite A)
then show ?case by simp
next
case empty
then show ?case by simp
next
case (insert x S)
fix 
  S :: "'x set" and
  x :: 'x
assume 
  fin: "finite S" and
  new: "x \<notin> S" and
  ih: " (\<bar>y\<bar> \<noteq> \<infinity> \<Longrightarrow> \<forall>s\<in>S. \<bar>f s\<bar> \<noteq> \<infinity> \<Longrightarrow> y * sum f S = (\<Sum>s\<in>S. y * f s))" and
  set_rational': "\<forall>s\<in>insert x S. \<bar>f s\<bar> \<noteq> \<infinity>"
have *: "\<bar>sum f S\<bar> \<noteq> \<infinity>" 
  using set_rational' fin 
  by (simp add: sum_Inf)
have "y * sum f (insert x S) = y * (sum f S + f x)" 
  using new
  by (simp add: add.commute fin)
moreover have "... = y * sum f S + y * f x" 
  using rational set_rational' erat_distrib * abs_erat.simps(2) abs_erat.simps(3) mult.commute
  by (metis (no_types, lifting))
moreover have "(\<Sum>z \<in> (insert x S). y * f z) = ((\<Sum>z \<in> S. y * f z) + y * f x)" 
  using new
  by (simp add: add.commute fin)
ultimately show "y * sum f (insert x S) = (\<Sum>x\<in>insert x S. y * f x)"
  using * fin ih rational sum_Inf
  by metis
qed 

end