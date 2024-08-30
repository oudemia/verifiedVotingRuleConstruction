theory Extended_Rat
imports 
    "HOL-Library.Extended_Nat"
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

typedef erat = "UNIV :: rat option set" ..

definition erat :: "rat \<Rightarrow> erat" where
  "erat r = Abs_erat (Some r)"

instantiation erat :: infinity
begin
definition "\<infinity> = Abs_erat None"
instance ..
end

lemma not_infinity_eq [iff]: "(x \<noteq> \<infinity>) = (\<exists>i. x = erat i)"
proof (cases x)
  case (Abs_erat y)
  then show ?thesis 
  proof (cases y)
    case None
    hence inf: "x = \<infinity>" by (simp add: Abs_erat(1) infinity_erat_def)
    hence "\<forall>i. x \<noteq> Abs_erat (Some i)" using Abs_erat(1) Abs_erat_inject None by blast
    hence "\<forall>i. x \<noteq> erat i" by (simp add: erat_def)
    thus ?thesis using inf by simp
  next
    case (Some a)
    hence not_inf: "x = erat a" by (simp add: Abs_erat(1) erat_def)
    hence "x \<noteq> \<infinity>" by (simp add: Abs_erat_inject erat_def infinity_erat_def)
    thus ?thesis using not_inf by blast
  qed
qed

lemma not_erat_eq [iff]: "(\<forall>y. x \<noteq> erat y) = (x = \<infinity>)"
  using Extended_Rat.not_infinity_eq by blast

declare [[coercion "erat::rat\<Rightarrow>erat"]]

lemma erat_ex_split: "(\<exists>c::erat. P c) \<longleftrightarrow> P \<infinity> \<or> (\<exists>c::rat. P c)"
  by (metis not_erat_eq)

old_rep_datatype erat "\<infinity> :: erat"
proof -
  fix 
    P :: "erat \<Rightarrow> bool" and
    r :: erat
  assume "\<And>j. P (erat j)" and "P \<infinity>"
  then show "P r"
  proof induct
    case (Abs_erat y) 
    thus ?case
      by (cases y rule: option.exhaust)
         (auto simp: erat_def infinity_erat_def)
  qed
next
  fix r1 r2 :: rat
  show "(erat r1 = erat r2) = (r1 = r2)"
  proof auto
    assume "erat r1 = erat r2"
    hence "Some r1 = Some r2" by (simp add: Abs_erat_inject erat_def)
    thus "r1 = r2" by simp
  qed
next
  fix r :: rat
  show "erat r \<noteq> \<infinity>" by blast
qed

primrec the_erat :: "erat \<Rightarrow> rat"
  where "the_erat (erat n) = n"



instantiation erat :: zero_neq_one
begin

definition
  "0 = erat (Fract 0 1)"

definition
  "1 = erat (Fract 1 1)"

instance sorry
  (* moreover have "Fract 0 1 \<noteq> Fract 1 1" using One_rat_def Zero_rat_def by auto
  hence "erat (Fract 0 1) \<noteq> erat (Fract 1 1)" by blast
  thus "0 \<noteq> 1" *)

end
subsection \<open>Addition\<close>

lemmas erat2_cases = erat.exhaust[case_product erat.exhaust]
lemmas erat3_cases = erat.exhaust[case_product erat.exhaust erat.exhaust]


instantiation erat :: comm_monoid_add
begin

definition [nitpick_simp]:
  "m + n = (case m of \<infinity> \<Rightarrow> \<infinity> | erat m \<Rightarrow> (case n of \<infinity> \<Rightarrow> \<infinity> | erat n \<Rightarrow> erat (m + n)))"

lemma plus_erat_simps [simp, code]:
  fixes q :: erat
  shows "erat m + erat n = erat (m + n)"
    and "\<infinity> + q = \<infinity>"
    and "q + \<infinity> = \<infinity>"
  by (simp_all add: plus_erat_def split: erat.splits)

instance
proof
  fix n m q :: erat
  show "n + m + q = n + (m + q)"
    by (cases n m q rule: erat3_cases) auto
  show "n + m = m + n"
    by (cases n m rule: erat2_cases) auto
  show "0 + n = n"
  proof (cases n)
    case (erat r)
    hence "0 + n = erat (0 + r)" by (simp add: Zero_rat_def zero_erat_def)
    thus ?thesis by (simp add: erat)
  next
    case infinity
    hence "0 + n = \<infinity>" by simp
    thus ?thesis by (simp add: infinity)
  qed
qed

end

subsection \<open>Multiplication\<close>

instantiation erat :: "{comm_semiring_1, semiring_no_zero_divisors}"
begin

definition times_erat_def [nitpick_simp]:
  "m * n = (case m of \<infinity> \<Rightarrow> if n = 0 then 0 else \<infinity> | erat m \<Rightarrow>
    (case n of \<infinity> \<Rightarrow> if m = 0 then 0 else \<infinity> | erat n \<Rightarrow> erat (m * n)))"

lemma times_erat_simps [simp, code]:
  "erat m * erat n = erat (m * n)"
  "\<infinity> * \<infinity> = (\<infinity>::erat)"
  "\<infinity> * erat n = (if n = 0 then 0 else \<infinity>)"
  "erat m * \<infinity> = (if m = 0 then 0 else \<infinity>)"
  unfolding times_erat_def zero_erat_def 
proof auto
  fix n
  assume "n = Fract 0 1"
  show "Fract 0 1 = 0" by (simp add: Zero_rat_def)
next
 fix n
  assume *: "Fract 0 1 \<noteq> 0" and "n = 0"
  show "False" using * by (simp add: Zero_rat_def)
qed

lemma times_rat_assoc: "\<forall> a b c :: erat. ((a \<noteq> \<infinity> \<and> b \<noteq> \<infinity> \<and> c \<noteq> \<infinity>) \<longrightarrow> (a * b) * c = a * (b * c))"
  by auto

lemma times_zero_assoc: "\<forall> a b c :: erat. ((a = 0 \<or> b = 0 \<or> c = 0) \<longrightarrow> (a * b) * c = a * (b * c))"
proof auto
  fix b c :: erat
  have "0 * b = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_cancel_left1 zero_erat_def)
  hence "0 * b * c = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_cancel_left1 zero_erat_def)
  moreover have "0 * (b * c) = 0" using times_erat_simps by (metis (mono_tags) Zero_rat_def erat.exhaust mult_zero_left zero_erat_def)
  ultimately show "(0 * b) * c = 0 * (b * c)" by simp
next
  fix a c :: erat
  have *: "a * 0 = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_zero_right zero_erat_def)
  hence **: "a * 0 * c = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_cancel_left1 zero_erat_def)
  moreover have "0 * c = 0" using times_erat_simps by (metis (mono_tags) Zero_rat_def erat.exhaust mult_zero_left zero_erat_def)
  moreover have " a * (0 * c) = 0" using * ** by simp
  ultimately show "a * 0 * c = a * (0 * c)" by simp
next
 fix a b :: erat
  have "0 * b = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_cancel_left1 zero_erat_def)
  hence "a * b * 0 = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_zero_right zero_erat_def)
  moreover have "b * 0 = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_zero_right zero_erat_def)
  moreover have " a * (b * 0) = 0" using times_erat_simps by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust mult_cancel_right1 zero_erat_def)
  ultimately show " a * b * 0 = a * (b * 0)" by simp
qed

lemma zero_helper: "\<forall> a b :: erat. ((a \<noteq> 0 \<and> b \<noteq> 0 ) \<longrightarrow> (a * b) \<noteq> 0)"
proof auto
  fix a b :: erat
  assume *: "a \<noteq> 0" and **: "b \<noteq> 0" and ***: "a * b = 0"
  show "False"
  proof cases
    assume "a = \<infinity> \<or> b = \<infinity>"
    hence "a * b = \<infinity>" using * ** times_erat_simps zero_erat_def by (metis (mono_tags, lifting) Zero_rat_def erat.exhaust)
    hence "a * b \<noteq> 0" by (simp add: zero_erat_def)
    thus "False" using *** by simp
  next
    assume "\<not>(a = \<infinity> \<or> b = \<infinity>)"
    hence no_inf: "a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>" by simp
    hence "\<exists> ra :: rat. a = erat ra \<and> ra \<noteq> 0" using *  Zero_rat_def zero_erat_def by fastforce
    moreover have "\<exists> rb :: rat. b = erat rb \<and> rb \<noteq> 0"  using ** no_inf Zero_rat_def zero_erat_def by fastforce
    ultimately have "\<exists> ra rb :: rat. (a * b) = erat (ra * rb) \<and> ra \<noteq> 0 \<and> rb \<noteq> 0" using times_erat_simps by blast
    hence "a * b \<noteq> 0" by (metis Zero_rat_def erat.inject mult_eq_0_iff zero_erat_def) 
    thus "False" using *** by simp
  qed
qed

instance
proof
  fix a b c :: erat
  show "(a * b) * c = a * (b * c)"
  proof cases
    assume no_inf: "a \<noteq> \<infinity> \<and> b \<noteq> \<infinity> \<and> c \<noteq> \<infinity>"
    thus ?thesis using times_rat_assoc by auto
  next
    assume "\<not>(a \<noteq> \<infinity> \<and> b \<noteq> \<infinity> \<and> c \<noteq> \<infinity>)"
    hence inf: "a = \<infinity> \<or> b = \<infinity> \<or> c = \<infinity>" by simp
    thus ?thesis 
    proof cases
      assume "a = 0 \<or> b = 0 \<or> c = 0"
      thus ?thesis using times_zero_assoc by blast
    next
      assume "\<not>(a = 0 \<or> b = 0 \<or> c = 0)"
      hence no_zero: "a \<noteq> 0 \<and> b \<noteq> 0 \<and> c \<noteq> 0" by simp
    thus ?thesis 
    proof cases
      assume a_inf: "a = \<infinity>"
      hence "a * b = \<infinity>" using no_zero times_erat_def by simp
      hence *: "(a * b) * c = \<infinity>" using no_zero times_erat_def by simp
      have "b \<noteq> 0 \<and> c \<noteq> 0" using no_zero by simp
      hence "b * c \<noteq> 0" using zero_helper by simp
      hence "a * (b * c) = \<infinity>" using a_inf times_erat_def by simp
      thus ?thesis using * by simp
    next
      assume a_fin: "\<not> a = \<infinity>"
      hence b_or_c_inf: "b = \<infinity> \<or> c = \<infinity>" using inf by blast
      thus ?thesis
      proof cases
        assume b_inf: "b = \<infinity>"
        hence *: "a * b = \<infinity>" using no_zero times_erat_def using a_fin zero_helper by fastforce
        hence **: "(a * b) * c = \<infinity>" using no_zero times_erat_def by simp
        have "b * c = \<infinity>" using  b_inf no_zero times_erat_def  by simp
        hence "a * (b * c) = \<infinity>" using * b_inf by auto
        thus ?thesis using ** by simp
      next
        assume b_fin: "\<not> b = \<infinity>"
        hence c_inf: "c = \<infinity>" using b_or_c_inf by auto
        hence "b * c = \<infinity>" using no_zero times_erat_def using b_fin zero_helper by fastforce
        hence **: "a * (b * c) = \<infinity>" using no_zero times_erat_def a_fin zero_helper by fastforce
        moreover have "(a * b) * c = \<infinity>" using no_zero c_inf a_fin b_fin zero_helper by fastforce
        thus ?thesis using ** by simp
      qed
    qed
  qed
qed
next
 fix a b  :: erat
  show "a * b = b * a"
  proof cases
    assume "a = \<infinity> \<or> b = \<infinity>"
    thus ?thesis by (metis not_erat_eq times_erat_simps(3) times_erat_simps(4))
  next
    assume "\<not>(a = \<infinity> \<or> b = \<infinity>)"
    hence "a \<noteq> \<infinity> \<and> b \<noteq> \<infinity>" by simp
    hence "\<exists> ra rb :: rat. a = erat ra \<and> b = erat rb" by simp
    then show ?thesis by (metis  mult.commute times_erat_simps(1))
  qed 
next
  fix a  :: erat
  show "1 * a = a" using  one_erat_def times_erat_simps zero_neq_one by (metis (mono_tags, lifting) One_rat_def erat.exhaust mult_1)
next
  fix a b c :: erat
  show distr: "(a + b) * c = a * c + b * c"
  oops

end


section \<open>Definition\<close>

text\<open>
  Extended rationals are a simplified representation of rational numbers extended by the
  special value "\<infinity>", i.e., infinity. An extended rational that unequal to \<infinity> is represented
  as the quotient of two integers; its numerator and its denominator.
\<close>

subsection \<open>Non-Negative Extended Rationals\<close>

definition eratrel_nn :: "(erat \<times> nat) \<Rightarrow> (erat \<times> nat) \<Rightarrow> bool"
  where "eratrel_nn = (\<lambda>x y. snd x \<noteq> 0 \<and> snd y \<noteq> 0 \<and> fst x * snd y = fst y * snd x)"

value "eratrel_nn (1, 2) (1, 2)"
value "eratrel_nn (\<infinity>, 1) (\<infinity>, 1)"
value "eratrel_nn (\<infinity>, 1) (\<infinity>, 5)"

lemma  eratrel_nn [simp]: "eratrel_nn (x1, y1) (x2, y2) \<longleftrightarrow>  (y1 \<noteq> 0 \<and> y2 \<noteq> 0 \<and> x1 * y2 = x2 * y1)"
  by (simp add:  eratrel_nn_def)

lemma exists_eratrel_nn_refl: "\<exists>x. eratrel_nn x x"
  by (auto intro!: one_neq_zero)

lemma symp_eratrel_nn: "symp eratrel_nn"
  by (simp add:  eratrel_nn_def symp_def)

lemma eratrel_inf: "eratrel_nn (x1, y1) (x2, y2) \<longrightarrow> (x1 = \<infinity> \<longleftrightarrow> x2 = \<infinity>)"
proof
  fix 
    x1 x2 :: erat and
    y1 y2 :: nat
  assume eq: "eratrel_nn (x1, y1) (x2, y2)"
  show "x1 = \<infinity> \<longleftrightarrow> x2 = \<infinity>"
  proof cases
    assume x1_inf: "x1 = \<infinity>"
    hence "x1 * y2 = \<infinity>" using eq by auto
    moreover have "x1 * y2 = x2 * y1" using eq by auto
    ultimately have "x2 * y1 = \<infinity>" by auto
    hence "x2 = \<infinity>" by (simp add: imult_is_infinity)
    thus "x1 = \<infinity> \<longleftrightarrow> x2 = \<infinity>" using x1_inf by simp
  next
    assume x1_not_inf: "x1 \<noteq> \<infinity>" 
    hence "x1 * y2 \<noteq> \<infinity>" using not_erat_eq by fastforce
    moreover have "x1 * y2 = x2 * y1" using eq by auto
    ultimately have "x2 * y1 \<noteq> \<infinity>" using not_erat_eq by fastforce
    hence "x2 \<noteq> \<infinity>" using eq erat_0_iff(2) imult_is_infinity by auto
    thus "x1 = \<infinity> \<longleftrightarrow> x2 = \<infinity>" using x1_not_inf by blast
  qed
qed

lemma transp_eratrel_nn: "transp eratrel_nn"
proof (rule transpI, unfold split_paired_all)
  fix 
    x1 x2 x3 :: erat and
    y1 y2 y3 :: nat
  assume eq12: "eratrel_nn (x1, y1) (x2, y2)"
  assume eq23: "eratrel_nn (x2, y2) (x3, y3)"
  show "eratrel_nn (x1, y1) (x3, y3)"
  proof cases
    assume x1_inf: "x1 = \<infinity>"
    hence x2_inf: "x2 = \<infinity>" using eq12 eratrel_inf by blast
    have "x3 = \<infinity>"  using x2_inf eq23 eratrel_inf by blast
    hence "x1 * y3 = x3 * y1" using eq12 eq23 x1_inf by auto
    thus "eratrel_nn (x1, y1) (x3, y3)" using eq12 eq23 by auto
  next
    assume x1_not_inf: "x1 \<noteq> \<infinity>" 
    hence "x1 * y2 \<noteq> \<infinity>" using not_erat_eq by fastforce
    moreover have "x1 * y2 = x2 * y1" using eq12 by auto
    ultimately have "x2 * y1 \<noteq> \<infinity>" using not_erat_eq by fastforce
    hence "x2 \<noteq> \<infinity>" using eq12 erat_0_iff(2) imult_is_infinity by auto
    hence "x2 * y3 \<noteq> \<infinity>" using eq23  using not_erat_eq by fastforce
    moreover have "x2 * y3 = x3 * y2" using eq23 by auto
    ultimately have "x3 * y2 \<noteq> \<infinity>"  using not_erat_eq by fastforce
    hence x3_not_inf: "x3 \<noteq> \<infinity>" using not_erat_eq eq23 by fastforce
    have "y2 * (x1 * y3) = y3 * (x1 * y2)" by (simp add: mult.commute mult.left_commute)
    also have "x1 * y2 = x2 * y1" using eq12 by auto
    also have "y3 * (x2 * y1) = y1 * (x2 * y3)" by (simp add: mult.commute mult.left_commute)
    also have "x2 * y3 = x3 * y2" using eq23 by auto
    also have "y1 * (x3 * y2) = y2 * (x3 * y1)" by (simp add: mult.commute mult.left_commute)
    finally have "y2 * (x1 * y3) = y2 * (x3 * y1)" .
    moreover have "y2 \<noteq> 0" using eq12 by auto
    ultimately have "x1 * y3 = x3 * y1" using x1_not_inf x3_not_inf by auto
    thus "eratrel_nn (x1, y1) (x3, y3)" using eq12 eq23 by auto
  qed
qed

lemma part_equivp_eratrel_nn: "part_equivp eratrel_nn"
  using exists_eratrel_nn_refl part_equivp_refl_symp_transp symp_eratrel_nn transp_eratrel_nn by blast

quotient_type  erat_nn = "erat \<times> nat" / partial: "eratrel_nn"
  morphisms Rep_Erat Abs_Erat
  by (rule part_equivp_eratrel_nn)

value "Rep_Erat x"
value "Abs_Erat x"


subsubsection \<open>Constructors, representation and asic operations\<close>

lift_definition Fract :: "erat \<Rightarrow> nat \<Rightarrow> erat_nn"
  is "\<lambda>a b. if b = 0 then (0, 1) else (a, b)"
  by simp

lemma eq_erat_nn:
  "\<And>a b c d. b \<noteq> 0 \<Longrightarrow> d \<noteq> 0 \<Longrightarrow> Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
  "\<And>a. Fract a 0 = Fract 0 1"
  "\<And>a c. Fract 0 a = Fract 0 c"
  by (transfer, simp)+


instantiation erat_nn :: field
begin

lift_definition zero_erat :: "erat_nn" is "(0, 1)" by simp

lift_definition one_erat :: "erat_nn" is "(1, 1)" by simp

lift_definition plus_erat :: "erat_nn \<Rightarrow> erat_nn \<Rightarrow> erat_nn"
is "\<lambda>x y. (fst x * erat (snd y) + fst y * erat (snd x), snd x * snd y)"
proof (auto)
  fix 
    x1 x2 x3 x4 :: erat and
    y1 y2 y3 y4 :: nat
  assume 
    y1: "0 < y1" and y2: "0 < y2" and y3: "0 < y3" and y4: "0 < y4" and
    eq12: "x1 * erat y2 = x2 * erat y1" and
    eq34: "x3 * erat y4 = x4 * erat y3"
  show "(x1 * erat y3 + x3 * erat y1) * erat (y2 * y4) =
       (x2 * erat y4 + x4 * erat y2) * erat (y1 * y3)"
  proof cases
    assume x1_inf: "x1 = \<infinity>"
    hence x2_inf: "x2 = \<infinity>" using eq12 eratrel_inf using y2 by fastforce
    have "(x1 * erat y3 + x3 * erat y1) * erat (y2 * y4) = \<infinity>" using x1_inf y1 y2 y3 y4 by auto
    moreover have "(x2 * erat y4 + x4 * erat y2) * erat (y1 * y3) = \<infinity>" using x2_inf y1 y2 y3 y4 by auto
    finally show "(x1 * erat y3 + x3 * erat y1) * erat (y2 * y4) = 
        (x2 * erat y4 + x4 * erat y2) * erat (y1 * y3)" by simp
  next
    assume x1_not_inf: "x1 \<noteq> \<infinity>"
    hence x2_not_inf: "x2 \<noteq> \<infinity>" using eq12 eratrel_inf y1 y2 by fastforce

  qed
qed

lift_definition uminus_int :: "erat_nn \<Rightarrow> erat_nn"
is "\<lambda>x y. (fst x * erat (snd y) - fst y * erat (snd x), snd x * snd y)"
  by try

lift_definition minus_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x + v, y + u)"
  by clarsimp

lift_definition times_int :: "int \<Rightarrow> int \<Rightarrow> int"
  is "\<lambda>(x, y) (u, v). (x*u + y*v, x*v + y*u)"
proof (unfold intrel_def, clarify)
  fix s t u v w x y z :: nat
  assume "s + v = u + t" and "w + z = y + x"
  then have "(s + v) * w + (u + t) * x + u * (w + z) + v * (y + x) =
    (u + t) * w + (s + v) * x + u * (y + x) + v * (w + z)"
    by simp
  then show "(s * w + t * x) + (u * z + v * y) = (u * y + v * z) + (s * x + t * w)"
    by (simp add: algebra_simps)
qed



end