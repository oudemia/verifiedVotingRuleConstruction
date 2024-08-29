theory Extended_Rat
imports 
    "HOL-Library.Extended_Nat"
begin

section \<open>Definition\<close>

text\<open>
  Extended rationals are a simplified representation of rational numbers extended by the
  special value "\<infinity>", i.e., infinity. An extended rational that unequal to \<infinity> is represented
  as the quotient of two integers; its numerator and its denominator.
\<close>

subsection \<open>Non-Negative Extended Rationals\<close>

definition eratrel_nn :: "(enat \<times> nat) \<Rightarrow> (enat \<times> nat) \<Rightarrow> bool"
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
    x1 x2 :: enat and
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
    hence "x1 * y2 \<noteq> \<infinity>" using not_enat_eq by fastforce
    moreover have "x1 * y2 = x2 * y1" using eq by auto
    ultimately have "x2 * y1 \<noteq> \<infinity>" using not_enat_eq by fastforce
    hence "x2 \<noteq> \<infinity>" using eq enat_0_iff(2) imult_is_infinity by auto
    thus "x1 = \<infinity> \<longleftrightarrow> x2 = \<infinity>" using x1_not_inf by blast
  qed
qed

lemma transp_eratrel_nn: "transp eratrel_nn"
proof (rule transpI, unfold split_paired_all)
  fix 
    x1 x2 x3 :: enat and
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
    hence "x1 * y2 \<noteq> \<infinity>" using not_enat_eq by fastforce
    moreover have "x1 * y2 = x2 * y1" using eq12 by auto
    ultimately have "x2 * y1 \<noteq> \<infinity>" using not_enat_eq by fastforce
    hence "x2 \<noteq> \<infinity>" using eq12 enat_0_iff(2) imult_is_infinity by auto
    hence "x2 * y3 \<noteq> \<infinity>" using eq23  using not_enat_eq by fastforce
    moreover have "x2 * y3 = x3 * y2" using eq23 by auto
    ultimately have "x3 * y2 \<noteq> \<infinity>"  using not_enat_eq by fastforce
    hence x3_not_inf: "x3 \<noteq> \<infinity>" using not_enat_eq eq23 by fastforce
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

quotient_type  erat_nn = "enat \<times> nat" / partial: "eratrel_nn"
  morphisms Rep_Erat Abs_Erat
  by (rule part_equivp_eratrel_nn)

value "Rep_Erat x"
value "Abs_Erat x"


subsubsection \<open>Constructors, representation and asic operations\<close>

lift_definition Fract :: "enat \<Rightarrow> nat \<Rightarrow> erat_nn"
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
is "\<lambda>x y. (fst x * enat (snd y) + fst y * enat (snd x), snd x * snd y)"
proof (auto)
  fix 
    x1 x2 x3 x4 :: enat and
    y1 y2 y3 y4 :: nat
  assume 
    y1: "0 < y1" and y2: "0 < y2" and y3: "0 < y3" and y4: "0 < y4" and
    eq12: "x1 * enat y2 = x2 * enat y1" and
    eq34: "x3 * enat y4 = x4 * enat y3"
  show "(x1 * enat y3 + x3 * enat y1) * enat (y2 * y4) =
       (x2 * enat y4 + x4 * enat y2) * enat (y1 * y3)"
  proof cases
    assume x1_inf: "x1 = \<infinity>"
    hence x2_inf: "x2 = \<infinity>" using eq12 eratrel_inf using y2 by fastforce
    have "(x1 * enat y3 + x3 * enat y1) * enat (y2 * y4) = \<infinity>" using x1_inf y1 y2 y3 y4 by auto
    moreover have "(x2 * enat y4 + x4 * enat y2) * enat (y1 * y3) = \<infinity>" using x2_inf y1 y2 y3 y4 by auto
    finally show "(x1 * enat y3 + x3 * enat y1) * enat (y2 * y4) = 
        (x2 * enat y4 + x4 * enat y2) * enat (y1 * y3)" by simp
  next
    assume x1_not_inf: "x1 \<noteq> \<infinity>"
    hence x2_not_inf: "x2 \<noteq> \<infinity>" using eq12 eratrel_inf y1 y2 by fastforce

  qed
qed

lift_definition uminus_int :: "erat_nn \<Rightarrow> erat_nn"
is "\<lambda>x y. (fst x * enat (snd y) - fst y * enat (snd x), snd x * snd y)"
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



subsection \<open>General Extended Rationals\<close>

definition eratrel :: "(erat_nn \<times>  erat_nn) \<Rightarrow> (erat_nn \<times> erat_nn) \<Rightarrow> bool"
  where "eratrel = (\<lambda>(x, y) (u, v). x + v = u + y)"

lemma eralrel_iff [simp]: "intrel (x, y) (u, v) \<longleftrightarrow> x + v = u + y"
  by (simp add: eratrel_def)

end