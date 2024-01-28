(*  File:       Plurality_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Valentin Springsklee, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Voting Rules\<close>

section \<open>Plurality Rule\<close>

theory Plurality_Rule
  imports "Compositional_Structures/Basic_Modules/Plurality_Module"
          "Compositional_Structures/Revision_Composition"
          "Compositional_Structures/Elect_Composition"
begin

text \<open>
  This is a definition of the plurality voting rule as elimination module as well as directly.
  In the former one, the max operator of the set of the scores of all alternatives is evaluated
  and is used as the threshold value.
\<close>

subsection \<open>Definition\<close>

fun plurality_rule :: "('a, 'v, 'a Result) Electoral_Module" where
  "plurality_rule V A p = elector plurality V A p"

fun plurality_rule' :: "('a, 'v, 'a Result) Electoral_Module" where
  "plurality_rule' V A p =
    ({a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a},
     {a \<in> A. \<exists> x \<in> A. win_count V p x > win_count V p a},
     {})"

lemma plurality_revision_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  shows "plurality' V A p = (plurality_rule'\<down>) V A p"
proof (unfold plurality_rule'.simps plurality'.simps revision_composition.simps,
        standard, clarsimp, standard, safe)
  fix
    a :: "'a" and
    b :: "'a"
  assume
    "finite V" and
    "b \<in> A" and
    "card {i. i \<in> V \<and> above (p i) a = {a}} <
      card {i. i \<in> V \<and> above (p i) b = {b}}" and
    "\<forall> a' \<in> A. card {i. i \<in> V \<and> above (p i) a' = {a'}} \<le>
      card {i. i \<in> V \<and> above (p i) a = {a}}"
  thus False
    using leD
    by blast
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    "finite V" and
    "b \<in> A" and
    "\<not> card {i. i \<in> V \<and> above (p i) b = {b}} \<le>
      card {i. i \<in> V \<and> above (p i) a = {a}}"
  thus "\<exists> x \<in> A.
          card {i. i \<in> V \<and> above (p i) a = {a}}
          < card {i. i \<in> V \<and> above (p i) x = {x}}"
    using linorder_not_less
    by blast
next
  fix
    a :: "'a" and
    b :: "'a"
  assume
    "finite V" and
    "b \<in> A" and
    "a \<in> A" and
    "card {v \<in> V. above (p v) a = {a}} < card {v \<in> V. above (p v) b = {b}}" and
    "\<forall> c \<in> A. card {v \<in> V. above (p v) c = {c}} \<le> card {v \<in> V. above (p v) a = {a}}"
  thus "False"
    by auto
qed

lemma plurality_elim_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "A \<noteq> {}" and
    "finite A" and
    "profile V A p"
  shows "plurality V A p = (plurality_rule'\<down>) V A p"
  using assms plurality_mod_elim_equiv plurality_revision_equiv
  by (metis (full_types))

subsection \<open>Soundness\<close>

theorem plurality_rule_sound[simp]: "social_choice_result.electoral_module plurality_rule"
  unfolding plurality_rule.simps
  using elector_sound plurality_sound
  by metis

theorem plurality_rule'_sound[simp]: "social_choice_result.electoral_module plurality_rule'"
proof (unfold social_choice_result.electoral_module_def, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  have "disjoint3 (
      {a \<in> A. \<forall> a' \<in> A. win_count V p a' \<le> win_count V p a},
      {a \<in> A. \<exists> a' \<in> A. win_count V p a < win_count V p a'},
      {})"
    by auto
  moreover have
    "{a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a} \<union>
      {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x} = A"
    using not_le_imp_less
    by auto
  ultimately show "well_formed_soc_choice A (plurality_rule' V A p)"
    by simp
qed

lemma plurality_rule_only_voters:
  "only_voters_vote plurality_rule"
  unfolding plurality_rule.simps
  using elector_only_voters plurality_only_voters
  by blast

subsection \<open>Electing\<close>

lemma plurality_rule_elect_non_empty:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    A_non_empty: "A \<noteq> {}" and
    prof_A: "profile V A p" and
    fin_A: "finite A"
  shows "elect plurality_rule V A p \<noteq> {}"
proof
  assume plurality_elect_none: "elect plurality_rule V A p = {}"
  obtain max where
    max: "max = Max (win_count V p ` A)"
    by simp
  then obtain a where
    max_a: "win_count V p a = max \<and> a \<in> A"
    using Max_in A_non_empty fin_A prof_A empty_is_image finite_imageI imageE
    by (metis (no_types, lifting))
  hence "\<forall> a' \<in> A. win_count V p a' \<le> win_count V p a"
    using fin_A prof_A max
    by simp
  moreover have "a \<in> A"
    using max_a
    by simp
  ultimately have "a \<in> {a' \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p a'}"
    by blast
  hence "a \<in> elect plurality_rule' V A p"
    by simp
  moreover have "elect plurality_rule' V A p = defer plurality V A p"
    using plurality_elim_equiv fin_A prof_A A_non_empty snd_conv
    unfolding revision_composition.simps
    by metis
  ultimately have "a \<in> defer plurality V A p"  
    by blast
  hence "a \<in> elect plurality_rule V A p"
    by simp
  thus False
    using plurality_elect_none all_not_in_conv
    by metis
qed

text \<open>
  The plurality module is electing.
\<close>

theorem plurality_rule_electing[simp]: "electing plurality_rule"
proof (unfold electing_def, safe)
  show "social_choice_result.electoral_module plurality_rule"
    using plurality_rule_sound
    by simp
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    a :: "'b"
  assume
    fin_A: "finite A" and
    prof_p: "profile V A p" and
    elect_none: "elect plurality_rule V A p = {}" and
    a_in_A: "a \<in> A"
  have "\<forall> A V p. A \<noteq> {} \<and> finite A \<and> profile V A p \<longrightarrow> elect plurality_rule V A p \<noteq> {}"
    using plurality_rule_elect_non_empty
    by (metis (no_types))
  hence empty_A: "A = {}"
    using fin_A prof_p elect_none
    by (metis (no_types))
  thus "a \<in> {}"
    using a_in_A
    by simp
qed

subsection \<open>Property\<close>

lemma plurality_rule_inv_mono_eq:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    elect_a: "a \<in> elect plurality_rule V A p" and
    lift_a: "lifted V A p q a"
  shows "elect plurality_rule V A q = elect plurality_rule V A p \<or>
          elect plurality_rule V A q = {a}"
proof -
  have "a \<in> elect (elector plurality) V A p"
    using elect_a
    by simp
  moreover have eq_p: "elect (elector plurality) V A p = defer plurality V A p"
    by simp
  ultimately have "a \<in> defer plurality V A p"
    by blast
  hence "defer plurality V A q = defer plurality V A p \<or> defer plurality V A q = {a}"
    using lift_a plurality_def_inv_mono_alts
    by metis
  moreover have "elect (elector plurality) V A q = defer plurality V A q"
    by simp
  ultimately show
    "elect plurality_rule V A q = elect plurality_rule V A p \<or>
      elect plurality_rule V A q = {a}"
    using eq_p
    by simp
qed

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_rule_inv_mono[simp]: "invariant_monotonicity plurality_rule"
proof (unfold invariant_monotonicity_def, intro conjI impI allI)
  show "social_choice_result.electoral_module plurality_rule"
    by simp
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    q :: "('b, 'a) Profile" and
    a :: "'b"
  assume "a \<in> elect plurality_rule V A p \<and> Profile.lifted V A p q a"
  thus "elect plurality_rule V A q = elect plurality_rule V A p \<or>
          elect plurality_rule V A q = {a}"
    using plurality_rule_inv_mono_eq
    by metis
qed

end