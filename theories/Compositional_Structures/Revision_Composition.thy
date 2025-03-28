(*  File:       Revision_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Revision Composition\<close>

theory Revision_Composition
  imports "Basic_Modules/Component_Types/Electoral_Module"
begin

text \<open>
  A revised electoral module rejects all originally rejected or deferred
  alternatives, and defers the originally elected alternatives.
  It does not elect any alternatives.
\<close>

subsection \<open>Definition\<close>

fun revision_composition :: "('v, 'b, 'r) Electoral_Module
        \<Rightarrow> ('v, 'b, 'r) Electoral_Module" where
  "revision_composition m V A p = ({}, A - elect m V A p, elect m V A p)"

abbreviation rev :: "('v, 'b, 'r) Electoral_Module
        \<Rightarrow> ('v, 'b, 'r) Electoral_Module" ("_\<down>" 50) where
  "m\<down> == revision_composition m"

subsection \<open>Soundness\<close>

theorem (in electoral_structure) rev_comp_sound[simp]:
  fixes m :: "('v, 'b, 'r) Electoral_Module"
  assumes "electoral_module m"
  shows "electoral_module (revision_composition m)"
proof -
  from assms
  have "\<forall> A V p. profile V A p \<longrightarrow> elect m V A p \<subseteq> A"
    using elect_in_alts
    by metis
  hence "\<forall> A V p. profile V A p \<longrightarrow> (A - elect m V A p) \<union> elect m V A p = A"
    by blast
  hence unity:
    "\<forall> A V p. profile V A p \<longrightarrow>
      set_equals_partition A (revision_composition m V A p)"
    by simp
  have "\<forall> A V p. profile V A p \<longrightarrow> (A - elect m V A p) \<inter> elect m V A p = {}"
    by blast
  hence disjoint:
    "\<forall> A V p. profile V A p \<longrightarrow> disjoint3 (revision_composition m V A p)"
    by simp
  from unity disjoint
  show ?thesis
    unfolding electoral_module.simps
    by simp
qed

lemma voters_determine_rev_comp:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "voters_determine_election m"
  shows "voters_determine_election (revision_composition m)"
  using assms
  unfolding voters_determine_election.simps revision_composition.simps
  by presburger

subsection \<open>Composition Rules\<close>

text \<open>
  An electoral module received by revision is never electing.
\<close>

theorem rev_comp_non_electing[simp]:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "\<S>\<C>\<F>_result.electoral_module m"
  shows "non_electing (m\<down>)"
  using assms fstI rev_comp_sound revision_composition.simps
  using non_electing_def
  by metis

text \<open>
  Revising an electing electoral module results in a
  non-blocking electoral module.
\<close>

theorem rev_comp_non_blocking[simp]:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "electing m"
  shows "non_blocking (m\<down>)"
proof (unfold non_blocking_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (m\<down>)"
    using assms rev_comp_sound
    unfolding electing_def
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile V A p" and
    reject_A: "reject (m\<down>) V A p = A" and
    x_in_A: "x \<in> A"
  hence "non_electing m"
    using assms empty_iff Diff_disjoint Int_absorb2
          elect_in_alts prod.collapse prod.inject
    unfolding electing_def revision_composition.simps
    by (metis (no_types, lifting))
  thus "x \<in> {}"
    using assms fin_A prof_A x_in_A
    unfolding electing_def non_electing_def
    by (metis (no_types, lifting))
qed

text \<open>
  Revising an invariant monotone electoral module results in a
  defer-invariant-monotone electoral module.
\<close>

theorem rev_comp_def_inv_mono[simp]:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "invariant_monotonicity m"
  shows "defer_invariant_monotonicity (m\<down>)"
proof (unfold defer_invariant_monotonicity_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (m\<down>)"
    using assms rev_comp_sound
    unfolding invariant_monotonicity_def
    by metis
next
  show "non_electing (m\<down>)"
    using assms rev_comp_non_electing
    unfolding invariant_monotonicity_def
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a" and
    x :: "'a" and
    x' :: "'a"
  assume
    rev_p_defer_a: "a \<in> defer (m\<down>) V A p" and
    a_lifted: "lifted V A p q a" and
    rev_q_defer_x: "x \<in> defer (m\<down>) V A q" and
    x_non_eq_a: "x \<noteq> a" and
    rev_q_defer_x': "x' \<in> defer (m\<down>) V A q"
  from rev_p_defer_a
  have elect_a_in_p: "a \<in> elect m V A p"
    by simp
  from rev_q_defer_x x_non_eq_a
  have elect_no_unique_a_in_q: "elect m V A q \<noteq> {a}"
    by force
  from assms
  have "elect m V A q = elect m V A p"
    using a_lifted elect_a_in_p elect_no_unique_a_in_q
    unfolding invariant_monotonicity_def
    by (metis (no_types))
  thus "x' \<in> defer (m\<down>) V A p"
    using rev_q_defer_x'
    by simp
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a" and
    x :: "'a" and
    x' :: "'a"
  assume
    rev_p_defer_a: "a \<in> defer (m\<down>) V A p" and
    a_lifted: "lifted V A p q a" and
    rev_q_defer_x: "x \<in> defer (m\<down>) V A q" and
    x_non_eq_a: "x \<noteq> a" and
    rev_p_defer_x': "x' \<in> defer (m\<down>) V A p"
  have reject_and_defer:
    "(A - elect m V A q, elect m V A q) = snd ((m\<down>) V A q)"
    by force
  have elect_p_eq_defer_rev_p: "elect m V A p = defer (m\<down>) V A p"
    by simp
  hence elect_a_in_p: "a \<in> elect m V A p"
    using rev_p_defer_a
    by presburger
  have "elect m V A q \<noteq> {a}"
    using rev_q_defer_x x_non_eq_a
    by force
  with assms
  show "x' \<in> defer (m\<down>) V A q"
    using a_lifted rev_p_defer_x' snd_conv elect_a_in_p
          elect_p_eq_defer_rev_p reject_and_defer
    unfolding invariant_monotonicity_def
    by (metis (no_types))
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a" and
    x :: "'a" and
    x' :: "'a"
  assume
    "a \<in> defer (m\<down>) V A p" and
    "lifted V A p q a" and
    "x' \<in> defer (m\<down>) V A q"
  with assms
  show "x' \<in> defer (m\<down>) V A p"
    using empty_iff insertE snd_conv revision_composition.elims
    unfolding invariant_monotonicity_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a" and
    x :: "'a" and
    x' :: "'a"
  assume
    rev_p_defer_a: "a \<in> defer (m\<down>) V A p" and
    a_lifted: "lifted V A p q a" and
    rev_q_not_defer_a: "a \<notin> defer (m\<down>) V A q"
  moreover from assms
  have lifted_inv:
    "\<forall> A V p q a. a \<in> elect m V A p \<and> lifted V A p q a \<longrightarrow>
      elect m V A q = elect m V A p \<or> elect m V A q = {a}"
    unfolding invariant_monotonicity_def
    by (metis (no_types))
  moreover have p_defer_rev_eq_elect: "defer (m\<down>) V A p = elect m V A p"
    by simp
  moreover have "defer (m\<down>) V A q = elect m V A q"
    by simp
  ultimately show "x' \<in> defer (m\<down>) V A q"
    using rev_p_defer_a rev_q_not_defer_a
    by blast
qed

end