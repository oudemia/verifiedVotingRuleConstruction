(*  File:       Elect_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elect Composition\<close>

theory Elect_Composition
  imports "Basic_Modules/Elect_Module"
          Sequential_Composition
begin

text \<open>
  The elect composition sequences an electoral module and the elect
  module. It finalizes the module's decision as it simply elects all their
  non-rejected alternatives. Thereby, any such elect-composed module induces
  a proper voting rule in the social choice sense, as all alternatives are
  either rejected or elected.
\<close>

subsection \<open>Definition\<close>

fun (in electoral_structure) elector :: "('r, 'v, 'b) Electoral_Module
                  \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "elector m = (m \<triangleright> elect_module)"

subsection \<open>Auxiliary Lemmas\<close>

lemma (in electoral_structure) elector_seqcomp_assoc:
  fixes
    a :: "('r, 'v, 'b) Electoral_Module" and
    b :: "('r, 'v, 'b) Electoral_Module"
  shows "(a \<triangleright> (elector b)) = (elector (a \<triangleright> b))"
  unfolding elector.simps elect_module.simps sequential_composition.simps
  using boolean_algebra_cancel.sup2 fst_eqD snd_eqD sup_commute
  by (metis (no_types, opaque_lifting))

subsection \<open>Soundness\<close>

theorem \<P>\<V>_elector_sound[simp]:
  fixes m :: "('v, 'a Preference_Relation, 'a) Electoral_Module"
  assumes "\<P>\<V>_\<S>\<C>\<F>.electoral_module m"
  shows "\<P>\<V>_\<S>\<C>\<F>.electoral_module (elector m)"
  using assms elect_mod_sound seq_comp_sound
  unfolding elector.simps
  by metis

theorem \<A>\<V>_elector_sound[simp]:
  fixes m :: "('v, 'a Approval_Set, 'a) Electoral_Module"
  assumes "\<A>\<V>_\<S>\<C>\<F>.electoral_module m"
  shows "\<A>\<V>_\<S>\<C>\<F>.electoral_module (elector m)"
  using assms elect_mod_sound seq_comp_sound
  unfolding elector.simps
  by metis


lemma voters_determine_elector:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "voters_determine_election m"
  shows "voters_determine_election (elector m)"
  using assms elect_mod_only_voters voters_determine_seq_comp
  unfolding elector.simps
  by metis

subsection \<open>Electing\<close>

theorem elector_electing[simp]:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes
    module_m: "\<S>\<C>\<F>_result.electoral_module m" and
    non_block_m: "non_blocking m"
  shows "electing (elector m)"
proof -
  have "\<forall> m'.
        (\<not> electing m' \<or> \<S>\<C>\<F>_result.electoral_module m' \<and>
          (\<forall> A' V' p'. (A' \<noteq> {} \<and> finite A' \<and> profile V' A' p')
            \<longrightarrow> elect m' V' A' p' \<noteq> {})) \<and>
          (electing m' \<or> \<not> \<S>\<C>\<F>_result.electoral_module m'
            \<or> (\<exists> A V p. (A \<noteq> {} \<and> finite A \<and> profile V A p \<and> elect m' V A p = {})))"
    unfolding electing_def
    by blast
  hence "\<forall> m'.
        (\<not> electing m' \<or> \<S>\<C>\<F>_result.electoral_module m' \<and>
          (\<forall> A' V' p'. (A' \<noteq> {} \<and> finite A' \<and> profile V' A' p')
            \<longrightarrow> elect m' V' A' p' \<noteq> {})) \<and>
        (\<exists> A V p. (electing m' \<or> \<not> \<S>\<C>\<F>_result.electoral_module m' \<or> A \<noteq> {}
          \<and> finite A \<and> profile V A p \<and> elect m' V A p = {}))"
    by simp
  then obtain
    A :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'a set" and
    V :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> 'v set" and
    p :: "('a, 'v, 'a Result) Electoral_Module \<Rightarrow> ('a, 'v) Profile" where
    electing_mod:
     "\<forall> m'::('a, 'v, 'a Result) Electoral_Module.
      (\<not> electing m' \<or> \<S>\<C>\<F>_result.electoral_module m' \<and>
        (\<forall> A' V' p'. (A' \<noteq> {} \<and> finite A' \<and> profile V' A' p')
          \<longrightarrow> elect m' V' A' p' \<noteq> {})) \<and>
        (electing m' \<or> \<not> \<S>\<C>\<F>_result.electoral_module m'
        \<or> A m' \<noteq> {} \<and> finite (A m') \<and> profile (V m') (A m') (p m')
                    \<and> elect m' (V m') (A m') (p m') = {})"
    by metis
  moreover have non_block:
    "non_blocking (elect_module::'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a Result)"
    by (simp add: electing_imp_non_blocking)
  moreover obtain
    e :: "'a Result \<Rightarrow> 'a set" and
    r :: "'a Result \<Rightarrow> 'a set" and
    d :: "'a Result \<Rightarrow> 'a set" where
    result: "\<forall> s. (e s, r s, d s) = s"
    using disjoint3.cases
    by (metis (no_types))
  moreover from this
  have "\<forall> s. (elect_r s, r s, d s) = s"
    by simp
  moreover from this
  have
    "profile (V (elector m)) (A (elector m)) (p (elector m)) \<and> finite (A (elector m))
      \<longrightarrow> d (elector m (V (elector m)) (A (elector m)) (p (elector m))) = {}"
    by simp
  moreover have "\<S>\<C>\<F>_result.electoral_module (elector m)"
    using elector_sound module_m
    by simp
  moreover from electing_mod result
  have "finite (A (elector m)) \<and>
          profile (V (elector m)) (A (elector m)) (p (elector m)) \<and>
          elect (elector m) (V (elector m)) (A (elector m)) (p (elector m)) = {} \<and>
          d (elector m (V (elector m)) (A (elector m)) (p (elector m))) = {} \<and>
          reject (elector m) (V (elector m)) (A (elector m)) (p (elector m)) =
            r (elector m (V (elector m)) (A (elector m)) (p (elector m))) \<longrightarrow>
              electing (elector m)"
    using Diff_empty elector.simps non_block_m snd_conv non_blocking_def reject_not_elec_or_def
          non_block seq_comp_presv_non_blocking
    by (metis (mono_tags, opaque_lifting))
  ultimately show ?thesis
    using non_block_m
    unfolding elector.simps
    by auto
qed

subsection \<open>Composition Rule\<close>

text \<open>
  If m is defer-Condorcet-consistent, then elector(m) is Condorcet consistent.
\<close>

lemma dcc_imp_cc_elector:
  fixes m :: "('a, 'v, 'a Result) Electoral_Module"
  assumes "defer_condorcet_consistency m"
  shows "condorcet_consistency (elector m)"
proof (unfold defer_condorcet_consistency_def condorcet_consistency_def, safe)
  show "\<S>\<C>\<F>_result.electoral_module (elector m)"
    using assms elector_sound
    unfolding defer_condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a"
  assume c_win: "condorcet_winner V A p w"
  have fin_A: "finite A"
    using condorcet_winner.simps c_win
    by metis
  have fin_V: "finite V"
    using condorcet_winner.simps c_win
    by metis
  have prof_A: "profile V A p"
    using c_win
    by simp
  have max_card_w: "\<forall> y \<in> A - {w}.
          card {i \<in> V. (w, y) \<in> (p i)}
            < card {i \<in> V. (y, w) \<in> (p i)}"
    using c_win fin_V
    by simp
  have rej_is_complement:
    "reject m V A p = A - (elect m V A p \<union> defer m V A p)"
    using double_diff sup_bot.left_neutral Un_upper2 assms fin_A prof_A fin_V
          defer_condorcet_consistency_def elec_and_def_not_rej reject_in_alts
    by (metis (no_types, opaque_lifting))
  have subset_in_win_set: "elect m V A p \<union> defer m V A p \<subseteq>
      {e \<in> A. e \<in> A \<and> (\<forall> x \<in> A - {e}.
        card {i \<in> V. (e, x) \<in> p i} < card {i \<in> V. (x, e) \<in> p i})}"
  proof (safe_step)
    fix x :: "'a"
    assume x_in_elect_or_defer: "x \<in> elect m V A p \<union> defer m V A p"
    hence x_eq_w: "x = w"
      using Diff_empty Diff_iff assms cond_winner_unique c_win fin_A fin_V insert_iff
            snd_conv prod.sel(1) sup_bot.left_neutral
      unfolding defer_condorcet_consistency_def
      by (metis (mono_tags, lifting))
    have "\<And> x. x \<in> elect m V A p \<Longrightarrow> x \<in> A"
      using fin_A prof_A fin_V assms elect_in_alts in_mono
      unfolding defer_condorcet_consistency_def
      by metis
    moreover have "\<And> x. x \<in> defer m V A p \<Longrightarrow> x \<in> A"
      using fin_A prof_A fin_V assms defer_in_alts in_mono
      unfolding defer_condorcet_consistency_def
      by metis
    ultimately have "x \<in> A"
      using x_in_elect_or_defer
      by auto
    thus "x \<in> {e \<in> A. e \<in> A \<and>
            (\<forall> x \<in> A - {e}.
              card {i \<in> V. (e, x) \<in> p i}
                < card {i \<in> V. (x, e) \<in> p i})}"
      using x_eq_w max_card_w
      by auto
  qed
  moreover have
    "{e \<in> A. e \<in> A \<and>
        (\<forall> x \<in> A - {e}.
            card {i \<in> V. (e, x) \<in> p i} <
              card {i \<in> V. (x, e) \<in> p i})}
          \<subseteq> elect m V A p \<union> defer m V A p"
  proof (safe)
    fix x :: "'a"
    assume
      x_not_in_defer: "x \<notin> defer m V A p" and
      "x \<in> A" and
      "\<forall> x' \<in> A - {x}.
        card {i \<in> V. (x, x') \<in> p i}
          < card {i \<in> V. (x', x) \<in> p i}"
    hence c_win_x: "condorcet_winner V A p x"
      using fin_A prof_A fin_V
      by simp
    have "(\<S>\<C>\<F>_result.electoral_module m \<and> \<not> defer_condorcet_consistency m \<longrightarrow>
          (\<exists> A V rs a. condorcet_winner V A rs a \<and>
            m V A rs \<noteq> ({}, A - defer m V A rs,
            {a \<in> A. condorcet_winner V A rs a})))
        \<and> (defer_condorcet_consistency m \<longrightarrow>
          (\<forall> A V rs a. finite A \<longrightarrow> finite V \<longrightarrow> condorcet_winner V A rs a \<longrightarrow>
            m V A rs =
      ({}, A - defer m V A rs, {a \<in> A. condorcet_winner V A rs a})))"
      unfolding defer_condorcet_consistency_def
      by blast
    hence
      "m V A p = ({}, A - defer m V A p, {a \<in> A. condorcet_winner V A p a})"
      using c_win_x assms fin_A fin_V
      by blast
    thus "x \<in> elect m V A p"
      using assms x_not_in_defer fin_A fin_V cond_winner_unique
            defer_condorcet_consistency_def insertCI snd_conv c_win_x
      by (metis (no_types, lifting))
  qed
  ultimately have
    "elect m V A p \<union> defer m V A p =
      {e \<in> A. e \<in> A \<and>
        (\<forall> x \<in> A - {e}.
          card {i \<in> V. (e, x) \<in> p i} <
            card {i \<in> V. (x, e) \<in> p i})}"
    by blast
  thus "elector m V A p =
          ({e \<in> A. condorcet_winner V A p e}, A - elect (elector m) V A p, {})"
    using fin_A prof_A fin_V rej_is_complement
    by simp
qed

end