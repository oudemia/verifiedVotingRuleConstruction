(*  File:       Plurality_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Plurality Module\<close>

theory Plurality_Module
  imports "Component_Types/Elimination_Module"
begin

text \<open>
  The plurality module implements the plurality voting rule.
  The plurality rule elects all modules with the maximum amount of top
  preferences among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical plurality (voting) rule
  from social-choice theory.
\<close>

subsection \<open>Definition\<close>

fun plurality_score :: "('a, 'v, 'a Preference_Relation) Evaluation_Function" where
  "plurality_score V x A p = \<P>\<V>_profile.win_count V p x"

fun plurality :: "('v, 'a Preference_Relation, 'a) Electoral_Module" where
  "plurality V A p = max_eliminator plurality_score V A p"

fun plurality' :: "('v, 'a Preference_Relation, 'a) Electoral_Module" where
  "plurality' V A p =
    ({},
     {a \<in> A. \<exists> x \<in> A. \<P>\<V>_profile.win_count V p x > \<P>\<V>_profile.win_count V p a},
     {a \<in> A. \<forall> x \<in> A. \<P>\<V>_profile.win_count V p x \<le> \<P>\<V>_profile.win_count V p a})"

lemma enat_leq_enat_set_max:
  fixes
    x :: "enat" and
    X :: "enat set"
  assumes
    "x \<in> X" and
    "finite X"
  shows "x \<le> Max X"
  using assms
  by simp

lemma plurality_mod_elim_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    non_empty_A: "A \<noteq> {}" and
    fin_A: "finite A" and
    prof: "\<P>\<V>_profile.well_formed_profile V A p"
  shows "plurality V A p = plurality' V A p"
proof (unfold plurality.simps plurality'.simps plurality_score.simps, standard)
  have "fst (max_eliminator (\<lambda> V x A p. win_count V p x) V A p) = {}"
    by simp
  also have "\<dots> = fst ({},
             {a \<in> A. \<exists> b \<in> A. win_count V p a < win_count V p b},
             {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a})"
    by simp
  finally show
    "fst (max_eliminator (\<lambda> V x A p. win_count V p x) V A p) =
      fst ({},
            {a \<in> A. \<exists> b \<in> A. win_count V p a < win_count V p b},
            {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a})"
    by simp
next
  let ?no_max =
    "{a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}} = A"
  have "?no_max \<Longrightarrow> {win_count V p x | x. x \<in> A} \<noteq> {}"
    using non_empty_A
    by blast
  moreover have finite_winners: "finite {win_count V p x | x. x \<in> A}"
    using fin_A
    by simp
  ultimately have exists_max: "?no_max \<Longrightarrow> False"
    using Max_in
    by fastforce
  have rej_eq:
    "reject_r (max_eliminator (\<lambda> V b A p. win_count V p b) V A p) =
      {a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x}"
  proof (unfold max_eliminator.simps less_eliminator.simps elimination_module.simps
                elimination_set.simps, safe)
    fix a :: "'a"
    assume
      "a \<in> reject_r
        (if {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}} \<noteq> A
        then ({},
            {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}},
            A - {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}})
        else ({}, {}, A))"
    moreover have
      "A \<noteq> {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}}"
      using exists_max
      by metis
    ultimately have
      "a \<in> {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}}"
      by force
    thus "a \<in> A"
      by fastforce
  next
    fix a :: "'a"
    assume
      reject_a:
      "a \<in> reject_r
          (if {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}} \<noteq> A
          then ({},
                {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}},
                A - {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}})
          else ({}, {}, A))"
    hence elect_nonempty:
      "{b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}} \<noteq> A"
      by fastforce
    obtain f :: "enat \<Rightarrow> bool" where
      all_winners_possible: "\<forall> x. f x = (\<exists> y. x = win_count V p y \<and> y \<in> A)"
      by fastforce
    hence "finite (Collect f)"
      using finite_winners
      by presburger
    hence max_winner_possible: "f (Max (Collect f))"
      using all_winners_possible Max_in elect_nonempty
      by blast
    obtain g :: "'a \<Rightarrow> bool" where
      all_losers_possible: "\<forall> x. g x = (x \<in> A \<and> win_count V p x < Max (Collect f))"
      by moura
    hence "a \<in> {a \<in> A. win_count V p a < Max {win_count V p a | a. a \<in> A}}
            \<longrightarrow> a \<in> Collect g"
      using all_winners_possible
      by presburger
    hence
      "a \<in> {a \<in> A. win_count V p a < Max {win_count V p a | a. a \<in> A}}
          \<longrightarrow> (\<exists> x \<in> A. win_count V p a < win_count V p x)"
      using max_winner_possible all_losers_possible all_winners_possible mem_Collect_eq
      by (metis (no_types))
    thus "\<exists> x \<in> A. win_count V p a < win_count V p x"
      using reject_a elect_nonempty
      by simp
  next
    fix
      a :: "'a" and
      b :: "'a"
    assume
      "b \<in> A" and
      "win_count V p a < win_count V p b"
    moreover from this have "\<exists> a. win_count V p b = win_count V p a \<and> a \<in> A"
      by blast
    ultimately have "win_count V p a < Max {win_count V p a |a. a \<in> A}"
      using finite_winners Max_gr_iff
      by fastforce
    moreover assume "a \<in> A"
    ultimately have
      "{a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}} \<noteq> A
          \<longrightarrow> a \<in> {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}}"
      by force
    moreover have
      "{a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}} = A
          \<longrightarrow> a \<in> {}"
      using exists_max
      by metis
    ultimately show
      "a \<in> reject_r
          (if {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}} \<noteq> A
          then ({},
              {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}},
              A - {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}})
          else ({}, {}, A))"
      by simp
  qed
  have "defer_r (max_eliminator (\<lambda> V b A p. win_count V p b) V A p) =
          {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a}"
  proof (unfold max_eliminator.simps less_eliminator.simps elimination_module.simps
                elimination_set.simps, safe)
    fix a :: "'a"
    assume
      "a \<in> defer_r
        (if {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}} \<noteq> A
        then ({},
                {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}},
                A - {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}})
        else ({}, {}, A))"
    moreover have
      "A \<noteq> {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}}"
      using exists_max
      by metis
    ultimately have
      "a \<in> A - {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}}"
      by force
    thus "a \<in> A"
      by fastforce
  next
    fix
      a :: "'a" and
      b :: "'a"
    assume "b \<in> A"
    hence "win_count V p b \<in> {win_count V p x | x. x \<in> A}"
      by blast
    hence "win_count V p b \<le> Max {win_count V p x | x. x \<in> A}"
      using fin_A
      by simp
    moreover assume
        "a \<in> defer_r
          (if {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}} \<noteq> A
          then ({},
              {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}},
              A - {b \<in> A. win_count V p b < Max {win_count V p x | x. x \<in> A}})
          else ({}, {}, A))"
    moreover have
      "{a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}} \<noteq> A"
      using exists_max
      by metis
    ultimately have "\<not> win_count V p a < win_count V p b"
      using dual_order.strict_trans1
      by force
    thus "win_count V p b \<le> win_count V p a"
      using linorder_le_less_linear
      by metis
  next
    fix a :: "'a"
    assume
      a_in_A: "a \<in> A" and
      win_count_lt_b: "\<forall> b \<in> A. win_count V p b \<le> win_count V p a"
    then obtain f :: "enat \<Rightarrow> 'a" where
      "\<forall> x. a \<in> A \<and> f x \<in> A
          \<and> (\<not> (\<forall> b. x = win_count V p b \<longrightarrow> b \<notin> A) \<longrightarrow> win_count V p (f x) = x)"
      by moura
    moreover from this have
      "f (Max {win_count V p x | x. x \<in> A}) \<in> A
        \<longrightarrow> Max {win_count V p x | x. x \<in> A} \<le> win_count V p a"
      using Max_in finite_winners win_count_lt_b
      by fastforce
    ultimately show
      "a \<in> defer_r
          (if {a \<in> A.
            win_count V p a < Max {win_count V p x | x. x \<in> A}} \<noteq> A
          then ({},
                {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}},
                A - {a \<in> A. win_count V p a < Max {win_count V p x | x. x \<in> A}})
          else ({}, {}, A))"
      by force
  qed
  thus "snd (max_eliminator (\<lambda> V b A p. win_count V p b) V A p) =
    snd ({},
         {a \<in> A. \<exists> b \<in> A. win_count V p a < win_count V p b},
         {a \<in> A. \<forall> b \<in> A. win_count V p b \<le> win_count V p a})"
    using snd_conv rej_eq prod.exhaust_sel
    by (metis (no_types, lifting))
qed

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "\<S>\<C>\<F>_result.electoral_module plurality"
  unfolding plurality.simps
  using max_elim_sound
  by metis

theorem plurality'_sound[simp]: "\<S>\<C>\<F>_result.electoral_module plurality'"
proof (unfold \<S>\<C>\<F>_result.electoral_module.simps, safe)
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  have "disjoint3 (
      {},
      {a \<in> A. \<exists> a' \<in> A. win_count V p a < win_count V p a'},
      {a \<in> A. \<forall> a' \<in> A. win_count V p a' \<le> win_count V p a})"
    by auto
  moreover have
    "{a \<in> A. \<exists> x \<in> A. win_count V p a < win_count V p x} \<union>
      {a \<in> A. \<forall> x \<in> A. win_count V p x \<le> win_count V p a} = A"
    using not_le_imp_less
    by blast
  ultimately show "well_formed_\<S>\<C>\<F> A (plurality' V A p)"
    by simp
qed

lemma voters_determine_plurality_score: "voters_determine_evaluation plurality_score"
proof (unfold plurality_score.simps voters_determine_evaluation.simps, safe)
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    p' :: "('b, 'a) Profile" and
    a :: "'b"
  assume
    "\<forall> v \<in> V. p v = p' v" and
    "a \<in> A"
  hence "finite V \<longrightarrow>
    card {v \<in> V. above (p v) a = {a}} = card {v \<in> V. above (p' v) a = {a}}"
    using Collect_cong
    by (metis (no_types, lifting))
  thus "win_count V p a = win_count V p' a"
    unfolding win_count.simps
    by presburger
qed

lemma voters_determine_plurality: "voters_determine_election plurality"
  unfolding plurality.simps
  using voters_determine_max_elim voters_determine_plurality_score
  by blast

subsection \<open>Non-Blocking\<close>

text \<open>
  The plurality module is non-blocking.
\<close>

theorem plurality_mod_non_blocking[simp]: "non_blocking plurality"
  unfolding plurality.simps
  using max_elim_non_blocking
  by metis

subsection \<open>Non-Electing\<close>

text \<open>
  The plurality module is non-electing.
\<close>

theorem plurality_non_electing[simp]: "non_electing plurality"
  using max_elim_non_electing
  unfolding plurality.simps non_electing_def
  by metis

theorem plurality'_non_electing[simp]: "non_electing plurality'"
  unfolding non_electing_def
  using plurality'_sound
  by simp

subsection \<open>Property\<close>

lemma plurality_def_inv_mono_alts:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    q :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    defer_a: "a \<in> defer plurality V A p" and
    lift_a: "lifted V A p q a"
  shows "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
proof -
  have set_disj: "\<forall> b c. (b::'a) \<notin> {c} \<or> b = c"
    by blast
  have lifted_winner: "\<forall> b \<in> A. \<forall> i \<in> V.
      above (p i) b = {b} \<longrightarrow> (above (q i) b = {b} \<or> above (q i) a = {a})"
    using lift_a lifted_above_winner_alts
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> i \<in> V. (above (p i) a = {a} \<longrightarrow> above (q i) a = {a})"
    using defer_a lift_a
    unfolding Profile.lifted_def
    by metis
  hence a_win_subset:
    "{i \<in> V. above (p i) a = {a}} \<subseteq> {i \<in> V. above (q i) a = {a}}"
    by blast
  moreover have lifted_prof: "profile V A q"
    using lift_a
    unfolding Profile.lifted_def
    by metis
  ultimately have win_count_a: "win_count V p a \<le> win_count V q a"
    by (simp add: card_mono)
  have fin_A: "finite A"
    using lift_a
    unfolding Profile.lifted_def
    by blast
  hence "\<forall> b \<in> A - {a}.
          \<forall> i \<in> V. (above (q i) a = {a} \<longrightarrow> above (q i) b \<noteq> {b})"
    using DiffE above_one lift_a insertCI insert_absorb insert_not_empty
    unfolding Profile.lifted_def profile_def
    by metis
  with lifted_winner
  have above_QtoP:
    "\<forall> b \<in> A - {a}.
      \<forall> i \<in> V. (above (q i) b = {b} \<longrightarrow> above (p i) b = {b})"
    using lifted_above_winner_other lift_a
    unfolding Profile.lifted_def
    by metis
  hence "\<forall> b \<in> A - {a}.
          {i \<in> V. above (q i) b = {b}} \<subseteq> {i \<in> V. above (p i) b = {b}}"
    by (simp add: Collect_mono)
  hence win_count_other: "\<forall> b \<in> A - {a}. win_count V p b \<ge> win_count V q b"
    by (simp add: card_mono)
  show "defer plurality V A q = defer plurality V A p
        \<or> defer plurality V A q = {a}"
  proof (cases)
    assume "win_count V p a = win_count V q a"
    hence "card {i \<in> V. above (p i) a = {a}} = card {i \<in> V. above (q i) a = {a}}"
      using win_count.simps Profile.lifted_def enat.inject lift_a
      by (metis (mono_tags, lifting))
    moreover have "finite {i \<in> V. above (q i) a = {a}}"
      using Collect_mem_eq Profile.lifted_def finite_Collect_conjI lift_a
      by (metis (mono_tags))
    ultimately have "{i \<in> V. above (p i) a = {a}} = {i \<in> V. above (q i) a = {a}}"
      using a_win_subset
      by (simp add: card_subset_eq)
    hence above_pq: "\<forall> i \<in> V. (above (p i) a = {a}) = (above (q i) a = {a})"
      by blast
    moreover have
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V.
          (above (p i) b = {b} \<longrightarrow> (above (q i) b = {b} \<or> above (q i) a = {a}))"
      using lifted_winner
      by auto
    moreover have
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> above (p i) a \<noteq> {a})"
    proof (intro ballI impI, safe)
      fix
        b :: "'a" and
        i :: "'v"
      assume
        "b \<in> A" and
        "i \<in> V"
      moreover from this have A_not_empty: "A \<noteq> {}"
        by blast
      ultimately have "linear_order_on A (p i)"
        using lift_a
        unfolding lifted_def profile_def
        by metis
      moreover assume
        b_neq_a: "b \<noteq> a" and
        abv_b: "above (p i) b = {b}" and
        abv_a: "above (p i) a = {a}"
      ultimately show False
        using above_one_eq A_not_empty fin_A
        by (metis (no_types))
    qed
    ultimately have above_PtoQ:
      "\<forall> b \<in> A - {a}. \<forall> i \<in> V. (above (p i) b = {b} \<longrightarrow> above (q i) b = {b})"
      by simp
    hence "\<forall> b \<in> A.
            card {i \<in> V. above (p i) b = {b}} =
              card {i \<in> V. above (q i) b = {b}}"
    proof (safe)
      fix b :: "'a"
      assume "b \<in> A"
      thus "card {i \<in> V. above (p i) b = {b}} =
              card {i \<in> V. above (q i) b = {b}}"
        using DiffI set_disj above_PtoQ above_QtoP above_pq
        by (metis (no_types, lifting))
    qed
    hence "{b \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p b} =
              {b \<in> A. \<forall> c \<in> A. win_count V q c \<le> win_count V q b}"
      by auto
    hence "defer plurality' V A q = defer plurality' V A p
            \<or> defer plurality' V A q = {a}"
      by simp
    hence "defer plurality V A q = defer plurality V A p
            \<or> defer plurality V A q = {a}"
      using plurality_mod_elim_equiv empty_not_insert insert_absorb lift_a
      unfolding Profile.lifted_def
      by (metis (no_types, opaque_lifting))
    thus ?thesis
      by simp
  next
    assume "win_count V p a \<noteq> win_count V q a"
    hence strict_less: "win_count V p a < win_count V q a"
      using win_count_a
      by simp
    have "a \<in> defer plurality V A p"
      using defer_a plurality.elims
      by (metis (no_types))
    moreover have non_empty_A: "A \<noteq> {}"
      using lift_a equals0D equiv_prof_except_a_def
            lifted_imp_equiv_prof_except_a
      by metis
    moreover have fin_A: "finite_profile V A p"
      using lift_a
      unfolding Profile.lifted_def
      by simp
    ultimately have "a \<in> defer plurality' V A p"
      using plurality_mod_elim_equiv
      by metis
    hence a_in_win_p:
      "a \<in> {b \<in> A. \<forall> c \<in> A. win_count V p c \<le> win_count V p b}"
      by simp
    hence "\<forall> b \<in> A. win_count V p b \<le> win_count V p a"
      by simp
    hence less: "\<forall> b \<in> A - {a}. win_count V q b < win_count V q a"
      using DiffD1 antisym dual_order.trans not_le_imp_less
            win_count_a strict_less win_count_other
      by metis
    hence "\<forall> b \<in> A - {a}. \<not> (\<forall> c \<in> A. win_count V q c \<le> win_count V q b)"
      using lift_a not_le
      unfolding Profile.lifted_def
      by metis
    hence "\<forall> b \<in> A - {a}.
            b \<notin> {c \<in> A. \<forall> b \<in> A. win_count V q b \<le> win_count V q c}"
      by blast
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality' V A q"
      by simp
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality V A q"
      using lift_a non_empty_A plurality_mod_elim_equiv
      unfolding Profile.lifted_def
      by (metis (no_types, lifting))
    hence "\<forall> b \<in> A - {a}. b \<notin> defer plurality V A q"
      by simp
    moreover have "a \<in> defer plurality V A q"
    proof -
      have "\<forall> b \<in> A - {a}. win_count V q b \<le> win_count V q a"
        using less less_imp_le
        by metis
      moreover have "win_count V q a \<le> win_count V q a"
        by simp
      ultimately have "\<forall> b \<in> A. win_count V q b \<le> win_count V q a"
        by auto
      moreover have "a \<in> A"
        using a_in_win_p
        by simp
      ultimately have
        "a \<in> {b \<in> A. \<forall> c \<in> A. win_count V q c \<le> win_count V q b}"
        by simp
      hence "a \<in> defer plurality' V A q"
        by simp
      hence "a \<in> defer plurality V A q"
        using plurality_mod_elim_equiv non_empty_A fin_A lift_a non_empty_A
        unfolding Profile.lifted_def
        by (metis (no_types))
      thus ?thesis
        by simp
    qed
    moreover have "defer plurality V A q \<subseteq> A"
      by simp
    ultimately show ?thesis
      by blast
  qed
qed

text \<open>
  The plurality rule is invariant-monotone.
\<close>

theorem plurality_mod_def_inv_mono[simp]: "defer_invariant_monotonicity plurality"
proof (unfold defer_invariant_monotonicity_def, intro conjI impI allI)
  show "\<S>\<C>\<F>_result.electoral_module plurality"
    using plurality_sound
    by metis
next
  show "non_electing plurality"
    by simp
next
  fix
    A :: "'b set" and
    V :: "'a set" and
    p :: "('b, 'a) Profile" and
    q :: "('b, 'a) Profile" and
    a :: "'b"
  assume "a \<in> defer plurality V A p \<and> Profile.lifted V A p q a"
  hence "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
    using plurality_def_inv_mono_alts
    by metis
  thus "defer plurality V A q = defer plurality V A p
          \<or> defer plurality V A q = {a}"
    by simp
qed

end