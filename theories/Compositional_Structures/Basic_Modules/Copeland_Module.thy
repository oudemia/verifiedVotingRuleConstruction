(*  File:       Copeland_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Copeland Module\<close>

theory Copeland_Module
  imports "Component_Types/Elimination_Module"
begin

text \<open>
  This is the Copeland module used by the Copeland voting rule. The Copeland
  rule elects the alternatives with the highest difference between the amount
  of simple-majority wins and the amount of simple-majority losses. The module
  implemented herein only rejects the alternatives not elected by the voting
  rule, and defers the alternatives that would be elected by the full voting
  rule.
\<close>

subsection \<open>Definition\<close>

fun copeland_score :: "'a Evaluation_Function" where
  "copeland_score x A p =
    card {y \<in> A . wins x p y} - card {y \<in> A . wins y p x}"

fun copeland :: "'a Electoral_Module" where
  "copeland A p = max_eliminator copeland_score A p"

subsection \<open>Soundness\<close>

theorem copeland_sound: "electoral_module copeland"
  unfolding copeland.simps
  using max_elim_sound
  by metis

subsection \<open>Lemmas\<close>

text \<open>
  For a Condorcet winner w, we have: "card {y in A . wins x p y} = |A| - 1".
\<close>

lemma cond_winner_imp_win_count:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assumes "condorcet_winner A p w"
  shows "card {a \<in> A. wins w p a} = card A - 1"
proof -
  from assms
  have 0: "\<forall> a \<in> A - {w}. wins w p a"
    by simp
  have 1: "\<forall> M. {x \<in> M. True} = M"
    by blast
  from 0 1
  have "{a \<in> A - {w}. wins w p a} = A - {w}"
    by blast
  hence 10: "card {a \<in> A - {w}. wins w p a} = card (A - {w})"
    by simp
  from assms
  have 11: "w \<in> A"
    by simp
  hence "card (A - {w}) = card A - 1"
    using card_Diff_singleton assms
    by metis
  hence winner_amount_one:
    "card {a \<in> A - {w}. wins w p a} = card (A) - 1"
    using "10"
    by linarith
  have 2: "\<forall> a \<in> {w}. \<not> wins a p a"
    by (simp add: wins_irreflex)
  have 3: "\<forall> M. {x \<in> M . False} = {}"
    by blast
  from 2 3
  have "{a \<in> {w}. wins w p a} = {}"
    by blast
  hence winner_amount_zero: "card {a \<in> {w}. wins w p a} = 0"
    by simp
  have disjunct:
    "{a \<in> A - {w}. wins w p a} \<inter> {a \<in> {w}. wins w p a} = {}"
    by blast
  have union:
    "{a \<in> A - {w}. wins w p a} \<union> {x \<in> {w}. wins w p x} =
        {a \<in> A. wins w p a}"
    using 2
    by blast
  have finite_defeated: "finite {a \<in> A - {w}. wins w p a}"
    using assms
    by simp
  have finitene_winners: "finite {a \<in> {w}. wins w p a}"
    by simp
  from finite_defeated finitene_winners disjunct card_Un_disjoint
  have
    "card ({a \<in> A - {w}. wins w p a} \<union> {a \<in> {w}. wins w p a}) =
        card {a \<in> A - {w}. wins w p a} + card {a \<in> {w}. wins w p a}"
    by blast
  with union
  have "card {a \<in> A. wins w p a} =
          card {a \<in> A - {w}. wins w p a} + card {a \<in> {w}. wins w p a}"
    by simp
  with winner_amount_one winner_amount_zero
  show ?thesis
    by linarith
qed

text \<open>
  For a Condorcet winner w, we have: "card {y in A . wins y p x} = 0".
\<close>

lemma cond_winner_imp_loss_count:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assumes winner: "condorcet_winner A p w"
  shows "card {a \<in> A. wins a p w} = 0"
  using Collect_empty_eq card_eq_0_iff insert_Diff insert_iff
        wins_antisym winner
  unfolding condorcet_winner.simps
  by (metis (no_types, lifting))

text \<open>
  Copeland score of a Condorcet winner.
\<close>

lemma cond_winner_imp_copeland_score:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assumes winner: "condorcet_winner A p w"
  shows "copeland_score w A p = card A - 1"
proof (unfold copeland_score.simps)
  have card_A_sub_one: "card {a \<in> A. wins w p a} = card A - 1"
    using cond_winner_imp_win_count winner
    by simp
  have card_zero: "card {a \<in> A. wins a p w} = 0"
    using cond_winner_imp_loss_count winner
    by (metis (no_types))
  have "card A - 1 - 0 = card A - 1"
    by simp
  thus
    "card {a \<in> A. wins w p a} - card {a \<in> A. wins a p w} =
      card A - 1"
    using card_zero card_A_sub_one
    by simp
qed

text \<open>
  For a non-Condorcet winner l, we have:
  "card {y in A . wins x p y} <= |A| - 1 - 1".
\<close>

lemma non_cond_winner_imp_win_count:
  fixes
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assumes
    winner: "condorcet_winner A p w" and
    loser: "l \<noteq> w" and
    l_in_A: "l \<in> A"
  shows "card {a \<in> A . wins l p a} \<le> card A - 2"
proof -
  from winner loser l_in_A
  have "wins w p l"
    by simp
  hence 0: "\<not> wins l p w"
    using wins_antisym
    by simp
  have 1: "\<not> wins l p l"
    using wins_irreflex
    by simp
  from 0 1 have 2:
    "{y \<in> A . wins l p y} =
        {y \<in> A - {l, w} . wins l p y}"
    by blast
  have 3: "\<forall> M f . finite M \<longrightarrow> card {x \<in> M . f x} \<le> card M"
    by (simp add: card_mono)
  have 4: "finite (A - {l, w})"
    using finite_Diff winner
    by simp
  from 3 4
  have 5:
    "card {y \<in> A - {l, w} . wins l p y} \<le>
      card (A - {l, w})"
    by (metis (full_types))
  have "w \<in> A"
    using winner
    by simp
  with l_in_A
  have "card (A - {l, w}) = card A - card {l, w}"
    by (simp add: card_Diff_subset)
  hence "card (A - {l, w}) = card A - 2"
    using loser
    by simp
  with 5 2
  show ?thesis
    by simp
qed

subsection \<open>Property\<close>

text \<open>
  The Copeland score is Condorcet rating.
\<close>

theorem copeland_score_is_cr: "condorcet_rating copeland_score"
proof (unfold condorcet_rating_def, unfold copeland_score.simps, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  from winner
  have 0:
    "card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w} = card A - 1"
    using cond_winner_imp_copeland_score
    by fastforce
  from winner l_neq_w l_in_A
  have 1:
    "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} \<le> card A - 2"
    using non_cond_winner_imp_win_count
    by fastforce
  have 2: "card A - 2 < card A - 1"
    using card_0_eq card_Diff_singleton diff_less_mono2
          empty_iff finite_Diff insertE insert_Diff
          l_in_A l_neq_w neq0_conv one_less_numeral_iff
          semiring_norm(76) winner zero_less_diff
    unfolding condorcet_winner.simps
    by metis
  hence
    "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} < card A - 1"
    using 1 le_less_trans
    by blast
  thus
    "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} <
      card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w}"
    using 0
    by linarith
qed

theorem copeland_is_dcc: "defer_condorcet_consistency copeland"
proof (unfold defer_condorcet_consistency_def electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    finA: "finite A" and
    profA: "profile A p"
  have "well_formed A (max_eliminator copeland_score A p)"
    using finA max_elim_sound profA
    unfolding electoral_module_def
    by metis
  thus "well_formed A (copeland A p)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a"
  assume
    cwin_w: "condorcet_winner A p w" and
    finA: "finite A"
  have max_cplscore_dcc:
    "defer_condorcet_consistency (max_eliminator copeland_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: copeland_score_is_cr)
  have
    "\<forall> A p. (copeland A p = max_eliminator copeland_score A p)"
    by simp
  thus
    "copeland A p =
      ({},
       A - defer copeland A p,
       {d \<in> A. condorcet_winner A p d})"
    using Collect_cong cwin_w finA max_cplscore_dcc
    unfolding defer_condorcet_consistency_def
    by (metis (no_types, lifting))
qed

end
