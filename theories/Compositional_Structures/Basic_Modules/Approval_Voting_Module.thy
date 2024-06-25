section \<open>Approval Voting Module\<close>

theory Approval_Voting_Module
  imports 
      "Component_Types/Elimination_Module"
      "Component_Types/Relay_Module"
begin

text \<open>
  The approval voting rule elects all modules with the maximum amount of approvals
  among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical (single-winner) approval voting rule
  from social-choice theory.
\<close>

subsection \<open>Approval Voting, Single Winner Case\<close>

(*win count in approval setting: number of approvals *)
fun av_score :: "('a, 'v, 'a Approval_Set) Evaluation_Function" where
  "av_score V x A p = \<A>\<V>_profile.win_count V p x"

fun av_committee_score :: "('a Committee, 'v, 'a Approval_Set) Evaluation_Function" where
  "av_committee_score V C A p = sum (\<lambda>c. \<A>\<V>_profile.win_count V p c) C"

fun single_winner_av :: "('v, 'a Approval_Set, 'a) Electoral_Module" where
  "single_winner_av V A p = max_eliminator av_score V A p"

fun single_winner_av' :: "('v, 'a Approval_Set, 'a) Electoral_Module" where
   "single_winner_av' V A p =
    ({},
     {a \<in> A. \<exists> x \<in> A. \<A>\<V>_profile.win_count V p x > \<A>\<V>_profile.win_count V p a},
     {a \<in> A. \<forall> x \<in> A. \<A>\<V>_profile.win_count V p x \<le> \<A>\<V>_profile.win_count V p a})"

fun (in committee_result) approval_voting :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
  "approval_voting V A p = committee_relay (max_eliminator av_committee_score) V A p"

fun (in committee_result) approval_voting' :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
    "approval_voting' V A p =
      (let C = {S. S \<subseteq> A \<and> (card S) = k} in
    ({},
     {c \<in> C. \<forall> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) c \<ge> sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) d},
     {c \<in> C. \<exists> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) d > sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) c}))"

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

lemma (in committee_result) av_mod_elim_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Approval_Set) Profile"
  assumes
    non_empty_A: "A \<noteq> {}" and
    fin_A: "finite A" and
    prof: "\<A>\<V>_profile.well_formed_profile V A p"
  shows "approval_voting V A p = approval_voting' V A p"
proof (unfold approval_voting.simps approval_voting'.simps av_committee_score.simps, standard)
  oops
end