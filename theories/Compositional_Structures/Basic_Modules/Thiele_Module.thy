section \<open>Thiele Module\<close>

theory Thiele_Module
  imports 
      "Component_Types/Voting_Rule"      
      "Component_Types/Elimination_Module"
      "Component_Types/Social_Choice_Types/Aggregate_Profile"
      "Component_Types/Social_Choice_Types/Electoral_Structure"
begin

subsection \<open>Aggregated Profiles for Thiele Methods\<close>

fun thiele_ballot :: "('a Committee) set \<Rightarrow> (('a Committee) \<Rightarrow> nat) \<Rightarrow> bool" where
"thiele_ballot R b = (\<forall> r \<in> R. b r \<ge> 0)"

fun thiele_result :: "('a Committee) set \<Rightarrow> ('a Committee) Result \<Rightarrow> bool" where
"thiele_result R r = (disjoint3 r \<and> set_equals_partition R r)"

fun (in committee_result) thiele_aggregate :: "('a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate b W = (card (W \<inter> b))"


sublocale committee_result \<subseteq> aggregate_ballot
"\<lambda> c. 0" (*empty ballot*) 
"\<lambda> b c d. (b c > b d)" (*prefers*)
"\<lambda> b c. (\<forall> d. b c \<ge> b d)" (*wins*)
"\<lambda> C b. b" (* "\<lambda> C b c. if c \<in> C then b c else 0" limit_ballot*)
"ballot_\<A>\<V>" (*base ballot*)
"default_ballot_\<A>\<V>" (*empty base*)
"prefers_\<A>\<V>" (*prefers base*) 
"wins_\<A>\<V>" (*wins base*)
"limit_\<A>\<V>_ballot" (*limit base*)
thiele_ballot (*well formed ballot*)
committee_contenders 
thiele_aggregate
proof (unfold_locales, auto)
  fix 
    c1 c2 :: "'a Committee" and 
    b :: "'a Committee \<Rightarrow> nat" and
    a :: 'a
  assume *: "b c2 < b c1" and **: " \<forall>d. b d \<le> b c2" and "a \<in> c1"
  hence "False" using * ** by (simp add: leD)
  thus "a \<in> c2" by simp
next
  fix 
    c1 c2 :: "'a Committee" and 
    b :: "'a Committee \<Rightarrow> nat" and
    a :: 'a
  assume *: "b c2 < b c1" and **: " \<forall>d. b d \<le> b c2" and "a \<in> c2"
  hence "False" using * ** by (simp add: leD)
  thus "a \<in> c1" by simp
next
  show "thiele_aggregate default_ballot_\<A>\<V> = (\<lambda>c. 0)"
  proof -
    fix c :: "'a Committee"
    have "card (default_ballot_\<A>\<V> \<inter> c) = 0" using default_ballot_\<A>\<V>_def by (metis card.empty inf_bot_left)
    thus "thiele_aggregate default_ballot_\<A>\<V> c = 0" using default_ballot_\<A>\<V>_def
      by (simp add: inf_commute)
  qed
  oops


subsection \<open>Definition\<close>

fun (in committee_result) thiele_agg_profile :: "('v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile p v W = thiele_aggregate (p v) W"

type_synonym Thiele_Score = "nat => erat"

fun thiele_score :: "Thiele_Score \<Rightarrow> bool" where
"thiele_score w = (w(0) = 0 \<and> mono w)"

fun thiele_module :: "Thiele_Score \<Rightarrow> ('a Committee, 'v, ('a Committee \<Rightarrow> nat)) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R p. (\<Sum> v \<in> V.  s (p v r)))) V C p"

text \<open>

\<close>

type_synonym 'i Aggregate_Evaulation = "'i \<Rightarrow> erat"

type_synonym ('v, 'a, 'b, 'r, 'i) Voting_Rule_Family = "'i Aggregate_Evaulation \<Rightarrow> ('v, 'a, 'b, 'r) Voting_Rule"


fun voting_rule_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

fun (in committee_result) thiele_family :: "('v, 'a, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where 
"thiele_family w V A p =
	elect (thiele_module w) V (committees A) (thiele_agg_profile p)"

subsection \<open>Properties\<close>

lemma thiele_anonymous : "True" by simp
lemma thiele_neutral : "True" by simp


subsection \<open>Prominent Thiele Methods\<close>

subsubsection \<open>Approval Voting\<close>

text \<open>
  The approval voting rule elects all modules with the maximum amount of approvals
  among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical (single-winner) approval voting rule
  from social-choice theory.
\<close>


(* win count in approval setting: number of approvals *)
(*
  "'v set \<Rightarrow> 'r \<Rightarrow> 'r set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> erat"
*)
fun av_thiele_score :: "Thiele_Score" where
  "av_thiele_score n = erat_of n"

lemma av_valid: "thiele_score av_thiele_score"
proof auto
  show "Fract 0 1 = 0" by (simp add: Zero_rat_def)
next
  show "incseq av_thiele_score"
  proof
    fix x y :: nat
    assume "x \<le> y"
    hence "erat_of x \<le> erat_of y" by simp
    thus "av_thiele_score x \<le> av_thiele_score y" by simp
  qed
qed


fun av_eval_fun :: "('a Committee, 'v, 'a Approval_Set) Evaluation_Function" where
  "av_eval_fun V c C p = sum (\<lambda>v. erat_of (card (c \<inter> (p v)))) V"

fun naive_av_em :: "('a Committee, 'v, 'a Approval_Set) Electoral_Module" where
  "naive_av_em V R p = max_eliminator av_eval_fun V R p"

fun (in committee_result) naive_av :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule" where
"naive_av V A p = elect naive_av_em V (committees A) p"

fun single_winner_av' :: "('v, 'a Approval_Set, 'a) Electoral_Module" where
   "single_winner_av' V A p =
    ({},
     {a \<in> A. \<exists> x \<in> A. \<A>\<V>_profile.win_count V p x > \<A>\<V>_profile.win_count V p a},
     {a \<in> A. \<forall> x \<in> A. \<A>\<V>_profile.win_count V p x \<le> \<A>\<V>_profile.win_count V p a})"



fun av_score' :: "('a Committee, 'v, 'a Approval_Set) Evaluation_Function" where
  "av_score' V C A p = thiele_score (\<lambda>x. x) V C A p"

lemma av_score_is_thiele:
  fixes
    V :: "'v set" and
    Cs :: "'a Committee set" and
    C :: "'a Committee" and
    p :: "('v, 'a Approval_Set) Profile"
  shows "av_score V C C_all p = av_score' V C Cs p"
  by (meson max_elim_non_blocking)


fun (in committee_result) approval_voting :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
  "approval_voting V A p = committee_relay (max_eliminator av_score) V A p"

fun (in committee_result) approval_voting' :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
    "approval_voting' V A p =
      (let C = {S. S \<subseteq> A \<and> (card S) = k} in
    ({},
     {c \<in> C. \<forall> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) c \<ge> sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) d},
     {c \<in> C. \<exists> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) d > sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) c}))"

fun (in committee_result) approval_voting'' :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
  "approval_voting'' V A p = thiele_method (\<lambda>x. x) V A p"

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
proof (unfold approval_voting.simps approval_voting'.simps av_score.simps, standard)
oops

subsection \<open>Sequential Thiele Methods\<close>

subsection \<open>Reverse-Sequential Thiele Methods\<close>

end