section \<open>Thiele Module\<close>

theory Thiele_Module
  imports 
      "Component_Types/Voting_Rule"      
      "Component_Types/Elimination_Module"
      "Component_Types/Social_Choice_Types/Aggregate_Profile"
      "Component_Types/Social_Choice_Types/Electoral_Structure"
begin

subsection \<open>Definition\<close>

subsubsection \<open>Aggregated Profiles for Thiele Methods\<close>

fun thiele_ballot :: "('a Committee) set \<Rightarrow> (('a Committee) \<Rightarrow> nat) \<Rightarrow> bool" where
"thiele_ballot R b = (\<forall> r \<in> R. b r \<ge> 0)"

fun thiele_result :: "('a Committee) set \<Rightarrow> ('a Committee) Result \<Rightarrow> bool" where
"thiele_result R r = (disjoint3 r \<and> set_equals_partition R r)"

fun (in committee_result) thiele_aggregate :: "('a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate b W = (card (W \<inter> b))"

fun (in committee_result) thiele_agg_profile :: "('v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile p v W = thiele_aggregate (p v) W"

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
  fix c :: "'a Committee"
  have "card (default_ballot_\<A>\<V> \<inter> c) = 0" using default_ballot_\<A>\<V>_def by (metis card.empty inf_bot_left)
  hence "thiele_aggregate default_ballot_\<A>\<V> c = 0" using default_ballot_\<A>\<V>_def by (simp add: inf_commute)
  hence "\<forall>d. thiele_aggregate default_ballot_\<A>\<V> d = 0" using default_ballot_\<A>\<V>_def
    by (metis card.empty inf_bot_right thiele_aggregate.simps)
  thus "thiele_aggregate default_ballot_\<A>\<V> = (\<lambda>c. 0)" by blast
qed


subsubsection \<open>Evaluation of Aggregated Profiles\<close>

type_synonym Thiele_Score = "nat Aggregate_Evaluation"

fun thiele_score :: "Thiele_Score \<Rightarrow> bool" where
"thiele_score w = (w 0 = 0 \<and> mono w)"


subsubsection \<open>Electoral Module for Thiele Methods\<close>

fun thiele_module :: "Thiele_Score \<Rightarrow> ('a Committee, 'v, ('a Committee \<Rightarrow> nat)) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R p. (\<Sum> v \<in> V. s (p v r)))) V C p"

fun (in committee_result) thiele_family :: "('v, 'a, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where 
"thiele_family w V A p =
	elect (thiele_module w) V (committees A) (thiele_agg_profile p)"

fun thiele_method :: "Thiele_Score \<Rightarrow> ('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where
"thiele_method w r = thiele_score w"


subsection \<open>Properties\<close>

subsubsection \<open>Anonymity\<close>

lemma (in committee_result) thiele_anonymous:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "\<A>\<V>_committee.vr_anonymity (thiele_family w)"
proof (unfold \<A>\<V>_committee.vr_anonymity_def, safe)
  fix 
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Approval_Set) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume bij: "bij \<pi>"
  show 
    "let (A', V', q) = \<A>\<V>_committee.rename \<pi> (A, V, p)
       in \<A>\<V>_committee.finite_profile V A p \<and> \<A>\<V>_committee.finite_profile V' A' q \<longrightarrow>
          thiele_family w V A p = thiele_family w V A q"
    by simp
qed

subsubsection \<open>Neutrality\<close>

subsection \<open>Prominent Thiele Methods\<close>

subsubsection \<open>Proportional Approval Voting\<close>

fun harmonic :: "nat \<Rightarrow> real" where
"harmonic n = sum (\<lambda>x. 1/x) {1..n::nat}"

fun pav_score :: "Thiele_Score" where
"pav_score n = harmonic n"

subsection \<open>Sequential Thiele Methods\<close>

subsection \<open>Reverse-Sequential Thiele Methods\<close>

end