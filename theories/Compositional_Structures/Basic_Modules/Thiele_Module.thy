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

text \<open>

\<close>

fun rename_committee :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a Committee) set => ('a Committee) set" where
"rename_committee \<pi> R = {} "

lemma committee_rename:
  fixes 
    V :: "'v set" and
    A :: "'a set"
  shows ""
 "vr_anonymity r \<equiv>
    voting_rule r \<and>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> r V A p = r V A q))"

  by simp

lemma  thiele_anonymous : "thiele_score w \<longrightarrow> vr_anonymity (thiele_family w)" 
proof auto
qed

lemma thiele_neutral : "True" by simp


subsection \<open>Prominent Thiele Methods\<close>

subsubsection \<open>Approval Voting\<close>

text \<open>
  The approval voting rule elects all modules with the maximum amount of approvals
  among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical (single-winner) approval voting rule
  from social-choice theory.
\<close>

fun av_thiele_score :: "Thiele_Score" where
  "av_thiele_score n = erat_of n"

lemma av_is_thiele: "thiele_score av_thiele_score"
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

fun (in committee_result) av :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule" where
"av V A p = thiele_family av_thiele_score V A p"


text \<open>
  The AV rule can be modeled without referencing the Thiele voting rule family. Firstly,
  as a standalone component-based voting rule. Secondly, defined directly by a winning set
  of committees.
\<close>

fun (in committee_result) naive_av :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule" where
"naive_av V A p = 
     {C \<in> committees A. \<forall> D \<in> committees A. (\<Sum> v \<in> V. card (C \<inter> (p v))) \<ge>  (\<Sum> v \<in> V. card (D \<inter> (p v)))}"


fun av_eval_fun :: "('a Committee, 'v, 'a Approval_Set) Evaluation_Function" where
  "av_eval_fun V c C p = sum (\<lambda>v. erat_of (card (c \<inter> (p v)))) V"

fun naive_av_em :: "('a Committee, 'v, 'a Approval_Set) Electoral_Module" where
  "naive_av_em V R p = max_eliminator av_eval_fun V R p"

fun (in committee_result) naive_av' :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule" where
"naive_av' V A p = elect naive_av_em V (committees A) p"

lemma erat_of_sum:
  fixes
    X :: "'a set" and
    f :: "'a \<Rightarrow> nat"
  shows "(\<Sum>x\<in>X. (erat_of (f x))) = erat_of (\<Sum>x\<in>X. (f x))"
proof (unfold erat_of.simps, simp)
  have "\<forall>x\<in>X. Fract (int (f x)) 1 = f x" by (simp add: of_rat_rat)
  hence *: "(\<Sum>x\<in>X. Fract (int (f x)) 1) = (\<Sum>x\<in>X. f x)"
    by (metis (mono_tags, lifting) Fract_of_nat_eq of_nat_sum of_rat_of_nat_eq sum.cong)
  have "Fract (\<Sum>x\<in>X. int (f x)) 1 = (\<Sum>x\<in>X. f x)"
    by (metis of_int_of_nat_eq of_int_rat of_nat_sum of_rat_of_int_eq)
  thus "(\<Sum>x\<in>X. Fract (int (f x)) 1) = Fract (\<Sum>x\<in>X. int (f x)) 1" using *
    by (metis of_rat_eq_iff)
qed

lemma erat_of_leq: "(x \<le> y) \<longleftrightarrow> (erat_of x \<le> erat_of y)"
proof
  assume "x \<le> y"
  thus "erat_of x \<le> erat_of y" by simp
next
  assume "erat_of x \<le> erat_of y"
  hence "Fract x 1 \<le> Fract y 1" using erat_of.simps by simp
  thus "x \<le> y" by simp
qed

lemma (in committee_result) av_equiv:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Approval_Set) Profile"
  assumes
    non_empty_A: "A \<noteq> {}" and
    fin_A: "finite A" and
    prof: "\<A>\<V>_profile.well_formed_profile V A p"
  shows "av V A p = naive_av V A p"
proof (unfold av.simps naive_av.simps av_thiele_score.simps, standard)
  show "thiele_family erat_of V A p \<subseteq> 
    {C\<in>committees A. \<forall> D\<in>committees A. (\<Sum>v\<in>V. card (D \<inter> p v)) \<le> (\<Sum>v\<in>V. card (C \<inter> p v))}"
    by auto
next
  show "{C \<in> committees A. \<forall>D\<in>committees A. (\<Sum>v\<in>V. card (D \<inter> p v)) \<le> (\<Sum>v\<in>V. card (C \<inter> p v))}
    \<subseteq> thiele_family erat_of V A p"
  proof (unfold thiele_family.simps, standard)
    fix W :: "'a Committee"
    assume wins: 
      "W \<in> {C \<in> committees A. \<forall>D\<in>committees A. (\<Sum>v\<in>V. card (D \<inter> p v)) \<le> (\<Sum>v\<in>V. card (C \<inter> p v))}"
    hence "\<forall>C\<in>committees A. (\<Sum>v\<in>V. card (C \<inter> p v)) \<le> (\<Sum>v\<in>V. card (W \<inter> p v))" by blast
    hence "\<forall>C\<in>committees A. (\<Sum>v\<in>V. thiele_agg_profile p v C) \<le> (\<Sum>v\<in>V.  thiele_agg_profile p v W)"
      using thiele_agg_profile.simps by fastforce
    hence "\<forall>C\<in>committees A. (\<Sum>v\<in>V. erat_of (thiele_agg_profile p v C)) \<le> (\<Sum>v\<in>V. erat_of (thiele_agg_profile p v W))"
      using erat_of_sum erat_of_leq by metis
    hence "W \<in> elect (max_eliminator (\<lambda> V r R p. (\<Sum> v \<in> V. erat_of (p v r)))) V (committees A) (thiele_agg_profile p)"
      by sledgehammer
    show "W \<in> (elect (thiele_module erat_of) V (committees A) (thiele_agg_profile p))" by sledgehammer
oops

subsection \<open>Sequential Thiele Methods\<close>

subsection \<open>Reverse-Sequential Thiele Methods\<close>

end