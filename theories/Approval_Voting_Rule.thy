(*  File:       Approval_Voting_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Henriette Färber, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Voting Rules\<close>

section \<open>Approval Voting Rule\<close>

theory Approval_Voting_Rule
  imports "Compositional_Structures/Basic_Modules/Thiele_Module"
begin

subsection \<open>Definition\<close>
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

end