(*  File:       Approval_Voting_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Henriette Färber, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Voting Rules\<close>

section \<open>Approval Voting Rule\<close>

theory Approval_Voting_Rule
  imports "Compositional_Structures/Basic_Modules/Thiele_Module"
begin

text \<open>
  This is a definition of the approval voting rule as elimination module as well as directly.
\<close>

subsection \<open>Definition\<close>


subsection \<open>Approval Voting\<close>

fun av_score :: "Thiele_Score" where
"av_score n = n"

fun (in committee_result) av_rule :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule" where 
"av_rule V A p = thiele_family av_score V A p"

fun harmonic :: "nat \<Rightarrow> real" where
"harmonic n = sum (\<lambda>x. 1/x) {1..n::nat}"

fun pav_score :: "Thiele_Score" where
"pav_score n = harmonic n"

fun (in committee_result) AV_rule' :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule" where
    "AV_rule' V A p =
      (let C = {S. S \<subseteq> A \<and> (card S) = k} in
    ({c \<in> C. \<forall> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) c \<ge> sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) d},
     {c \<in> C. \<exists> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) d > sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) c},
     {}))"

end