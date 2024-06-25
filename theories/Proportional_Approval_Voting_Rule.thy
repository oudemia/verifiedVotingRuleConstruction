(*  File:       Approval_Voting_Rule.thy
    Copyright   2023  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Henriette Färber, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Voting Rules\<close>

section \<open>Approval Voting Rule\<close>

theory Proportional_Approval_Voting_Rule
  imports "Compositional_Structures/Basic_Modules/Approval_Voting_Module"
          "Compositional_Structures/Revision_Composition"
          "Compositional_Structures/Elect_Composition"
          "Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Electoral_Structure"
begin

text \<open>
  This is a definition of the approval voting rule as elimination module as well as directly.
\<close>

subsection \<open>Definition\<close>


fun single_winner_AV_rule :: "('v, 'a Approval_Set,'a) Electoral_Module" where
  "single_winner_AV_rule A p = \<A>\<V>_\<S>\<C>\<F>.elector single_winner_av A p"
  
fun single_winner_AV_rule' :: "('v, 'a Approval_Set,'a) Electoral_Module" where
  "single_winner_AV_rule' V A p =
    ({x \<in> A. \<forall> y \<in> A. \<A>\<V>_profile.win_count V p y \<le> \<A>\<V>_profile.win_count V p x},
     {y \<in> A. \<exists> x \<in> A. \<A>\<V>_profile.win_count V p x > \<A>\<V>_profile.win_count V p y},
     {})"

fun (in committee_result) approval_voting_rule :: "('v, 'a, 'a Approval_Set,'a Committee) Relay_Module" where
    "approval_voting_rule V A p = committee_relay (\<A>\<V>_committee.elector max_eliminator approval_voting) V A p"


fun (in committee_result) approval_voting_rule' :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
    "approval_voting_rule' V A p =
      (let C = {S. S \<subseteq> A \<and> (card S) = k} in
    ({c \<in> C. \<forall> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) c \<ge> sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) d},
     {c \<in> C. \<exists> d \<in> C. sum (\<lambda> x. \<A>\<V>_profile.win_count V p x) d > sum (\<lambda>x. \<A>\<V>_profile.win_count V p x) c},
     {}))"

end