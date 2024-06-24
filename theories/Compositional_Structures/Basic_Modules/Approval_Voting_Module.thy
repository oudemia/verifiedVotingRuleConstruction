section \<open>Approval Voting Module\<close>

theory Approval_Voting_Module
  imports "Component_Types/Elimination_Module"
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

fun approval_voting :: "('v, 'a Approval_Set, 'a) Electoral_Module" where
  "approval_voting V A p = max_eliminator av_score V A p"

fun approval_voting' :: "('v, 'a Approval_Set, 'a) Electoral_Module" where
  "approval_voting' V A p =
    ({},
     {a \<in> A. \<exists> x \<in> A. \<A>\<V>_profile.win_count V p x > \<A>\<V>_profile.win_count V p a},
     {a \<in> A. \<forall> x \<in> A. \<A>\<V>_profile.win_count V p x \<le> \<A>\<V>_profile.win_count V p a})"

end