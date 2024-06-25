section \<open>Approval Voting Module\<close>

theory Proportional_Approval_Voting_Module
  imports 
      "Component_Types/Elimination_Module"
      "Component_Types/Relay_Module"
      "Thiele_Module"
begin

text \<open>
  The approval voting rule elects all modules with the maximum amount of approvals
  among all alternatives, and rejects all the other alternatives.
  It is electing and induces the classical (single-winner) approval voting rule
  from social-choice theory.
\<close>

subsection \<open>Approval Voting, Single Winner Case\<close>


fun harmonic :: "enat \<Rightarrow> ereal" where
"harmonic \<infinity> = \<infinity>" |
"harmonic n = sum (\<lambda>x. 1/x) {1..n::nat}"

fun pav_score :: "('a Committee, 'v, 'a Approval_Set) Evaluation_Function" where
  "pav_score V C A p = sum (\<lambda> v. harmonic (sum (\<lambda>c. \<A>\<V>_profile.win_count {v} p c) C)) V"

fun (in committee_result) pav :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
  "pav V A p = committee_relay (max_eliminator pav_score) V A p"

fun (in committee_result) pav' :: "('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
    "pav' V A p =
      (let C = {S. S \<subseteq> A \<and> (card S) = k} in
    ({},
     {c \<in> C. \<forall> d \<in> C. pav_score V c C p \<ge> pav_score V c C p},
     {c \<in> C. \<exists> d \<in> C. pav_score V c C p > pav_score V c C p}))"

end