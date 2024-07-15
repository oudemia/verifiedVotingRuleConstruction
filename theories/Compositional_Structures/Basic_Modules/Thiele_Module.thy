section \<open>Approval Voting Module\<close>

theory Thiele_Module
  imports 
      "Component_Types/Elimination_Module"
      "Component_Types/Voting_Rule"
begin

subsection \<open>Prototype of Thiele Methods\<close>

type_synonym id_function = "enat \<Rightarrow> ereal"

fun thiele_score :: "id_function \<Rightarrow> ('a Committee, 'v, 'a Approval_Set) Evaluation_Function" where
  "thiele_score w V C A p = sum (\<lambda> v. w (sum (\<lambda>c. \<A>\<V>_profile.win_count {v} p c) C)) V"

fun (in committee_result) thiele_method :: "id_function \<Rightarrow> ('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
  "thiele_method w V A p = committee_relay (max_eliminator (thiele_score w)) V A p"

fun (in committee_result) thiele_method' :: "id_function \<Rightarrow> ('v, 'a, 'a Approval_Set, 'a Committee) Relay_Module" where
    "thiele_method' w V A p =
      (let C = {S. S \<subseteq> A \<and> (card S) = k} in
    ({},
     {c \<in> C. \<forall> d \<in> C. thiele_score w V c C p \<ge> thiele_score w V d C p},
     {c \<in> C. \<exists> d \<in> C. thiele_score w V c C p < thiele_score w V d C p}))"

end