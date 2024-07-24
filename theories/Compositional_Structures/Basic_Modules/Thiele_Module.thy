section \<open>Approval Voting Module\<close>

theory Thiele_Module
  imports 
      "Component_Types/Elimination_Module"
      "Component_Types/Voting_Rule"
      "Component_Types/Enhanced_Profile"
      "Component_Types/Social_Choice_Types/Electoral_Structure"
begin

subsection \<open>Prototype of Thiele Methods\<close>

type_synonym Thiele_Score = "nat => nat"

type_synonym Thiele_Score' = "nat => real"

fun thiele_score :: "Thiele_Score \<Rightarrow> bool" where
"thiele_score w = ((w 0 = 0) \<and> (\<forall> x. \<forall> y. x < y \<longrightarrow> (w x \<le> w y)))"


text \<open>
  The enhanced profile for a Thiele method has a specific shape: For any voter v and any
  committee W, the profile returns the Thiele score of the ballot of v and W.
\<close>

fun (in committee_result) thiele_contenders :: "'a set => ('a Committee) set" where
"thiele_contenders A = {W. W \<subseteq> A \<and> card W = k}"

fun (in committee_result) thiele_profile :: "('v, 'a Approval_Set) Profile \<Rightarrow> ('v, 'a Committee, nat) Enhanced_Profile" where
"thiele_profile p v W = (card (W \<inter> (p v)))"

fun thiele_module :: "Thiele_Score \<Rightarrow> ('v, 'a Committee, nat) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R ep. (\<Sum> v \<in> V.  s (ep v r)))) V C p"

fun (in committee_result) thiele_family :: "('v, 'a, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where 
"thiele_family w V A p =
	elect (thiele_module w) V (thiele_contenders A) (thiele_profile p)"












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



fun av_score :: "Thiele_Score" where
"av_score n = n"

fun av_schema :: "('v, 'a Approval_Set) Profile \<Rightarrow> ('v, 'a Committee, ereal) Enhanced_Profile" where
"av_schema p = thiele_choice_schema av_score p"

fun harmonic :: "nat \<Rightarrow> ereal" where
"harmonic n = sum (\<lambda>x. 1/x) {1..n::nat}"

fun pav_score :: "Thiele_Score" where
"pav_score n = harmonic n"

end