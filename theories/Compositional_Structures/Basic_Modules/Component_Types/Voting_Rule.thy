section \<open>Voting Rules\<close>

theory Voting_Rule

imports
    Electoral_Module
    Enhanced_Profile
begin

text \<open>
  Voting Rules are a special component type of the composable
  modules voting framework. In contrast to an electoral module, a voting rule
  is not composable. It does not abstract from voting rules in social choice,
  but aims to model them, therefore "making the final decision" that an electoral
  model does not mae by design.

  A voting rule therefore receives a set ov voters, a set of eligible alternatives
  and a profile. It returns a set of (tied) winners.
\<close>

subsection \<open>Definition\<close>

type_synonym ('v, 'a, 'b, 'r) Voting_Rule = "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set"

type_synonym ('v, 'a, 'b, 'r, 'i) Voting_Rule_Family = 
	"('i => nat) => ('v, 'a, 'b, 'r) Voting_Rule"

fun voting_rule_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

end