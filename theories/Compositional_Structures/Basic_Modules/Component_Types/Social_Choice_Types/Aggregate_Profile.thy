theory Aggregate_Profile
  imports
    Profile_Interpretations
    Result
begin

section \<open>Aggregate Profiles\<close>
text \<open>
  While a voting rule receives a set of alternatives, electoral modules operate on contenders,
  which are of the same type as the results of an election. This is negligible in
  the case of single winner voting, where contenders are alternatives.

  An aggregate profile is a generalization of a profile and aims to capture information
  about the preference of voters on contenders (in contrast to profiles, which capture
  the preferences of voters on alternatives). An aggregate profile is computed based on a
  profile.
  For the sake of clarity, an aggregate profile should always store minimally complex data.
\<close>

subsection \<open>Defintion\<close>

type_synonym ('r, 'i) Contender_Score = "'r \<Rightarrow> 'i"

type_synonym ('v, 'r, 'i) Aggregate_Profile = "('v, ('r, 'i) Contender_Score) Profile"

type_synonym ('v, 'b, 'r, 'i) Profile_Aggregation = "('v, 'b) Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"

type_synonym ('b, 'r, 'i) Ballot_Aggregation = "'b \<Rightarrow> ('r, 'i) Contender_Score"

type_synonym ('v, 'a, 'b, 'r) Voting_Rule = "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set"

type_synonym ('v, 'a, 'b, 'r, 'i) Voting_Rule_Family = 
	"('v, 'b, 'r, 'i) Profile_Aggregation \<Rightarrow>  ('i \<Rightarrow> real)  \<Rightarrow> ('v, 'a, 'b, 'r) Voting_Rule"

fun voting_rule_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

locale aggregate_ballot =
  base: ballot base_ballot empty_base prefers_base wins_base limit_base +
  ballot well_formed_ballot  for
    base_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    empty_base :: "'b" and
    prefers_base :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and
    wins_base :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and
    limit_base :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b" and
    well_formed_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" +
  fixes
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('b, 'r, 'i) Ballot_Aggregation"
assumes
    preserve_valid: "\<And> (A :: 'a set) (b:: 'b). base_ballot A b \<Longrightarrow> well_formed_ballot (contenders A) (aggregate b)" and
    valid_trans: "\<And> (A :: 'a set)(B :: 'a set) (b :: 'b). A \<subseteq> B \<and> base_ballot A b 
        \<Longrightarrow> well_formed_ballot (contenders B) (aggregate b)"

sublocale aggregate_ballot \<subseteq> ballot
 using ballot_axioms
  by simp


subsection \<open>Contenders\<close>
text \<open>
  Contenders are of the same type as election results and represent possible or incomplete
  results that are part of the computation of a final result.
\<close>

fun single_contenders :: "'a set \<Rightarrow> 'a set" where
"single_contenders A = A"

fun (in committee_result) committee_contenders :: "'a set \<Rightarrow> ('a Committee) set" where
"committee_contenders A = committees A"
end