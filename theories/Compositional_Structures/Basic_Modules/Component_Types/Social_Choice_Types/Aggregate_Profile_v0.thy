theory Aggregate_Profile_v0
  imports
    Electoral_Structure
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

locale aggregate_profile =
  base: ballot well_formed_ballot\<^sub>B empty\<^sub>B prefers\<^sub>B wins\<^sub>B limit_ballot\<^sub>B +
        electoral_structure empty_ballot _ _ _ limit_contenders for
    well_formed_ballot\<^sub>B :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    empty\<^sub>B :: "'b" and
    prefers\<^sub>B :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and
    wins\<^sub>B :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and    
    limit_ballot\<^sub>B :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b" and
    empty_ballot :: "'r \<Rightarrow> 'i" and
    limit_contenders :: "'r set \<Rightarrow> 'r set \<Rightarrow> 'r set" +
  fixes
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('b, 'r, 'i) Ballot_Aggregation"
  assumes
    preserve_valid: "\<And> (b:: 'b). well_formed_ballot\<^sub>B A b \<longrightarrow> well_formed_ballot (contenders A) (aggretate b)" and
    valid_trans: "\<And> (A :: 'a set)(B :: 'a set) (b :: 'b). A \<subseteq> B \<and> well_formed_ballot\<^sub>B A b 
        \<longrightarrow> well_formed_ballot (contenders B) (aggretate b)"

sublocale aggregate_profile \<subseteq> electoral_structure
 using electoral_structure_axioms
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

subsection \<open>Thiele Methods\<close>


type_synonym Thiele_Score = "nat => nat"

type_synonym Thiele_Score' = "nat => real"

fun thiele_score :: "Thiele_Score \<Rightarrow> bool" where
"thiele_score w = ((w 0 = 0) \<and> (\<forall> x. \<forall> y. x < y \<longrightarrow> (w x \<le> w y)))"

fun (in committee_result) thiele_aggregator :: "('a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregator b W = (card (W \<inter> b))"

fun (in committee_result) thiele_agg_profile :: "('v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile p v W = thiele_aggregator (p v) W"

fun thiele_ballot :: "('a Committee) set \<Rightarrow> (('a Committee) \<Rightarrow> nat) \<Rightarrow> bool" where
"thiele_ballot R b = (\<forall> r \<in> R. b r \<ge> 0)"

global_interpretation (in committee_result) thiele_profile:
  aggregate_profile "\<lambda> c. 0" "\<lambda> b c d. (b c > b d)" "\<lambda> b c. (\<forall> d. b c \<ge> b d)" "\<lambda> R b. b" 
  "ballot_\<A>\<V>" "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" 
    thiele_ballot committee_contenders thiele_aggregator
proof (unfold_locales, safe)
oops


end