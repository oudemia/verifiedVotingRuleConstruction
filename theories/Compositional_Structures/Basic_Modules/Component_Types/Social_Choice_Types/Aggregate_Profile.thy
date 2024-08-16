theory Aggregate_Profile
  imports
    Profile
    Result
    "HOL-Library.Extended_Real"
begin

section \<open>Contender Schemata\<close>
text \<open>
  While a voting rule receives an alternative, electoral modules operate on choices,
  which are of the same type as the results of an election.

  A choice schema is a generalization of a profile and aims to capture information
  about the preference of voters on choices (in contrast to profiles, which capture
  the preferences of voters on alternatives).
  For the sake of clarity, an abstract profile should always store minimally complex data.
\<close>


subsection \<open>Defintion\<close>

type_synonym ('v, 'r, 'i) Aggregate_Profile = "('v,  'r \<Rightarrow> 'i) Profile"

locale aggregate_profile =
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
    aggregate :: "('v, 'b) Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"
assumes
    "\<And> (V :: 'v set) (A:: 'a set) (p :: ('v, 'b) Profile). \<forall> v \<in> V. base_ballot A (p v) \<longrightarrow> well_formed_ballot (contenders A) ((aggretate p) v)"

sublocale aggregate_profile \<subseteq> ballot
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