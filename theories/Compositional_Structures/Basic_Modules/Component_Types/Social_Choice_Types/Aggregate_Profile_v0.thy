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
  ballot +
  fixes 
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" and 
    limit_aggregate_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> ('r \<Rightarrow> 'i)" and 
    aggregate :: "('v, 'b) Profile  \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"
  assumes
    valid_aggregate: "\<And> (A :: 'a set) (V :: 'v set) (p :: ('v, 'b) Profile).
      \<forall> v \<in> V. well_formed_ballot A (p v) \<Longrightarrow> aggregate_ballot (contenders A) ((aggretate p) v)" and
   limit_sound: "\<And> (R::'r set) (S::'r set) (V :: 'v set) (p :: ('v, 'r, 'i) Aggregate_Profile).
      \<forall> v \<in> V. aggregate_ballot R (p v) \<and> S \<subseteq> R \<Longrightarrow> aggregate_ballot S (limit_aggregate_ballot S (p v))"

subsection \<open>Contenders\<close>
text \<open>
  Contenders are of the same type as election results and represent possible or incomplete
  results that are part of the computation of a final result.
\<close>

fun single_contenders :: "'a set \<Rightarrow> 'a set" where
"single_contenders A = A"

fun (in committee_result) committee_contenders :: "'a set \<Rightarrow> ('a Committee) set" where
"committee_contenders A = committees A"


(*

locale aggregate_profile =
  ballot +
  ballot aggregate_ballot aggregate_base prefers_contender winning_contender limit_aggregate_ballot for
  aggregate_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" and 
  prefers_contender :: "('r \<Rightarrow> 'i) \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" and 
  winning_contender :: "('r \<Rightarrow> 'i) \<Rightarrow> 'r \<Rightarrow> bool" +
  fixes aggregate :: "('v, 'b) Profile  \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"
  assumes
    "\<And> (V :: 'v set) (p :: ('v, 'b) Profile). \<forall> v \<in> V. well_formed_ballot p v \<rightarrow> aggregate_ballot (aggretate p) v"
*)

end