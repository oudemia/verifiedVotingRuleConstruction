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

type_synonym ('v, 'r, 'i) Aggregate_Profile = "('v, ('r \<Rightarrow>'i)) Profile"
  
type_synonym ('v, 'b, 'r, 'i) Profile_Aggregation = "('v, 'b) Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"

type_synonym ('a, 'v, 'b, 'r, 'i) Profile_Aggregation' = "'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"

type_synonym ('b, 'r, 'i) Ballot_Aggregation = "'b \<Rightarrow> ('r \<Rightarrow> 'i)"

type_synonym ('a, 'b, 'r, 'i) Ballot_Aggregation' = "'a set \<Rightarrow> 'b \<Rightarrow> ('r \<Rightarrow> 'i)"


locale aggregation =
  ballot well_formed_ballot for
    well_formed_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" +
  fixes
    well_formed_base :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('a, 'b, 'r, 'i) Ballot_Aggregation'"
  assumes
    preserve_valid: "\<And> (A :: 'a set) (b:: 'b). well_formed_base A b 
        \<Longrightarrow> well_formed_ballot (contenders A) (aggregate A b)" 
(*
and
    valid_trans: "\<And> (A :: 'a set)(B :: 'a set) (b :: 'b). A \<subseteq> B \<and> well_formed_base A b 
        \<Longrightarrow> well_formed_ballot (contenders B) (limit_ballot (contenders B) (aggregate b))"
*)
begin

lemma aggregate_preserves_permute:
fixes 
  \<pi> :: "'v \<Rightarrow> 'v" and
  p q :: "('v, 'b) Profile" and 
  V V' :: "'v set" and 
  A A' :: "'a set"
assumes 
  bij: "bij \<pi>" and 
  rename: "rename \<pi> (A, V, p) = (A', V', q)"
  shows "rename \<pi> ((committees A), V, (aggregate A) \<circ> p) = ((committees A'), V', (aggregate A') \<circ> q)"
  proof (standard, simp)
    have A_id: "A = A'" using rename by simp
    thus "committees A = committees A'" by simp
  next
    show "snd (rename \<pi> (committees A, V, aggregate A \<circ> p)) = snd (committees A', V', aggregate A' \<circ> q)"
    proof (standard, simp)
      show "\<pi> ` V = V'" using rename by simp 
    next
      have A_id: "A = A'" using rename by simp
      have "q = p \<circ> (the_inv \<pi>)" using rename by simp
      hence "(aggregate A') \<circ> q = (aggregate A') \<circ> p \<circ> (the_inv \<pi>)" by auto
      hence "(aggregate A') \<circ> q = (aggregate A) \<circ> p \<circ> (the_inv \<pi>)" 
        using A_id 
        by simp
      thus "snd (snd (rename \<pi> (committees A, V, aggregate A \<circ> p))) = 
        snd (snd (committees A', V', aggregate A' \<circ> q))" 
        by simp
  qed
qed
  
end



locale aggregate_ballot =
  base: ballot well_formed_ballot +
  ballot ballot_agg empty_agg prefers_agg wins_agg limit_agg  for
    well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    ballot_agg :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" and
    empty_agg :: "('r \<Rightarrow> 'i)" and
    prefers_agg :: "('r \<Rightarrow> 'i) \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" and
    wins_agg :: "('r \<Rightarrow> 'i) \<Rightarrow> 'r \<Rightarrow> bool" and
    limit_agg :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> ('r \<Rightarrow> 'i)" +
  fixes
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('b, 'r, 'i) Ballot_Aggregation"
  assumes
    preserve_valid: "\<And> (A :: 'a set) (b:: 'b). well_formed_ballot A b 
        \<Longrightarrow> ballot_agg (contenders A) (aggregate b)" and
    preserve_empty: "aggregate empty_ballot = empty_agg" and
    valid_trans: "\<And> (A :: 'a set)(B :: 'a set) (b :: 'b). A \<subseteq> B \<and> well_formed_ballot A b 
        \<Longrightarrow> ballot_agg (contenders B) (aggregate (limit_ballot B b))"

text \<open>
 Aggregate ballots are ballots. This is important because it allows us to use them in
 electoral structures later on.
\<close>
sublocale aggregation \<subseteq> ballot
  by (simp add: ballot_axioms)

sublocale aggregate_ballot \<subseteq> ballot
  by (simp add: base.ballot_axioms)
  
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