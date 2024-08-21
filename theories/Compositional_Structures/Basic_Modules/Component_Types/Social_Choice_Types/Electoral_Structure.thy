theory Electoral_Structure 
  imports 
     Profile_Interpretations 
     Result_Interpretations
begin

locale electoral_structure =
  ballot well_formed_ballot + result well_formed_result for
  well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  well_formed_result :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool" + 
  fixes limit_by_conts :: "'r set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes
    "\<And> (A :: 'a set) (b :: 'b) (R :: 'r set). limit_by_conts R b = limit_ballot (affected_alts R) b"


fun limit_pref_to_alts :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
"limit_pref_to_alts A b = (A \<times> A) \<inter> b"

global_interpretation \<P>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot" 
     "limit_alts" "affected_alts_\<S>\<C>\<F>" "ballot_\<P>\<V>" "well_formed_\<S>\<C>\<F>" "limit_pref_to_alts"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a" and
    b2 :: "'a Preference_Relation" and
    R :: "'a set"
  assume a1_pref: "(a1, a2) \<in> limit_pref_to_alts R b"
  hence "a1 \<in> R"  by auto
  hence a1_affected: "a1  \<in> affected_alts_\<S>\<C>\<F> R" by auto
  have "a2 \<in> R" using a1_pref by auto
  hence a2_affected: "a2  \<in> affected_alts_\<S>\<C>\<F> R" by auto
  moreover have "(a1, a2) \<in> b" using a1_pref by auto
  hence "(a1, a2) \<in> {(c1, c2) \<in> b . c1 \<in> affected_alts_\<S>\<C>\<F> R \<and> c2 \<in> affected_alts_\<S>\<C>\<F> R}"
    using a1_affected a2_affected by auto
  thus "(a1, a2) \<in> limit_\<P>\<V>_ballot (affected_alts_\<S>\<C>\<F> R) b" by simp
next
fix
    A :: "'a set" and
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a" and
    b2 :: "'a Preference_Relation" and
    R :: "'a set"
  assume as_in_b: "(a1, a2) \<in> limit_\<P>\<V>_ballot (affected_alts_\<S>\<C>\<F> R) b"
  hence a1_in_R: "a1 \<in> R"  by auto
  have a2_in_R:  "a2 \<in> R" using as_in_b by auto
  moreover have "(a1, a2) \<in> b" using as_in_b by auto
  thus "(a1, a2) \<in> limit_pref_to_alts R b" by (simp add: a1_in_R a2_in_R)
qed


fun limit_app_to_alts :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_alts A b = A \<inter> b"

fun limit_app_to_comm :: "('a Committee) set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_comm C b = \<Union>C \<inter> b"

global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" 
     "limit_alts" "affected_alts_\<S>\<C>\<F>" "ballot_\<A>\<V>" "well_formed_\<S>\<C>\<F>" "limit_app_to_alts"
  by unfold_locales auto

global_interpretation \<A>\<V>_committee:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" 
  "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs" "ballot_\<A>\<V>" "\<lambda> A r. disjoint3 r" "limit_app_to_comm"
  by unfold_locales auto


subsection \<open>Aggregate Profiles\<close>
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

type_synonym ('b, 'r, 'i) Ballot_Aggregation = "'b \<Rightarrow> ('r \<Rightarrow> 'i)"

locale aggregate_structure =
  base: electoral_structure 
        empty\<^sub>B prefers\<^sub>B wins\<^sub>B limit_ballot\<^sub>B limit_conts\<^sub>B affected_alts\<^sub>B
        well_formed_ballot\<^sub>B well_formed_result\<^sub>B limit_by_conts\<^sub>B +
  agg: electoral_structure 
        _ _ _ limit_ballot _ _ _ _ limit_ballot for
    empty\<^sub>B :: "'b" and
    prefers\<^sub>B :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and
    wins\<^sub>B :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and    
    limit_ballot\<^sub>B :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b" and
    limit_conts\<^sub>B :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set" and
    affected_alts\<^sub>B :: "'r set \<Rightarrow> 'a set" and
    well_formed_ballot\<^sub>B :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    well_formed_result\<^sub>B :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool" and
    limit_by_conts\<^sub>B :: "'r set \<Rightarrow> 'b \<Rightarrow> 'b" and
    limit_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> ('r \<Rightarrow> 'i)" +
  fixes
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('b, 'r, 'i) Ballot_Aggregation"
  assumes
    dummy: "limit_by_conts = limit_ballot" and 
    conts_are_alts: "\<And> (R :: 'r set). affected_alts R = R" and
    preserve_empty: "aggregate empty\<^sub>B = empty_ballot" and
    contenders_valid: "\<And>(A :: 'a set). affected_alts\<^sub>B (contenders A) = A" and
    agg_valid: "\<And> (A:: 'a set) (b:: 'b). well_formed_ballot\<^sub>B A b \<Longrightarrow> well_formed_ballot (contenders A) (aggretate b)" and
    valid_trans: "\<And> (A :: 'a set)(B :: 'a set) (b :: 'b). A \<subseteq> B \<and> well_formed_ballot\<^sub>B A b 
        \<Longrightarrow> well_formed_ballot (contenders B) (aggretate b)"


sublocale aggregate_structure \<subseteq> electoral_structure
proof (unfold_locales)
  fix 
    R :: "'r set" and
    b :: "'r \<Rightarrow> 'i"
  have "affected_alts R = R" using conts_are_alts by simp
  moreover have "limit_by_conts = limit_ballot" using dummy by simp
  ultimately show "limit_by_conts R b =  limit_ballot (affected_alts R) b" by simp
qed


end