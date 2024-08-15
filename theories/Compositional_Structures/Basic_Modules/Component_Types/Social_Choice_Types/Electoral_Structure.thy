theory Electoral_Structure 
  imports 
     Profile_Interpretations 
     Result_Interpretations
begin

locale electoral_structure =
  ballot well_formed_ballot + result well_formed_result for
  well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  well_formed_result :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool" + 
  fixes limit_by_res :: "'r set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes
    "\<And> (A :: 'a set) (b :: 'b) (R :: 'r set). limit_by_res R b = limit_ballot (affected_alts R) b"

fun limit_by_res_\<P>\<V>_\<S>\<C>\<F> :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
"limit_by_res_\<P>\<V>_\<S>\<C>\<F> A b = (A \<times> A) \<inter> b"

    
global_interpretation \<P>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot" 
     "limit_set_\<S>\<C>\<F>" "affected_alts_\<S>\<C>\<F>" "ballot_\<P>\<V>" "well_formed_\<S>\<C>\<F>" "limit_by_res_\<P>\<V>_\<S>\<C>\<F>"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a" and
    b2 :: "'a Preference_Relation" and
    R :: "'a set"
  assume a1_pref: "(a1, a2) \<in> limit_by_res_\<P>\<V>_\<S>\<C>\<F> R b"
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
  thus "(a1, a2) \<in> limit_by_res_\<P>\<V>_\<S>\<C>\<F> R b" by (simp add: a1_in_R a2_in_R)
qed

fun limit_by_res_\<A>\<V>_\<S>\<C>\<F> :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_by_res_\<A>\<V>_\<S>\<C>\<F> A b = A \<inter> b"

fun limit_by_committee_\<A>\<V> :: "('a Committee) set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_by_committee_\<A>\<V> C b = \<Union>C \<inter> b"

global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" 
     "limit_set_\<S>\<C>\<F>" "affected_alts_\<S>\<C>\<F>" "ballot_\<A>\<V>" "well_formed_\<S>\<C>\<F>" "limit_by_res_\<A>\<V>_\<S>\<C>\<F>"
  by unfold_locales auto

global_interpretation \<A>\<V>_committee:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" 
  "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs" "ballot_\<A>\<V>" "\<lambda> A r. disjoint3 r" "limit_by_committee_\<A>\<V>"
  by unfold_locales auto

end