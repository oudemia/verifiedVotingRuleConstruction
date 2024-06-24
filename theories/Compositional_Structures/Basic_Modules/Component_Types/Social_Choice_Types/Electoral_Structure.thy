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
  by unfold_locales simp


fun limit_by_res_\<A>\<V>_\<S>\<C>\<F> :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_by_res_\<A>\<V>_\<S>\<C>\<F> A b = A \<inter> b"

global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" 
     "limit_set_\<S>\<C>\<F>" "affected_alts_\<S>\<C>\<F>" "ballot_\<A>\<V>" "well_formed_\<S>\<C>\<F>" "limit_by_res_\<A>\<V>_\<S>\<C>\<F>"
  by unfold_locales auto

end