theory Electoral_Structure 
imports Profile_Interpretations Result_Interpretations
begin

locale electoral_structure =
  ballot well_formed_ballot + result well_formed_result for
  well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  well_formed_result :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool"
    
global_interpretation \<P>\<V>_\<S>\<W>\<F>:
  electoral_structure "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot" "limit_set_\<S>\<C>\<F>" "ballot_\<P>\<V>" "well_formed_\<S>\<C>\<F>"
  by unfold_locales

global_interpretation \<A>\<V>_\<S>\<W>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" "limit_set_\<S>\<C>\<F>" "ballot_\<A>\<V>" "well_formed_\<S>\<C>\<F>"
  by unfold_locales auto

end