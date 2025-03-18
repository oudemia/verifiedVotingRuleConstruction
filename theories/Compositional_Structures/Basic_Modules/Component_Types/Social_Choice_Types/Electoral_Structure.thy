(*  File:       Electoral_Structure.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Henriette Färber, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Structure\<close>

theory Electoral_Structure
  imports 
     Profile_Interpretations 
     Result_Interpretations
     Aggregate_Profile
     begin

locale electoral_structure =
  ballot well_formed_ballot + result contenders for
  well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  contenders :: "'a set \<Rightarrow> 'r set"
begin

fun limit_by_conts :: "'r set \<Rightarrow> 'b \<Rightarrow> 'b" where
"limit_by_conts R b = limit_ballot (affected_alts R) b"


lemma well_formed_ballots_inherit:
fixes
  V :: "'v set" and
  A :: "'a set" and
  p p' :: "('v, 'b) Profile" and
  v :: 'v
assumes 
  elem: "v \<in> V" and
  fp: "finite_profile V A p" and
  lim: "p' = (limit_by_conts (contenders A) \<circ> p)"
shows "well_formed_ballot (affected_alts (contenders A)) (p' v)"
proof -
  let ?R = "contenders A"
  have "finite A" using fp by simp
  hence subR: "affected_alts ?R \<subseteq> A" 
    using result_axioms
    by (metis bot.extremum result_def subset_iff_psubset_eq)
  moreover have "well_formed_ballot A (p v)" 
    using fp elem
    by (simp add: well_formed_profile_def)
  moreover have "limit_by_conts ?R (p' v) = limit_ballot (affected_alts ?R) (p' v)"
  by simp
  ultimately show "well_formed_ballot (affected_alts ?R) (p' v)"
    by (simp add: lim limit_sound)
qed

sublocale ballot
by (simp add: ballot_axioms)

sublocale result
by (simp add: result_axioms)

end


sublocale electoral_structure \<subseteq> ballot
by unfold_locales

sublocale electoral_structure \<subseteq> result
by unfold_locales


subsection \<open>Interpretations\<close>


global_interpretation \<P>\<V>_\<S>\<C>\<F>:
  electoral_structure default_ballot_\<P>\<V> prefers_\<P>\<V> wins_\<P>\<V> limit_\<P>\<V>_ballot
  limit_alts affected_alts_\<S>\<C>\<F> ballot_\<P>\<V> id
by unfold_locales auto


global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure default_ballot_\<A>\<V> prefers_\<A>\<V> wins_\<A>\<V> limit_\<A>\<V>_ballot
     limit_alts affected_alts_\<S>\<C>\<F> ballot_\<A>\<V> id
by unfold_locales auto


sublocale committee_result \<subseteq> \<A>\<V>_committee:
  electoral_structure default_ballot_\<A>\<V> prefers_\<A>\<V> wins_\<A>\<V> limit_\<A>\<V>_ballot
  limit_committees affected_alts_committee ballot_\<A>\<V> committees
by (simp add: \<A>\<V>_profile.ballot_axioms electoral_structure_def result_axioms)

end