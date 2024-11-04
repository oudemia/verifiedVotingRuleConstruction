theory Electoral_Structure 
  imports 
     Profile_Interpretations 
     Result_Interpretations
     Aggregate_Profile
     begin

locale electoral_structure =
  ballot well_formed_ballot + result contenders for
  well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  contenders :: "'a set \<Rightarrow> 'r set" + 
  fixes limit_by_conts :: "'r set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes
    limit_inherit: "limit_by_conts R b = limit_ballot (affected_alts R) b"
begin

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
    using limit_inherit 
    by blast
  ultimately show "well_formed_ballot (affected_alts ?R) (p' v)"
    by (simp add: lim limit_inherit limit_sound)
qed

sublocale ballot well_formed_ballot empty_ballot prefers wins limit_ballot
by (simp add: ballot_axioms)

sublocale result
by (simp add: result_axioms)

end


sublocale electoral_structure \<subseteq> ballot
proof (unfold_locales)
qed 

sublocale electoral_structure \<subseteq> result
proof (unfold_locales)
qed


fun limit_pref_to_alts :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
"limit_pref_to_alts A b = (A \<times> A) \<inter> b"

global_interpretation \<P>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot"
     "limit_alts" "affected_alts_\<S>\<C>\<F>" "ballot_\<P>\<V>" id "limit_pref_to_alts"
proof (unfold_locales, standard)
  fix A :: "'a set" 
  show "affected_alts_\<S>\<C>\<F> (id A) = A" by simp 
next
  fix
    A B:: "'a set"
  show " A \<subseteq> B \<longrightarrow> affected_alts_\<S>\<C>\<F> (id A) \<subseteq> affected_alts_\<S>\<C>\<F> (id B)" by simp
next
  fix
    R :: "'a set" and
    b :: "'a Preference_Relation"
  have "limit_pref_to_alts R b = (R \<times> R) \<inter> b" by simp
  moreover have "affected_alts_\<S>\<C>\<F> R = R" by simp
  moreover have "limit_\<P>\<V>_ballot (affected_alts_\<S>\<C>\<F> R) b = (R \<times> R) \<inter> b" by auto
  ultimately show "limit_pref_to_alts R b = limit_\<P>\<V>_ballot (affected_alts_\<S>\<C>\<F> R) b" by simp
next
  fix A :: "'a set"
  show "A \<noteq> {} \<and> affected_alts_\<S>\<C>\<F> (id A) = {} \<longrightarrow> id A = {}" by simp
qed

fun limit_app_to_alts :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_alts A b = A \<inter> b"

fun limit_app_to_comm :: "('a Committee) set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_comm C b = \<Union>C \<inter> b"

global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" limit_\<A>\<V>_ballot
     limit_alts affected_alts_\<S>\<C>\<F> ballot_\<A>\<V> id limit_app_to_alts
  by unfold_locales auto

sublocale committee_result \<subseteq> \<A>\<V>_committee:
  electoral_structure default_ballot_\<A>\<V> prefers_\<A>\<V> wins_\<A>\<V> limit_\<A>\<V>_ballot
  "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" affected_alts_committee ballot_\<A>\<V> committees limit_app_to_comm
proof (unfold_locales, unfold affected_alts_committee.simps, safe)
    fix  
      A :: "'a set" and
      R :: "('a Committee) set" and
      a :: 'a and
      b :: "'a Approval_Set"
    assume "a \<in> limit_app_to_comm R b"
    thus "a \<in> limit_\<A>\<V>_ballot (\<Union> R) b" by fastforce
  next
    fix  
      A :: "'a set" and
      R :: "('a Committee) set" and
      a :: 'a and
      b :: "'a Approval_Set"
    assume "a \<in> limit_\<A>\<V>_ballot (\<Union> R) b"
    thus "a \<in> limit_app_to_comm R b"  by fastforce
qed   

end