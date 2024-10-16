theory Electoral_Structure 
  imports 
     Profile_Interpretations 
     Result_Interpretations
begin

locale electoral_structure =
  ballot well_formed_ballot + result _ well_formed_result for
  well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  well_formed_result :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool" + 
  fixes limit_by_conts :: "'r set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes
    limit_inherit: "\<And> (A :: 'a set) (b :: 'b) (R :: 'r set). limit_by_conts R b = limit_ballot (affected_alts R) b"
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

(*
function permute_bal :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "permute_bal \<pi> b = let \<rho>"
proof (auto)
qed  

function permute_cont :: "('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r" where
  "permute_cont \<pi> c = c"
proof (auto)
qed  

fun permute_alts :: "('v \<Rightarrow> 'v) \<Rightarrow> ('x, 'v, 'b) Election \<Rightarrow> ('x, 'v, 'b) Election" where
  "permute_alts \<pi> (X, V, p) = (X, \<pi> ` V, p \<circ> (the_inv \<pi>))"
*)

lemma wtf: 
fixes \<pi> :: "'a \<Rightarrow> 'a"
assumes "bij \<pi>"
shows "\<exists>(\<rho> :: 'b \<Rightarrow> 'b). bij \<rho> \<and> (\<forall> b. well_formed_ballot A b \<longrightarrow> (\<forall> B \<subseteq> A. limit_ballot (\<pi> ` B) (\<rho> b) = \<rho> (limit_ballot B b)))"
proof
oops

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
  electoral_structure "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot" "\<lambda>A. A"
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
  next
qed
(*
fix
    A :: "'a set" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assume bij: "bij \<pi>"
  show "\<exists>\<rho>. bij \<rho> \<and> (\<forall>b. ballot_\<P>\<V> A b \<longrightarrow> (\<forall>B\<subseteq>A. limit_\<P>\<V>_ballot (\<pi> ` B) (\<rho> b) = \<rho> (limit_\<P>\<V>_ballot B b)))"
  proof (standard)
    obtain \<rho> where *: "\<rho> = (\<lambda> b. (\<lambda> (a1, a2). (\<pi> a1, \<pi> a2)) ` b)" by simp
    have "bij \<rho> \<and> (\<forall>b. ballot_\<P>\<V> A b \<longrightarrow> (\<forall>B\<subseteq>A. limit_\<P>\<V>_ballot (\<pi> ` B) (\<rho> b) = \<rho> (limit_\<P>\<V>_ballot B b)))"
    proof (standard)
    have "bij \<rho>" 
    proof (unfold bij_def inj_def surj_def, auto)
    fix 
      x y :: "('a \<times> 'a) set" and
      a b :: 'a
    assume 
      eq: "\<rho> x = \<rho> y" and 
      elem: "(a, b) \<in> x"
    hence "(\<pi> a, \<pi> b) \<in> \<rho> x" using * by fast
    hence "(\<pi> a, \<pi> b) \<in> \<rho> y" using eq by simp
    hence "((the_inv \<pi>)(\<pi> a), (the_inv \<pi>)(\<pi> b)) \<in> y" using bij * by try

    thus "(a, b) \<in> y" using bij by try
    proof (auto)
    fix
   
    qed      
    next
      fix B :: "'a set"
      assume sub: "B \<subseteq> A"
      have "bij \<rho> \<and> (\<forall>b. ballot_\<P>\<V> A b \<longrightarrow> (\<forall>B\<subseteq>A. limit_\<P>\<V>_ballot (\<pi> ` B) (\<rho> b) = \<rho> (limit_\<P>\<V>_ballot B b)))" sorry
   thus ?thesis
qed

emma "EX x. P x"
proof -
obtain x where <...>
<...>
have "P x" <...>
show ?thesis ..
qed 
*)


fun limit_app_to_alts :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_alts A b = A \<inter> b"

fun limit_app_to_comm :: "('a Committee) set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_comm C b = \<Union>C \<inter> b"

global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" "\<lambda>A. A"
     "limit_alts" "affected_alts_\<S>\<C>\<F>" "ballot_\<A>\<V>" "well_formed_\<S>\<C>\<F>" "limit_app_to_alts"
  by unfold_locales auto

sublocale committee_result \<subseteq> \<A>\<V>_committee:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" "committees"
  "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs" "ballot_\<A>\<V>" "\<lambda> A r. disjoint3 r" "limit_app_to_comm"
proof (unfold_locales, safe)
    fix 
      A C :: "'a set" and
      a :: 'a
    assume 
      committee: " C \<in> committees A" and 
      elem: "a \<in> C"
    show "a \<in> A"
      using committee elem by auto
  next
    fix 
      A C:: "'a set" and
      a :: 'a
      assume
      comm: "C \<in> committees A" and
      elem: "a \<in> A"
    show "a \<in> \<Union> (committees A)" 
      proof (cases)
        assume fin: "finite A"
        have "card C > 0" using comm k_positive by force
        hence "card C = k" using comm by fastforce
        have "C \<subseteq> A" using comm by simp
        hence "card C \<le> card A" using fin by (simp add: card_mono)
        hence "card A \<ge> k" using fin comm by simp
        hence "\<Union>(committees A) = A" using committees_cover_A by auto
        hence "\<exists>D \<in> committees A. a \<in> D" using elem by auto
        thus ?thesis by simp
      next
        assume inf: "infinite A"
        hence "\<exists>D \<subseteq> A. card D = k \<and> a \<in> D" using elem fin_subset_with_elem k_positive by metis
        then obtain D where *: "D \<subseteq> A \<and> card D = k \<and> a \<in> D" by blast
        hence "D \<in> committees A" by simp
        thus ?thesis using elem comm committees.simps using "*" by auto
      qed 
  next
    fix 
      A B C :: "'a set" and
      a :: 'a
    assume 
      sub: "A \<subseteq> B" and 
      comm: " C \<in> committees A" and 
      elem: "a \<in> C"
    have "committees A \<subseteq> committees B" using sub by auto
    moreover have "a \<in>  \<Union> (committees A)" using comm elem by blast 
    ultimately show "a \<in> \<Union> (committees B)" by blast
 next
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