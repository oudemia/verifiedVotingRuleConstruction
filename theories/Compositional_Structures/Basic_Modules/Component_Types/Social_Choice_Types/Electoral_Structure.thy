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
    "\<And> (A :: 'a set) (b :: 'b) (R :: 'r set). limit_by_conts R b = limit_ballot (affected_alts R) b"

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
  fix
    A e r d:: "'a set"
  assume 
    part: "set_equals_partition (limit_alts A UNIV) (e, r, d)" and 
    disj: " disjoint3 (e, r, d)"
  thus "well_formed_\<S>\<C>\<F> A (e, r, d)" by fastforce
next
  fix
    A R :: "'a set" and
    a :: 'a
  assume "a \<in> affected_alts_\<S>\<C>\<F> (limit_alts A R)"
  thus "a \<in> A" by fastforce
next
  fix
    A :: "'a set" and
    a b :: 'a
  assume "a \<notin> {}" and "b \<in> affected_alts_\<S>\<C>\<F> A"
  thus "b \<in> A" by auto
next
  fix
    A :: "'a set" and
    a b :: 'a
  assume "a \<notin> {}" and "b \<in> A"
  thus "b \<in> affected_alts_\<S>\<C>\<F> A" by auto
next
 fix
    A B :: "'a set" and
    a :: 'a
  assume "A \<subseteq> B" and "a \<in> affected_alts_\<S>\<C>\<F> A"
  thus "a \<in> affected_alts_\<S>\<C>\<F> B" by auto
qed


fun limit_app_to_alts :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_alts A b = A \<inter> b"

fun limit_app_to_comm :: "('a Committee) set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_app_to_comm C b = \<Union>C \<inter> b"

global_interpretation \<A>\<V>_\<S>\<C>\<F>:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" "\<lambda>A. A"
     "limit_alts" "affected_alts_\<S>\<C>\<F>" "ballot_\<A>\<V>" "well_formed_\<S>\<C>\<F>" "limit_app_to_alts"
  by unfold_locales auto

lemma fin_subset_with_elem:
  fixes 
    A :: "'a set" and
    a :: 'a and
    n :: nat
  assumes 
    inf: "infinite A" and
    elem: "a \<in> A" and
    n_pos: "n \<ge> 1"
  shows "\<exists>B \<subseteq> A. card B = n \<and> a \<in> B"
proof cases
    assume "n = 1"
    hence"{a} \<subseteq> A \<and> card {a} = n" using elem by simp
    thus ?thesis by blast
  next
    assume "\<not> n = 1"
    hence ge1: "n > 1" using n_pos by simp
    have "infinite (A - {a})" by (simp add: inf)
    hence "\<exists>B \<subseteq> (A - {a}). card B = n-1" using inf n_pos by (meson infinite_arbitrarily_large) 
    then obtain B where sub: "B \<subseteq> (A - {a}) \<and> card B = n-1" by blast
    hence "finite B" using ge1 by (simp add: card_ge_0_finite)
    moreover have "a \<notin> B" using sub by auto
    ultimately have car: "card (B \<union> {a}) = n" using ge1 by (simp add: sub)
    have "B \<union> {a} \<subseteq> A" using sub elem by auto
    thus ?thesis using car by blast
qed


sublocale committee_result \<subseteq> \<A>\<V>_committee:
  electoral_structure "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot" "committees"
  "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs" "ballot_\<A>\<V>" "\<lambda> A r. disjoint3 r" "limit_app_to_comm"
proof (unfold_locales, auto)
  fix 
    A C :: "'a set" and
    a :: 'a
  assume 
    sub: "C \<subseteq> A" and 
    committee: "k = card C" and 
    elem: "a \<in> A"
  show "\<exists>D \<subseteq> A. card D = card C \<and> a \<in> D"
  proof cases
    assume "finite A"
    hence "card C \<le> card A" using sub card_mono by blast
    hence "card A \<ge> k" using sub committee by simp
    hence "\<Union>(committees A) = A" using committees_cover_A by auto
    hence "\<exists>D \<in> committees A. a \<in> D" using elem by auto
    thus ?thesis using elem committee committees.simps 
        by (metis (mono_tags, lifting) mem_Collect_eq)
  next
    assume inf: "infinite A"
    hence "\<exists>D \<subseteq> A. card D = k \<and> a \<in> D" using elem fin_subset_with_elem k_positive by metis
    then obtain D where *: "D \<subseteq> A \<and> card D = k \<and> a \<in> D" by blast
    hence "D \<in> committees A" by simp
    thus ?thesis using elem committee committees.simps using "*" by auto
  qed
qed

end