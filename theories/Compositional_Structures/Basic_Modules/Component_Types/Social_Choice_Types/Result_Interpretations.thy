(*  File:       Result_Interpretations.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Specific Electoral Result Types\<close>

theory Result_Interpretations
  imports Social_Choice_Result
          Social_Welfare_Result
          Collections.Locale_Code
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale-Code block
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale-Code block as well.
\<close>

setup Locale_Code.open_block

text \<open>
  Results from social choice functions (\<open>\<S>\<C>\<F>s\<close>), for the purpose of composability and
  modularity given as three sets of (potentially tied) alternatives. See
  \<^file>\<open>Social_Choice_Result.thy\<close> for details.
\<close>
global_interpretation \<S>\<C>\<F>_result:
  result "well_formed_\<S>\<C>\<F>" "limit_alts" "affected_alts_\<S>\<C>\<F>"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assume
    "set_equals_partition (limit_alts A UNIV) (e, r, d)" and
    "disjoint3 (e, r, d)"
  thus "well_formed_\<S>\<C>\<F> A (e, r, d)"
    by simp
next
  fix
    A :: "'a set" and
    a :: "'a" and
    R :: "'a set"
  assume
    "a \<in> affected_alts_\<S>\<C>\<F> (limit_alts A R)" 
  thus "a \<in> A"
    by simp
qed

text \<open>
  Results from multi-winner functions, for the purpose of composability and
  modularity given as three sets of (potentially tied) sets of alternatives.
  \<open>[[Not actually used yet.]]\<close>
\<close>
global_interpretation multi_winner_result:
  result "\<lambda> A r. set_equals_partition (Pow A) r \<and> disjoint3 r"
          "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs"
proof (unfold_locales, safe)
  fix
    A :: "'b set" and
    e :: "'b set set" and
    r :: "'b set set" and
    d :: "'b set set"
  assume "set_equals_partition {r \<inter> A |r. r \<in> UNIV} (e, r, d)"
  thus "set_equals_partition (Pow A) (e, r, d)"
    by force
qed

text \<open>
  Results from social welfare functions (\<open>\<S>\<W>\<F>s\<close>), for the purpose of composability and
  modularity given as three sets of (potentially tied) linear orders over the alternatives. See
  \<^file>\<open>Social_Welfare_Result.thy\<close> for details.
\<close>
global_interpretation \<S>\<W>\<F>_result:
  result "well_formed_\<S>\<W>\<F>" "limit_set_\<S>\<W>\<F>" "affected_alts_\<S>\<W>\<F>"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    e :: "('a Preference_Relation) set" and
    r :: "('a Preference_Relation) set" and
    d :: "('a Preference_Relation) set"
  assume
    "set_equals_partition (limit_set_\<S>\<W>\<F> A UNIV) (e, r, d)" and
    "disjoint3 (e, r, d)"
  moreover have
    "limit_set_\<S>\<W>\<F> A UNIV = {limit A r' | r'. linear_order_on A (limit A r')}"
    by simp
  moreover have "\<dots> = {r'. linear_order_on A r'}"
  proof (safe)
    fix r' :: "'a Preference_Relation"
    assume lin_ord: "linear_order_on A r'"
    hence "\<forall> (a, b) \<in> r'. (a, b) \<in> limit A r'"
      unfolding linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      by force
    hence "r' = limit A r'"
      by force
    thus "\<exists> x. r' = limit A x \<and> linear_order_on A (limit A x)"
      using lin_ord
      by metis
  qed
  ultimately show "well_formed_\<S>\<W>\<F> A (e, r, d)"
    by simp
next
  fix
    A :: "'a set" and
    a :: "'a" and
    R :: "('a Preference_Relation) set"
  assume
    "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A R)" 
  thus "a \<in> A"
  by auto
qed


text \<open>
  Results in a committee voting context depend on the concrete value of the parameter k.
  This means that interpretation is not possible in the general, but depends on the 
  condition of k having a specific value. This can be done with the sublocale command. 
\<close>

sublocale committee_result \<subseteq> 
result "well_formed_committee_result" "limit_committees" "affected_alts_committee"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    e :: "'a Committee set" and
    r :: "'a Committee set" and
    d :: "'a Committee set"
  assume partition: "set_equals_partition (limit_committees A UNIV) (e, r, d)" and
    disjoint: "disjoint3 (e, r, d)"
  moreover have comm_eq: "committees A = limit_committees A UNIV"
  proof (unfold_locales, cases)
    assume no_committees: "committees A = {}"
    have "k \<ge> 1" using k_positive by simp
    moreover have "\<forall> C \<subseteq> A. card C \<noteq> k" using no_committees by auto
    moreover have le_k: "\<forall> C \<subseteq> A. card C < k" by (meson calculation(2) not_less obtain_subset_with_card_n subset_iff)
    have "A \<subseteq> A" by simp
    hence A_le_k: "card A < k" using le_k by simp
    hence "\<forall> C::('a Committee). card (C \<inter> A) < k" using le_k by simp
    hence "limit_committees A UNIV = {}" using calculation(2) by auto
    thus "committees A = limit_committees A UNIV" using no_committees by auto
  next
    assume "committees A \<noteq> {}"
    show "committees A = limit_committees A UNIV"
    proof
      show "committees A \<subseteq> limit_committees A UNIV"
        proof
          fix C :: "'a Committee"
          assume comm_C: "C \<in> committees A"
          hence card_k: "card C = k"  by auto
          moreover have "C = A \<inter> C" using comm_C by auto
          hence "\<exists>R \<in> UNIV. C = A \<inter> R"  by auto
          thus "C \<in> limit_committees A UNIV" using card_k by simp
        qed
    next
      show "(limit_committees A UNIV) \<subseteq> committees A"
      proof
        fix C :: "'a Committee"
        assume limit_C: "C \<in> limit_committees A UNIV"
        hence card_k: "card C = k"  by auto
        moreover have "\<exists>R \<in> UNIV. C = A \<inter> R" using limit_C by auto
        hence "C \<subseteq> A" by auto
        thus "C \<in> committees A" using card_k by simp
      qed
    qed
  qed
  thus "well_formed_committee_result A (e, r, d)" using partition disjoint by auto
next
 fix
    A :: "'a set" and
    R :: "'a Committee set" and
    a :: "'a"
  assume affected: "a \<in> affected_alts_committee (limit_committees A R)"
  thus "a \<in> A" by auto
qed

setup Locale_Code.close_block

end