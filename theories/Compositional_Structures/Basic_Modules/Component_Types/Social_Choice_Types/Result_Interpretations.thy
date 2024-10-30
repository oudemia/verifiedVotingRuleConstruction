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
  result "\<lambda> A. A" "well_formed_\<S>\<C>\<F>" "limit_alts" "affected_alts_\<S>\<C>\<F>"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    e :: "'a set" and
    r :: "'a set" and
    d :: "'a set"
  assume
    "set_equals_partition A (e, r, d)" and
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
next
  fix A :: "'a set" and a :: 'a
  assume "a \<in> affected_alts_\<S>\<C>\<F> A"
  thus "a \<in> A" by simp
next
  fix A :: "'a set" and a :: 'a
  assume "a \<in> A"
  thus "a \<in> affected_alts_\<S>\<C>\<F> A" by simp
next
  fix 
    A B:: "'a set" and 
    a :: 'a
  assume 
    sub: "A \<subseteq> B" and 
    cont: "a \<in> affected_alts_\<S>\<C>\<F> A"
  show "a \<in> affected_alts_\<S>\<C>\<F> B" using sub cont by auto
qed

text \<open>
  Results from multi-winner functions, for the purpose of composability and
  modularity given as three sets of (potentially tied) sets of alternatives.
  \<open>[[Not actually used yet.]]\<close>
\<close>
global_interpretation multi_winner_result:
  result "\<lambda> A. Pow A" "\<lambda> A r. set_equals_partition (Pow A) r \<and> disjoint3 r"
          "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs"
proof (unfold_locales, safe)
  fix
    A X :: "'a set" and
    a :: 'a
  assume "a \<in> X" and "X \<subseteq> A"
  thus "a \<in> A" by blast
next
  fix
    A :: "'a set" and
    a :: 'a
  assume "a \<in> A"
  thus "a \<in> \<Union> (Pow A)" by blast
next
  fix
    A B C :: "'a set" and
    a :: 'a
  assume "A \<subseteq> B" and "C \<subseteq> A" and  "a \<in> C"
  thus "a \<in>  \<Union> (Pow B)" by blast
qed

text \<open>
  Results from social welfare functions (\<open>\<S>\<W>\<F>s\<close>), for the purpose of composability and
  modularity given as three sets of (potentially tied) linear orders over the alternatives. See
  \<^file>\<open>Social_Welfare_Result.thy\<close> for details.
\<close>

global_interpretation \<S>\<W>\<F>_result:
  result "\<lambda>A. limit_set_\<S>\<W>\<F> A UNIV" "well_formed_\<S>\<W>\<F>" "limit_set_\<S>\<W>\<F>" "affected_alts_\<S>\<W>\<F>"
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
next
  fix
    A :: "'a set" and
    a :: "'a"
  assume
    "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)" 
  thus "a \<in> A"
    by auto
next
  fix
    A :: "'a set" and
    a :: "'a"
  assume elem: "a \<in> A"
  show "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)"
  using elem by (metis res_surj_\<S>\<W>\<F>)
next
 fix
    A B :: "'a set" and
    a :: 'a
  assume 
    sub: "A \<subseteq> B" and 
    elem: "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)"
  show "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> B UNIV)"
  proof -
    have "a \<in> A" using elem by (metis res_surj_\<S>\<W>\<F>)
    hence "a \<in> B" using sub by blast
    thus "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> B UNIV)" by (metis res_surj_\<S>\<W>\<F>)
  qed
qed



text \<open>
  Results in a committee voting context depend on the concrete value of the parameter k.
  This means that interpretation is not possible in the general, but depends on the 
  condition of k having a specific value. This can be done with the sublocale command. 
\<close>
   
sublocale committee_result \<subseteq> 
result "committees" "well_formed_committee_result" "limit_committees" "affected_alts_committee"
proof (unfold_locales, safe)
  fix
    A :: "'a set" and
    r :: "('a Committee) Result"
  assume 
    partition: "set_equals_partition (committees A) r" and
    disjoint: "disjoint3 r"
  thus "well_formed_committee_result A r" using partition disjoint by auto
next
   fix
    A :: "'a set" and
    C :: "('a Committee) set" and
    a :: 'a
  assume 
    elem: "a \<in> affected_alts_committee (limit_committees A C)"
  thus "a \<in> A" by auto
next
   fix
    A :: "'a set" and
    a :: 'a
  assume 
    elem: "a \<in> affected_alts_committee (committees A)"
  thus "a \<in> A" by auto
next
  fix
    A :: "'a set" and
    a b :: 'a
  assume 
    nonemp: "b \<in> affected_alts_committee (committees A)" and
    n: "b \<notin> {}" and
    elem: "a \<in> A"
  show "a \<in> affected_alts_committee (committees A)"
    proof cases
      assume fin: "finite A"
      have "affected_alts_committee (committees A) \<noteq> {}" using nonemp by blast
      hence "\<exists>C. C \<in> committees A \<and> C \<noteq> {}" by auto
      hence "committees A \<noteq> {}" by auto
      hence "\<exists>C. C \<subseteq> A \<and> card C = k" by simp
      hence large_A: "card A \<ge> k" using k_positive fin using card_mono by blast
      hence "c \<in> A \<longrightarrow> (\<exists>C.  C \<in> committees A \<and> c \<in> C)" using committees_cover_A by auto
      hence "\<exists>C. C \<in> committees A \<and> a \<in> C" 
        using large_A elem by (metis Union_iff committees_cover_A)
      thus "a \<in> affected_alts_committee (committees A)" by simp
    next
      assume inf: "infinite A"
      hence "\<exists>D \<subseteq> A. card D = k \<and> a \<in> D" using elem by (meson fin_subset_with_elem k_positive)
      then obtain D where *: "D \<subseteq> A \<and> card D = k \<and> a \<in> D" by blast
      hence "D \<in> committees A" by simp
      thus "a \<in> affected_alts_committee (committees A)" using "*" by auto
    qed
next
  fix
    A B :: "'a set" and
    a :: 'a
  assume 
    elem: "a \<in> affected_alts_committee (committees A)" and
    sub: "A \<subseteq> B"
  have "affected_alts_committee (committees A) \<subseteq> affected_alts_committee (committees B)" 
    using sub by (metis affected_alts_committee.simps subset_committees)
  thus "a \<in> affected_alts_committee (committees B)" using elem by blast
qed

setup Locale_Code.close_block

end