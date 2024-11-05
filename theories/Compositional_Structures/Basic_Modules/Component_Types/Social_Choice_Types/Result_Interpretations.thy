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
  result "\<lambda> A. A" "limit_alts" "affected_alts_\<S>\<C>\<F>"
proof (unfold_locales, standard; simp)
qed

text \<open>
  Results from multi-winner functions, for the purpose of composability and
  modularity given as three sets of (potentially tied) sets of alternatives.
  \<open>[[Not actually used yet.]]\<close>
\<close>
global_interpretation multi_winner_result:
  result "\<lambda> A. Pow A" "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" "\<lambda> rs. \<Union> rs"
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
    A C :: "'a set" and
    a :: 'a
  assume "\<Union> (Pow A) = {}" and "a \<in> A" and "C \<subseteq> A"
  thus "C \<in> {}" by auto  
next
  fix
    A :: "'a set" and
    C D :: "'a set set" and
    a :: 'a
  assume "C \<subseteq> D" and "A \<in> C" and  "a \<in> A"
  thus "a \<in> \<Union> D" by blast
next
  fix
    A B C:: "'a set" and
    a:: 'a
  assume "A \<subseteq> B" and "C \<subseteq> A" and  "a \<in> C"
  thus "a \<in> B" by blast
qed

text \<open>
  Results from social welfare functions (\<open>\<S>\<W>\<F>s\<close>), for the purpose of composability and
  modularity given as three sets of (potentially tied) linear orders over the alternatives. See
  \<^file>\<open>Social_Welfare_Result.thy\<close> for details.
\<close>

global_interpretation \<S>\<W>\<F>_result:
  result "\<lambda>A. limit_set_\<S>\<W>\<F> A UNIV" "limit_set_\<S>\<W>\<F>" "affected_alts_\<S>\<W>\<F>"
proof (unfold_locales, safe)
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
    assm: "a \<in> A"
    have "limit_set_\<S>\<W>\<F> A UNIV = { r. linear_order_on A r}"
      using rel_extend_supset 
      by fastforce
    moreover have "\<forall>r. linear_order_on A r \<longrightarrow> a \<in> Domain r \<or> a \<in> Range r" 
      using assm
      by (meson Range_iff connex_imp_refl lin_ord_imp_connex refl_on_def')
    ultimately show "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)"
      using assm
      by (metis res_surj_\<S>\<W>\<F>)
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
next
  fix
    A :: "'a set" and
    a :: 'a and
    r :: "'a Preference_Relation"
  assume 
    "affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV) = {}" and 
    "a \<in> A" and
    "r \<in> limit_set_\<S>\<W>\<F> A UNIV"
  thus "r \<in> {}"
    by (metis empty_iff res_surj_\<S>\<W>\<F>)
qed



text \<open>
  Results in a committee voting context depend on the concrete value of the parameter k.
  This means that interpretation is not possible in the general, but depends on the 
  condition of k having a specific value. This can be done with the sublocale command. 
\<close>
   
sublocale committee_result \<subseteq> 
result "committees" "limit_committees" "affected_alts_committee"
proof (unfold_locales, safe)
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
next
  fix
    A :: "'a set" and
    a :: 'a and
    C :: "'a Committee"
  assume 
    no_conts: "affected_alts_committee (committees A) = {}" and
    elem: "a \<in> A" and 
    comm: "C \<in> committees A"
  have "\<Union> (committees A) = {}" 
    using no_conts 
    by simp
  moreover have "\<forall>D \<in> committees A. card D \<ge> 1" 
    using k_positive
    by simp
  ultimately have "committees A = {}" by auto
  thus "C \<in> {}" 
    using comm 
    by auto
qed

setup Locale_Code.close_block

end