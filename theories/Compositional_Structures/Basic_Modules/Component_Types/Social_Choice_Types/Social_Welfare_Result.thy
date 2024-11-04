(*  File:       Social_Welfare_Result.thy
    Copyright   2024  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Alicia Appelhagen, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Social Welfare Result\<close>

theory Social_Welfare_Result
  imports Result
          Preference_Relation
begin

subsection \<open>Social Welfare Result\<close>

text \<open>
  A social welfare result contains three sets of relations:
  elected, rejected, and deferred
  A well-formed social welfare result consists only of linear
  orders on the alternatives.
\<close>

fun well_formed_\<S>\<W>\<F> :: "'a set \<Rightarrow> ('a Preference_Relation) Result \<Rightarrow> bool" where
  "well_formed_\<S>\<W>\<F> A res = (disjoint3 res \<and>
                                  set_equals_partition {r. linear_order_on A r} res)"

fun limit_set_\<S>\<W>\<F> ::
  "'a set \<Rightarrow> ('a Preference_Relation) set \<Rightarrow> ('a Preference_Relation) set" where
  "limit_set_\<S>\<W>\<F> A res = {limit A r | r. r \<in> res \<and> linear_order_on A (limit A r)}"

fun affected_alts_\<S>\<W>\<F> :: "('a Preference_Relation) set \<Rightarrow> 'a set" where
  "affected_alts_\<S>\<W>\<F> res = \<Union> ((\<lambda>r. Domain r \<union> Range r) `res)"

  
lemma res_surj_\<S>\<W>\<F>:
  fixes A :: "'a set"
  shows "affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV) = A"
proof (standard)
  show "affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV) \<subseteq> A"
  proof
    fix a :: 'a
    assume "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)"
    hence "\<exists>r. r \<in> (limit_set_\<S>\<W>\<F> A UNIV) \<and> (a \<in> Domain r \<or> a \<in> Range r)" by simp
    then obtain r where *: " r \<in> (limit_set_\<S>\<W>\<F> A UNIV) \<and> (a \<in> Domain r \<or> a \<in> Range r)" by blast
    hence "r \<subseteq> A \<times> A"
      using linear_order_on_def partial_order_onD(1) refl_onD1 refl_onD2 by fastforce
    thus "a \<in> A" using "*" by blast
  qed
  next
  show "A \<subseteq> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)"
  proof (standard)
    fix a :: 'a
    assume elem: "a \<in> A"
    have "\<exists>r. linear_order_on A r"  using well_order_on well_order_on_def by blast
    then obtain r where ord: "linear_order_on A r" by blast
    hence "limit A r = r" using rel_extend_supset by fastforce
    hence "r \<in> limit_set_\<S>\<W>\<F> A UNIV" using ord by fastforce
    hence sub: "Domain r \<subseteq> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)" by auto
    have "refl_on A r" using ord by (simp add: linear_order_on_def partial_order_onD(1))
    hence "(a, a) \<in> r" by (simp add: local.elem refl_on_def')
    hence "a \<in> Domain r" by auto
    thus "a \<in> affected_alts_\<S>\<W>\<F> (limit_set_\<S>\<W>\<F> A UNIV)" using sub by blast
  qed
qed

end