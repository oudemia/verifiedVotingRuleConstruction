(*  File:       Social_Choice_Result.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Social Choice Result\<close>

theory Social_Choice_Result
  imports Result
begin

subsection \<open>Social Choice Result\<close>

text \<open>
  A social choice result contains three sets of alternatives:
  elected, rejected, and deferred alternatives.
\<close>

fun well_formed_\<S>\<C>\<F> :: "'a set \<Rightarrow> 'a Result \<Rightarrow> bool" where
  "well_formed_\<S>\<C>\<F> A r = (disjoint3 r \<and> set_equals_partition A r)"

fun limit_alts :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit_alts A c = A \<inter> c"

fun affected_alts_\<S>\<C>\<F> :: "'a set  \<Rightarrow> 'a set" where
  "affected_alts_\<S>\<C>\<F> c = c"

subsection \<open>Auxiliary Lemmas\<close>

lemma defer_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed_\<S>\<C>\<F> A r"
  shows "defer_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> defer_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have
    "\<forall> p. \<exists> e r d. set_equals_partition A p \<longrightarrow> (e, r, d) = p \<and> e \<union> r \<union> d = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI snd_conv
    by metis
qed

lemma elect_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed_\<S>\<C>\<F> A r"
  shows "elect_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> elect_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have
    "\<forall> p. \<exists> e r d. set_equals_partition A p \<longrightarrow> (e, r, d) = p \<and> e \<union> r \<union> d = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI assms fst_conv
    by metis
qed

lemma reject_subset:
  fixes
    A :: "'a set" and
    r :: "'a Result"
  assumes "well_formed_\<S>\<C>\<F> A r"
  shows "reject_r r \<subseteq> A"
proof (safe)
  fix a :: "'a"
  assume "a \<in> reject_r r"
  moreover obtain
    f :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a set" and
    g :: "'a Result \<Rightarrow> 'a set \<Rightarrow> 'a Result" where
    "A = f r A \<and> r = g r A \<and> disjoint3 (g r A) \<and> set_equals_partition (f r A) (g r A)"
    using assms
    by simp
  moreover have
    "\<forall> p. \<exists> e r d. set_equals_partition A p \<longrightarrow> (e, r, d) = p \<and> e \<union> r \<union> d = A"
    by simp
  ultimately show "a \<in> A"
    using UnCI assms fst_conv snd_conv disjoint3.cases
    by metis
qed

end