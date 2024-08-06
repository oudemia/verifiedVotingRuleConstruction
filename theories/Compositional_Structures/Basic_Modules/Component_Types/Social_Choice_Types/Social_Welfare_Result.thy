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
  "affected_alts_\<S>\<W>\<F> res =  \<Union> ((\<lambda>r. {a. \<exists> b. (a, b) \<in> r \<or> (b, a) \<in> r}) `res)"

end