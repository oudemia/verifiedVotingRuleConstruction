(*  File:       Result.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Result\<close>

theory Result
  imports Main
          Profile
begin

text \<open>
  An electoral result is the principal result type of the composable modules
  voting framework, as it is a generalization of the set of winning
  alternatives from social choice functions. Electoral results are selections
  of the received (possibly empty) set of alternatives into the three disjoint
  groups of elected, rejected and deferred alternatives.
  Any of those sets, e.g., the set of winning (elected) alternatives, may also
  be left empty, as long as they collectively still hold all the received
  alternatives.
\<close>

subsection \<open>Auxiliary Functions\<close>

type_synonym 'r Result = "'r set * 'r set * 'r set"

text \<open>
  A partition of a set A are pairwise disjoint sets that "set equals
  partition" A. For this specific predicate, we have three disjoint sets
  in a three-tuple.
\<close>

fun disjoint3 :: "'r Result \<Rightarrow> bool" where
  "disjoint3 (e, r, d) =
    ((e \<inter> r = {}) \<and>
      (e \<inter> d = {}) \<and>
      (r \<inter> d = {}))"

fun set_equals_partition :: "'r set \<Rightarrow>'r Result \<Rightarrow> bool" where
  "set_equals_partition X (r1, r2, r3) = (r1 \<union> r2 \<union> r3 = X)"

subsection \<open>Definition\<close>

text \<open>
  A result generally is related to the alternative set A (of type 'a).
  A result should be well-formed on the alternatives.
  Also it should be possible to limit a well-formed result to a subset of the alternatives.

  Specific result types like social choice results (sets of alternatives) can be realized
  via sublocales of the result locale.
\<close>

locale result =
  fixes well_formed :: "'a set \<Rightarrow> ('r Result) \<Rightarrow> bool"
    and limit_set :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set"
  assumes "\<And> A r. (set_equals_partition (limit_set A UNIV) r \<and> disjoint3 r)
            \<Longrightarrow> well_formed A r"

(* and "\<And> A B r1 r2 r3. A \<subseteq> B \<Longrightarrow> well_formed B (r1, r2, r3)
            \<Longrightarrow> well_formed A ((limit_set A r1), (limit_set A r2), (limit_set A r3))" *)

text \<open>
  These three functions return the elect, reject, or defer set of a result.
\<close>

fun (in result) limit_res :: "'a set \<Rightarrow> 'r Result \<Rightarrow> 'r Result" where
  "limit_res A (e, r, d) = (limit_set A e, limit_set A r, limit_set A d)"

abbreviation elect_r :: "'r Result \<Rightarrow> 'r set" where
  "elect_r r \<equiv> fst r"

abbreviation reject_r :: "'r Result \<Rightarrow> 'r set" where
  "reject_r r \<equiv> fst (snd r)"

abbreviation defer_r :: "'r Result \<Rightarrow> 'r set" where
  "defer_r r \<equiv> snd (snd r)"

end