(*  File:       Result.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Result\<close>

theory Result
  imports Main
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
  "set_equals_partition X (e, r, d) = (e \<union> r \<union> d = X)"

subsection \<open>Definition\<close>

text \<open>
  A result generally is related to the alternative set A (of type 'a).
  A result should be well-formed on the alternatives.
  Also it should be possible to limit a well-formed result to a subset of the alternatives.

  Specific result types like social choice results (sets of alternatives) can be realized
  via sublocales of the result locale.
\<close>

locale result =
  fixes
    well_formed_result :: "'a set \<Rightarrow> ('r Result) \<Rightarrow> bool" and
    limit_set :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set" and
    affected_alts :: "'r set \<Rightarrow> 'a set"
  assumes "\<And> (A::('a set)) (r::('r Result)).
    (set_equals_partition (limit_set A UNIV) r \<and> disjoint3 r) \<Longrightarrow> well_formed_result A r" and
    "\<And> (A::('a set)) (r::('r set)). (affected_alts (limit_set A r)) \<subseteq> A"


type_synonym 'a Committee = "'a set"

(* 
  TODO: This is a WIP. Fixing the parameter k is not what we want
  to do in the end, as k is... well, not fixed.
  Idea 1: 
    Handle committee results as multi-winner results, add
    validity checking function that receives parameter k
*) 
locale committee_result = result + 
  fixes k :: "nat" 
  assumes "\<And> (A:: ('a set)) (e :: ('a set set)) (d :: ('a set set)) (r :: ('a set set)). 
    well_formed_result A (e, d, r) \<Longrightarrow>( \<forall> a \<in> e \<union> d \<union> r . card a = k)"

(* Idea 2:    
text \<open>
  Results from committee functions, given as three sets of (potentially tied) sets
 committees. Committees are sets of alternatives with fixed cardinality k.
\<close>

fun committee_res :: "'a set \<Rightarrow> ('a set Result) \<Rightarrow> nat \<Rightarrow> bool" where
"committee_res A r k =
      ( set_equals_partition {A' \<in> Pow(A). card A' = k} r 
      \<and> disjoint3 r 
      \<and> card (elect_r r) = k \<and> card (reject_r r) = k \<and> card (defer_r r) = k)"

(*
fun committee_res :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a set Result) \<Rightarrow> bool" where
"committee_res k A r =
      ( set_equals_partition {A' \<in> Pow(A). card A' = k} r 
      \<and> disjoint3 r 
      \<and> card (elect_r r) = k \<and> card (reject_r r) = k \<and> card (defer_r r) = k)"
      
global_interpretation committee_result:
  result "(committee_res)" "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}"

proof (unfold_locales, safe)
  fix
    A :: "'b set" and
    e :: "'b set set" and
    r :: "'b set set" and
    d :: "'b set set"
  assume "set_equals_partition {r \<inter> A |r. r \<in> UNIV} (e, r, d)"
  thus "set_equals_partition {A' \<in> Pow(A). card A' = k} (e, r, d)"
    by force
qed
*)
*)

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