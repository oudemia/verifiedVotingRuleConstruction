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
    contenders :: "'a set \<Rightarrow> 'r set" and
    well_formed_result :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool" and
    limit_contenders :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set" and
    affected_alts :: "'r set \<Rightarrow> 'a set"
  assumes "\<And> (A::('a set)) (r::('r Result)).
    (set_equals_partition (limit_contenders A UNIV) r \<and> disjoint3 r) \<Longrightarrow> well_formed_result A r" and
    "\<And> (A::('a set)) (r::('r set)). (affected_alts (limit_contenders A r)) \<subseteq> A" and
    "\<And> (A::('a set)). affected_alts (contenders A) = A \<or> contenders A = {}" and
    "\<And> (A :: 'a set)(B :: 'a set). A \<subseteq> B  \<Longrightarrow> (affected_alts (contenders A)) \<subseteq> (affected_alts (contenders B))"

text \<open>
  These three functions return the elect, reject, or defer set of a result.
\<close>

fun (in result) limit_res :: "'a set \<Rightarrow> 'r Result \<Rightarrow> 'r Result" where
  "limit_res A (e, r, d) = (limit_contenders A e, limit_contenders A r, limit_contenders A d)"

abbreviation elect_r :: "'r Result \<Rightarrow> 'r set" where
  "elect_r r \<equiv> fst r"

abbreviation reject_r :: "'r Result \<Rightarrow> 'r set" where
  "reject_r r \<equiv> fst (snd r)"

abbreviation defer_r :: "'r Result \<Rightarrow> 'r set" where
  "defer_r r \<equiv> snd (snd r)"


subsection \<open>Committee Results\<close>

text \<open>
  In a committee voting scenario, the well-formedness of results, i.e., committees, depends
  on an additional parameter k, the desired committee size.
\<close>

(* WHAT DIDN'T WORK:

locale committee_result = result + 
  fixes k :: "nat"
  assumes k_positive [simp] : "k \<ge> 1"
begin
...

...
assumes "\<And> (A:: 'a set) (e :: 'r set set) (r:: 'r set) (d:: 'r set).
    (well_formed_result A (e, r, d)) \<Longrightarrow> (\<forall> c. c \<in> e \<longrightarrow> (card c = k))"
 *)

type_synonym 'a Committee = "'a set"

locale committee_result =
  fixes k :: "nat"
  assumes k_positive : "k \<ge> 1" 
begin
fun committees :: "'a set \<Rightarrow> 'a Committee set" where
  "committees A = {C. C \<subseteq> A \<and> card C = k}"

lemma committees_cover_A: "k \<le> card A \<longrightarrow> \<Union>(committees A) = A "
proof standard
  fix A :: "'a set"
  assume *: "k \<le> card A"
  show "\<Union> (committees A) = A"
  proof safe
    fix
      C :: "'a set" and
      a :: 'a
    assume 
      elem:"a \<in> C" and
      comm: "C \<in> committees A"
    have "C \<subseteq> A" using comm by simp
    thus "a \<in> A" using elem by auto
  next
    fix
      a :: 'a
    assume 
      elem:"a \<in> A"
    have "card (A - {a}) \<ge> k-1" using elem * by force
    hence "\<exists>C \<subseteq> (A - {a}). card C = k-1" using * by (meson obtain_subset_with_card_n)
    then obtain C where comm: "C \<subseteq> (A - {a}) \<and> card C = k-1" by blast
    hence "a \<notin> C" by blast
    hence "card (C \<union> {a}) = k" using comm * k_positive
      by (metis One_nat_def Suc_pred Un_insert_right card.infinite card_insert_disjoint finite_Diff finite_subset less_eq_Suc_le not_one_le_zero sup_bot_right)
    hence "C \<union> {a} \<in> committees A" using elem comm * by auto
    thus "a \<in> \<Union>(committees A)" by blast
  qed
qed

fun well_formed_committee_result :: "'a set \<Rightarrow> ('a Committee) Result \<Rightarrow> bool" where
  "well_formed_committee_result A res = (disjoint3 res \<and> set_equals_partition (committees A) res)"

fun limit_committees :: "'a set \<Rightarrow> ('a Committee) set \<Rightarrow> ('a Committee) set" where
  "limit_committees A res = {C. (\<exists>r \<in> res. C = A \<inter> r) \<and> card C = k}"
end

fun affected_alts_committee :: "('a Committee) set  \<Rightarrow> 'a set" where
  "affected_alts_committee res = \<Union> res"

end