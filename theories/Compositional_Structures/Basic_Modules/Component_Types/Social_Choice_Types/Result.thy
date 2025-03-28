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

text \<open>
  Contenders are of the same type as election results and represent possible or incomplete
  results that are part of the computation of a final result.
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

  
fun rename_result :: "('r \<Rightarrow> 'r) \<Rightarrow> 'r Result \<Rightarrow> 'r Result" where
"rename_result \<pi> (e, r, d) = (\<pi> ` e, \<pi> ` r, \<pi> ` d)"

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
    limit_contenders :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set" and
    affected_alts :: "'r set \<Rightarrow> 'a set"
  assumes 
    conts_cover: "affected_alts (contenders A) = A \<or> affected_alts (contenders A) = {}" and
    no_conts: "A \<noteq> {} \<and> affected_alts (contenders A) = {} \<longrightarrow> contenders A = {}" and
    sub_coincide: "C \<subseteq> D \<longrightarrow> (affected_alts C) \<subseteq> (affected_alts D)" and
    limit_is_superset: "affected_alts (limit_contenders A R) \<subseteq> A" and
(* Does not hold for social welfare: *)
    limit_conts_sound: "A \<subseteq> B \<longrightarrow> (contenders A) = limit_contenders A (contenders B)" 
begin

fun limit_res :: "'a set \<Rightarrow> 'r Result \<Rightarrow> 'r Result" where
  "limit_res A (e, r, d) = (limit_contenders A e, limit_contenders A r, limit_contenders A d)"

fun well_formed_result :: "'r set \<Rightarrow> 'r Result \<Rightarrow> bool" where  
  "well_formed_result R r = (set_equals_partition R r \<and> disjoint3 r)"


lemma bij_preserves_result:
  fixes \<pi> :: "'r \<Rightarrow> 'r" and R :: "'r set" and e r d :: "'r set"
  assumes bij: "bij \<pi>" and wf: "well_formed_result R (e, r, d)"
  shows "well_formed_result (\<pi> ` R) (rename_result \<pi> (e, r, d))"
proof (unfold well_formed_result.simps, safe)
  show "set_equals_partition (\<pi> ` R) (rename_result \<pi> (e, r, d))"
    using assms 
    by auto
next
  have "disjoint3 (e, r, d)" using wf by simp
  hence 
    "\<pi> ` e \<inter> \<pi> ` r = {}" and 
    "\<pi> ` e \<inter> \<pi> ` d = {}" and
    "\<pi> ` r \<inter> \<pi> ` d = {}"
    using bij bij_betw_imp_inj_on disjoint3.simps image_Int image_empty
    by (metis, metis, metis)
  thus "disjoint3 (rename_result \<pi> (e, r, d))" by simp
qed

end
text \<open>
  These three functions return the elect, reject, or defer set of a result.
\<close>

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


type_synonym 'a Committee = "'a set"

locale committee_result =
  fixes k :: "nat"
  assumes k_positive : "k \<ge> 1" 
begin
fun committees :: "'a set \<Rightarrow> 'a Committee set" where
  "committees A = {C. C \<subseteq> A \<and> card C = k}"

fun well_formed_committee_result :: "'a set \<Rightarrow> ('a Committee) Result \<Rightarrow> bool" where
  "well_formed_committee_result A res = (disjoint3 res \<and> set_equals_partition (committees A) res)"

fun limit_committees :: "'a set \<Rightarrow> ('a Committee) set \<Rightarrow> ('a Committee) set" where
  "limit_committees A res = {C. (\<exists>r \<in> res. C = A \<inter> r) \<and> card C = k}"

lemma committees_cover_A:
fixes A :: "'a set"
assumes geq_k: "k \<le> card A"
shows "\<Union>(committees A) = A "
proof (safe)
fix
  C :: "'a set" and
  a :: 'a
assume 
  elem:"a \<in> C" and
  comm: "C \<in> committees A"
have "C \<subseteq> A" using comm by simp
thus "a \<in> A" using elem by auto
next
fix a :: 'a
assume elem:"a \<in> A"
have "card (A - {a}) \<ge> k-1"
  using elem geq_k
  by force
hence "\<exists>C \<subseteq> (A - {a}). card C = k-1" 
  using geq_k obtain_subset_with_card_n 
  by metis
then obtain C where comm: "C \<subseteq> (A - {a}) \<and> card C = k-1" by blast
hence "a \<notin> C" by blast
moreover have "finite C" 
  using comm One_nat_def card.infinite finite_Diff finite_subset geq_k k_positive not_less_eq_eq
  by metis
ultimately have "card (insert a C) = k" 
  using comm geq_k k_positive
  by simp
hence "insert a C \<in> committees A" 
  using elem comm geq_k 
  by auto
thus "a \<in> \<Union>(committees A)" by blast
qed

  
lemma no_committees_possible:
fixes A :: "'a set"
assumes 
fin: "finite A" and 
*: "k > card A"
shows "committees A = {}"
using "*" card_mono fin leD by auto

lemma all_committees:
  fixes A :: "'a set"
  shows "committees A = limit_committees A UNIV"
proof (standard)
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

lemma subset_committees:
  fixes A B :: "'a set"
  assumes sub: "A \<subseteq> B"
  shows "\<Union> (committees A) \<subseteq> \<Union> (committees B)"
proof (standard)
  fix a :: 'a
  assume elem: "a \<in> \<Union> (committees A)"
   hence "\<exists>C. C \<in> committees A \<and> a \<in> C" by simp
   then obtain C where *:  "C \<in> committees A \<and> a \<in> C" by blast
   hence "C \<in> committees B" using sub by auto
   thus "a \<in> \<Union> (committees B)" using "*" by blast
qed
  
end

fun affected_alts_committee :: "('a Committee) set  \<Rightarrow> 'a set" where
  "affected_alts_committee res = \<Union> res"
  
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


subsection \<open>Auxiliary Lemmas\<close>

context result 
begin

lemma result_imp_rej:
  fixes R e r d:: "'r set"
  assumes "well_formed_result R (e, r, d)"
  shows "R - (e \<union> d) = r"
proof (safe)
  fix r' :: "'r"
  assume
    "r' \<in> R" and
    "r' \<notin> r" and
    "r' \<notin> d"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = R)"
    using assms
    by simp
  ultimately show "r' \<in> e"
    by blast
next
  fix r' :: "'r"
  assume "r' \<in> r"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = R)"
    using assms
    by simp
  ultimately show "r' \<in> R"
    by blast
next
  fix r' :: "'r"
  assume
    "r' \<in> r" and
    "r' \<in> e"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = R)"
    using assms
    by simp
  ultimately show False
    by auto
next
  fix r' :: "'r"
  assume
    "r' \<in> r" and
    "r' \<in> d"
  moreover have
    "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {}) \<and> (e \<union> r \<union> d = R)"
    using assms
    by simp
  ultimately show False
    by blast
qed

lemma result_count:
  fixes R e r d:: "'r set"
  assumes 
    wf_result: "well_formed_result R (e, r, d)" and
    fin_R: "finite R"
  shows "card R = card e + card r + card d"
proof -
  have "e \<union> r \<union> d = R"
    using wf_result
    by simp
  moreover have "(e \<inter> r = {}) \<and> (e \<inter> d = {}) \<and> (r \<inter> d = {})"
    using wf_result
    by simp
  ultimately show ?thesis
    using fin_R Int_Un_distrib2 finite_Un card_Un_disjoint sup_bot.right_neutral
    by metis
qed  
    
end
    
end