(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Module\<close>

theory Choice_Module
imports 
  "Social_Choice_Types/Property_Interpretations" 
  "Social_Choice_Types/Electoral_Structure"
  Choice_Schema
begin

(* 
  This is a WIP and part of the switch from electoral modules on alternatives to 
  electoral modules on choices (which are of the result type)
*)

text \<open>
  Electoral modules are the principal component type of the composable
  modules voting framework, as they are a generalization of voting rules in
  the sense of social choice functions.
  These are only the types used for electoral modules. Further restrictions
  are encompassed by the electoral-module predicate.

  An electoral module does not need to make final decisions for all
  alternatives, but can instead defer the decision for some or all of them
  to other modules. Hence, electoral modules partition the received
  (possibly empty) set of alternatives into elected, rejected and deferred
  alternatives.
  In particular, any of those sets, e.g., the set of winning (elected)
  alternatives, may also be left empty, as long as they collectively still
  hold all the received alternatives. Just like a voting rule, an electoral
  module also receives a profile which holds the voters’ preferences, which,
  unlike a voting rule, consider only the (sub-)set of alternatives that
  the module receives.
\<close>

subsection \<open>Definition\<close>

text \<open>
  An electoral module maps an election to a result.
  To enable currying, the Election type is not used here because that would require tuples.
\<close>

type_synonym ('v, 'r, 'i) Electoral_Module = "'v set \<Rightarrow> 'r set
                                              \<Rightarrow> ('v, 'r, 'i) Choice_Schema \<Rightarrow> 'r Result"

fun fun\<^sub>\<E> :: "('v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r)
                  \<Rightarrow> (('a, 'v, 'b) Election \<Rightarrow> 'r)" where
  "fun\<^sub>\<E> m = (\<lambda> E. m (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E))"

text \<open>
  The next three functions take an electoral module and turn it into a
  function only outputting the elect, reject, or defer set respectively.
\<close>

abbreviation elect :: " ('v, 'r, 'i) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'r set
        \<Rightarrow> ('v, 'r, 'i) Choice_Schema \<Rightarrow> 'r set" where
  "elect m V R p \<equiv> elect_r (m V R p)"

abbreviation reject :: " ('v, 'r, 'i) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'r set
        \<Rightarrow> ('v, 'r, 'i) Choice_Schema \<Rightarrow> 'r set" where
  "reject m V A p \<equiv> reject_r (m V A p)"

abbreviation "defer" :: " ('v, 'r, 'i) Electoral_Module \<Rightarrow> 'v set \<Rightarrow> 'r set
        \<Rightarrow> ('v, 'r, 'i) Choice_Schema \<Rightarrow> 'r set" where
  "defer m V A p \<equiv> defer_r (m V A p)"

subsection \<open>Auxiliary Definitions\<close>

text \<open>
  Electoral modules partition a given set of alternatives A into a set of
  elected alternatives e, a set of rejected alternatives r, and a set of
  deferred alternatives d, using a profile.
  e, r, and d partition A.
  Electoral modules can be used as voting rules. They can also be composed
  in multiple structures to create more complex electoral modules.
\<close>

subsection \<open>Properties\<close>

text \<open>
  We only require voting rules to behave a specific way on admissible elections,
  i.e., elections that are valid profiles (= votes are linear orders on the alternatives).
  Note that we do not assume finiteness of voter or alternative sets by default.
\<close>

subsubsection \<open>Anonymity\<close>

text \<open>
  An electoral module is anonymous iff the result is invariant under renamings of voters,
  i.e., any permutation of the voter set that does not change the preferences leads to an
  identical result.
\<close>

(* definition (in electoral_structure) anonymity :: "('v, 'b, 'r) Electoral_Module
                                          \<Rightarrow> bool" where *)
definition (in electoral_structure) anonymity :: "('v, 'b, 'r) Electoral_Module
                                          \<Rightarrow> bool" where 
  "anonymity m \<equiv>
    electoral_module m \<and>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> m V (limit_set A UNIV) p = m V' (limit_set A' UNIV) q))"

text \<open>
  Anonymity can alternatively be described as invariance
  under the voter permutation group acting on elections
  via the rename function.
\<close>

(* Note: Only single winner case 'r = 'a *)
fun (in ballot) anonymity' :: "('a, 'v, 'b) Election set \<Rightarrow> ('v, 'b, 'a) Electoral_Module \<Rightarrow> bool" where
  "anonymity' X m = is_symmetry (fun\<^sub>\<E> m) (Invariance (anonymity\<^sub>\<R> X))"


subsubsection \<open>Neutrality\<close>

text \<open>
  Neutrality is equivariance under consistent renaming of
  candidates in the candidate set and election results.
\<close>

fun (in result_properties) neutrality :: "('a, 'v) Election set
        \<Rightarrow> ('a, 'v, 'b Result) Electoral_Module \<Rightarrow> bool" where
  "neutrality X m =
    is_symmetry (fun\<^sub>\<E> m) (action_induced_equivariance (carrier neutrality\<^sub>\<G>) X
          (\<phi>_neutr X) (result_action \<psi>_neutr))"


subsection \<open>Social Choice Modules\<close>

text \<open>
  The following results require electoral modules to return social choice results,
  i.e., sets of elected, rejected and deferred alternatives.
  In order to export code, we use the hack provided by Locale-Code.
\<close>

text \<open>
  "defers n" is true for all electoral modules that defer exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition defers :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite A \<and> profile V A p)
          \<longrightarrow> card (defer m V A p) = n)"

text \<open>
  "rejects n" is true for all electoral modules that reject exactly
  n alternatives, whenever there are n or more alternatives.
\<close>

definition rejects :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> finite A \<and> profile V A p)
          \<longrightarrow> card (reject m V A p) = n)"

text \<open>
  As opposed to "rejects", "eliminates" allows to stop rejecting if no
  alternatives were to remain.
\<close>

definition eliminates :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A > n \<and> profile V A p) \<longrightarrow> card (reject m V A p) = n)"

text \<open>
  "elects n" is true for all electoral modules that
  elect exactly n alternatives, whenever there are n or more alternatives.
\<close>

definition elects :: "nat \<Rightarrow> ('a, 'v, 'a Result) Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    \<S>\<C>\<F>_result.electoral_module m \<and>
      (\<forall> A V p. (card A \<ge> n \<and> profile V A p) \<longrightarrow> card (elect m V A p) = n)"

end