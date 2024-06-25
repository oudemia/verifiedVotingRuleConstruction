(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Electoral Module\<close>

theory Relay_Module
  imports Electoral_Module
begin

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
  A relay module maps an election to a result.
  To enable currying, the Election type is not used here because that would require tuples.
\<close>

type_synonym ('v, 'a, 'b, 'r) Relay_Module = "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r Result"

fun fun\<^sub>\<E> :: "('v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r)
                  \<Rightarrow> (('a, 'v, 'b) Election \<Rightarrow> 'r)" where
  "fun\<^sub>\<E> m = (\<lambda> E. m (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E))"

text \<open>
  The next three functions take an electoral module and turn it into a
  function only outputting the elect, reject, or defer set respectively.
\<close>

fun single_winner_results :: "'a set \<Rightarrow> 'a set" where
"single_winner_results A = A"

fun committee_results :: "'a set \<Rightarrow> nat \<Rightarrow> ('a Committee) set" where
"committee_results A k = {C. C \<subseteq> A \<and> card C = k}"

fun seq_committee_results :: "'a set \<Rightarrow> nat \<Rightarrow> ('a Committee) set" where
"seq_committee_results A k = {C. C \<subseteq> A \<and> card C \<le> k}"

fun rev_seq_committee_results :: "'a set \<Rightarrow> nat \<Rightarrow> ('a Committee) set" where
"rev_seq_committee_results A k = {C. C \<subseteq> A \<and> card C \<ge> k}"


abbreviation elect :: "('v, 'a, 'b, 'r) Relay_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
        \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set" where
  "elect m V A p \<equiv> elect_r (m V A p)"

abbreviation reject :: "('v, 'a, 'b, 'r) Relay_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
        \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set" where
  "reject m V A p \<equiv> reject_r (m V A p)"

abbreviation "defer" :: "('v, 'a, 'b, 'r) Relay_Module \<Rightarrow> 'v set \<Rightarrow> 'a set
        \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set" where
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

fun (in electoral_structure) relay_module :: "('v, 'a, 'b, 'r) Relay_Module
                                      \<Rightarrow> bool" where
"relay_module m = (\<forall> A V p. well_formed_profile V A p \<longrightarrow> well_formed_result A (m V A p))"


fun relay :: "('a set \<Rightarrow> 'r set) \<Rightarrow> ('v, 'b, 'r) Electoral_Module
                                      \<Rightarrow> ('v, 'a, 'b, 'r) Relay_Module" where
"relay r m V A p = m V (r A) p"

fun single_winner_relay :: "('v, 'b, 'a) Electoral_Module \<Rightarrow> ('v, 'a, 'b, 'a) Relay_Module" where
"single_winner_relay m = relay single_winner_results m"

fun (in committee_result) committee_relay :: "('v, 'b, 'a Committee) Electoral_Module \<Rightarrow> ('v, 'a, 'b, 'a Committee) Relay_Module" where
"committee_relay m = relay (\<lambda> A. committee_results A k) m"


fun (in committee_result) rev_seq_committee_relay :: "('v, 'b, 'a Committee) Electoral_Module \<Rightarrow> ('v, 'a, 'b, 'a Committee) Relay_Module" where
"rev_seq_committee_relay m = relay (\<lambda> A. rev_seq_committee_results A k) m"
 
end