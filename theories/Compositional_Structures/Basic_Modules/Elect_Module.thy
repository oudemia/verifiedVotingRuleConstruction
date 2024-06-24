(*  File:       Elect_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elect Module\<close>

theory Elect_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  The elect module is not concerned about the voter's ballots, and
  just elects all alternatives. It is primarily used in sequence after
  an electoral module that only defers alternatives to finalize the decision,
  thereby inducing a proper voting rule in the social choice sense.
\<close>

subsection \<open>Definition\<close>

fun (in electoral_structure) elect_module :: "('v, 'b, 'r) Electoral_Module" where
  "elect_module V R p = (R, {}, {})"

subsection \<open>Soundness\<close>

theorem \<P>\<V>_elect_mod_sound[simp]: "\<P>\<V>_\<S>\<C>\<F>.electoral_module \<P>\<V>_\<S>\<C>\<F>.elect_module"
  unfolding \<P>\<V>_\<S>\<C>\<F>.electoral_module.simps
  by simp

theorem \<A>\<V>_elect_mod_sound[simp]: "\<A>\<V>_\<S>\<C>\<F>.electoral_module \<A>\<V>_\<S>\<C>\<F>.elect_module"
  unfolding \<A>\<V>_\<S>\<C>\<F>.electoral_module.simps
  by simp

lemma (in electoral_structure) elect_mod_only_voters: "voters_determine_election elect_module"
  unfolding voters_determine_election.simps
  by simp

subsection \<open>Electing\<close>

theorem elect_mod_electing[simp]: "electing elect_module"
  unfolding electing_def
  by simp

end