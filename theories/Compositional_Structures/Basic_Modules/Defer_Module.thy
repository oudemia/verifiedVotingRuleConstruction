(*  File:       Defer_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Basic Modules\<close>

section \<open>Defer Module\<close>

theory Defer_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  The defer module is not concerned about the voter's ballots, and
  simply defers all alternatives.
  It is primarily used for defining an empty loop.
\<close>

subsection \<open>Definition\<close>

fun defer_module :: "('a, 'v, 'r) Electoral_Module" where
  "defer_module V R p = ({}, {}, R)"

subsection \<open>Soundness\<close>

theorem def_mod_sound[simp]: "\<P>\<V>_\<S>\<C>\<F>.electoral_module defer_module"
  unfolding \<P>\<V>_\<S>\<C>\<F>.electoral_module.simps
  by simp

subsection \<open>Properties\<close>

theorem (in electoral_structure) def_mod_non_electing: "non_electing defer_module"
  unfolding non_electing_def
  by simp

theorem def_mod_def_lift_inv: "defer_lift_invariance defer_module"
  unfolding defer_lift_invariance_def
  by simp

end