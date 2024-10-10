section \<open>Voting Rules\<close>

theory Voting_Rule

imports
    Electoral_Module
    Evaluation_Function
    "Social_Choice_Types/Aggregate_Profile"
begin

text \<open>
  Voting Rules are a special component type of the composable
  modules voting framework. In contrast to an electoral module, a voting rule
  is not composable. It does not abstract from voting rules in social choice,
  but aims to model them, therefore "making the final decision" that an electoral
  model does not make by design.

  A voting rule therefore receives a set of voters, a set of eligible alternatives
  and a profile. It returns a set of (tied) winners.
\<close>

subsection \<open>Definition\<close>

type_synonym ('a, 'v, 'b, 'r) Voting_Rule = "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set"

fun (in result) electing :: "('r, 'v, 'b) Electoral_Module \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule" where
"electing m V A p = elect m V (contenders A) p"


subsection \<open>Properties\<close>

  
fun rename_pr :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
  "rename_pr \<pi> b = (\<lambda> (a1, a2). (\<pi> a1, \<pi> a2)) ` b"

fun rename_comm :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "rename_comm \<pi> C = \<pi> ` C"
  
  
definition vr_neutrality_swpb :: "('a, 'v, 'a Preference_Relation, 'a) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality_swpb r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (V', A', q) =  (V, \<pi> ` A, (rename_pr \<pi>) \<circ> p) in
            \<P>\<V>_profile.finite_profile V A p \<and> \<P>\<V>_profile.finite_profile V' A' q \<longrightarrow> \<pi> ` (r V A p) = r V' A' q))"

definition vr_neutrality_commpb :: "('a, 'v, 'a Preference_Relation, 'a Committee) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality_commpb r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (V', A', q) =  (V, \<pi> ` A, (rename_pr \<pi>) \<circ> p) in
            \<P>\<V>_profile.finite_profile V A p \<and> \<P>\<V>_profile.finite_profile V' A' q \<longrightarrow>  (rename_comm \<pi>) ` (r V A p) = r V' A' q))"

definition vr_neutrality_swab :: "('a, 'v, 'a Approval_Set, 'a) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality_swab r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (V', A', q) =  (V, \<pi> ` A, (rename_comm \<pi>) \<circ> p) in
            \<A>\<V>_profile.finite_profile V A p \<and> \<A>\<V>_profile.finite_profile V' A' q \<longrightarrow> \<pi> ` (r V A p) = r V' A' q))"

definition vr_neutrality_commab :: "('a, 'v, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality_commab r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (V', A', q) =  (V, \<pi> ` A, (rename_comm \<pi>) \<circ> p) in
            \<A>\<V>_profile.finite_profile V A p \<and> \<A>\<V>_profile.finite_profile V' A' q \<longrightarrow>  (rename_comm \<pi>) ` (r V A p) = r V' A' q))"
            
            
context electoral_structure 
begin

definition vr_anonymity :: "('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool" where 
  "vr_anonymity r \<equiv>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> r V A p = r V' A' q))"


            
fun rename_conts :: "('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r set" where
  "rename_conts \<pi> c = (let A = affected_alts {c} in {c' \<in> contenders ((\<lambda>a. \<pi> a) A)})"

definition vr_neutrality :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where
  "neutrality_\<A>\<B>\<C> r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename_alts_\<A>\<V> \<pi> (A, V, p)) in
            \<A>\<V>_profile.finite_profile V A p \<and> \<A>\<V>_profile.finite_profile V' A' q \<longrightarrow> r V A p = r V' A' q))"

end

subsection \<open>Voting Rule Families\<close>

type_synonym 'i Aggregate_Evaluation = "'i \<Rightarrow> erat"

type_synonym ('v, 'a, 'b, 'r, 'i) Voting_Rule_Family = "'i Aggregate_Evaluation \<Rightarrow> ('v, 'a, 'b, 'r) Voting_Rule"

fun voting_rule_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

end