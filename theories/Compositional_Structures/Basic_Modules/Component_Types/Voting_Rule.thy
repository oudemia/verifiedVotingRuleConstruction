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
  model does not mae by design.

  A voting rule therefore receives a set ov voters, a set of eligible alternatives
  and a profile. It returns a set of (tied) winners.
\<close>

subsection \<open>Definition\<close>

type_synonym ('v, 'a, 'b, 'r) Voting_Rule = "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set"

fun (in result) electing :: "('r, 'v, 'b) Electoral_Module \<Rightarrow> ('v, 'a, 'b, 'r) Voting_Rule" where
"electing m V A p = elect m V (contenders A) p"

context electoral_structure 
begin


subsection \<open>Properties\<close>

definition vr_anonymity :: "('v, 'a, 'b, 'r) Voting_Rule \<Rightarrow> bool" where 
  "vr_anonymity r \<equiv>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> r V A p = r V A q))"

lemma sw_lift_anonymity: 
  fixes 
    m :: "('a, 'v, 'b) Electoral_Module" and
    r :: "('v, 'a, 'b, 'r) Voting_Rule"
  assumes 
    vr: "voting_rule r" and
    eq: "\<forall> A R V p. affected_alts R = A \<longrightarrow> (r V A p = elect m V R p)" and 
    anon: "anonymity m"
  shows "vr_anonymity r"
proof (unfold anonymity_def vr_anonymity_def, auto)
  fix 
    V :: "'v set" and
    A :: "'a set" and
    p :: "('v, 'b) Profile"
  assume "well_formed_profile V A p"
  thus "0 < card (r V A p)" using vr by simp
next
 fix 
    V :: "'v set" and
    A :: "'a set" and
    p :: "('v, 'b) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    res :: "'r"
  assume 
    "bij \<pi>" and
    "finite V" and "finite A" and
    "well_formed_profile V A p" and
    "well_formed_profile (\<pi> ` V) A (p \<circ> the_inv \<pi>)" and
    "res \<in> r V A p"
  show "res \<in> r V A (p \<circ> the_inv \<pi>)"
  proof
  qed

qed

end

subsection \<open>Voting Rule Families\<close>

type_synonym 'i Aggregate_Evaluation = "'i \<Rightarrow> erat"

type_synonym ('v, 'a, 'b, 'r, 'i) Voting_Rule_Family = "'i Aggregate_Evaluation \<Rightarrow> ('v, 'a, 'b, 'r) Voting_Rule"

fun voting_rule_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

end