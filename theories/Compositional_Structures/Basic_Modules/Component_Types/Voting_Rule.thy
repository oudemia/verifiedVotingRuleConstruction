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

definition vr_neutrality_relpb :: "('a, 'v, 'a Preference_Relation, 'a rel) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality_relpb r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (V', A', q) =  (V, \<pi> ` A, (rename_pr \<pi>) \<circ> p) in
            \<P>\<V>_profile.finite_profile V A p \<and> \<P>\<V>_profile.finite_profile V' A' q \<longrightarrow>  (rename_pr \<pi>) ` (r V A p) = r V' A' q))"
            
            
context electoral_structure 
begin

definition vr_anonymity :: "('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool" where 
  "vr_anonymity r \<equiv>
      (\<forall> A V p \<pi>::('v \<Rightarrow> 'v).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> r V A p = r V' A' q))"


definition permute_bal :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)" where
   "permute_bal \<pi> A = (SOME \<rho>. bij \<rho> \<and> (\<forall>S \<subseteq> A. \<forall> b. 
      well_formed_ballot A b \<longrightarrow> limit_ballot (\<pi> ` S) (\<rho> b) = \<rho> (limit_ballot S b)))"

definition permute_cont :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('r \<Rightarrow> 'r)" where
   "permute_cont \<pi> A = (SOME \<rho>. bij \<rho> \<and> (\<forall>S \<subseteq> A. \<forall> c \<in> contenders A.
      limit_contenders (\<pi> ` S) {\<rho> c} = \<rho> ` (limit_contenders S {c})))"

definition vr_neutrality :: "('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (V', A', q) =  (V, \<pi> ` A, (permute_bal \<pi> A) \<circ> p) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow>  (permute_cont \<pi> A) ` (r V A p) = r V' A' q))"

end

subsection \<open>The Elector Voting Rule\<close>

text \<open>
  The elector voting rule elects exactly those contenders that a given electoral module elects.
  It therefore discards all deferred and rejected contenders.
\<close>

lemma bij_id:
fixes 
  \<pi> :: "'x \<Rightarrow>'x"
assumes "bij \<pi>"
shows "\<pi> \<circ> (the_inv \<pi>) = id" 
by (metis DEADID.in_rel assms comp_def eq_id_iff f_the_inv_into_f_bij_betw)

lemma bij_inv_inv:
fixes 
  \<pi> :: "'x \<Rightarrow>'x"
assumes "bij \<pi>"
shows "the_inv (the_inv \<pi>) = \<pi>"
proof -
  have "\<forall>x. the_inv (the_inv \<pi>) x = \<pi> x"
    by (metis (no_types) assms bij_betw_the_inv_into bij_is_inj the_inv_f_f)
  thus ?thesis by presburger
qed

context electoral_structure 
begin

fun elector :: "('r, 'v, 'b) Electoral_Module \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule" where
"elector m V A p = elect m V (contenders A) ((\<lambda>b. limit_by_conts (contenders A) b ) \<circ> p)"

text \<open>
  The following variant of the  elector voting rule elects elected and deferred contenders,
  therefore discarding exactly the rejected contenders.
\<close>
fun elector\<^sub>d :: "('r, 'v, 'b) Electoral_Module \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule" where
"elector\<^sub>d m V A p = ((elect m V (contenders A) ((\<lambda>b. limit_by_conts (contenders A) b ) \<circ> p))
        \<union> (defer m V (contenders A) ((\<lambda>b. limit_by_conts (contenders A) b ) \<circ> p)))"

  
lemma elector_inherits_anonymity:   
fixes m :: "('r, 'v, 'b) Electoral_Module"
assumes anon: "anonymity m"
shows "vr_anonymity (elector m)"
proof (unfold vr_anonymity_def, simp add: Let_def, safe)
fix 
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
let ?V = "(\<pi> ` V)"
let ?p = "(limit_by_conts (contenders A) \<circ> p)"
let ?q = "(p \<circ> the_inv \<pi>)"
assume 
  bij: "bij \<pi>" and
  finA: "finite A" and
  finV: "finite V" and
  wfp: "well_formed_profile V A p" and
  finV': "finite ?V" and
  wfp': "well_formed_profile ?V A ?q" and
  win: "c \<in> elect m V (contenders A) ?p"
  have "(A, ?V, ?q) = rename \<pi> (A, V, p)" by simp
  thus "c \<in> elect m ?V (contenders A) (limit_by_conts (contenders A) \<circ> ?q)"
  using anon bij finA finV finV' wfp wfp' win permute_V_preserves_result
  by metis
next
fix 
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
  let ?V = "(\<pi> ` V)"
  let ?p = "(limit_by_conts (contenders A) \<circ> p)"
  let ?q = "(p \<circ> the_inv \<pi>)"
assume 
  bij: "bij \<pi>" and
  finA: "finite A" and
  finV: "finite V" and
  wfp: "well_formed_profile V A p" and
  finV': "finite ?V" and
  wfp': "well_formed_profile ?V A ?q" and
  win: "c \<in> elect m ?V (contenders A) (limit_by_conts (contenders A) \<circ> ?q)"
  have inv_bij: "bij (the_inv \<pi>)"
    using bij
    by (simp add: bij_betw_the_inv_into)
  have inv_inv: "the_inv (the_inv \<pi>) = \<pi>" 
    using bij bij_inv_inv 
    by auto
  have *: "V = ((the_inv \<pi>) \<circ> \<pi>) ` V"
    using bij
    by (simp add: bij_betw_def the_inv_f_f)
  hence "V = (the_inv \<pi>) ` ?V" by auto
  have "p = p \<circ> the_inv \<pi> \<circ> \<pi>" 
    using inv_bij inv_inv
    by (metis comp_assoc comp_id bij_id)
  hence "p = ?q \<circ> \<pi>" by simp
  hence "p = (?q \<circ> the_inv (the_inv \<pi>))" 
    using inv_inv by presburger
  hence "(A, V, p) = rename (the_inv \<pi>) (A, ?V, ?q)"
    using * 
    by fastforce
  thus "c \<in> elect m V (contenders A) ?p"
    using anon inv_bij finA finV finV' wfp wfp' win permute_V_preserves_result
    by metis
qed

lemma elector\<^sub>d_inherits_anonymity:   
fixes m :: "('r, 'v, 'b) Electoral_Module"
assumes anon: "anonymity m"
shows "vr_anonymity (elector\<^sub>d m)"
proof (unfold vr_anonymity_def Let_def, safe)
fix 
  A A' :: "'a set" and
  V V' :: "'v set" and
  p q :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
assume 
  bij: "bij \<pi>" and
  rename: "rename \<pi> (A, V, p) = (A', V', q)" and
  finA: "finite A" and
  finV: "finite V" and
  finV': "finite V'" and
  wfp: "well_formed_profile V A p" and
  wfp': "well_formed_profile V' A' q" and
  win: "c \<in> elector\<^sub>d m V A p"
  have "V' = (\<pi> ` V)" using rename by simp
  have A_id: "A' = A" using rename by simp
  have "q = (p \<circ> the_inv \<pi>)" using rename by simp
  have *: "c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p) \<union>
         defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)" 
    using win elector\<^sub>d.simps 
    by simp
  thus "c \<in> elector\<^sub>d m V' A' q"
  proof (cases)
    assume "c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)" 
    hence "c \<in> elect m V' (contenders A') (limit_by_conts (contenders A) \<circ> q)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V' A' q" by (simp add: A_id)
  next
    assume "\<not> c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
    hence "c \<in> defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
      using * by blast
    hence "c \<in> defer m V' (contenders A') (limit_by_conts (contenders A) \<circ> q)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V' A' q" by (simp add: A_id)
  qed
next
fix 
  A A' :: "'a set" and
  V V' :: "'v set" and
  p q :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
assume 
  bij: "bij \<pi>" and
  rename: "rename \<pi> (A, V, p) = (A', V', q)" and
  finA: "finite A" and
  finV: "finite V" and
  finV': "finite V'" and
  wfp: "well_formed_profile V A p" and
  wfp': "well_formed_profile V' A' q" and
  win: "c \<in> elector\<^sub>d m V' A' q"
  have "V' = (\<pi> ` V)" using rename by simp
  have A_id: "A' = A" using rename by simp
  have "q = (p \<circ> the_inv \<pi>)" using rename by simp
  have *: "c \<in> elect m V' (contenders A') (limit_by_conts (contenders A') \<circ> q) \<union>
         defer m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)" 
    using win elector\<^sub>d.simps 
    by simp
  thus "c \<in> elector\<^sub>d m V A p"
  proof (cases)
    assume "c \<in> elect m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)" 
    hence "c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V A p" by (simp add: A_id)
  next
    assume "\<not> c \<in> elect m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)"
    hence "c \<in> defer m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)"
      using * by blast
    hence "c \<in> defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V A p" by (simp add: A_id)
    qed
qed

end

subsection \<open>Voting Rule Families\<close>

type_synonym 'i Aggregate_Evaluation = "'i \<Rightarrow> erat"

type_synonym ('a, 'v, 'b, 'r, 'i) Voting_Rule_Family = "'i Aggregate_Evaluation \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule"

fun voting_rule_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

end