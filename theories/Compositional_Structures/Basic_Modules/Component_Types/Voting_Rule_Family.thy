section \<open>Voting Rule Families\<close>

theory Voting_Rule_Family

imports
    Voting_Rule
    Evaluation_Function
    "Social_Choice_Types/Aggregate_Profile"
begin

text \<open>
  Aggregate ballots are ballots w.r.t. contenders in the role of alternatives. Therefore,
  aggregate ballots induce an electoral structure that corresponds to a single winner setting on
  the contenders as alternatives.
\<close>

context aggregation
begin

sublocale agg_structure:
electoral_structure 
  empty_ballot
  prefers
  wins (* wins *)
  limit_ballot (* limit_ballot *)
  "(\<inter>)" (* limit_contenders *)
  id (*  affected_alts *)
  well_formed_ballot (* well_formed_ballot *)
  id (* contenders *)
  limit_ballot (* limit_by_conts *)
proof (unfold_locales, clarify+)
show "\<And>R. id (id R) = R" by simp
next
show "\<And>R. R \<noteq> {} \<and> id (id R) = {} \<longrightarrow> id R = {}" by simp
next
show "\<And>R R'. R \<subseteq> R' \<longrightarrow> id R \<subseteq> id R'" by simp
next
show "\<And>R R'. id (R \<inter> R') \<subseteq> R" by simp
next
show "\<And>R b. limit_ballot R b = limit_ballot (id R) b" by simp
qed

end

subsection \<open>Definition\<close>

type_synonym ('a, 'v, 'b, 'r, 'i) Voting_Rule_Family = 
  "'i Aggregate_Score \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule"

locale family_structure =
  aggregation empty_agg pref_agg wins_agg limit_agg well_formed_agg well_formed_base
  + base_struct: electoral_structure empty_ballot _ _ _ _ _ well_formed_base for 
  empty_agg :: "'r \<Rightarrow> 'i" and
  pref_agg :: "('r \<Rightarrow> 'i) => 'r \<Rightarrow> 'r \<Rightarrow> bool" and
  wins_agg :: "('r \<Rightarrow> 'i) \<Rightarrow> 'r \<Rightarrow> bool" and
  limit_agg :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> 'r \<Rightarrow> 'i" and
  well_formed_agg :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" and
  well_formed_base :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
  empty_ballot :: "'b" + 
fixes
  family_score :: "'i Aggregate_Score \<Rightarrow> bool" and (*thiele_score :: Thiele_Score \<Rightarrow> bool*)
  family_module :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Electoral_Module"
begin

fun family_member :: "('a, 'v, 'b, 'r, 'i) Voting_Rule_Family" where
"family_member score V A p = elect (family_module score) V (contenders A) (aggregate_profile A p)"


subsection \<open>Properties Shared by Family Members\<close>

subsubsection \<open>Anonymity\<close>

lemma family_anonymous:
  fixes score :: "'i Aggregate_Score"
  assumes 
    wf_score: "family_score score" and
    mod_anon: "agg_structure.anonymity (family_module score)"
  shows "base_struct.vr_anonymity (family_member score)"
proof (unfold base_struct.vr_anonymity_def Let_def, clarify)
  fix 
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('v, 'b) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume 
    bij: "bij \<pi>" and
    rename: "base_struct.rename \<pi> (A, V, p) = (A', V', q)" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    wf_p: "base_struct.well_formed_profile V A p" and
    wf_q: "base_struct.well_formed_profile V' A' q"
  have A_eq: "A' = A" using rename by simp
  let ?R = "contenders A"  
  let ?R' = "contenders A'"
  have fin_R: "finite ?R" using fin_A fin_preserve by simp  
  have R_eq: "?R = ?R'" using A_eq by simp
  let ?p_agg = "(limit_agg ?R) \<circ> (aggregate_profile A p)"
  let ?q_agg = "(limit_agg ?R') \<circ> (aggregate_profile A' q)"
  have p_agg_eq: "?p_agg = (aggregate_profile A p)" 
    using limit_valid 
    by auto
  have q_agg_eq: "?q_agg = (aggregate_profile A' q)" 
    using limit_valid 
    by auto
  have rename_res: "rename \<pi> (?R, V, (aggregate_profile A p)) =
      (?R', V', (aggregate_profile A' q))"
    using rename agg_preserves_alt_rename
    by fastforce
  moreover have fp_res: "finite_profile V (id ?R) (aggregate_profile A p)"
    using fin_V fin_R wf_p preserve_valid well_formed_profile_def aggregate_profile.elims 
          id_apply base_struct.well_formed_profile_def
    by metis
  moreover have "finite_profile V' (id ?R') (aggregate_profile A' q)"
    using fin_V fin_R R_eq wf_q preserve_valid id_apply fp_res rename_finite rename_res bij
    by metis
  ultimately have "(family_module score) V ?R (aggregate_profile A p) =
    (family_module score) V' ?R' (aggregate_profile A' q)"
    using bij agg_structure.anonymity_prereq mod_anon
    by metis
  thus "family_member score V A p =  family_member score V' A' q" 
  by simp
qed


subsubsection \<open>Neutrality\<close>


subsubsection \<open>Continuity\<close>

lemma aggregate_join_commute:
fixes 
  V V' :: "'v set" and 
  A :: "'a set" and
  p q :: "('v, 'b) Profile" and
  v :: 'v
assumes 
  wf_p: "well_formed_base_profile V A p" and
  wf_p: "well_formed_base_profile V' A q" and
  voter: "v \<in> V \<union> V'"
shows "(aggregate_profile A (base_struct.joint_profile V V' p q)) v = 
  joint_profile V V' (aggregate_profile A p) (aggregate_profile A q) v"
proof (cases "v \<in> V")
case in_V: True
  hence "base_struct.joint_profile V V' p q v = p v" by simp
  hence "(aggregate_profile A (base_struct.joint_profile V V' p q)) v = (aggregate_profile A p) v"
    by simp
  moreover have "joint_profile V V' (aggregate_profile A p) (aggregate_profile A q) v = 
    aggregate_profile A p v"
    using in_V by simp
  ultimately show ?thesis by simp
next
case notin_V: False
  then show ?thesis
  proof (cases "v \<in> V'")
  case in_V': True
    hence "base_struct.joint_profile V V' p q v = q v" using If_def notin_V by simp
    hence "(aggregate_profile A (base_struct.joint_profile V V' p q)) v = (aggregate_profile A q) v"
    by simp
  moreover have "joint_profile V V' (aggregate_profile A p) (aggregate_profile A q) v = 
    aggregate_profile A q v"
    using If_def notin_V in_V' by simp
  ultimately show ?thesis by simp
  next
  case False
  then show ?thesis using notin_V voter by blast
  qed
qed


lemma family_continous:
  fixes score :: "'i Aggregate_Score"
  assumes 
    wf_score: "family_score score" and
    mod_cont: "agg_structure.continuity (family_module score)" and
    vde: "voters_determine_election (family_module score)"
  shows "base_struct.vr_continuity (family_member score)"
proof (unfold base_struct.vr_continuity_def Let_def, clarify)
fix 
    A :: "'a set" and
    V V' W :: "'v set" and
    p q s :: "('v, 'b) Profile" and
    n :: nat and
    c :: 'r
assume 
  wf_p: "base_struct.well_formed_profile V A p" and
  wf_q: "base_struct.well_formed_profile V' A q" and
  disj: "V \<inter> V' = {}" and
  fin_A: "finite A" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  copy: "n_copy n V W p s" and
  win: "c \<in> family_member score (W \<union> V') A (base_struct.joint_profile V' W q s)"
let ?m = "family_module score"
let ?R = "contenders A"
let ?p_agg = "aggregate_profile A p"
let ?q_agg = "aggregate_profile A q"
let ?s_agg = "aggregate_profile A s"
have "finite_profile V ?R ?p_agg"
  using wf_p fin_V preserve_valid base_struct.well_formed_profile_def fin_A fin_preserve 
        well_formed_profile_def
        by (metis aggregate_profile.elims)
moreover have "finite_profile V' ?R ?q_agg"
  using wf_q fin_V' preserve_valid base_struct.well_formed_profile_def fin_A fin_preserve 
        well_formed_profile_def
  by (metis aggregate_profile.elims)
moreover have "n_copy n V W ?p_agg ?s_agg" 
  using copy_aggregate_commute copy base_struct.well_formed_profile_def well_formed_base_profile_def wf_p
  by metis
ultimately have "(defer ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq> 
  defer ?m V ?R ?p_agg \<union> elect ?m V ?R ?p_agg) \<and>
  (elect ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq> elect ?m V ?R ?p_agg)"
  using mod_cont agg_structure.continuity_prereq disj id_apply 
  by metis
hence *: "elect ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq> elect ?m V ?R ?p_agg" by simp
have "\<forall>v \<in> (W \<union> V'). (aggregate_profile A (base_struct.joint_profile V' W q s)) v = 
  (joint_profile V' W ?q_agg ?s_agg) v" 
  using aggregate_join_commute 
  by auto
hence "?m (W \<union> V') ?R (aggregate_profile A (base_struct.joint_profile V' W q s))
  = ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg)"
  using vde
  by simp
moreover have "c \<in> elect ?m (W \<union> V') ?R (aggregate_profile A (base_struct.joint_profile V' W q s))"
  using win 
  by simp
ultimately have "c \<in> elect ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg)" by simp
hence "c \<in> elect ?m V ?R ?p_agg" using win * by auto
thus "c \<in> family_member score V A p" by simp
qed

(*
sublocale elim_family :
fixes family_eval :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Evaluation_Function"
assumes "family_module score = elimination_module (family_eval score) t r"
begin
end
*)

lemma elim_module_continous:
fixes family_eval :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Evaluation_Function"
assumes 
  wf_score: "family_score score" and
  elim_mod: "family_module = elimination_module (family_eval score)"
shows "agg_structure.continuity (family_module score)"
proof (unfold agg_structure.continuity_def, clarify)
have "voters_determine_election (family_module score)" sorry

oops

  
end


locale elim_family =
fixes 
  family_eval :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Evaluation_Function" and
  family_score :: "'i Aggregate_Score \<Rightarrow> bool" and (*thiele_score :: Thiele_Score \<Rightarrow> bool*)
  family_module :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Electoral_Module"
begin
end


end