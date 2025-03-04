section \<open>Voting Rule Families\<close>

theory Voting_Rule_Family

imports
    Voting_Rule
    Evaluation_Function
    Elimination_Module
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

(*
lemma n_copy_multiplies_score_sum:
fixes 
  V W :: "'v set" and 
  p q :: "('v, 'r, 'i) Aggregate_Profile" and
  score :: "'i Aggregate_Score" and
  n :: nat and
  r :: 'r
assumes 
  copy: "n_copy n V W p q" and
  fin_V: "finite V" and
  fin_W: "finite W" and
  rat_score: "\<forall>b \<in> p ` V. (\<bar>score (b r)\<bar> \<noteq> \<infinity>)" and
  pos_score: "\<forall>b \<in> p ` V. (score (b r) > 0)"
shows "score_sum score q W r = erat_of n * (score_sum score p V r)" 

lemma join_adds_score_sum:
fixes 
  V V' :: "'v set" and 
  p q :: "('v, 'r, 'i) Aggregate_Profile" and
  score :: "'i Aggregate_Score" and
  r :: 'r
assumes 
  disj: "V \<inter> V' = {}" and
  fin_V: "finite V" and
  fin_V': "finite V'"
shows "score_sum score (joint_profile V V' p q) (V \<union> V') r = 
  score_sum score p V r + score_sum score q V' r" 
*)


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
    p q s :: "('v, 'b) Profile"
assume 
  fin_A: "finite A" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  disj: "V \<inter> V' = {}" and
  wf_p: "base_struct.well_formed_profile V A p" and
  wf_q: "base_struct.well_formed_profile V' A q"
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
ultimately have **: "\<exists>n. n_copy n V W ?p_agg ?s_agg \<longrightarrow> 
  (defer ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq>
  defer ?m V ?R ?p_agg \<union> elect ?m V ?R ?p_agg) \<and>
  (elect ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq> elect ?m V ?R ?p_agg)"
  using agg_structure.continuity_prereq mod_cont disj id_apply
  by metis
then obtain n where *: "n_copy n V W ?p_agg ?s_agg \<longrightarrow> 
  (defer ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq> 
  defer ?m V ?R ?p_agg \<union> elect ?m V ?R ?p_agg) \<and>
  (elect ?m (W \<union> V') ?R (joint_profile V' W ?q_agg ?s_agg) \<subseteq> elect ?m V ?R ?p_agg)" by blast  
show "\<exists>n. n_copy n V W p s \<longrightarrow>
  family_member score (W \<union> V') A (base_struct.joint_profile V' W q s) \<subseteq> family_member score V A p"
proof (standard, safe)
  fix c :: 'r
  assume 
    copy: "n_copy n V W p s" and
    win: "c \<in> family_member score (W \<union> V') A (base_struct.joint_profile V' W q s)"
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
  thus "c \<in> family_member score V A p"
  by (metis (no_types, lifting) "*" base_struct.well_formed_profile_def copy copy_aggregate_commute 
    family_member.elims subsetD well_formed_base_profile_def wf_p)
  qed
qed

(*
type_synonym ('r, 'v, 'b) Evaluation_Function =
  "'v set \<Rightarrow> 'r \<Rightarrow> 'r set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> erat"


fun score_sum :: "'i Aggregate_Score \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile \<Rightarrow> 'v set \<Rightarrow> ('r \<Rightarrow> erat)" where
"score_sum score p V r = sum (\<lambda>v. score (p v r)) V"


*)

fun sum_eval_fun :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Evaluation_Function" where
"sum_eval_fun score V r R p = score_sum score p V r"

fun real_score :: "'i Aggregate_Score \<Rightarrow> bool" where
"real_score score = (\<forall>i. score i \<ge> 0 \<and> \<bar>score i \<bar> \<noteq> \<infinity>)"


lemma max_elim_module_continous:
fixes score :: "'i Aggregate_Score"
assumes 
  wf_score: "family_score score" and
  r_score: "real_score score" and
  elim_mod: "family_module score = max_eliminator (sum_eval_fun score)"
shows "agg_structure.continuity (family_module score)"
proof (unfold agg_structure.continuity_def id_apply, clarify)
fix
  V V' W :: "'v set" and
  R :: "'r set" and
  p q s :: "('v, 'r, 'i) Aggregate_Profile"
assume
  fin_R : "finite R" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  disj: "V \<inter> V' = {}" and
  wf_p: "well_formed_profile V R p" and
  wf_q: "well_formed_profile V' R q"
have det: "voters_determine_election (family_module score)" 
  using elim_mod 
  by simp
let ?n = "4"
show "\<exists>n. n_copy n V W p s \<longrightarrow>
           defer (family_module score) (W \<union> V') R (joint_profile V' W q s)
           \<subseteq> defer (family_module score) V R p \<union> elect (family_module score) V R p \<and>
           elect (family_module score) (W \<union> V') R (joint_profile V' W q s)
           \<subseteq> elect (family_module score) V R p"
proof (standard, safe)
  fix r :: 'r
  assume 
    copy: "n_copy ?n V W p s" and 
    def_joint: "r \<in> defer (family_module score) (W \<union> V') R (joint_profile V' W q s)" and
    loose_V: "r \<notin> elect (family_module score) V R p"
  thus "r \<in> defer (family_module score) V R p" sorry
next
  fix r :: 'r
  assume 
    copy: "n_copy ?n V W p s" and 
    elect_joint: "r \<in> elect (family_module score) (W \<union> V') R (joint_profile V' W q s)" and
    loose_V: "r \<in> elect (family_module score) V R p"
  thus "r \<in> elect (family_module score) V R p" sorry
next
qed

qed

  
end

end