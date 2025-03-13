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
next
show "\<And>A B. A \<subseteq> B \<longrightarrow> id A = A \<inter> id B" using id_apply by auto
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
assumes
  agg_empty: "aggregate A empty_ballot = empty_agg" and
  score_empty: "family_score score \<Longrightarrow> score (empty_agg r) = 0"
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
    p q s :: "('v, 'b) Profile"
assume 
  fin_A: "finite A" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  disj: "V \<inter> V' = {}" and
  disj_W: "W \<inter> V' = {}" and
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
  using agg_structure.continuity_prereq mod_cont disj disj_W id_apply
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


lemma continuity_helper:
fixes
  score :: "'i Aggregate_Score" and
  V V' W :: "'v set" and
  r :: 'r and
  p q s :: "('v, 'r, 'i) Aggregate_Profile" and
  n :: nat
assumes
  copy: "n_copy n V W p s" and
  large_n: "erat_of n * (score_sum score p V r) > (score_sum score q V' r)" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  fin_W: "finite W" and
  disj: "W \<inter> V' = {}" and
  rat_score: "\<forall>b. (\<bar>score (b r)\<bar> \<noteq> \<infinity>)" and
  nn_score: "\<forall>b. (score (b r) \<ge> 0)" and
  non_zero_voter: "\<exists>v \<in> V. (score (p v r) > 0)"
shows "score_sum score (joint_profile W V' s q) (W \<union> V') r > score_sum score q V' r"
proof -
*)

fun sum_eval_fun :: "'i Aggregate_Score \<Rightarrow> ('r, 'v, ('r \<Rightarrow> 'i)) Evaluation_Function" where
"sum_eval_fun score V r R p = score_sum score p V r"

fun real_score :: "'i Aggregate_Score \<Rightarrow> bool" where
"real_score score = (\<forall>i. score i \<ge> 0 \<and> \<bar>score i\<bar> \<noteq> \<infinity>)"



lemma nn_score_sum:
fixes
  score :: "'i Aggregate_Score" and
  V :: "'v set" and
  r :: 'r and
  p :: "('v, 'r, 'i) Aggregate_Profile"
assumes r_score: "real_score score"
shows  "score_sum score p V r \<ge> 0" 
proof -
have "\<forall>v \<in> V. score (p v r) \<ge> 0"
  using r_score
  by simp
hence "(\<Sum>v \<in> V. score (p v r)) \<ge> 0"
  using sum_nonneg
  by metis
thus ?thesis by simp
qed


lemma real_score_sum:
fixes
  score :: "'i Aggregate_Score" and
  V :: "'v set" and
  r :: 'r and
  p :: "('v, 'r, 'i) Aggregate_Profile"
assumes r_score: "real_score score"
shows  "\<bar>score_sum score p V r\<bar> \<noteq> \<infinity>" 
proof -
have "\<forall>v \<in> V. \<bar>score (p v r)\<bar> \<noteq> \<infinity>"
  using r_score real_score.simps
  by meson
hence "\<bar>(\<Sum>v \<in> V. score (p v r))\<bar> \<noteq> \<infinity>"
  using sum_Inf 
  by meson
thus ?thesis by simp
qed


lemma we_dont_need_to_know_n:
fixes e f :: erat
assumes
  e_rat: "\<bar>e\<bar> \<noteq> \<infinity>" and
  f_rat: "\<bar>f\<bar> \<noteq> \<infinity>" and
  e_pos: "e > 0" and
  f_nn: "f \<ge> 0"
shows "\<exists>n. erat_of n * e > f"
proof (cases "e < f")
case e_le_f: True
have f_id: "erat (rat_of_erat f) = f"
  using f_rat 
  by auto
moreover have e_id: "erat (rat_of_erat e) = e" 
  using e_rat 
  by auto
ultimately have "rat_of_erat f / rat_of_erat e > 0"
  using e_le_f e_pos erat_less(2) order_less_trans zero_less_divide_iff
  by metis
hence *: "\<lceil>rat_of_erat f / rat_of_erat e\<rceil> = int (nat \<lceil>rat_of_erat f / rat_of_erat e\<rceil>)"
  by simp
have "rat_of_erat f = (rat_of_erat f) / (rat_of_erat e) * rat_of_erat e"
  using e_pos e_id
  by force
hence "f = (rat_of_erat f) / (rat_of_erat e) *  e"
  using e_id f_id times_erat.simps(1)
  by metis
moreover have "... \<le> Fract \<lceil>(rat_of_erat f) / (rat_of_erat e)\<rceil> 1 * e"
  using Fract_of_int_quotient e_pos erat_mult_right_mono 
  by auto
moreover have "... < (Fract (\<lceil>(rat_of_erat f) / (rat_of_erat e)\<rceil>) 1 + 1) * e"
  using e_pos e_id erat_mult_strict_right_mono less_add_one less_erat.simps
  by metis
moreover have "... = Fract ((\<lceil>(rat_of_erat f) / (rat_of_erat e)\<rceil>) + 1) 1 * e"
  by (simp add: Fract_add_one)
moreover have "... = Fract (nat (\<lceil>(rat_of_erat f) / (rat_of_erat e)\<rceil>) + 1) 1 * e"
  using * of_nat_1 of_nat_add
  by metis
moreover have "... = erat_of (nat (\<lceil>(rat_of_erat f) / (rat_of_erat e)\<rceil>) + 1) * e" by simp
ultimately have "f < erat_of (nat (\<lceil>(rat_of_erat f) / (rat_of_erat e)\<rceil>) + 1) * e" by order
thus  ?thesis by blast
next
case False
hence "f \<le> e" by simp
moreover have "e < 2 * e" 
  using e_pos e_rat 
  by fastforce
moreover have "... = Fract 2 1 * e" by (simp add: rat_number_collapse(3))
moreover have "... = erat_of 2 * e" by simp
ultimately have "f < erat_of 2 * e" by order
thus  ?thesis by blast
qed


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
  disj_V: "V \<inter> V' = {}" and
  disj_W: "W \<inter> V' = {}" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  fin_W: "finite W" and
  wf_p: "well_formed_profile V R p" and
  wf_q: "well_formed_profile V' R q" and
  wf_s: "well_formed_profile W R s"

have det: "voters_determine_election (family_module score)"
  using elim_mod 
  by simp
have fin_img_V: "finite {(sum_eval_fun score) V x R p | x. x \<in> R}" 
  using fin_R
  by simp

let ?elect_joint = "elect (family_module score) (W \<union> V') R (joint_profile V' W q s)"
let ?elect_V = "elect (family_module score) V R p"
let ?defer_joint = "defer (family_module score) (W \<union> V') R (joint_profile V' W q s)"
let ?defer_V = "defer (family_module score) V R p"

let ?max_V = "Max {(sum_eval_fun score) V x R p | x. x \<in> R}"
let ?max_V' = "Max {(sum_eval_fun score) V' x R q | x. x \<in> R}"
let ?max_W = "Max {(sum_eval_fun score) W x R s | x. x \<in> R}"
let ?max_joint = "Max {(sum_eval_fun score) (W \<union> V') x R (joint_profile V' W q s) | x. x \<in> R}"


show "\<exists>n. n_copy n V W p s \<longrightarrow> ?defer_joint \<subseteq> ?defer_V \<union> ?elect_V \<and> ?elect_joint \<subseteq> ?elect_V"
proof (cases "defer (family_module score) V R p = R"; standard; standard)
  case trivial_p: True
  have "defer (family_module score) (W \<union> V') R (joint_profile V' W q s) \<subseteq> R" 
    using elim_mod agg_structure.max_elim_sound 
    by simp
  moreover have "elect (family_module score) V R p = {}" 
    using elim_mod
    by simp
  moreover have "elect (family_module score) (W \<union> V') R (joint_profile V' W q s) = {}" 
    using elim_mod
    by simp
  ultimately show "?defer_joint \<subseteq> ?defer_V \<union> ?elect_V \<and> ?elect_joint \<subseteq> ?elect_V" 
    using trivial_p 
    by simp
next
  case nontrivial_p: False
  let ?min_diff = "Min {?max_V -((sum_eval_fun score) V x R p) | x. x \<in> R \<and> (sum_eval_fun score) V x R p \<noteq> ?max_V}"
  have real_min_diff: "\<bar>?min_diff\<bar> \<noteq> \<infinity>" sorry
  moreover have  real_max_V': "\<bar>?max_V'\<bar> \<noteq> \<infinity>" sorry
  moreover have "?min_diff > 0" sorry
  moreover have "?max_V' \<ge> 0" sorry
  then obtain n where large_n: "erat_of n * ?min_diff > ?max_V'" sorry
  thus "?defer_joint \<subseteq> ?defer_V \<union> ?elect_V \<and> ?elect_joint \<subseteq> ?elect_V"
  proof -
  have "?elect_joint = {}" using elim_mod by simp
  moreover have "?elect_V = {}" using elim_mod by simp
  ultimately have "?elect_joint \<subseteq> ?elect_V" by simp
  moreover have "?defer_joint \<subseteq> ?defer_V \<union> ?elect_V"
  proof
    fix r :: 'r
    assume 
      def_joint: "r \<in> ?defer_joint"      
    thus "r \<in> ?defer_V \<union> ?elect_V" sorry 
  qed
  ultimately show ?thesis by blast
qed
  (*
      
have *: "\<forall>r \<in> R. \<bar>score_sum score p V r\<bar> \<noteq> \<infinity>" 
  using real_score_sum r_score 
  by metis
hence "\<forall>r \<in> R. \<bar>(sum_eval_fun score) V r R p\<bar> \<noteq> \<infinity>" by simp
moreover have "?max_V \<in> {(sum_eval_fun score) V x R p | x. x \<in> R}"
  using Max_in fin_img_V elem 
  by blast
ultimately have ex_max_arg: "\<exists>r \<in> R. (sum_eval_fun score) V r R p = ?max_V"
  by auto
  hence real_max_V: "\<bar>?max_V\<bar> \<noteq> \<infinity>" using * by auto
  

    have "defer (family_module score) (W \<union> V') R (joint_profile V' W q s) \<subseteq> R" 
    using elim_mod agg_structure.max_elim_sound 
    by simp
    hence in_R: "r \<in> R"
    using def_joint 
    by auto
    hence "(sum_eval_fun score) (W \<union> V') r R (joint_profile V' W q s) = ?max_joint" 
      using elim_mod agg_structure.defer_of_max_elim[where e="sum_eval_fun score"] fin_R in_R wf_p 
      sorry (*TODO well formed joint profile*)
    hence "(sum_eval_fun score) (W \<union> V') r R (joint_profile V' W q s) = ?max_joint" 
        using in_R Max.coboundedI fin_img_V order_neq_le_trans 
        by auto
    hence *: "erat_of n * ((sum_eval_fun score) V r R p) + (sum_eval_fun score) V' r R q = ?max_joint"
    sorry
    show "r \<in> defer (family_module score) V R p"
    proof (rule ccontr)
      assume "r \<notin> defer (family_module score) V R p"
      hence "(sum_eval_fun score) V r R p \<noteq> ?max_V" 
      using elim_mod agg_structure.defer_of_max_elim[where e="sum_eval_fun score"] fin_R in_R wf_p 
      by simp
      hence "(sum_eval_fun score) V r R p < ?max_V" 
        using in_R Max.coboundedI fin_img_V order_neq_le_trans 
        by auto
      hence "erat_of n * ((sum_eval_fun score) V r R p) < erat_of n * ?max_V" sorry
      hence "erat_of n * ((sum_eval_fun score) V r R p) + (sum_eval_fun score) V' r R q
        < erat_of n * ?max_V + (sum_eval_fun score) V' r R q"
        using add.commute erat_less_add r_score real_score_sum sum_eval_fun.simps
        by (metis (no_types, lifting))
      hence "?max_joint < erat_of n * ?max_V + (sum_eval_fun score) V' r R q" 
        using * by simp


      have "R \<noteq> {}" using in_R by auto
      hence "defer (family_module score) V R p \<noteq> {}"
      using elim_mod max_eliminator.simps agg_structure.max_elim_non_blocking by auto
      hence "\<exists>w. w \<in> defer (family_module score) V R p" by auto
      then obtain w where winner: "w \<in> defer (family_module score) V R p" by auto
      moreover have "defer  (family_module score) V R p \<subseteq> R" 
        using elim_mod agg_structure.max_elim_sound 
          by simp
      ultimately have w_in_R: "w \<in> R"
      by auto
      have "(sum_eval_fun score) V w R p = ?max_V" 
      using elim_mod agg_structure.defer_of_max_elim[where e="sum_eval_fun score"] fin_R w_in_R wf_p winner 
      by simp
      
      thus False sorry
    qed
    (*
    have "defer (family_module score) (W \<union> V') R (joint_profile V' W q s) \<subseteq> R" 
    using elim_mod agg_structure.max_elim_sound 
    by simp
    hence "r \<in> R"
    using def_joint 
    by auto

    have "\<exists>v \<in> V. (score (p v r) > 0)" sorry
    hence "score_sum score (joint_profile W V' s q) (W \<union> V') r > score_sum score q V' r"
    using continuity_helper copy large_n fin_V fin_V' fin_W disj_W r_score sorry
    have "(sum_eval_fun score) V r R p < ?max_joint" sorry
  thus "r \<in> defer (family_module score) V R p" sorry
*)

qed
qed
*)

(* after real_max_V:

moreover have  real_max_V': "\<bar>?max_V'\<bar> \<noteq> \<infinity>" sorry
moreover have "?max_V > 0" sorry
moreover have "?max_V' \<ge> 0" sorry
ultimately have "\<exists>n. erat_of n * ?max_V > ?max_V'" 
  using we_dont_need_to_know_n 
  by simp
then obtain n where large_n: "erat_of n * ?max_V > ?max_V'" by auto

*)

  
end

end