section \<open>Thiele Module\<close>

theory Thiele_Module
imports
      "Component_Types/Voting_Rule_Family"      
      "Component_Types/Elimination_Module"
      "Component_Types/Social_Choice_Types/Aggregate_Profile"
      "Component_Types/Social_Choice_Types/Electoral_Structure"
begin

subsection \<open>Definition\<close>

subsubsection \<open>Aggregated Profiles for Thiele Methods\<close>

type_synonym 'a Thiele_Ballot = "'a Committee \<Rightarrow> nat"

type_synonym Thiele_Score = "nat Aggregate_Score"

fun thiele_ballot :: "('a Committee) set \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> bool" where
"thiele_ballot R b = (\<forall>r \<in> R. finite r \<longrightarrow> b r \<le> card r)"
(* "thiele_ballot R b = (\<forall> r. r \<notin> R \<longrightarrow> b r = 0)" *)

fun default_thiele_ballot :: "'a Thiele_Ballot" where
"default_thiele_ballot C = 0"

fun limit_thiele_ballot :: "('a Committee) set \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> 'a Thiele_Ballot" where
"limit_thiele_ballot C b = b"
(* "limit_thiele_ballot C b c = (if c \<in> C then b c else 0)" *)

fun thiele_prefers :: " 'a Thiele_Ballot \<Rightarrow> 'a Committee \<Rightarrow> 'a Committee \<Rightarrow> bool" where
"thiele_prefers b C D = (b C > b D)"

fun thiele_wins :: "'a Thiele_Ballot \<Rightarrow> 'a Committee \<Rightarrow> bool" where
"thiele_wins b C = (\<forall> D. b C \<ge> b D)"

fun thiele_score :: "Thiele_Score \<Rightarrow> bool" where
"thiele_score w = (w 0 = 0 \<and> mono w \<and> (\<forall>n. \<bar>w n\<bar> \<noteq> \<infinity>))"

fun score_sum :: "Thiele_Score \<Rightarrow> 'v set \<Rightarrow> 'a Committee \<Rightarrow> ('v, 'a Thiele_Ballot) Profile \<Rightarrow> erat" where
"score_sum s V c p = (\<Sum> v \<in> V. s (p v c))"


lemma score_sum_is_rat:
fixes 
  w :: "Thiele_Score" and 
  V :: "'v set" and 
  p :: "('v, 'a Thiele_Ballot) Profile" and 
  c :: "'a Committee"
assumes valid_w: "thiele_score w"
shows "\<bar>score_sum w V c p\<bar> \<noteq> \<infinity>"
proof (unfold score_sum.simps)
have "\<forall>v \<in> V. \<bar>w (p v c)\<bar> \<noteq> \<infinity>" using valid_w by simp
moreover have "\<forall>S \<subseteq> V. \<forall> v \<in> V - S. \<bar>\<Sum>s\<in>S. w (p s c)\<bar> \<noteq> \<infinity> \<longrightarrow> \<bar>\<Sum>s\<in>S\<union>{v}. w (p s c)\<bar> \<noteq> \<infinity> " 
  using valid_w
  by (simp add: sum_Inf)
ultimately show "\<bar>\<Sum>v\<in>V. w (p v c)\<bar> \<noteq> \<infinity>" by (meson sum_Inf)
qed

context committee_result
begin

fun thiele_aggregate :: "('a, 'a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate A b C = card (C \<inter> b)"
(* "thiele_aggregate A b C = (if C \<in> committees A then (card (C \<inter> b)) else 0)" *)

fun thiele_agg_profile :: 
  "('a, 'v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile A p v C = thiele_aggregate A (p v) C"


subsubsection \<open>Electoral Module for Thiele Methods\<close>

fun thiele_module :: "Thiele_Score \<Rightarrow> ('a Committee, 'v, 'a Thiele_Ballot) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R p. score_sum s V r p)) V C p"

(*
fun thiele_family :: "('a, 'v, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where
"thiele_family w V A p =
	thiele_structure.elector\<^sub>d (thiele_module w) V (committees A) (thiele_agg_profile A p)"
*)

fun thiele_method :: "Thiele_Score \<Rightarrow> ('a, 'v, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where
"thiele_method w r = thiele_score w"

sublocale thiele_structure:
family_structure
  committees (* contenders *)
  thiele_aggregate
  (* base ballot information *)
  prefers_\<A>\<V>
  wins_\<A>\<V> 
  limit_\<A>\<V>_ballot
  limit_committees (* limit_contenders *)
  affected_alts_committee 
  (* agg ballot information *)
  default_thiele_ballot (* empty agg ballot *)
  thiele_prefers 
  thiele_wins
  limit_thiele_ballot
  thiele_ballot (* well formed agg *)
  (* mixed *)
  ballot_\<A>\<V>
  default_ballot_\<A>\<V> (* empty base ballot *)
  thiele_score (* family score *)
  thiele_module (* family_module *)
proof (unfold_locales, clarsimp)
fix 
  a :: 'a and
  C1 C2 :: "'a Committee" and 
  b :: "'a Committee \<Rightarrow> nat"
assume 
  neq: "C1 \<noteq> C2" and
  c1_wins: "b C2 < b C1"
thus "\<exists>d. \<not> b d \<le> b C2" using leD by blast
next
show "\<And>A b. thiele_ballot A b \<Longrightarrow> limit_thiele_ballot A b = b" by simp
next
fix 
  R S :: "('a Committee) set" and
  b :: "'a Committee \<Rightarrow> nat"
assume "R \<subseteq> S"
thus " limit_thiele_ballot R b =limit_thiele_ballot R (limit_thiele_ballot S b)" by fastforce
next
fix 
  R S :: "('a Committee) set" and
  b :: "'a Committee \<Rightarrow> nat"
assume "thiele_ballot S b \<and> R \<subseteq> S"
thus "thiele_ballot R (limit_thiele_ballot R b)" by auto
next
fix 
  A :: "'a set" and
  b :: "'a Approval_Set"
assume bal: "ballot_\<A>\<V> A b"
have "\<forall>C \<in> committees A. card C > 0"
using k_positive 
by simp
hence "\<forall> C \<in> committees A. card (C \<inter> b) \<le> card C" 
using  Int_lower1 card_ge_0_finite card_mono 
by meson
thus "thiele_ballot (committees A) (thiele_aggregate A b)" by simp
next
fix 
  A :: "'a set" and
  b b' :: "'a Approval_Set"
assume 
  bal: "ballot_\<A>\<V> A b" and 
  bal' :"ballot_\<A>\<V> A b'" and
  neq : "b \<noteq> b'"
have "b \<union> b' \<subseteq> A" 
  using bal bal' 
  by simp
moreover have "b \<union> b' \<noteq> {}" 
  using neq 
  by fastforce
moreover have "b \<inter> b' \<noteq> A" 
  using neq calculation(1) 
  by blast
ultimately have "\<exists>a \<in> A. a \<in> b \<union> b' \<and> a \<notin> b \<inter> b'"
  using neq 
  by blast
then obtain a where "a \<in> b \<union> b' \<and> a \<notin> b \<inter> b'" by blast
hence "card ({a} \<inter> b) \<noteq> card ({a} \<inter> b')" by auto
thus "\<exists>C. thiele_aggregate A b C \<noteq> thiele_aggregate A b' C"
  unfolding thiele_aggregate.simps 
  by blast
next
fix 
  A :: "'a set" and
  b :: "'a Approval_Set"
show "limit_thiele_ballot (committees A) (thiele_aggregate A b) = thiele_aggregate A b" by auto
next
show "\<And>A. finite A \<Longrightarrow> finite (committees A)" by simp
next
show "\<And>score r. thiele_score score \<Longrightarrow> score (default_thiele_ballot r) = 0" by simp
next
fix 
  A :: "'a set" 
  have "\<forall>C. C \<inter> default_ballot_\<A>\<V> = {}" using default_ballot_\<A>\<V>_def by auto
  hence "\<forall>C. card (C \<inter> default_ballot_\<A>\<V>) = 0" using card.empty by metis
  thus "thiele_aggregate A default_ballot_\<A>\<V> = default_thiele_ballot" by fastforce
qed

(*  fix
    b :: "'a Thiele_Ballot" and
    C D :: "'a Committee"
  assume  
    "C \<noteq> D" and  
    *: "b D < b C" and 
    **: "\<forall>E. b E \<le> b D"
  show "False"
    using * ** linorder_not_less 
    by blast
*)

subsection \<open>Properties\<close>

lemma thiele_mod_sound[simp]:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "thiele_structure.electoral_module (thiele_module w)"
  by auto

lemma thiele_family_simp [simp]:
fixes 
  w :: "Thiele_Score" and
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'a Approval_Set) Profile"
assumes 
  w_valid: "thiele_score w" 
shows "thiele_family w V A p = (elect (thiele_module w) V (committees A) (thiele_agg_profile A p)
        \<union> defer (thiele_module w) V (committees A) (thiele_agg_profile A p))"
proof -
  let ?p_agg = "(limit_thiele_ballot (committees A)) \<circ> (thiele_agg_profile A p)"
  have p_agg_eq: "?p_agg = (thiele_agg_profile A p)" by fastforce
  moreover have "?p_agg = (limit_thiele_ballot (committees A)) \<circ> ?p_agg"
    using p_agg_eq 
    by simp
  ultimately show "thiele_family w V A p =
    elect (thiele_module w) V (committees A) (thiele_agg_profile A p) \<union>
    defer (thiele_module w) V (committees A) (thiele_agg_profile A p)" 
    by simp  
qed


subsubsection \<open>Anonymity\<close>

lemma (in committee_result) thiele_module_anonymous:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "thiele_structure.anonymity (thiele_module w)"
proof (unfold thiele_structure.anonymity_def Let_def, safe)
  show "thiele_structure.electoral_module (thiele_module w)" by auto
next
  fix 
    R R' :: "('a Committee) set" and
    V V' :: "'v set" and
    p q :: "('v, 'a Thiele_Ballot) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume 
    bij: "bij \<pi>" and
    rename: "thiele_aggregation.rename \<pi> (R, V, p) = (R', V', q)"
  have perm: "V' = \<pi> ` V" using rename by simp
  have R_id: "R' = R" using rename by simp
  have q_id: "q = p \<circ> (the_inv \<pi>)" using rename by simp
  let ?e = "\<lambda> V r R p. score_sum w V r p"
  have "\<forall>C \<in> R. (?e V C R p) = (?e V' C R q)"
  proof (unfold score_sum.simps, safe)
    fix C :: "'a Committee"
    have "(\<Sum>v\<in>V.(\<lambda> x. w (p x C)) v) = (\<Sum>v\<in>V'.((\<lambda> x. w (p x C)) \<circ> (the_inv \<pi>)) v)" 
      using bij perm sum_bij 
      by auto
    thus "(\<Sum>v\<in>V. w (p v C)) = (\<Sum>v\<in>V'. w (q v C))"
      using q_id 
      by fastforce
  qed 
  thus "thiele_module w V R p = thiele_module w V' R' q"
    unfolding thiele_module.simps 
    using  thiele_structure.profiles_determine_max_elim
    by (metis (no_types, lifting) R_id)
qed

lemma (in committee_result) thiele_anonymous:
  fixes w :: "nat Aggregate_Evaluation"
  assumes w_valid: "thiele_score w"
  shows "\<A>\<V>_committee.vr_anonymity (thiele_family w)"
proof (unfold \<A>\<V>_committee.vr_anonymity_def Let_def, clarify)
  fix 
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('v, 'a Approval_Set) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assume 
    bij: "bij \<pi>" and
    rename: "\<A>\<V>_committee.rename \<pi> (A, V, p) = (A', V', q)" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    fin_V': "finite V'"
  have A_eq: "A' = A" using rename by simp
  let ?R = "committees A"  
  let ?R' = "committees A'"
  have fin_R: "finite ?R" using fin_A by simp  
  have R_eq: "?R = ?R'" using A_eq by simp
  let ?p_agg = "(limit_thiele_ballot ?R) \<circ> (thiele_agg_profile A p)"
  let ?q_agg = "(limit_thiele_ballot ?R') \<circ> (thiele_agg_profile A' q)"
  have p_agg_eq: "?p_agg = (thiele_agg_profile A p)" by fastforce
  have q_agg_eq: "?q_agg = (thiele_agg_profile A' q)" by fastforce
  have mod_anon: "thiele_structure.anonymity (thiele_module w)"
    using thiele_module_anonymous w_valid 
    by auto
  moreover have rename_res: "thiele_aggregation.rename \<pi> (?R, V, (thiele_agg_profile A p)) =
      (?R', V', (thiele_agg_profile A' q))"
    using rename thiele_aggregation.agg_preserves_alt_rename
    by fastforce
  moreover have fp_res: "thiele_aggregation.finite_profile V (id ?R) (thiele_agg_profile A p)"
    using fin_V fin_R thiele_aggregation.preserve_valid
    by (simp add: thiele_aggregation.well_formed_profile_def)
  moreover have "thiele_aggregation.finite_profile V (id ?R') (thiele_agg_profile A' q)"
    using fin_V fin_R R_eq thiele_aggregation.preserve_valid
    by (simp add: thiele_aggregation.well_formed_profile_def)
  ultimately have "(thiele_module w) V ?R (thiele_agg_profile A p) =
    (thiele_module w) V' ?R' (thiele_agg_profile A' q)"
    using bij thiele_structure.anonymity_prereq
    by (metis A_eq fin_V' id_apply thiele_aggregation.rename_sound)
  hence "(thiele_module w) V ?R ?p_agg = (thiele_module w) V' ?R' ?q_agg"
  using p_agg_eq q_agg_eq by simp
  thus "thiele_family w V A p =  thiele_family w V' A' q" 
    by simp
qed


subsubsection \<open>Neutrality\<close>

fun rename_committee :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a Committee) set => ('a Committee) set" where
"rename_committee \<pi> R = (`) ((`) \<pi>) R"

fun rename_alt_set :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "rename_alt_set \<pi> C = \<pi> ` C"

fun rename_thiele_ballot :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> 'a Thiele_Ballot" where
  "rename_thiele_ballot \<pi> = permute_agg_ballot (rename_alt_set (the_inv \<pi>))"

lemma rename_inherits_bij:
  fixes \<pi> :: "'a \<Rightarrow> 'a"
  assumes "bij \<pi>"
  shows "bij (rename_alt_set \<pi>)" 
  using assms
  by (metis Pow_UNIV bij_betw_Pow bij_betw_cong rename_alt_set.elims)   

lemma (in committee_result) rename_distr:
  fixes 
    A :: "'a set" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes bij: "bij \<pi>"
  shows "committees (\<pi> ` A) = (rename_alt_set \<pi>) ` (committees A)"
proof safe
  fix C :: "'a Committee"
  assume "C \<in> committees (\<pi> ` A)"
  hence comm_C: "C \<subseteq> \<pi> ` A \<and> card C = k" by simp
  hence "\<exists>D \<subseteq> A. C = \<pi> ` D" by (meson subset_imageE)
  then obtain D where comm_D: "D \<subseteq> A \<and> C = \<pi> ` D" by blast
  hence "card D = k" 
    using comm_C bij 
    by (metis bij_betw_def bij_betw_subset card_image top_greatest)
  hence "D \<in> committees A" using comm_D by simp
  thus "C \<in> rename_alt_set \<pi> ` committees A"  by (simp add: comm_D)
next
  fix C :: "'a Committee"
  assume comm: "C \<in> committees A"
  hence "C \<subseteq> A" by simp
  hence *: "rename_alt_set \<pi> C \<subseteq> (\<pi> ` A)" by auto
  have "card C = k" using comm by simp
  hence "card (rename_alt_set \<pi> C) = k" 
    using bij
    by (metis bij_betw_same_card bij_betw_subset rename_alt_set.elims subset_UNIV)
  thus "rename_alt_set \<pi> C \<in> committees (\<pi> ` A) " 
    using * 
    by simp
qed

lemma inv_rename:
  fixes \<pi> :: "'a \<Rightarrow> 'a"
  assumes bij: "bij \<pi>"
  shows "the_inv (rename_alt_set \<pi>) = (rename_alt_set (the_inv \<pi>))" 
proof (unfold rename_alt_set.simps, standard)
fix C :: "'a Committee"  
have "id = \<pi> \<circ> the_inv \<pi>"
  using bij f_the_inv_into_f_bij_betw 
  by fastforce
hence "C = ( \<pi> ` (the_inv \<pi> ` C))" 
  by (simp add: image_comp)
thus "the_inv ((`) \<pi>) C = the_inv \<pi> ` C"
  using bij
  by (metis Pow_UNIV bij_betw_Pow bij_def the_inv_f_f)
qed


lemma (in committee_result) thiele_permutes_coinc:
fixes 
  R :: "('a Committee) set" and
  \<pi> :: "'a \<Rightarrow> 'a"
assumes 
  bij: "bij \<pi>"
shows "thiele_structure.coinciding_permutes R (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>)"
proof (unfold thiele_structure.coinciding_permutes_def, standard+)
fix 
  S :: "('a Committee) set" and
  b :: "'a Thiele_Ballot" and
  C :: "'a Committee"
assume 
  sub: "S \<subseteq> R" and 
  bal: "thiele_ballot (id R) b"
  hence "\<forall> r. r \<notin> R \<longrightarrow> b r = 0" by simp
  hence "\<forall> r. (\<pi> ` r) \<notin> (rename_alt_set \<pi> ` R) \<longrightarrow> b ((the_inv \<pi>) ` (\<pi> ` r)) = 0" 
    using bij rename_inherits_bij
    by (metis bij_def image_eqI inv_rename rename_alt_set.elims the_inv_f_f)
  hence "\<forall> r. r \<notin> (rename_alt_set \<pi> ` R) \<longrightarrow> b ((the_inv \<pi>) ` r) = 0"
    by (metis bij_id bij bij_betw_def bij_betw_id_iff image_comp)
  hence renamed_bal: "thiele_ballot (rename_alt_set \<pi> ` R) (rename_thiele_ballot \<pi> b)"
    using bal 
    by simp
let ?permute_then_limit = "limit_thiele_ballot (rename_alt_set \<pi> ` S) (rename_thiele_ballot \<pi> b)"
let ?limit_then_permute = "rename_thiele_ballot \<pi> (limit_thiele_ballot S b)"
show "?permute_then_limit C = ?limit_then_permute C"
  proof (cases "C \<in> rename_alt_set \<pi> ` S")
    case elem: True
    hence "(the_inv \<pi>) ` C \<in> S" 
      using bij rename_inherits_bij inv_rename rename_alt_set.elims
      by (metis (no_types, lifting) bij_def image_iff the_inv_f_f)
    hence "(limit_thiele_ballot S b) ((the_inv \<pi>) ` C) = b ((the_inv \<pi>) ` C)" by simp
    hence "?limit_then_permute C = b ((the_inv \<pi>) ` C)" by simp
    moreover have "?permute_then_limit C = b ((the_inv \<pi>) ` C)" using elem by simp
    ultimately show ?thesis by simp
  next
    case nelem: False
    hence "(the_inv \<pi>) ` C \<notin> S" 
      using bij rename_inherits_bij inv_rename rename_alt_set.elims
      by (metis (no_types, lifting) UNIV_I bij_def f_the_inv_into_f image_iff)
    hence "(limit_thiele_ballot S b) ((the_inv \<pi>) ` C) = 0" by simp
    hence "?limit_then_permute C = 0" by simp
    moreover have "?permute_then_limit C = 0"
      using nelem 
      by fastforce
    ultimately show ?thesis by simp  
  qed         
qed

lemma (in committee_result) thiele_module_neutral:
fixes 
  w :: "nat Aggregate_Evaluation" and 
  \<pi> :: "'a \<Rightarrow> 'a"
assumes 
  w_valid: "thiele_score w" and 
  bij: "bij \<pi>"
shows "thiele_structure.neutrality (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>) (thiele_module w)"
proof (unfold thiele_structure.neutrality_def, safe)
  show "thiele_structure.electoral_module (thiele_module w)" by auto
next
  fix 
    R :: "('a Committee) set" and 
    V :: "'v set" and 
    p :: "('v, 'a Thiele_Ballot) Profile"    
  assume
    wf: "thiele_structure.well_formed_profile V (id R) p" 
  let ?R = "rename_alt_set \<pi> ` R"
  let ?q = "rename_thiele_ballot \<pi> \<circ> p"
  let ?e = "\<lambda> V r R p. score_sum w V r p"
  let ?res = "rename_result (rename_alt_set \<pi>) (thiele_module w V R p)"
  have "\<forall>C \<in> R. (?e V C R p) = (?e V (\<pi> ` C) ?R ?q)"
    proof (unfold score_sum.simps, safe)
      fix C :: "'a Committee"
      assume "C \<in> R"
      have "C = the_inv \<pi> ` (\<pi> ` C)"
      proof -
        have "bij (the_inv \<pi>)" by (simp add: bij bij_betw_the_inv_into)
        thus ?thesis
          by (metis (no_types) bij_id bij bij_betw_def bij_betw_id image_comp)
      qed
      hence "\<forall>v \<in> V. w (p v C) = w (p v (the_inv \<pi> ` (\<pi> ` C)))"
        using bij 
        by simp     
      thus "(\<Sum>v\<in>V. w (p v C)) = (\<Sum>v\<in>V. w (?q v (\<pi> ` C)))" 
        using bij sum_bij 
        by simp
    qed 
  hence "\<forall>C \<in> R. (?e V C R p) = (?e V (rename_alt_set \<pi> C) ?R ?q)" by simp
  thus "(thiele_module w) V ?R ?q = ?res" 
    unfolding thiele_module.simps
    using bij wf rename_inherits_bij thiele_structure.eval_determine_max_elim
    by (metis (no_types, lifting))
qed


lemma  (in committee_result) bal_coinc:
fixes 
  \<pi> :: "'a \<Rightarrow> 'a" and
  A :: "'a set"
assumes bij: "bij \<pi>"
shows "\<A>\<V>_committee.coinciding_bal_permute A \<pi> (rename_alt_set \<pi>)"
proof (unfold \<A>\<V>_committee.coinciding_bal_permute_def, clarify)
  fix 
  S :: "'a set" and
  b :: "'a Approval_Set" and a :: 'a
  assume 
  sub: "S \<subseteq> A" and 
  bal: "ballot_\<A>\<V> A b" 
  have "limit_\<A>\<V>_ballot (\<pi> ` S) (rename_alt_set \<pi> b) = (\<pi> ` S) \<inter> (\<pi> ` b)" by simp
  hence "limit_\<A>\<V>_ballot (\<pi> ` S) (rename_alt_set \<pi> b) =  \<pi> ` (S \<inter> b)" 
    using bij 
    by (simp add: bij_def image_Int)
  thus "limit_\<A>\<V>_ballot (\<pi> ` S) (rename_alt_set \<pi> b) = rename_alt_set \<pi> (limit_\<A>\<V>_ballot S b)" 
    by simp
qed

lemma  (in committee_result) cont_coinc:
fixes 
  \<pi> :: "'a \<Rightarrow> 'a" and
  A :: "'a set"
assumes bij: "bij \<pi>"
shows "\<A>\<V>_committee.coinciding_cont_permute A \<pi> (rename_alt_set \<pi>)"
proof (unfold \<A>\<V>_committee.coinciding_cont_permute_def, clarify)
  fix S C :: "'a set"
  assume 
    sub: "S \<subseteq> A" and 
    comm: "C \<in> committees A"
  have "rename_alt_set \<pi> C = \<pi> ` C" by simp
  hence "{r \<inter> \<pi> ` S |r. r \<in> {rename_alt_set \<pi> C}} = {\<pi> ` S \<inter> \<pi> ` C}" by auto
  moreover have "rename_alt_set \<pi> ` {r \<inter> S |r. r \<in> {C}} = {\<pi> ` (S \<inter> C)}" by auto
  moreover have "\<pi> ` S \<inter> \<pi> ` C = \<pi> ` (S \<inter> C)" by (simp add: bij bij_is_inj image_Int)
  ultimately show "{r \<inter> \<pi> ` S |r. r \<in> {rename_alt_set \<pi> C}} = 
    rename_alt_set \<pi> ` {r \<inter> S |r. r \<in> {C}}" by simp
qed

lemma (in committee_result) thiele_permutes_coinc_with_agg:
fixes 
  \<pi> :: "'a \<Rightarrow> 'a"
assumes 
  bij: "bij \<pi>"
shows "thiele_aggregation.coinciding_with_agg' \<pi> (rename_alt_set \<pi>) (rename_alt_set \<pi>)"
proof (unfold thiele_aggregation.coinciding_with_agg'.simps, standard+)
fix 
A :: "'a set" and
b :: "'a Approval_Set" and 
C :: "'a Committee"
let ?b = "rename_alt_set \<pi> b"
have "(thiele_aggregate A b \<circ> rename_alt_set \<pi>) C = thiele_aggregate A b (rename_alt_set \<pi> C)"
  by simp
  have card_pres: "\<forall>S. card S = card (\<pi> ` S)" 
    using bij
    by (metis bij_betw_imp_inj_on bij_betw_same_card inj_imp_bij_betw_inv)
  hence "\<forall>C \<in> committees A. card (C \<inter> b) = card ((\<pi> ` C) \<inter> (\<pi> ` (b)))"
    using bij 
    by (metis bij_def image_Int)
  hence "\<forall>C \<in> committees A. card (C \<inter> b) = card ((\<pi> ` C) \<inter> rename_alt_set \<pi> b)" 
    by simp
  moreover have *: "C \<in> committees A \<longleftrightarrow> rename_alt_set \<pi> C \<in> committees (\<pi> ` A)" 
    unfolding committees.simps 
    using bij card_pres vimage_subset_eq 
    by fastforce
  moreover have "C \<notin> committees A \<longrightarrow> thiele_aggregate (\<pi> ` A) (rename_alt_set \<pi> b) (\<pi> ` C) = 0" 
    using * 
    by simp 
  ultimately have "thiele_aggregate (\<pi> ` A) (rename_alt_set \<pi> b) (\<pi> ` C) = thiele_aggregate A b C" 
    by simp
  thus "(thiele_aggregate (\<pi> ` A) (rename_alt_set \<pi> b) \<circ> rename_alt_set \<pi>) C = thiele_aggregate A b C" 
    using rename_alt_set.simps by simp
qed

lemma (in committee_result) thiele_neutral:
  fixes 
    w :: "nat Aggregate_Evaluation" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes w_valid: "thiele_score w" and bij: "bij \<pi>"
  shows "\<A>\<V>_committee.vr_neutrality \<pi> (rename_alt_set \<pi>) (rename_alt_set \<pi>) (thiele_family w)"
proof (unfold \<A>\<V>_committee.vr_neutrality_def, clarify)
  fix 
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Approval_Set) Profile"
  assume
    coinc_bal: "\<A>\<V>_committee.coinciding_bal_permute A \<pi> (rename_alt_set \<pi>)" and
    coinc_cont: "\<A>\<V>_committee.coinciding_cont_permute A \<pi> (rename_alt_set \<pi>)" and
    wf: "\<A>\<V>_committee.well_formed_profile V A p" and
    rename: "\<A>\<V>_committee.well_formed_profile V (\<pi> ` A) (rename_alt_set \<pi> \<circ> p)"
  let ?q_agg = "thiele_aggregation.aggregate_profile (\<pi> ` A) (rename_alt_set \<pi> \<circ> p)"
  let ?p_agg = "thiele_aggregation.aggregate_profile A p"
  have p_agg_eq: "?p_agg = thiele_agg_profile A p" by fastforce
  have q_agg_eq: "?q_agg = thiele_agg_profile (\<pi> ` A) (rename_alt_set \<pi> \<circ> p)" by fastforce
  have "?p_agg = permute_agg_profile (rename_alt_set \<pi>) ?q_agg"
    using thiele_permutes_coinc_with_agg p_agg_eq q_agg_eq bij rename_inherits_bij 
          thiele_aggregation.agg_preserves_alt_rename_v2 
    by blast
  hence "?q_agg = permute_agg_profile (rename_alt_set (the_inv \<pi>)) ?p_agg"
    using agg_bij bij inv_rename rename_inherits_bij
    by metis
  hence "?q_agg = rename_thiele_ballot \<pi> \<circ> ?p_agg"
    by fastforce
  moreover have "committees (\<pi> ` A) = (rename_alt_set \<pi>) ` (committees A)" 
    using rename_distr bij 
    by blast
  moreover have mod_neutr:
    "thiele_structure.neutrality (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>) (thiele_module w)"
    using thiele_module_neutral w_valid bij
    by auto
  moreover have "thiele_structure.coinciding_permutes (committees A) 
      (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>)"
    using thiele_permutes_coinc bij
    by blast
  moreover have "thiele_structure.well_formed_profile V (committees A) ?p_agg" 
      using wf
      by (simp add: thiele_structure.well_formed_profile_def)
  moreover have "thiele_structure.well_formed_profile V (committees (\<pi> ` A)) ?q_agg" 
      using rename
      by (simp add: thiele_structure.well_formed_profile_def)
  ultimately have "(thiele_module w) V (committees (\<pi> ` A)) (?q_agg) = 
      rename_result (rename_alt_set \<pi>) ((thiele_module w) V (committees A) ?p_agg)"
    using thiele_structure.neutrality_prereq 
    by (metis id_def)
  thus "rename_alt_set \<pi> ` thiele_family w V A p = thiele_family w V (\<pi> ` A) (rename_alt_set \<pi> \<circ> p)" 
    using thiele_family_simp p_agg_eq q_agg_eq rename_result.simps w_valid
    by (metis image_Un split_pairs)
qed


subsubsection \<open>Continuity\<close>


lemma score_sum_by_bal:
fixes 
  w :: "Thiele_Score" and 
  V :: "'v set" and 
  p :: "('v, 'a Thiele_Ballot) Profile" and 
  c :: "'a Committee"
assumes 
  valid_w: "thiele_score w" and
  fin_V: "finite V"
shows "score_sum w V c p = (\<Sum>b\<in>range p. ((erat_of (card (bal_voters b p V)) * (w (b c)))))"
proof (unfold score_sum.simps)
let ?f = "\<lambda>v. w (p v c)"
let ?part = "{bal_voters b p V| b. b \<in> p ` V}"
have "finite ?part" 
  using fin_V 
  by simp
  moreover have "disjoint ?part"
  using ballots_partitions_voters partition_on_def 
  by blast
moreover have "\<forall>B \<in> ?part. finite B"
  using fin_V
  by auto
ultimately have "sum ?f (\<Union> ?part) = sum (sum ?f) ?part" 
  using disjoint_erat_sum
  by blast
moreover have *: "score_sum w V c p = sum ?f (\<Union> ?part)"
  using bal_voters_complete score_sum.elims
  by metis

have "\<forall>b \<in> p ` V. (\<Sum>v\<in>bal_voters b p V. w (p v c)) = erat_of (card (bal_voters b p V)) * w (b c)"
  using fin_V bal_voters_sum 
  by fast
hence "\<forall>b \<in> p ` V. (sum ?f (bal_voters b p V)) = erat_of (card (bal_voters b p V)) * (w (b c))" 
  by simp
moreover have "V = \<Union> ?part"
  using ballots_partitions_voters 
  by auto
hence "sum (sum ?f) ?part = (\<Sum>b\<in>range p. erat_of (card (bal_voters b p V)) * (w (b c)))"
sorry
hence ?thesis 
using * calculation by argo
  
  
hence "score_sum w V c p = (\<Sum>v \<in> (\<Union> ?part). w (p v c))"
  using ballots_partitions_voters 
  by fastforce 
 
thus "(\<Sum>v\<in>V. w (p v c)) = (\<Sum>b\<in>range p. erat_of (card (bal_votes b p V)) * w (b c))" 
sorry
(*
  let ?f = "\<lambda>v. w (p v c)"
  have "\<forall>b \<in> {bal_voters b p V| b. b \<in> p ` V}. finite b" 
  using ballots_partitions_voters partition_on_def disjoint_erat_sum by try
moreover have "(\<Sum>v \<in> (\<Union>{bal_voters b p V| b. b \<in> p ` V}). w (p v c)) = 
  (\<Sum> b \<in> p ` V. (\<Sum>v \<in> bal_voters b p V. w (p v c)))" 
  
  proof -
    have "disjoint {bal_voters b p V| b. b \<in> p ` V}" 
    using ballots_partitions_voters partition_on_def 
    by blast
    hence "\<forall>v \<in> V. \<exists>b \<in> p ` V. v \<in> bal_voters b p V \<and> (\<forall>b' \<in> p ` V. b \<noteq> b' \<longrightarrow> (v \<notin> bal_voters b' p V))"
    by simp
    moreover have "\<forall>b \<in> p` V. \<Sum>v \<in> bal_voters b p V. w (p v c)"
    hence ?thesis sorry
  oops *)
  oops

lemma score_sum_by_bal:
fixes 
  w :: "Thiele_Score" and 
  V :: "'v set" and 
  p :: "('v, 'a Thiele_Ballot) Profile" and 
  c :: "'a Committee"
assumes valid_w: "thiele_score w"
shows "score_sum w V c p = (\<Sum>b\<in>range p. ((of_nat (card (bal_votes b p V)) * (w (b c)))))"
proof (unfold score_sum.simps)
have "(\<Sum>v\<in>V. w (p v c)) = (\<Sum>v\<in>(\<Union>{bal_votes b p V | b. b \<in> range p}). w (p v c))" 
  using profile_partitions_voters 
  by metis
have "\<forall>b \<in> range p. \<bar>\<Sum>v\<in>(bal_votes b p V). (w (p v c))\<bar> \<noteq> \<infinity>" 
proof
  fix b :: "'a Thiele_Ballot"
  have "\<forall>v \<in> V. \<bar>w (p v c)\<bar> \<noteq> \<infinity>" using valid_w by simp
  moreover have "\<forall>S \<subseteq> V. \<forall> v \<in> V - S. \<bar>\<Sum>s\<in>S. w (p s c)\<bar> \<noteq> \<infinity> \<longrightarrow> \<bar>\<Sum>s\<in>S\<union>{v}. w (p s c)\<bar> \<noteq> \<infinity> " 
    using valid_w
    by (simp add: sum_Inf)
  ultimately have "\<forall>S \<subseteq> V. \<bar>\<Sum>s\<in>S. w (p s c)\<bar> \<noteq> \<infinity>" by (meson in_mono sum_Inf)
  moreover have "bal_votes b p V \<subseteq> V" by simp
  ultimately show "\<bar>\<Sum>v\<in>(bal_votes b p V). (w (p v c))\<bar> \<noteq> \<infinity>" by metis
qed
moreover have "\<forall>b \<in> range p. (\<Sum>v\<in>(bal_votes b p V). (w (p v c))) =  (\<Sum>v\<in>bal_votes b p V. (w (b c)))"
by simp
ultimately have "\<forall>b \<in> range p. rat_of_erat (\<Sum>v\<in>(bal_votes b p V). (w (p v c))) = 
    (card (bal_votes b p V)) * rat_of_erat (w (b c))"
proof (safe)
  fix b :: "'a Thiele_Ballot"
  have "\<forall>v \<in> bal_votes b p V. w (p v c) = rat_of_erat (w (p v c))" 
  using valid_w assms erat_rat
  by simp
  hence "\<forall>v \<in> bal_votes b p V. w (p v c) = 1 * rat_of_erat (w (b c))" by simp
  moreover have "(\<Sum>v\<in>(bal_votes b p V). rat_of_erat (w (b c))) = 
      (card (bal_votes b p V)) *  rat_of_erat (w (b c))" 
      by (simp add: of_rat_mult)
  ultimately have "(\<Sum>v\<in>(bal_votes b p V). rat_of_erat (w (p v c))) = 
    (card (bal_votes b p V)) * rat_of_erat (w (b c))" sorry
    thus "rat_of_erat (\<Sum>v\<in>(bal_votes b p V). (w (p v c))) = 
    (card (bal_votes b p V)) * rat_of_erat (w (b c))" sorry
oops

(*
lemma copy_score_simp:
fixes 
  V W :: "'v set" and
  C :: "('a Committee) set" and
  p q :: "('v, 'a Thiele_Ballot) Profile" and
  n :: nat and
  c :: "'a Committee"
assumes copy: "n_copy n V W p q"
shows "score_sum w W c q = erat_of n * score_sum w V c p"
proof (unfold erat_of.simps)
have "\<forall>b. card {v | v. v \<in> W \<and> q v = b} = n * card {v | v. v \<in> V \<and> p v = b}" using copy by simp
moreover have "score_sum w W c q = (\<Sum> b \<in> range q. (\<Sum> v \<in> {x | x. x \<in> W \<and> q x = b}. w (q v c)))"
proof (unfold score_sum.simps)
let ?b_votes = "\<lambda>b. {x |x. x \<in> W \<and> q x = b}"
have "\<forall>b \<in> range q. (\<Sum>v\<in> ?b_votes b. w (q v c)) =  (\<Sum>v\<in> ?b_votes b. w (b c))" by simp
hence "\<forall>b \<in> range q. (\<Sum>v\<in> ?b_votes b. w (q v c)) = erat_of (card (?b_votes b)) *  w (b c)" sorry
oops
oops
*)


lemma (in committee_result) thiele_module_continous:
fixes 
  w :: "nat Aggregate_Evaluation" 
assumes 
  w_valid: "thiele_score w"
shows "thiele_structure.continuity (thiele_module w)"
proof (unfold thiele_structure.continuity_def, clarify)
fix 
R :: "('a Committee) set" and
V V' :: "'v set" and
p q :: "('v, 'a Thiele_Ballot) Profile"
assume
wf: "thiele_structure.well_formed_profile V (id R) p" and
wf': "thiele_structure.well_formed_profile V' (id R) q" and
fin_R: "finite (id R)" and
fin_V: "finite V" and
fin_V': "finite V'" and
disjoint: "V \<inter> V' = {}"
let ?n = "4"
have " \<forall>W s. n_copy ?n V W p s \<longrightarrow>
          defer (thiele_module w) (W \<union> V') R (thiele_structure.joint_profile V' W q s)
          \<subseteq> defer (thiele_module w) V R p \<union> elect (thiele_module w) V R p \<and>
          elect (thiele_module w) (W \<union> V') R (thiele_structure.joint_profile V' W q s)
          \<subseteq> elect (thiele_module w) V R p"
  proof(safe)
    fix 
      W :: "'v set" and
      s :: "('v, 'a Thiele_Ballot) Profile" and
      c :: "'a Committee"
    assume 
      copy: "n_copy ?n V W p s" and
      def: "c \<in> defer (thiele_module w) (W \<union> V') R (thiele_structure.joint_profile V' W q s)" and
      not_elect: "c  \<notin> elect (thiele_module w) V R p"
      let ?e = "\<lambda> V r R p. score_sum w V r p"
      have "c \<in> defer (max_eliminator ?e) V R p" 
      using def thiele_module.elims
      by try
    moreover have "c \<in> R" 
      using thiele_mod_sound w_valid wf def thiele_structure.defer_in_conts
      sorry
    ultimately have "?e V c R p < Max {?e V x R p | x. x \<in> R}"
      using thiele_structure.defer_of_max_elim wf
      sorry
    have "score_sum w W c s = ?n * score_sum w V c p" 
      using copy 
      sorry
    moreover have "Max {?e W x R s | x. x \<in> R} = ?n * Max {?e V x R p | x. x \<in> R}" 
      using copy 
      sorry
    ultimately show "c \<in> defer (thiele_module w) V R p" 
    sorry

  next
    fix 
      W :: "'v set" and
      s :: "('v, 'a Thiele_Ballot) Profile" and
      c :: "'a Committee"
    assume 
      copy: "n_copy ?n V W p s" and
      elect: "c \<in> elect (thiele_module w) (W \<union> V') R (thiele_structure.joint_profile V' W q s)" and
      let ?e = "\<lambda> V r R p. score_sum w V r p"
      show "c \<in> elect (thiele_module w) V R p" sorry
  qed
thus "\<exists>n. \<forall>W s. n_copy n V W p s \<longrightarrow>
  defer (thiele_module w) (W \<union> V') R (thiele_structure.joint_profile V' W q s)
  \<subseteq> defer (thiele_module w) V R p \<union> elect (thiele_module w) V R p \<and>
  elect (thiele_module w) (W \<union> V') R (thiele_structure.joint_profile V' W q s)
  \<subseteq> elect (thiele_module w) V R p"
  by blast  
oops

subsubsection \<open>Independence of Losers\<close>

subsubsection \<open>Axiomatic Characterization of Thiele Methods\<close>

end
end