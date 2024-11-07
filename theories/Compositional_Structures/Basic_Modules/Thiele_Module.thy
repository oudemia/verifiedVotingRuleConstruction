section \<open>Thiele Module\<close>

theory Thiele_Module
  imports 
      "Component_Types/Voting_Rule"      
      "Component_Types/Elimination_Module"
      "Component_Types/Social_Choice_Types/Aggregate_Profile"
      "Component_Types/Social_Choice_Types/Electoral_Structure"
begin

subsection \<open>Definition\<close>

subsubsection \<open>Aggregated Profiles for Thiele Methods\<close>

type_synonym 'a Thiele_Ballot = "'a Committee \<Rightarrow> nat"

fun thiele_ballot :: "('a Committee) set \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> bool" where
"thiele_ballot R b = (\<forall> r. r \<notin> R \<longrightarrow> b r = 0)"

fun (in committee_result) thiele_aggregate :: 
  "('a, 'a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate A b C = (if C \<in> committees A then (card (C \<inter> b)) else 0)"

fun (in committee_result) thiele_agg_profile :: 
  "('a, 'v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile A p v C = thiele_aggregate A (p v) C"

fun limit_thiele_ballot :: "('a Committee) set \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> 'a Thiele_Ballot" where
"limit_thiele_ballot C b c = (if c \<in> C then b c else 0)"

sublocale committee_result \<subseteq> thiele_aggregation:
aggregation
  "\<lambda> C. 0" (*empty ballot*) 
  "\<lambda> b C D. (b C > b D)" (*prefers*)
  "\<lambda> b C. (\<forall> D. b C \<ge> b D)" (*wins*)
  "\<lambda> C b c. if c \<in> C then b c else 0" (* limit_ballot"\<lambda> C b. b" *)
  thiele_ballot (*well formed ballot*)
  ballot_\<A>\<V> (*base ballot*)
  committees
  thiele_aggregate (*agg*)
proof (unfold_locales)
  fix 
    c1 c2 :: "'a Committee" and 
    b :: "'a Committee \<Rightarrow> nat"
  assume *: "c1 \<noteq> c2 \<and> b c2 < b c1"
  thus "\<not> (\<forall>D. b D \<le> b c2)" using leD by blast
next
  fix 
    R :: "('a Committee) set" and
    b :: "'a Committee \<Rightarrow> nat"
  assume bal: "thiele_ballot R b"
  hence *: "\<forall>r. r \<notin> R \<longrightarrow> b r = 0" using thiele_ballot.simps by simp
  moreover have "\<forall>r. if r \<in> R then b r = b r else b r = 0"
  proof (simp split: if_splits, standard)
    fix r :: "'a Committee"
    show "r \<notin> R \<longrightarrow> b r = 0 " using * by blast
  qed
  ultimately show "(\<lambda>c. if c \<in> R then b c else 0) = b" by auto
next
  fix 
    R S :: "('a Committee) set" and
    b :: "'a Committee \<Rightarrow> nat"
  assume sub: "R \<subseteq> S"
  thus "(\<lambda>c. if c \<in> R then b c else 0) = (\<lambda>c. if c \<in> R then if c \<in> S then b c else 0 else 0)"
  by fastforce
next
  fix 
    R S :: "('a Committee) set" and
    b :: "'a Committee \<Rightarrow> nat"
  assume *: "thiele_ballot S b \<and> R \<subseteq> S"
  thus "thiele_ballot R (\<lambda>c. if c \<in> R then b c else 0)" by simp
next
  fix 
    A :: "'a set" and
    b :: "'a Approval_Set"
  assume bal: "ballot_\<A>\<V> A b"
  thus "thiele_ballot (committees A) (thiele_aggregate A b)"
  proof (unfold thiele_aggregate.simps thiele_ballot.simps, safe)
    fix r :: "'a Committee" 
    assume nocom: "r \<notin> committees A" 
    thus "(if r \<in> committees A then card (r \<inter> b) else 0) = 0" by presburger
  qed
qed

sublocale committee_result \<subseteq> thiele_structure:
electoral_structure 
  "\<lambda>C. 0" (* empty_ballot *)
  "\<lambda> b C D. (b C > b D)" (* prefers *)
  "\<lambda> b C. (\<forall> D. b C \<ge> b D)" (* wins *)
  limit_thiele_ballot (* limit_ballot *)
  "\<lambda> R S. R \<inter> S" (* limit_contenders *)
  id (*  affected_alts *)
  thiele_ballot (* well_formed_ballot *)
  id (* contenders *)
  limit_thiele_ballot (* limit_by_conts *)
proof (unfold_locales, clarify)
  fix 
    b :: "'a Thiele_Ballot" and
    C D :: "'a Committee"
  assume  
    "C \<noteq> D" and  
    *: "b D < b C" and 
    **: "\<forall>E. b E \<le> b D"
  show "False"
    using * ** linorder_not_less 
    by blast
next
  fix 
    C :: "('a Committee) set" and
    b :: "'a Thiele_Ballot"
  show "thiele_ballot C b \<Longrightarrow> limit_thiele_ballot C b = b" by auto
next
  fix 
    C D :: "('a Committee) set" and
    b :: "'a Thiele_Ballot"
  assume "C \<subseteq> D"
  thus "limit_thiele_ballot C b = limit_thiele_ballot C (limit_thiele_ballot D b)" by fastforce
next
  fix 
    C D :: "('a Committee) set" and
    b :: "'a Thiele_Ballot"
  assume "thiele_ballot D b \<and> C \<subseteq> D"
  thus "thiele_ballot C (limit_thiele_ballot C b)" by simp
next
  fix C :: "('a Committee) set"
  show "id (id C) = C \<or> id (id C) = {}" by simp
next
  fix 
    C D :: "('a Committee) set"
  show "C \<subseteq> D \<longrightarrow> id C \<subseteq> id D" by simp
next
  fix 
    C :: "('a Committee) set" and
    b :: "'a Thiele_Ballot"
  show "limit_thiele_ballot C b = limit_thiele_ballot (id C) b " by simp
next
  fix C :: "('a Committee) set"
  show "C \<noteq> {} \<and> id (id C) = {} \<longrightarrow> id C = {}" by simp
qed


subsubsection \<open>Evaluation of Aggregated Profiles\<close>

type_synonym Thiele_Score = "nat Aggregate_Evaluation"

fun thiele_score :: "Thiele_Score \<Rightarrow> bool" where
"thiele_score w = (w 0 = 0 \<and> mono w)"

fun score_sum :: "Thiele_Score \<Rightarrow> 'v set \<Rightarrow> 'a Committee \<Rightarrow> ('v, 'a Thiele_Ballot) Profile \<Rightarrow> erat" where
"score_sum s V C p = (\<Sum> v \<in> V. s (p v C))"


subsubsection \<open>Electoral Module for Thiele Methods\<close>

fun thiele_module :: "Thiele_Score \<Rightarrow> ('a Committee, 'v, 'a Thiele_Ballot) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R p. score_sum s V r p)) V C p"

fun (in committee_result) thiele_family :: "('a, 'v, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where
"thiele_family w V A p =
	thiele_structure.elector\<^sub>d (thiele_module w) V (committees A) (thiele_agg_profile A p)"

fun thiele_method :: "Thiele_Score \<Rightarrow> ('a, 'v, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where
"thiele_method w r = thiele_score w"


subsection \<open>Properties\<close>

lemma (in committee_result) thiele_mod_sound[simp]:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "thiele_structure.electoral_module (thiele_module w)"
by auto


lemma (in committee_result) thiele_family_simp [simp]:
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

lemma sum_bij:
fixes 
  \<pi> :: "'v \<Rightarrow> 'v" and 
  f :: "'v \<Rightarrow> erat" and
  V V' :: "'v set"
assumes 
  bij: "bij \<pi>" and
  perm: "V' = \<pi> ` V"
shows "(\<Sum>v\<in>V. f v) = (\<Sum>v\<in>V'. (f \<circ> the_inv \<pi>) v)"
  proof -
  have "(\<Sum>v\<in>V. f v) = (\<Sum>v\<in>V. (f \<circ> the_inv \<pi>) (\<pi> v))" 
    using bij
    by (metis bij_betw_imp_inj_on comp_eq_dest_lhs id_apply the_inv_f_o_f_id)
  hence "(\<Sum>v\<in>V. f v) = (\<Sum>v\<in>(\<pi> ` V). (f \<circ> the_inv \<pi>) v)"
    by (metis (no_types, lifting) bij bij_betw_def bij_betw_subset sum.reindex_cong top_greatest)
  thus ?thesis using perm by simp
qed

(*
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

*)
subsubsection \<open>Neutrality\<close>

fun rename_committee :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a Committee) set => ('a Committee) set" where
"rename_committee \<pi> R = (`) ((`) \<pi>) R"

fun rename_alts_\<A>\<V> :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'v, 'a Approval_Set) Election \<Rightarrow> ('a, 'v, 'a Approval_Set) Election" where
  "rename_alts_\<A>\<V> \<pi> (A, V, p) = (let q = (\<lambda>v. \<pi> ` (p v)) in (\<pi> ` A, V, q))"

fun rename_alt_set :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "rename_alt_set \<pi> C = \<pi> ` C"

fun rename_thiele_ballot :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> 'a Thiele_Ballot" where
  "rename_thiele_ballot \<pi> b C =  b (the_inv \<pi> ` C)"

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
  assumes "bij \<pi>"
  shows "the_inv (rename_alt_set \<pi>) = (rename_alt_set (the_inv \<pi>))" 
  sorry


lemma (in committee_result) thiele_permutes_coinc:
fixes 
  V :: "'v set" and
  \<pi> :: "'a \<Rightarrow> 'a"
assumes 
  bij: "bij \<pi>"
shows "thiele_aggregation.coinciding_permutes V \<pi> (rename_alt_set \<pi>) (rename_alt_set \<pi>)"
proof (unfold thiele_aggregation.coinciding_permutes.simps, clarify)
fix 
  A :: "'a set" and
  p :: "('v, 'a Approval_Set) Profile" and 
  v :: 'v
assume elem: "v \<in> V"
  let ?q = "(rename_alt_set \<pi> \<circ> p)"
  let ?p_agg = "thiele_aggregation.aggregate_profile A p"
  let ?q_agg = "thiele_aggregation.aggregate_profile (\<pi> ` A) ?q"
  have card_pres: "\<forall>S. card S = card (\<pi> ` S)" 
    using bij
    by (metis bij_betw_imp_inj_on bij_betw_same_card inj_imp_bij_betw_inv)
  hence "\<forall>C \<in> committees A. card (C \<inter> p v) = card ((\<pi> ` C) \<inter> (\<pi> ` (p v)))"
    using bij 
    by (metis bij_def image_Int)
  hence "\<forall>C \<in> committees A. card (C \<inter> p v) = card ((\<pi> ` C) \<inter> (rename_alt_set \<pi> \<circ> p) v)" 
    by simp
  moreover have *: "\<forall>C. C \<in> committees A \<longleftrightarrow> rename_alt_set \<pi> C \<in> committees (\<pi> ` A)" 
    unfolding committees.simps 
    using bij card_pres vimage_subset_eq 
    by fastforce
  moreover have "\<forall>C. C \<notin> committees A \<longrightarrow> ?q_agg v (\<pi> ` C) = 0" 
    using * 
    by simp 
  ultimately have "\<forall>C. ?q_agg v (\<pi> ` C) = ?p_agg v C" by simp
  thus "thiele_aggregate (\<pi> ` A) ((rename_alt_set \<pi> \<circ> p) v) \<circ> rename_alt_set \<pi> =
       thiele_aggregate A (p v)" by auto
qed

lemma (in committee_result) thiele_permutes_coinc':
fixes 
  \<pi> :: "'a \<Rightarrow> 'a"
assumes 
  bij: "bij \<pi>"
shows "thiele_aggregation.coinciding_permutes' \<pi> (rename_alt_set \<pi>) (rename_alt_set \<pi>)"
proof (unfold thiele_aggregation.coinciding_permutes'.simps, standard+)
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

(*
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
    sub: "S \<subseteq> A" and have rename_bij: "bij (rename_alt_set \<pi>)" 
      using bij
      by (metis Pow_UNIV bij_betw_Pow bij_betw_cong rename_alt_set.elims)
    comm: "C \<in> committees A"
  have "rename_alt_set \<pi> C = \<pi> ` C" by simp
  hence "{r \<inter> \<pi> ` S |r. r \<in> {rename_alt_set \<pi> C}} = {\<pi> ` S \<inter> \<pi> ` C}" by auto
  moreover have "rename_alt_set \<pi> ` {r \<inter> S |r. r \<in> {C}} = {\<pi> ` (S \<inter> C)}" by auto
  moreover have "\<pi> ` S \<inter> \<pi> ` C = \<pi> ` (S \<inter> C)" by (simp add: bij bij_is_inj image_Int)
  ultimately show "{r \<inter> \<pi> ` S |r. r \<in> {rename_alt_set \<pi> C}} = 
    rename_alt_set \<pi> ` {r \<inter> S |r. r \<in> {C}}" by simp
qed
*)

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
  show "bij (rename_alt_set \<pi>)" using bij rename_inherits_bij by auto
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
          by (metis (no_types) Voting_Rule.bij_id bij bij_betw_def bij_betw_id image_comp)
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


lemma (in committee_result) thiele_neutral:
  fixes 
    w :: "nat Aggregate_Evaluation" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes w_valid: "thiele_score w" and bij: "bij \<pi>"
  shows "\<A>\<V>_committee.vr_neutrality' \<pi> (rename_alt_set \<pi>) (rename_alt_set \<pi>) (thiele_family w)"
proof (unfold \<A>\<V>_committee.vr_neutrality'_def Let_def, clarify)
  fix 
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Approval_Set) Profile"
  assume
    coinc_bal: "\<A>\<V>_committee.coinciding_bal_permute A \<pi> (rename_alt_set (the_inv \<pi>))" and
    coinc_cont: "\<A>\<V>_committee.coinciding_cont_permute A \<pi> (rename_alt_set \<pi>)" and
    fin_A: "finite A" and
    "finite (\<pi> ` A)" and
    fin_V: "finite V" and
    wf: "\<A>\<V>_committee.well_formed_profile V A p" and
    rename: "\<A>\<V>_committee.well_formed_profile V (\<pi> ` A) (rename_alt_set (the_inv \<pi>) \<circ> p)"
  
  let ?R = "committees A"
  let ?R' = "committees (\<pi> ` A)"
  have fin_R: "finite ?R" using fin_A by simp
  have R_eq: "?R' = (rename_alt_set \<pi>) ` ?R" using rename_distr bij by blast

  let ?q = "(rename_alt_set (the_inv \<pi>)) \<circ> p"
  let ?q_agg = "thiele_aggregation.aggregate_profile (\<pi> ` A) ?q"
  let ?p_agg = "thiele_aggregation.aggregate_profile A p"
  let ?res = "rename_result (rename_alt_set \<pi>) (thiele_module w V ?R ?p_agg)"

  have p_agg_eq: "?p_agg = thiele_agg_profile A p" by fastforce
  have q_agg_eq: "?q_agg = thiele_agg_profile (\<pi> ` A) ?q" by fastforce

  (*
  hence "\<forall>v \<in> V. (?q_agg v) = permute_agg_ballot (rename_alt_set \<pi>) ((?p_agg) v)"
    using thiele_permutes_coinc wf bij rename_inherits_bij inv_rename
      thiele_aggregation.agg_preserves_alt_rename
    by (metis \<A>\<V>_profile.well_formed_profile_def thiele_aggregation.well_formed_base_profile_def)
  hence "\<forall>v \<in> V. (?q_agg v) = permute_agg_ballot (rename_alt_set (the_inv \<pi>)) ((?p_agg) v)"
    using inv_rename bij 
    by metis
  hence "\<forall>v \<in> V. (?q_agg v) = ((?p_agg) v) \<circ> (rename_alt_set (the_inv \<pi>))"
    by auto
  hence "\<forall>v \<in> V. ?q_agg v = (rename_thiele_ballot \<pi> \<circ> ?p_agg) v" 
  by auto
  *)
  have "?p_agg = permute_agg_profile (rename_alt_set \<pi>) ?q_agg"
 using thiele_permutes_coinc' p_agg_eq q_agg_eq bij  by try
      
  moreover have mod_neutr:
    "thiele_structure.neutrality (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>) (thiele_module w)"
    using thiele_module_neutral w_valid bij
    by auto
    moreover have "thiele_aggregation.finite_profile V ?R ?p_agg" using wf fin_V fin_R 
    by (simp add: thiele_structure.well_formed_profile_def)

moreover have "thiele_aggregation.finite_profile V ?R' ?q_agg" using * sorry
  ultimately have "rename_result (rename_alt_set \<pi>) (thiele_module w V ?R ?p_agg) = 
      (thiele_module w) V ?R' (rename_thiele_ballot \<pi> \<circ> ?p_agg)" 
   using w_valid thiele_mod_sound bij fin_A fin_V thiele_permutes_coinc sorry
  (* "?res = thiele_module w V ?R' ?q_agg" *)
   
   hence "rename_result (rename_alt_set \<pi>) (thiele_module w V ?R ?p_agg) = 
thiele_module w V ?R' ?q_agg" 
  using w_valid bij by simp
  hence "rename_alt_set \<pi> ` defer_r (thiele_module w V ?R ?p_agg) = 
defer_r (thiele_module w V ?R' ?q_agg)" 
  using rename_result.simps
  by (metis prod.collapse snd_conv)
  moreover have "rename_alt_set \<pi> ` elect_r (thiele_module w V ?R ?p_agg) = 
    elect_r (thiele_module w V ?R' ?q_agg)"
by simp
ultimately show "(rename_alt_set \<pi>) ` (thiele_family w V A p) =
       thiele_family w V (\<pi> ` A) ?q" 
       using rename_alt_set.simps q_agg_eq p_agg_eq thiele_family_simp
       by (metis image_Un w_valid)
oops
    
subsubsection \<open>Consistency\<close>

subsubsection \<open>Continuity\<close>

subsubsection \<open>Independence of Losers\<close>

subsubsection \<open>Axiomatic Characterization of Thiele Methods\<close>


end