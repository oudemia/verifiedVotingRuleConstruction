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
(*"thiele_ballot R b = (\<forall> r. b r \<ge> 0 \<and> (r \<notin> R \<longrightarrow> b r = 0))" unnecessary because nat *)

fun thiele_result :: "('a Committee) set \<Rightarrow> ('a Committee) Result \<Rightarrow> bool" where
"thiele_result R r = (disjoint3 r \<and> set_equals_partition R r)"

fun (in committee_result) thiele_aggregate :: "('a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate b W = (card (W \<inter> b))"

fun (in committee_result) thiele_agg_profile :: "('v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile p v W = thiele_aggregate (p v) W"

fun (in committee_result) thiele_agg_prof :: "('a, 'v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation'" where
"thiele_agg_prof A p v W = (if W \<in> committees A then (card (W \<inter> (p v))) else 0)"


sublocale committee_result \<subseteq> thiele_aggregation:
aggregation
"\<lambda> C. 0" (*empty ballot*) 
"\<lambda> b C D. (b C > b D)" (*prefers*)
"\<lambda> b C. (\<forall> D. b C \<ge> b D)" (*wins*)
"\<lambda> C b c. if c \<in> C then b c else 0" (* limit_ballot"\<lambda> C b. b" *)
thiele_ballot (*well formed ballot*)
ballot_\<A>\<V> (*base ballot*)
committees
"\<lambda> A b C. if C \<in> committees A then (card (C \<inter> b)) else 0" (*agg*)
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
  thus "thiele_ballot (committees A) (\<lambda>C. if C  \<in> committees A then card (C \<inter> b) else 0)"
  proof (unfold thiele_aggregate.simps thiele_ballot.simps, safe)
    fix r :: "'a Committee" 
    assume nocom: "r \<notin> committees A" 
    thus "(if r \<in> committees A then card (r \<inter> b) else 0) = 0" by presburger
  qed
qed

sublocale committee_result \<subseteq> thiele_structure:
  electoral_structure "\<lambda>C. 0" "\<lambda> b C D. (b C > b D)" "\<lambda> b C. (\<forall> D. b C \<ge> b D)" 
  "\<lambda> C b c. if c \<in> C then b c else 0" id "\<lambda> R S. R \<inter> S" id "thiele_ballot" "\<lambda> A r. disjoint3 r" 
  "\<lambda> C b c. if c \<in> C then b c else 0"
proof (unfold_locales, auto)
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
	elect (thiele_module w) V (committees A) (thiele_agg_profile p)"

fun (in committee_result) thiele_family' :: "('a, 'v, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where
"thiele_family' w V A p =
	thiele_structure.elector\<^sub>d (thiele_module w) V (committees A) (thiele_agg_prof A p)"

fun thiele_method :: "Thiele_Score \<Rightarrow> ('a, 'v, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where
"thiele_method w r = thiele_score w"


subsection \<open>Properties\<close>

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


lemma (in committee_result) thiele_module_anonymous:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "thiele_structure.anonymity (thiele_module w)"
proof (unfold thiele_structure.anonymity_def Let_def, safe)
  show "thiele_structure.electoral_module (thiele_module w)" by simp
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
  have *: "\<forall>C \<in> R. (?e V C R p) = (?e V' C R q)"
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
proof (unfold \<A>\<V>_committee.vr_anonymity_def, simp add: Let_def)
qed

lemma (in committee_result) thiele'_anonymous:
  fixes w :: "nat Aggregate_Evaluation"
  assumes w_valid: "thiele_score w"
  shows "\<A>\<V>_committee.vr_anonymity (thiele_family' w)"
proof (unfold \<A>\<V>_committee.vr_anonymity_def Let_def, safe)
  fix 
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('v, 'a Approval_Set) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    C :: "'a Committee"
  assume 
    bij: "bij \<pi>" and
    rename: "\<A>\<V>_committee.rename \<pi> (A, V, p) = (A', V', q)" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    fin_V': "finite V'" and
    win: "C \<in> thiele_family' w V A p"
  have A_eq: "A' = A" using rename by simp
  let ?R = "committees A"  
  let ?R' = "committees A'"
  have fin_R: "finite ?R" using fin_A by simp  
  have R_eq: "?R = ?R'" using A_eq by simp
  let ?p_agg = "(\<lambda>b c. if c \<in> id ?R then b c else 0) \<circ> (thiele_agg_prof A p)"
  let ?q_agg = "(\<lambda>b c. if c \<in> id ?R' then b c else 0) \<circ> (thiele_agg_prof A' q)"
  have p_agg_eq: "?p_agg = (thiele_agg_prof A p)" by fastforce
  have q_agg_eq: "?q_agg = (thiele_agg_prof A' q)" by fastforce
  have mod_anon: "thiele_structure.anonymity (thiele_module w)"
    using thiele_module_anonymous w_valid 
    by auto
  moreover have rename_res: "thiele_aggregation.rename \<pi> (?R, V, (thiele_agg_prof A p)) =
      (?R', V', (thiele_agg_prof A' q))"
    using rename thiele_aggregation.aggregate_preserves_permute 
    by fastforce
  moreover have fp_res: "thiele_aggregation.finite_profile V (id ?R) (thiele_agg_prof A p)"
    using fin_V fin_R thiele_aggregation.preserve_valid
    by (simp add: thiele_aggregation.well_formed_profile_def)
  moreover have "thiele_aggregation.finite_profile V (id ?R') (thiele_agg_prof A' q)"
    using fin_V fin_R R_eq thiele_aggregation.preserve_valid
    by (simp add: thiele_aggregation.well_formed_profile_def)
  ultimately have "(thiele_module w) V ?R (thiele_agg_prof A p) =
    (thiele_module w) V' ?R' (thiele_agg_prof A' q)"
    using bij thiele_structure.anonymity_prereq
    by (metis A_eq fin_V' id_apply thiele_aggregation.rename_sound)
  hence "(thiele_module w) V (id ?R) ?p_agg = (thiele_module w) V' (id ?R') ?q_agg"
    using p_agg_eq q_agg_eq by simp
  moreover have "C \<in> thiele_structure.elector\<^sub>d (thiele_module w) V ?R (thiele_agg_prof A p)"
    using thiele_family'.elims win 
    by blast
  ultimately have "C \<in> thiele_structure.elector\<^sub>d (thiele_module w) V' ?R' (thiele_agg_prof A' q)"
    by simp
  thus "C \<in> thiele_family' w V' A' q" by simp
next 
  fix 
    A A' :: "'a set" and
    V V' :: "'v set" and
    p q :: "('v, 'a Approval_Set) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v" and
    C :: "'a Committee"
  assume 
    bij: "bij \<pi>" and
    rename: "\<A>\<V>_committee.rename \<pi> (A, V, p) = (A', V', q)" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    fin_V': "finite V'" and
    win: "C \<in> thiele_family' w V' A' q"
  have A_eq: "A' = A" using rename by simp
  let ?R = "committees A"  
  let ?R' = "committees A'"
  have fin_R: "finite ?R" using fin_A by simp  
  have R_eq: "?R = ?R'" using A_eq by simp
  let ?p_agg = "(\<lambda>b c. if c \<in> id ?R then b c else 0) \<circ> (thiele_agg_prof A p)"
  let ?q_agg = "(\<lambda>b c. if c \<in> id ?R' then b c else 0) \<circ> (thiele_agg_prof A' q)"
  have p_agg_eq: "?p_agg = (thiele_agg_prof A p)" by fastforce
  have q_agg_eq: "?q_agg = (thiele_agg_prof A' q)" by fastforce
  have mod_anon: "thiele_structure.anonymity (thiele_module w)"
    using thiele_module_anonymous w_valid 
    by auto
  moreover have rename_res: "thiele_aggregation.rename \<pi> (?R, V, (thiele_agg_prof A p)) =
      (?R', V', (thiele_agg_prof A' q))"
    using rename thiele_aggregation.aggregate_preserves_permute 
    by fastforce
  moreover have fp_res: "thiele_aggregation.finite_profile V (id ?R) (thiele_agg_prof A p)"
    using fin_V fin_R thiele_aggregation.preserve_valid
    by (simp add: thiele_aggregation.well_formed_profile_def)
  moreover have "thiele_aggregation.finite_profile V (id ?R') (thiele_agg_prof A' q)"
    using fin_V fin_R R_eq thiele_aggregation.preserve_valid
    by (simp add: thiele_aggregation.well_formed_profile_def)
  ultimately have "(thiele_module w) V ?R (thiele_agg_prof A p) =
    (thiele_module w) V' ?R' (thiele_agg_prof A' q)"
    using bij thiele_structure.anonymity_prereq
    by (metis A_eq fin_V' id_apply thiele_aggregation.rename_sound)
  hence "(thiele_module w) V (id ?R) ?p_agg = (thiele_module w) V' (id ?R') ?q_agg"
    using p_agg_eq q_agg_eq by simp
  moreover have "C \<in> thiele_structure.elector\<^sub>d (thiele_module w) V' ?R' (thiele_agg_prof A' q)"
    using thiele_family'.elims win 
    by blast
  ultimately have "C \<in> thiele_structure.elector\<^sub>d (thiele_module w) V ?R (thiele_agg_prof A p)"
    by simp
  thus "C \<in> thiele_family' w V A p" by simp
qed


subsubsection \<open>Neutrality\<close>

fun rename_committee :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a Committee) set => ('a Committee) set" where
"rename_committee \<pi> R = 
      (let \<pi>' = (\<lambda>C. \<pi> ` C) in \<pi>' ` R)"

fun rename_alts_\<A>\<V> :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'v, 'a Approval_Set) Election \<Rightarrow> ('a, 'v, 'a Approval_Set) Election" where
  "rename_alts_\<A>\<V> \<pi> (A, V, p) = (let q = (\<lambda>v. \<pi> ` (p v)) in (\<pi> ` A, V, q))"

lemma (in committee_result) rename_distr:
  fixes 
    A :: "'a set" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assumes bij: "bij \<pi>"
  shows "committees (\<pi> ` A) = rename_committee \<pi> (committees A)"
proof safe
  fix C :: "'a Committee"
  assume "C \<in> committees (\<pi> ` A)"
  hence comm_C: "C \<subseteq> \<pi> ` A \<and> card C = k" by simp
  hence "\<exists>D \<subseteq> A. C = \<pi> ` D" by (meson subset_imageE)
  then obtain D where comm_D: "D \<subseteq> A \<and> C = \<pi> ` D" by blast
  hence "card D = k" using comm_C bij by (metis bij_betw_def bij_betw_subset card_image top_greatest)
  hence "D \<in> committees A" using comm_D by simp
  thus "C \<in> rename_committee \<pi> (committees A)" by (metis comm_D imageI rename_committee.elims)
next
  fix C :: "'a Committee"
  assume "C \<in> rename_committee \<pi> (committees A)"
  hence "\<exists>D \<in> committees A. C = \<pi> ` D" by auto
  then obtain D where comm_D: "D \<in> committees A \<and> C = \<pi> ` D" by blast
  hence "card D = k" by simp
  hence card: "card C = k" using comm_D bij by (metis bij_betw_def card_vimage_inj inj_vimage_image_eq top_greatest)
  have "C \<subseteq> \<pi> ` A" using comm_D bij by auto
  thus "C \<in> committees (\<pi> ` A)" using card by simp
qed

definition neutrality_\<A>\<B>\<C> :: "('v, 'a, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where 
  "neutrality_\<A>\<B>\<C> r \<equiv>
      (\<forall> A V p \<pi>::('a \<Rightarrow> 'a).
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename_alts_\<A>\<V> \<pi> (A, V, p)) in
            \<A>\<V>_profile.finite_profile V A p \<and> \<A>\<V>_profile.finite_profile V' A' q \<longrightarrow> r V A p = r V' A' q))"

lemma (in committee_result) thiele_neutral:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "neutrality_\<A>\<B>\<C> (thiele_family w)"
  unfolding neutrality_\<A>\<B>\<C>_def by simp

subsubsection \<open>Consistency\<close>

subsubsection \<open>Continuity\<close>

subsubsection \<open>Independence of Losers\<close>

subsubsection \<open>Axiomatic Characterization of Thiele Methods\<close>


end