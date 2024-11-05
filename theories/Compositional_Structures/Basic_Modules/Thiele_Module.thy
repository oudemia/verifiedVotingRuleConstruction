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

fun limit_thiele_ballot :: "('a Committee) set \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> 'a Thiele_Ballot" where
"limit_thiele_ballot C b c = ( if c \<in> C then b c else 0)"

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
	thiele_structure.elector\<^sub>d (thiele_module w) V (committees A) (thiele_agg_prof A p)"

fun thiele_method :: "Thiele_Score \<Rightarrow> ('a, 'v, 'a Approval_Set, 'a Committee) Voting_Rule \<Rightarrow> bool" where
"thiele_method w r = thiele_score w"


subsection \<open>Properties\<close>

lemma (in committee_result) thiele_mod_sound[simp]:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "thiele_structure.electoral_module (thiele_module w)"
by auto


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
  let ?p_agg = "(limit_thiele_ballot ?R) \<circ> (thiele_agg_prof A p)"
  let ?q_agg = "(limit_thiele_ballot ?R') \<circ> (thiele_agg_prof A' q)"
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
  hence "(thiele_module w) V ?R ?p_agg = (thiele_module w) V' ?R' ?q_agg"
  using p_agg_eq q_agg_eq by simp
  thus "thiele_family w V A p =  thiele_family w V' A' q" 
    by simp
qed

*)
subsubsection \<open>Neutrality\<close>

fun rename_committee :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a Committee) set => ('a Committee) set" where
"rename_committee \<pi> R = 
      (let \<pi>' = (\<lambda>C. \<pi> ` C) in \<pi>' ` R)"

fun rename_alts_\<A>\<V> :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a, 'v, 'a Approval_Set) Election \<Rightarrow> ('a, 'v, 'a Approval_Set) Election" where
  "rename_alts_\<A>\<V> \<pi> (A, V, p) = (let q = (\<lambda>v. \<pi> ` (p v)) in (\<pi> ` A, V, q))"

fun rename_alt_set :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "rename_alt_set \<pi> C = \<pi> ` C"

fun rename_thiele_ballot :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a Thiele_Ballot \<Rightarrow> 'a Thiele_Ballot" where
  "rename_thiele_ballot \<pi> b C =  b (the_inv \<pi> ` C)"

(*
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
*)

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

(*
lemma (in committee_result) thiele_module_neutral':
  fixes w :: "nat Aggregate_Evaluation" and \<pi> :: "'a \<Rightarrow> 'a"
  assumes "thiele_score w" and bij: "bij \<pi>"
  shows "thiele_structure.neutrality'' (rename_alt_set \<pi>) (thiele_module w)"
proof (unfold thiele_structure.neutrality''_def Let_def, safe)
  show "thiele_structure.electoral_module (thiele_module w)" by auto
next
  show "bij (rename_alt_set \<pi>)" 
    using bij
    by (metis Pow_UNIV bij_betw_Pow bij_betw_cong rename_alt_set.elims)
next
oops
*)

lemma (in committee_result) thiele_module_neutral:
fixes 
  w :: "nat Aggregate_Evaluation" and 
  \<pi> :: "'a \<Rightarrow> 'a"
assumes 
  w_valid: "thiele_score w" and 
  bij: "bij \<pi>"
shows "thiele_structure.neutrality' (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>) (thiele_module w)"
proof (unfold thiele_structure.neutrality'_def Let_def, safe)
  show "thiele_structure.electoral_module (thiele_module w)" by auto
next
  show "bij (rename_alt_set \<pi>)" 
    using bij
    by (metis Pow_UNIV bij_betw_Pow bij_betw_cong rename_alt_set.elims)
next
  fix 
    R :: "('a Committee) set" and 
    V :: "'v set" and 
    p :: "('v, 'a Thiele_Ballot) Profile"    
  assume
    coinc: "thiele_structure.coinciding_permutes R (rename_alt_set \<pi>) (rename_thiele_ballot \<pi>)"and   
    "finite (id R)" and 
    "finite (id (rename_alt_set \<pi> ` R))" and
    "finite V" and
    wf: "thiele_structure.well_formed_profile V (id R) p" and 
    "thiele_structure.well_formed_profile V (id (rename_alt_set \<pi> ` R)) (rename_thiele_ballot \<pi> \<circ> p)"
  let ?R = "rename_alt_set \<pi> ` R"
  let ?q = "rename_thiele_ballot \<pi> \<circ> p"
  let ?e = "\<lambda> V r R p. score_sum w V r p"
  let ?max = "(Max {?e V x R p | x. x \<in> R})" 
  let ?max' = "(Max {?e V x ?R ?q | x. x \<in> ?R})"
  let ?res = "thiele_structure.rename_result (rename_alt_set \<pi>) (thiele_module w V R p)"
  have rename_bij: "bij (rename_alt_set \<pi>)" 
      using bij
      by (metis Pow_UNIV bij_betw_Pow bij_betw_cong rename_alt_set.elims)
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
  hence *: "\<forall>C \<in> R. (?e V C R p) = (?e V (rename_alt_set \<pi> C) ?R ?q)" by simp
  hence "\<forall>n. rename_alt_set \<pi> ` {C | C. C \<in> R \<and> (?e V C R p < n)} = 
    {C | C. C \<in> ?R \<and> (?e V C ?R ?q < n)}"
    by auto        
  hence "rename_alt_set \<pi> ` {C | C. C \<in> R \<and> (?e V C R p < ?max)} = 
    {C | C. C \<in> ?R \<and> (?e V C ?R ?q < ?max)}"
    by simp   
  moreover have max_eq: "?max = ?max'" 
    using *
    by (metis (no_types, opaque_lifting) imageE imageI)
  ultimately have set_eq: "rename_alt_set \<pi> `(elimination_set ?e ?max (<) V R p) = 
    elimination_set ?e ?max' (<) V ?R ?q" 
    by simp  
  have elect_eq: "elect (thiele_module w) V ?R ?q = elect_r ?res" by simp
  have defer_eq: "defer (thiele_module w) V ?R ?q = defer_r ?res"
  proof (cases)
    assume **:"(elimination_set ?e ?max (<) V R p) = R"
    hence ***: "(elimination_set ?e ?max' (<) V ?R ?q) = ?R"
      using set_eq
      by presburger
    hence "defer (thiele_module w) V ?R ?q = ?R" 
      using thiele_structure.result_presv_conts thiele_structure.max_elim_non_electing 
      by simp
    moreover have "defer (thiele_module w) V R p = R" 
      using thiele_structure.result_presv_conts thiele_structure.max_elim_non_electing **
      by simp
    ultimately show ?thesis
      by (metis prod.collapse snd_eqD thiele_structure.rename_result.simps)
  next
    assume **:"(elimination_set ?e ?max (<) V R p) \<noteq> R"
    hence def: "defer (thiele_module w) V R p = R - (elimination_set ?e ?max (<) V R p)"
    by simp
    hence "rename_alt_set \<pi> `(elimination_set ?e ?max (<) V R p) \<noteq> ?R" 
      using ** rename_bij
      by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_imp_surj_on inj_imp_bij_betw_inv)
    hence "(elimination_set ?e ?max' (<) V ?R ?q) \<noteq> ?R" 
      using set_eq 
      by argo
    hence "defer (thiele_module w) V ?R ?q = ?R - (elimination_set ?e ?max' (<) V ?R ?q)"
    by simp
    moreover have "rename_alt_set \<pi> ` (R - (elimination_set ?e ?max (<) V R p)) =
      ?R - (elimination_set ?e ?max' (<) V ?R ?q)" 
      using set_eq rename_bij
      by (metis (no_types, lifting) bij_betw_imp_inj_on image_set_diff)
    thus ?thesis by auto
    qed
  have "thiele_structure.well_formed_result ?R ?res" 
    using thiele_mod_sound rename_bij thiele_structure.bij_preserves_result wf w_valid
    by (metis multi_winner_result.rename_result.elims thiele_structure.electoral_module.elims(2))
  hence "reject_r ?res = ?R -(elect_r ?res \<union> defer_r ?res)"
    using thiele_structure.result_imp_rej
    by (metis prod.collapse)
  moreover have "reject (thiele_module w) V ?R ?q = ?R - 
    (elect (thiele_module w) V ?R ?q \<union> defer (thiele_module w) V ?R ?q)" by auto
  ultimately have "reject (thiele_module w) V ?R ?q = reject_r ?res"
    using elect_eq defer_eq 
    by simp
  thus "(thiele_module w) V ?R ?q = ?res" 
    using elect_eq defer_eq
    by (meson prod.expand)
qed

lemma (in committee_result) thiele_neutral:
  fixes w :: "nat Aggregate_Evaluation"
  assumes "thiele_score w"
  shows "\<A>\<V>_committee.vr_neutrality' rename_alt_set rename_alt_set (thiele_family w)"
proof (unfold \<A>\<V>_committee.vr_neutrality'_def Let_def, clarify)
  fix 
    A A' :: "'a set" and
    V :: "'v set" and
    p q :: "('v, 'a Approval_Set) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assume
    bij: "bij \<pi>" and
    coinc_bal: "\<A>\<V>_committee.coinciding_bal_permute A \<pi> (rename_alt_set \<pi>)" and
    coinc_cont: "\<A>\<V>_committee.coinciding_cont_permute A \<pi> (rename_alt_set \<pi>)" and
    fin_A: "finite A" and
    "finite (\<pi> ` A)" and
    fin_V: "finite V" and
    wf: "\<A>\<V>_committee.well_formed_profile V A p" and
    rename: "\<A>\<V>_committee.well_formed_profile V (\<pi> ` A) (rename_alt_set \<pi> \<circ> p)"
  let ?R = "committees A"  
  let ?R' = "committees A'"
  have fin_R: "finite ?R" using fin_A by simp  
  let ?p_agg = "(limit_thiele_ballot ?R) \<circ> (thiele_agg_prof A p)"
  let ?q_agg = "(limit_thiele_ballot ?R') \<circ> (thiele_agg_prof A' q)"
  have p_agg_eq: "?p_agg = (thiele_agg_prof A p)" by fastforce
  have q_agg_eq: "?q_agg = (thiele_agg_prof A' q)" by fastforce
  have mod_neutr: "thiele_structure.neutrality' (rename_alt_set \<pi>) ((rename_alt_set \<pi>) (\<circ>)) (thiele_module w)"
    using thiele_module_neutral w_valid 
    sorry
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
  hence "(thiele_module w) V ?R ?p_agg = (thiele_module w) V' ?R' ?q_agg"
  using p_agg_eq q_agg_eq by simp
  
  show "rename_alt_set \<pi> ` thiele_family w V A p = thiele_family w V (\<pi> ` A) (rename_alt_set \<pi> \<circ> p)"
oops

subsubsection \<open>Consistency\<close>

subsubsection \<open>Continuity\<close>

subsubsection \<open>Independence of Losers\<close>

subsubsection \<open>Axiomatic Characterization of Thiele Methods\<close>


end