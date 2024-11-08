theory Aggregate_Profile
  imports
    Profile_Interpretations
    Result
begin

section \<open>Aggregate Profiles\<close>
text \<open>
  While a voting rule receives a set of alternatives, electoral modules operate on contenders,
  which are of the same type as the results of an election. This is negligible in
  the case of single winner voting, where contenders are alternatives.

  An aggregate profile is a generalization of a profile and aims to capture information
  about the preference of voters on contenders (in contrast to profiles, which capture
  the preferences of voters on alternatives). An aggregate profile is computed based on a
  profile.
  For the sake of clarity, an aggregate profile should always store minimally complex data.
\<close>

subsection \<open>Defintion\<close>

type_synonym ('v, 'r, 'i) Aggregate_Profile = "('v, ('r \<Rightarrow>'i)) Profile"
  
type_synonym ('a, 'v, 'b, 'r, 'i) Profile_Aggregation = "'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"

type_synonym ('a, 'b, 'r, 'i) Ballot_Aggregation = "'a set \<Rightarrow> 'b \<Rightarrow> ('r \<Rightarrow> 'i)"

fun permute_agg_ballot :: "('r \<Rightarrow> 'r) \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> ('r \<Rightarrow> 'i)" where
"permute_agg_ballot \<pi> b c =  b (\<pi> c)"

fun permute_agg_profile :: "('r \<Rightarrow> 'r) \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile" where
"permute_agg_profile \<pi> p v = permute_agg_ballot \<pi> (p v)"

locale aggregation =
  ballot well_formed_ballot for
    well_formed_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" +
  fixes
    well_formed_base :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('a, 'b, 'r, 'i) Ballot_Aggregation"
  assumes
    preserve_valid: "well_formed_base A b 
        \<Longrightarrow> well_formed_ballot (contenders A) (aggregate A b)" 
(*
and
    valid_trans: "\<And> (A :: 'a set)(B :: 'a set) (b :: 'b). A \<subseteq> B \<and> well_formed_base A b 
        \<Longrightarrow> well_formed_ballot (contenders B) (limit_ballot (contenders B) (aggregate b))"
*)
begin

definition well_formed_base_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "well_formed_base_profile V A p \<equiv> (\<forall> v \<in> V. well_formed_base A (p v))"

fun aggregate_profile :: "('a, 'v, 'b, 'r, 'i) Profile_Aggregation" where
"aggregate_profile A p v = aggregate A (p v)"

subsection \<open>Renaming Voters\<close>

lemma agg_preserves_voter_rename:
fixes 
  \<pi> :: "'v \<Rightarrow> 'v" and
  p q :: "('v, 'b) Profile" and 
  V V' :: "'v set" and 
  A A' :: "'a set"
assumes 
  bij: "bij \<pi>" and 
  rename: "rename \<pi> (A, V, p) = (A', V', q)"
  shows "rename \<pi> ((contenders A), V, (aggregate A) \<circ> p) = ((contenders A'), V', (aggregate A') \<circ> q)"
  proof (standard, simp)
    have A_id: "A = A'" using rename by simp
    thus "contenders A = contenders A'" by simp
  next
    show "snd (rename \<pi> (contenders A, V, aggregate A \<circ> p)) = snd (contenders A', V', aggregate A' \<circ> q)"
    proof (standard, simp)
      show "\<pi> ` V = V'" using rename by simp 
    next
      have A_id: "A = A'" using rename by simp
      have "q = p \<circ> (the_inv \<pi>)" using rename by simp
      hence "(aggregate A') \<circ> q = (aggregate A') \<circ> p \<circ> (the_inv \<pi>)" by auto
      hence "(aggregate A') \<circ> q = (aggregate A) \<circ> p \<circ> (the_inv \<pi>)" 
        using A_id 
        by simp
      thus "snd (snd (rename \<pi> (contenders A, V, aggregate A \<circ> p))) = 
        snd (snd (contenders A', V', aggregate A' \<circ> q))" 
        by simp
  qed
qed

subsection \<open>Renaming Alternatives\<close>


fun coinciding_with_agg :: "'v set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool" where
"coinciding_with_agg V \<alpha> \<kappa> \<beta> = (\<forall> A p. (well_formed_base_profile V A p \<longrightarrow>
      (\<forall>v \<in> V. aggregate (\<alpha> ` A) ((\<beta> \<circ> p) v) \<circ> \<kappa> = (aggregate A (p v)))))"

fun coinciding_with_agg' :: "('a \<Rightarrow> 'a) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool" where
"coinciding_with_agg' \<alpha> \<kappa> \<beta> = ((\<lambda>A b. aggregate (\<alpha> ` A) (\<beta> b) \<circ> \<kappa>) = (\<lambda>A b. aggregate A b))"


lemma agg_preserves_alt_rename:
fixes 
  \<alpha> :: "'a \<Rightarrow> 'a" and
  \<kappa> :: "'r \<Rightarrow> 'r" and
  \<beta> :: "'b \<Rightarrow> 'b" and
  p :: "('v, 'b) Profile" and 
  V :: "'v set" and 
  A :: "'a set"
assumes
  wf: "well_formed_base_profile V A p" and
  coinc: "coinciding_with_agg V \<alpha> \<kappa> \<beta>" and
  bij: "bij \<kappa>"
shows "\<forall>v \<in> V. (aggregate_profile (\<alpha> ` A) (\<beta> \<circ> p) v) = 
  permute_agg_ballot (the_inv \<kappa>) ((aggregate_profile A p) v)"
proof
  fix v :: 'v
  assume elem: "v \<in> V"
  let ?p_agg = "aggregate_profile A p"
  let ?q_agg = "aggregate_profile (\<alpha> ` A) (\<beta> \<circ> p)"
  have "aggregate (\<alpha> ` A) ((\<beta> \<circ> p) v) \<circ> \<kappa> = aggregate A (p v)"
    using elem coinc wf
    by simp
  hence "aggregate (\<alpha> ` A) ((\<beta> \<circ> p) v) \<circ> \<kappa> \<circ> (the_inv \<kappa>) = aggregate A (p v) \<circ> (the_inv \<kappa>)" 
    by simp
  hence "aggregate (\<alpha> ` A) ((\<beta> \<circ> p) v) = aggregate A (p v) \<circ> (the_inv \<kappa>)"
    using bij
    by (simp add: comp_def f_the_inv_into_f_bij_betw)
  moreover  have "(permute_agg_ballot (the_inv \<kappa>) \<circ> ?p_agg) v = aggregate A (p v) \<circ> (the_inv \<kappa>)" 
    by auto
  ultimately show "?q_agg v = permute_agg_ballot (the_inv \<kappa>) (?p_agg v)" by simp
qed 

lemma agg_preserves_alt_rename_v2:
fixes 
  \<alpha> :: "'a \<Rightarrow> 'a" and
  \<kappa> :: "'r \<Rightarrow> 'r" and
  \<beta> :: "'b \<Rightarrow> 'b" and
  p :: "('v, 'b) Profile" and 
  V :: "'v set" and 
  A :: "'a set"
assumes
  coinc: "coinciding_with_agg' \<alpha> \<kappa> \<beta>" and
  bij: "bij \<kappa>"
shows "aggregate_profile A p = permute_agg_profile \<kappa> (aggregate_profile (\<alpha> ` A) (\<beta> \<circ> p))"
proof
  fix v :: 'v
  let ?p_agg = "aggregate_profile A p"
  let ?q_agg = "aggregate_profile (\<alpha> ` A) (\<beta> \<circ> p)"
  have "aggregate A (p v) = (aggregate (\<alpha> ` A) (\<beta> (p v))) \<circ> \<kappa>"
    using coinc
    by (metis coinciding_with_agg'.simps)
  hence "aggregate A (p v) = aggregate (\<alpha> ` A) ((\<beta> \<circ> p) v) \<circ> \<kappa>" by simp
  hence "?p_agg v =permute_agg_ballot \<kappa> (?q_agg v)" by auto
  thus "?p_agg v = permute_agg_profile \<kappa> ?q_agg v" by simp
qed 

(*
 have *: "?q_agg = (rename_thiele_ballot \<pi> \<circ> ?p_agg)"
  proof (unfold thiele_aggregation.aggregate_profile.simps, standard)
    fix v :: 'v
    have "\<forall>C. thiele_aggregate A (p v) ((the_inv \<pi>) ` (\<pi> ` C)) = (thiele_aggregate A (p v) C)" 
      using bij
      by (metis bij_def inv_rename rename_alt_set.simps rename_inherits_bij the_inv_f_f)
    hence "\<forall>C. thiele_aggregate (\<pi> ` A) (((rename_alt_set (the_inv \<pi>)) \<circ> p) v) (\<pi> ` C) =
    (thiele_aggregate A (p v) C)" sorry

  moreover have "\<forall>C. C \<in> committees A \<longleftrightarrow> \<pi> ` C \<in> committees (\<pi> ` A)"
    by (metis Pow_UNIV R_eq bij bij_betw_Pow bij_def image_cong inj_image_mem_iff rename_alt_set.simps)
    moreover have "\<forall>S T. S \<subseteq> A \<and> T \<subseteq> A \<longrightarrow> (card (S \<inter> T) = card ((\<pi> ` S) \<inter> \<pi> ` T))"
    using bij
    by (metis bij_betw_imp_inj_on bij_betw_same_card image_Int inj_imp_bij_betw_inv)
  ultimately have "\<forall>C. thiele_aggregate (\<pi> ` A) (?q v) (\<pi> ` C) = thiele_aggregate A (p v) C"
    using bij rename_inherits_bij by simp
  hence "\<forall>D. thiele_aggregate (\<pi> ` A) (?q v) D = (thiele_aggregate A (p v) (the_inv \<pi> ` D))" 
    using bij
    by (metis Voting_Rule.bij_id bij_betw_id_iff bij_betw_imp_surj_on image_comp)
  hence "thiele_aggregate (\<pi> ` A) (?q v) = rename_thiele_ballot \<pi> (thiele_aggregate A (p v))" by auto
  thus "thiele_aggregate (\<pi> ` A) (?q v) =
         (rename_thiele_ballot \<pi> \<circ> (\<lambda>v. thiele_aggregate A (p v))) v" by simp
  qed
*)
end

text \<open>
 Aggregate ballots are ballots. This is important because it allows us to use them in
 electoral structures later on.
\<close>

sublocale aggregation \<subseteq> ballot
  by (simp add: ballot_axioms)

end