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

type_synonym 'i Aggregate_Score = "'i \<Rightarrow> erat"
  
type_synonym ('a, 'v, 'b, 'r, 'i) Profile_Aggregation = "'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile"

type_synonym ('a, 'b, 'r, 'i) Ballot_Aggregation = "'a set \<Rightarrow> 'b \<Rightarrow> ('r \<Rightarrow> 'i)"

fun permute_agg_ballot :: "('r \<Rightarrow> 'r) \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> ('r \<Rightarrow> 'i)" where
"permute_agg_ballot \<pi> b c =  b (\<pi> c)"

fun permute_agg_profile :: "('r \<Rightarrow> 'r) \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile" where
"permute_agg_profile \<pi> p v = permute_agg_ballot \<pi> (p v)"

lemma agg_bij:
fixes 
  \<alpha> :: "'a \<Rightarrow> 'a" and
  \<kappa> :: "'r \<Rightarrow> 'r" and
  \<beta> :: "'b \<Rightarrow> 'b" and
  p q:: "('v, 'r, 'i) Aggregate_Profile" 
assumes
  coinc: "q = permute_agg_profile \<kappa> p" and
  bij: "bij \<kappa>"
shows "p = permute_agg_profile (the_inv \<kappa>) q"
proof
fix v :: 'v
have "q v =  p v \<circ> \<kappa>"
  using coinc
  by auto
hence "p v =  q v \<circ> (the_inv \<kappa>)"
  using bij
  by (metis (no_types, lifting) bij_id comp_assoc comp_id)
hence "p v = permute_agg_profile (the_inv \<kappa>) q v"
  by fastforce
hence "p v = (permute_agg_ballot (the_inv \<kappa>) \<circ> q) v"
  by fastforce
thus "p v = permute_agg_profile (the_inv \<kappa>) q v" by simp
qed

locale aggregation =
  ballot well_formed_ballot for
    well_formed_ballot :: "'r set \<Rightarrow> ('r \<Rightarrow> 'i) \<Rightarrow> bool" +
  fixes
    well_formed_base :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    contenders :: "'a set \<Rightarrow> 'r set" and
    aggregate :: "('a, 'b, 'r, 'i) Ballot_Aggregation"
  assumes
    preserve_valid: "well_formed_base A b 
        \<Longrightarrow> well_formed_ballot (contenders A) (aggregate A b)" and
    unique: "well_formed_base A b \<Longrightarrow> well_formed_base A b' \<Longrightarrow> b \<noteq> b'
        \<Longrightarrow> \<exists>c. aggregate A b c \<noteq> aggregate A b' c" and
    limit_valid: "limit_ballot (contenders A) (aggregate A b) = aggregate A b" and
    fin_preserve: "finite A \<Longrightarrow> finite (contenders A)"
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
"coinciding_with_agg' \<alpha> \<kappa> \<beta> = (\<forall> A b. (aggregate (\<alpha> ` A) (\<beta> b) \<circ> \<kappa>) = aggregate A b)"

 
lemma agg_profile_partition:
fixes 
  V :: "'v set" and 
  A :: "'a set" and
  p :: "('v, 'b) Profile" and 
  c :: "'a Committee"
shows "V = \<Union>{bal_voters b (aggregate_profile A p) V | b. b \<in> (aggregate_profile A p) ` V}"
using bal_voters_complete 
by metis


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


lemma aggregate_bal_voters:
fixes 
  V :: "'v set" and 
  A :: "'a set" and
  p :: "('v, 'b) Profile" and 
  p_agg :: "('v, 'r, 'i) Aggregate_Profile"
assumes wf_p: "well_formed_base_profile V A p"
shows "\<forall>b \<in> p ` V. bal_voters b p V = bal_voters (aggregate A b) (aggregate_profile A p) V"
proof (clarify)
fix v :: 'v
assume elem: "v \<in> V"
have "\<forall>b \<in> p ` V. well_formed_base A b" 
  using wf_p well_formed_base_profile_def
  by blast
hence "\<forall>b \<in> p ` V. b \<noteq> p v \<longrightarrow> aggregate A b \<noteq> aggregate A (p v)" 
  using unique elem
  by fastforce
moreover have "\<forall>b \<in> p ` V. b \<noteq> p v \<longrightarrow> bal_voters b p V \<inter> bal_voters (p v) p V = {}"
  using bal_voters_disjoint 
  by auto
ultimately show "bal_voters (p v) p V = bal_voters (aggregate A (p v)) (aggregate_profile A p) V" 
using assms unique by auto
qed


lemma copy_aggregate_commute:
fixes 
  V W :: "'v set" and 
  A :: "'a set" and
  p q :: "('v, 'b) Profile" and 
  p_agg q_agg:: "('v, 'r, 'i) Aggregate_Profile" and
  n :: nat
assumes 
  wf_p: "well_formed_base_profile V A p" and
  copy: "n_copy n V W p q"
shows "n_copy n V W (aggregate_profile A p) (aggregate_profile A q)"
proof (unfold n_copy.simps, standard)
let ?p_agg = "aggregate_profile A p"
let ?q_agg = "aggregate_profile A q"
show "?p_agg ` V = ?q_agg ` W" using assms by force
next 
let ?p_agg = "aggregate_profile A p"
let ?q_agg = "aggregate_profile A q"
show "\<forall>b \<in> ?p_agg ` V. card (bal_voters b ?q_agg W) = n * card (bal_voters b ?p_agg V)"
proof (clarify)
  fix v :: 'v
  assume elem: "v \<in> V"
  have "\<forall>b \<in> p ` V. well_formed_base A b"
    using wf_p well_formed_base_profile_def 
    by fast
  hence "\<forall>b \<in> q ` W. well_formed_base A b"
    using copy copy_preserves_bal_props 
    by metis
  hence "well_formed_base_profile W A q" 
    using  well_formed_base_profile_def
    by auto
  hence "bal_voters (p v) q W = bal_voters (?p_agg v) ?q_agg W"
    using aggregate_bal_voters elem aggregate_profile.simps copy
    by (metis  imageI n_copy.elims(2))
  moreover have "bal_voters (p v) p V = bal_voters (?p_agg v) ?p_agg V"
    using wf_p aggregate_bal_voters elem 
    by fastforce
  moreover have "card (bal_voters (p v) q W) = n * card (bal_voters (p v) p V)"
    using copy elem 
    by simp
  ultimately show "card (bal_voters (?p_agg v) ?q_agg W) = n * card (bal_voters (?p_agg v) ?p_agg V)"
    by simp
  qed
qed


fun score_sum :: "'i Aggregate_Score \<Rightarrow> ('v, 'r, 'i) Aggregate_Profile \<Rightarrow> 'v set \<Rightarrow> ('r \<Rightarrow> erat)" where
"score_sum score p V r = sum (\<lambda>v. score (p v r)) V"


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
  rat_score: "\<forall>b \<in> p ` V. (\<bar>score (b r)\<bar> \<noteq> \<infinity>)"
shows "score_sum score q W r = erat_of n * (score_sum score p V r)" 
proof -
let ?f = "\<lambda>b. score (b r)"
have "sum (?f \<circ> q) W = erat_of n * (sum (?f \<circ> p) V)" 
  using copy_multiplies_sum assms
  by metis
thus ?thesis by simp
qed


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
proof -
let ?f = "\<lambda>b. score (b r)"
let ?join = "joint_profile V V' p q"
have "sum (?f \<circ> ?join) (V \<union> V') = sum (?f \<circ> p) V + sum (?f \<circ> q) V'" 
using join_adds_sum assms 
by blast
thus ?thesis by simp
qed

lemma copy_join_score_sum:
fixes
  score :: "'i Aggregate_Score" and
  V V' W :: "'v set" and
  r :: 'r and
  p q s :: "('v, 'r, 'i) Aggregate_Profile" and
  n :: nat
assumes
  copy: "n_copy n V W p s" and
  fin_V: "finite V" and
  fin_V': "finite V'" and
  fin_W: "finite W" and
  disj: "W \<inter> V' = {}" and
  rat_score: "\<forall>b \<in> p ` V. (\<bar>score (b r)\<bar> \<noteq> \<infinity>)"
shows "score_sum score (joint_profile W V' s q) (W \<union> V') r =
  erat_of n * (score_sum score p V r) + score_sum score q V' r"
proof - 
have "score_sum score s W r = erat_of n * (score_sum score p V r)" 
using n_copy_multiplies_score_sum copy fin_V fin_W rat_score 
by blast
moreover have "score_sum score (joint_profile W V' s q) (W \<union> V') r = 
  score_sum score s W r + score_sum score q V' r"
  using join_adds_score_sum disj fin_W fin_V' 
  by blast
ultimately show ?thesis by simp
qed


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
have "\<forall>v \<in> V'. score (q v r) \<ge> 0"
  using nn_score
  by blast
hence "(\<Sum>v \<in> V'. score (q v r)) \<ge> 0"
  using nn_score sum_nonneg
  by metis
hence "score_sum score q V' r \<ge> 0" by simp
moreover have "score_sum score (joint_profile W V' s q) (W \<union> V') r =
  erat_of n * (score_sum score p V r) + score_sum score q V' r"
  using copy_join_score_sum fin_V fin_V' fin_W copy disj rat_score
  by metis
ultimately show ?thesis 
  using add_increasing2 large_n leD order_eq_refl order_less_le 
  by metis
qed 

(*
moreover have "(score_sum score p V r) > 0"
proof -
  obtain v where live_voter: "v \<in> V \<and> (score (p v r) > 0)" using non_zero_voter by auto
  hence "\<forall>v' \<in> V - {v} . score (p v r) \<ge> 0" 
    using nn_score
    by blast
  hence "(\<Sum>v'\<in>V - {v}. score (p v' r)) \<ge> 0"
    using nn_score sum_nonneg
    by metis
  hence "(score_sum score p (V - {v}) r) \<ge> 0" 
    by simp
  moreover have "(score_sum score p V r) = (score_sum score p (V - {v}) r) + score (p v r)"
    using live_voter add.commute fin_V score_sum.simps sum.remove 
    by metis
  ultimately show ?thesis 
    using live_voter add_nonneg_pos
    by metis
*)


end

text \<open>
 Aggregate ballots are ballots. This is important because it allows us to use them in
 electoral structures later on.
\<close>

sublocale aggregation \<subseteq> ballot
  by (simp add: ballot_axioms)

end