(*  File:       Elimination_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elimination Module\<close>

theory Elimination_Module
  imports 
      Evaluation_Function
      Electoral_Module
begin

text \<open>
  This is the elimination module. It rejects a set of alternatives only if
  these are not all alternatives. The alternatives potentially to be rejected
  are put in a so-called elimination set. These are all alternatives that score
  below a preset threshold value that depends on the specific voting rule.
\<close>

subsection \<open>General Definitions\<close>

type_synonym Threshold_Value = "erat"

type_synonym Threshold_Relation = "erat \<Rightarrow> erat \<Rightarrow> bool"

type_synonym ('r, 'v, 'b) Electoral_Set = "'v set \<Rightarrow> 'r set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set"

fun elimination_set :: "('r, 'v, 'b) Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> ('r, 'v, 'b) Electoral_Set" where
 "elimination_set e t r V A p = {a \<in> A . r (e V a A p) t}"

fun average :: "('r, 'v, 'b) Evaluation_Function \<Rightarrow> 'v set \<Rightarrow>
  'r set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> Threshold_Value" where
  "average e V A p = (let sum = (\<Sum> x \<in> A. e V x A p) in
                      (if (sum = infinity) then (infinity)
                       else ((rat_of_erat sum) div (Fract (card A) 1))))"

subsection \<open>Social Choice Definitions\<close>

fun elimination_module :: "('r, 'v, 'b) Evaluation_Function \<Rightarrow> Threshold_Value
                              \<Rightarrow> Threshold_Relation
                              \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "elimination_module e t r V R p =
      (if (elimination_set e t r V R p) \<noteq> R
        then ({}, (elimination_set e t r V R p), R - (elimination_set e t r V R p))
        else ({}, {}, R))"

subsection \<open>Common Social Choice Eliminators\<close>

fun less_eliminator :: "('r, 'v, 'b) Evaluation_Function \<Rightarrow> Threshold_Value
                          \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "less_eliminator e t V R p = elimination_module e t (<) V R p"

fun max_eliminator :: "('r, 'v, 'b) Evaluation_Function
                          \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "max_eliminator e V R p =
    less_eliminator e (Max {e V x R p | x. x \<in> R}) V R p"

fun leq_eliminator :: "('r, 'v, 'b) Evaluation_Function \<Rightarrow> Threshold_Value
                          \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "leq_eliminator e t V R p = elimination_module e t (\<le>) V R p"

fun min_eliminator ::  "('r, 'v, 'b) Evaluation_Function
                          \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "min_eliminator e V R p =
    leq_eliminator e (Min {e V x R p | x. x \<in> R}) V R p"

fun less_average_eliminator ::  "('r, 'v, 'b) Evaluation_Function
                          \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "less_average_eliminator e V R p = less_eliminator e (average e V R p) V R p"

fun leq_average_eliminator :: "('r, 'v, 'b) Evaluation_Function
                          \<Rightarrow> ('r, 'v, 'b) Electoral_Module" where
  "leq_average_eliminator e V R p = leq_eliminator e (average e V R p) V R p"

  
context electoral_structure
begin
  
subsection \<open>Soundness\<close>

lemma elim_mod_sound[simp]:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "electoral_module (elimination_module e t r)"
proof (unfold electoral_module.simps, safe)
fix 
R :: "'r set" and
V :: "'v set" and 
p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
let ?r = "elimination_module e t r V R p"
have "disjoint3 ?r" by simp
moreover have "set_equals_partition R ?r" by auto
ultimately show "well_formed_result R (elimination_module e t r V R p)" 
  by simp
qed 

lemma less_elim_sound[simp]:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "electoral_module (less_eliminator e t)"
proof (unfold electoral_module.simps less_eliminator.simps, safe)
fix 
  R :: "'r set" and
  V :: "'v set" and 
  p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
thus "well_formed_result R (elimination_module e t (<) V R p)"
  using electoral_module.simps elim_mod_sound
  by blast
qed

lemma leq_elim_sound[simp]:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "electoral_module (leq_eliminator e t)"
proof (unfold electoral_module.simps leq_eliminator.simps, safe)
fix
  R :: "'r set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
thus "well_formed_result R (elimination_module e t (\<le>) V R p)"
  using electoral_module.simps elim_mod_sound
  by blast
qed
  
lemma max_elim_sound[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "electoral_module (max_eliminator e)"
proof (unfold electoral_module.simps max_eliminator.simps, safe)
fix
  R :: "'r set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
thus "well_formed_result R
    (less_eliminator e (Max {e V x R p |x. x \<in> R}) V R p)"
  using electoral_module.simps less_elim_sound
  by blast
qed
  
lemma min_elim_sound[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "electoral_module (min_eliminator e)"
proof (unfold electoral_module.simps min_eliminator.simps, safe)
fix
  R :: "'r set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
thus "well_formed_result R 
    (leq_eliminator e (Min {e V x R p |x. x \<in> R}) V R p)"
  using electoral_module.simps leq_elim_sound
  by blast
qed
  
lemma less_avg_elim_sound[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "electoral_module (less_average_eliminator e)"
proof (unfold electoral_module.simps less_average_eliminator.simps, safe)
fix
  R :: "'r set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
thus "well_formed_result R (less_eliminator e (average e V R p) V R p) "
  using electoral_module.simps less_elim_sound
  by blast
qed
 
lemma leq_avg_elim_sound[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "electoral_module (leq_average_eliminator e)"
proof (unfold electoral_module.simps leq_average_eliminator.simps, safe)
fix
  R :: "'r set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile"
assume "well_formed_profile V (affected_alts R) p"
thus "well_formed_result R (leq_eliminator e (average e V R p) V R p) "
  using electoral_module.simps leq_elim_sound
  by blast
qed
  

subsection \<open>Only participating voters impact the result\<close>

lemma voters_determine_elim_mod[simp]:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (elimination_module e t r)"
proof (unfold voters_determine_election.simps elimination_module.simps, safe)
  fix
    R :: "'r set" and
    V :: "'v set" and
    p p':: "('v, 'b) Profile"
  assume "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> c \<in> R. (e V c R p) = (e V c R p')"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "{c \<in> R. r (e V c R p) t} = {c \<in> R. r (e V c R p') t}"
    by metis
  hence "elimination_set e t r V R p = elimination_set e t r V R p'"
    unfolding elimination_set.simps
    by presburger
  thus "(if elimination_set e t r V R p \<noteq> R
        then ({}, elimination_set e t r V R p, R - elimination_set e t r V R p)
        else ({}, {}, R)) =
     (if elimination_set e t r V R p' \<noteq> R
        then ({}, elimination_set e t r V R p', R - elimination_set e t r V R p')
        else ({}, {}, R))"
    by presburger
qed


lemma voters_determine_less_elim[simp]:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (less_eliminator e t)"
  using assms voters_determine_elim_mod
  unfolding less_eliminator.simps voters_determine_election.simps
  by (metis (full_types))

  
lemma voters_determine_leq_elim[simp]:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (leq_eliminator e t)"
  using assms voters_determine_elim_mod
  unfolding leq_eliminator.simps voters_determine_election.simps
  by (metis (full_types))


lemma voters_determine_max_elim[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (max_eliminator e)"
proof (unfold max_eliminator.simps voters_determine_election.simps, safe)
  fix
    R :: "'r set" and
    V :: "'v set" and
    p p' :: "('v, 'b) Profile" 
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> R. e V x R p = e V x R p'"
    using assms
    unfolding voters_determine_evaluation.simps
    by simp
  hence "Max {e V x R p | x. x \<in> R} = Max {e V x R p' | x. x \<in> R}"
    by metis
  thus "less_eliminator e (Max {e V x R p | x. x \<in> R}) V R p =
       less_eliminator e (Max {e V x R p' | x. x \<in> R}) V R p'"
    using coinciding assms voters_determine_less_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed


lemma voters_determine_min_elim[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (min_eliminator e)"
proof (unfold min_eliminator.simps voters_determine_election.simps, safe)
  fix
    R :: "'r set" and
    V :: "'v set" and
    p p' :: "('v, 'b) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> R. e V x R p = e V x R p'"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "Min {e V x R p | x. x \<in> R} = Min {e V x R p' | x. x \<in> R}"
    by metis
  thus "leq_eliminator e (Min {e V x R p | x. x \<in> R}) V R p =
       leq_eliminator e (Min {e V x R p' | x. x \<in> R}) V R p'"
    using coinciding assms voters_determine_leq_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed



lemma voters_determine_less_avg_elim[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (less_average_eliminator e)"
proof (unfold less_average_eliminator.simps voters_determine_election.simps, safe)
  fix
    R :: "'r set" and
    V :: "'v set" and
    p p' :: "('v, 'b) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> R. e V x R p = e V x R p'"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "average e V R p = average e V R p'"
    unfolding average.simps
    by auto
  thus "less_eliminator e (average e V R p) V R p =
       less_eliminator e (average e V R p') V R p'"
    using coinciding assms voters_determine_less_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed


lemma voters_determine_leq_avg_elim[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  assumes "voters_determine_evaluation e"
  shows "voters_determine_election (leq_average_eliminator e)"
proof (unfold leq_average_eliminator.simps voters_determine_election.simps, safe)
  fix
    R :: "'r set" and
    V :: "'v set" and
    p p' :: "('v, 'b) Profile"
  assume coinciding: "\<forall> v \<in> V. p v = p' v"
  hence "\<forall> x \<in> R. e V x R p = e V x R p'"
    using assms
    unfolding voters_determine_election.simps
    by simp
  hence "average e V R p = average e V R p'"
    unfolding average.simps
    by auto
  thus "leq_eliminator e (average e V R p) V R p =
       leq_eliminator e (average e V R p') V R p'"
    using coinciding assms voters_determine_leq_elim
    unfolding voters_determine_election.simps
    by (metis (no_types, lifting))
qed


subsection \<open>Non-Blocking\<close>

lemma elim_mod_non_blocking:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "non_blocking (elimination_module e t r)"
proof (unfold non_blocking_def, standard)
  show " electoral_module (elimination_module e t r)" using elim_mod_sound by blast
next
  show "\<forall>V R p. R \<noteq> {} \<and> finite R \<and>  well_formed_profile V (affected_alts R) p \<longrightarrow>
       reject (elimination_module e t r) V R p \<noteq> R" 
    by auto
qed


lemma less_elim_non_blocking:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_blocking (less_eliminator e t)"
  unfolding less_eliminator.simps
  using elim_mod_non_blocking
  by auto
  

lemma leq_elim_non_blocking:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_blocking (leq_eliminator e t)"
  unfolding leq_eliminator.simps
  using elim_mod_non_blocking
  by auto

  
lemma max_elim_non_blocking:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_blocking (max_eliminator e)"
proof (unfold non_blocking_def, standard)
  show " electoral_module (max_eliminator e)" using max_elim_sound by blast
next
  show "\<forall>V R p. R \<noteq> {} \<and> finite R \<and>  well_formed_profile V (affected_alts R) p \<longrightarrow>
       reject (max_eliminator e) V R p \<noteq> R" 
    by auto
qed

lemma min_elim_non_blocking:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_blocking (min_eliminator e)"
proof (unfold non_blocking_def, standard)
  show " electoral_module (min_eliminator e)" using min_elim_sound by blast
next
  show "\<forall>V R p. R \<noteq> {} \<and> finite R \<and>  well_formed_profile V (affected_alts R) p \<longrightarrow>
       reject (min_eliminator e) V R p \<noteq> R" 
    by auto
qed

lemma less_avg_elim_non_blocking:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_blocking (less_average_eliminator e)"
proof (unfold non_blocking_def, standard)
  show " electoral_module (less_average_eliminator e)" using less_avg_elim_sound by blast
next
  show "\<forall>V R p. R \<noteq> {} \<and> finite R \<and>  well_formed_profile V (affected_alts R) p \<longrightarrow>
       reject (less_average_eliminator e) V R p \<noteq> R" 
    by auto
qed

lemma leq_avg_elim_non_blocking:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_blocking (leq_average_eliminator e)"
proof (unfold non_blocking_def, standard)
  show " electoral_module (leq_average_eliminator e)" using leq_avg_elim_sound by blast
next
  show "\<forall>V R p. R \<noteq> {} \<and> finite R \<and>  well_formed_profile V (affected_alts R) p \<longrightarrow>
       reject (leq_average_eliminator e) V R p \<noteq> R" 
    by auto
qed
    
  
subsection \<open>Non-Electing\<close>

lemma elim_mod_non_electing:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value" and
    r :: "Threshold_Relation"
  shows "non_electing (elimination_module e t r)"
  unfolding non_electing_def
  by force

 
lemma less_elim_non_electing:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing less_elim_sound
  unfolding non_electing_def
  by force

lemma leq_elim_non_electing:
  fixes
    e :: "('r, 'v, 'b) Evaluation_Function" and
    t :: "Threshold_Value"
  shows "non_electing (leq_eliminator e t)"
  unfolding non_electing_def
  by force

lemma max_elim_non_electing:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_electing (max_eliminator e)"
  unfolding non_electing_def
  by force

lemma min_elim_non_electing:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_electing (min_eliminator e)"
  unfolding non_electing_def
  by force

lemma less_avg_elim_non_electing:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_electing (less_average_eliminator e)"
  unfolding non_electing_def
  by auto

lemma leq_avg_elim_non_electing:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  shows "non_electing (leq_average_eliminator e)"
  unfolding non_electing_def
  by force

(*
subsection \<open>Inference Rules\<close>

text \<open>
  If the used evaluation function is Condorcet rating,
    max-eliminator is Condorcet compatible.
\<close>

theorem cr_eval_imp_ccomp_max_elim[simp]:
  fixes e :: "('r, 'v, 'b) Evaluation_Function"
  assumes "condorcet_rating e"
  shows "condorcet_compatibility (max_eliminator e)"
proof (unfold condorcet_compatibility_def, safe)
  show "electoral_module (max_eliminator e)"
    by force
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume
    c_win: "condorcet_winner V A p a" and
    rej_a: "a \<in> reject (max_eliminator e) V A p"
  have "e V a A p = Max {e V b A p | b. b \<in> A}"
    using c_win cond_winner_imp_max_eval_val assms
    by fastforce
  hence "a \<notin> reject (max_eliminator e) V A p"
    by simp
  thus False
    using rej_a
    by linarith
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume "a \<in> elect (max_eliminator e) V A p"
  moreover have "a \<notin> elect (max_eliminator e) V A p"
    by simp
  ultimately show False
    by linarith
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    a' :: "'a"
  assume
    "condorcet_winner V A p a" and
    "a \<in> elect (max_eliminator e) V A p"
  thus "a' \<in> reject (max_eliminator e) V A p"
    using empty_iff max_elim_non_electing
    unfolding condorcet_winner.simps non_electing_def
    by metis
qed

text \<open>
  If the used evaluation function is Condorcet rating, max-eliminator
  is defer-Condorcet-consistent.
\<close>

theorem cr_eval_imp_dcc_max_elim[simp]:
  fixes e :: "('a, 'v, 'b) Evaluation_Function"
  assumes "condorcet_rating e"
  shows "defer_condorcet_consistency (max_eliminator e)"
proof (unfold defer_condorcet_consistency_def, safe)
  show "electoral_module (max_eliminator e)"
    using max_elim_sound
    by metis
next
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assume winner: "condorcet_winner V A p a"
  hence f_prof: "finite_profile V A p"
    by simp
  let ?trsh = "Max {e V b A p | b. b \<in> A}"
  show
    "max_eliminator e V A p =
      ({},
        A - defer (max_eliminator e) V A p,
        {b \<in> A. condorcet_winner V A p b})"
  proof (cases "elimination_set e (?trsh) (<) V A p \<noteq> A")
    have "e V a A p = Max {e V x A p | x. x \<in> A}"
      using winner assms cond_winner_imp_max_eval_val
      by fastforce
    hence "\<forall> b \<in> A. b \<noteq> a
        \<longleftrightarrow> b \<in> {c \<in> A. e V c A p < Max {e V b A p | b. b \<in> A}}"
      using winner assms mem_Collect_eq linorder_neq_iff
      unfolding condorcet_rating_def
      by (metis (mono_tags, lifting))
    hence elim_set: "(elimination_set e ?trsh (<) V A p) = A - {a}"
      unfolding elimination_set.simps
      by blast
    case True
    hence
      "max_eliminator e V A p =
        ({},
          (elimination_set e ?trsh (<) V A p),
          A - (elimination_set e ?trsh (<) V A p))"
      by simp
    also have "\<dots> = ({},A - defer (max_eliminator e) V A p, {a})"
      using elim_set winner
      by auto
    also have
      "\<dots> = ({},
              A - defer (max_eliminator e) V A p,
              {b \<in> A. condorcet_winner V A p b})"
      using cond_winner_unique winner Collect_cong
      by (metis (no_types, lifting))
    finally show ?thesis
      using winner
      by metis
  next
    case False
    moreover have "?trsh = e V a A p"
      using assms winner cond_winner_imp_max_eval_val
      by fastforce
    ultimately show ?thesis
      using winner
      by auto
  qed
qed
*)


lemma profiles_determine_max_elim[simp]:
fixes 
  e :: "('r, 'v, 'b) Evaluation_Function" and
  R :: "'r set" and
  V V' :: "'v set" and
  p q :: "('v, 'b) Profile"
assumes *: "\<forall>r \<in> R. (e V r R p) = (e V' r R q)"
shows "max_eliminator e V R p = max_eliminator e V' R q"
proof -
  let ?max = "(Max {e V x R p | x. x \<in> R})" 
  let ?max' = "(Max {e V' x R q | x. x \<in> R})" 
  have max_eq: "?max = ?max'" 
    using * 
    by metis
  hence elem_eq: "elimination_set e ?max (<) V R p = elimination_set e ?max' (<) V' R q" 
    using * 
    by auto
  have "max_eliminator e V R p = elimination_module e ?max (<) V R p" by simp
  have "max_eliminator e V' R q = elimination_module e ?max' (<) V' R q" by simp
  show "max_eliminator e V R p = max_eliminator e V' R q"
  proof (cases)
    assume all_elim: "(elimination_set e ?max (<) V R p) = R"
    hence "(elimination_set e ?max' (<) V' R q) = R" 
      using elem_eq 
      by simp
    have "max_eliminator e V R p = ({}, {}, R)" using all_elim by simp
    thus "max_eliminator e V R p = max_eliminator e V' R q"
      using all_elim elem_eq 
      by auto
  next
    assume not_all_elim: "\<not>(elimination_set e ?max (<) V R p) = R"
    hence "(elimination_set e ?max (<) V R p) \<subset> R" by auto
    have "max_eliminator e V R p = 
      ({}, (elimination_set e ?max (<) V R p), R - (elimination_set e ?max (<) V R p))" 
      using not_all_elim by simp
    hence "max_eliminator e V' R q = 
      ({}, (elimination_set e ?max' (<) V' R q), R - (elimination_set e ?max' (<) V' R q))" 
      using elem_eq 
      by auto
    thus "max_eliminator e V R p = max_eliminator e V' R q"
      using not_all_elim elem_eq 
      by auto
  qed
qed


lemma eval_determine_max_elim[simp]:
fixes 
  e :: "('r, 'v, 'b) Evaluation_Function" and
  R :: "'r set" and
  V :: "'v set" and
  p q :: "('v, 'b) Profile" and
  \<pi> :: "'r \<Rightarrow> 'r"
assumes 
  bij: "bij \<pi>" and
  eval_eq: "\<forall>r \<in> R. (e V r R p) = (e V (\<pi> r) (\<pi> ` R) q)" and
  wf: "well_formed_profile V (affected_alts R) p" 
shows "rename_result \<pi> (max_eliminator e V R p) = max_eliminator e V (\<pi> ` R) q"
proof -
  let ?max = "(Max {e V x R p | x. x \<in> R})"
  let ?max' = "(Max {e V x (\<pi> ` R) q | x. x \<in> (\<pi> ` R)})"
  let ?renamed = "rename_result \<pi> (max_eliminator e V R p)"
  have max_eq: "?max = ?max'"
    using eval_eq
    by (metis (no_types, opaque_lifting) imageE imageI)
  hence set_eq: "\<pi> `(elimination_set e ?max (<) V R p) = 
    elimination_set e ?max' (<) V (\<pi> ` R) q" 
    using eval_eq
    by auto
  have elect_eq: "elect (max_eliminator e) V (\<pi> ` R) q = elect_r ?renamed" by simp
  have defer_eq: "defer (max_eliminator e) V (\<pi> ` R) q = defer_r ?renamed"
  proof (cases)
    assume *:"(elimination_set e ?max (<) V R p) = R"
    hence "(elimination_set e ?max' (<) V (\<pi> ` R) q) = (\<pi> ` R)"
      using set_eq
      by presburger
    hence "defer (max_eliminator e) V (\<pi> ` R) q = (\<pi> ` R)" 
      using result_presv_conts max_elim_non_electing 
      by simp
    moreover have "defer (max_eliminator e) V R p = R" 
      using result_presv_conts max_elim_non_electing *
      by simp
    ultimately show ?thesis
      by (metis prod.collapse snd_eqD rename_result.simps)
  next
    assume *:"(elimination_set e ?max (<) V R p) \<noteq> R"
    hence def: "defer (max_eliminator e) V R p = R - (elimination_set e ?max (<) V R p)"
    by simp
    hence "\<pi> `(elimination_set e ?max (<) V R p) \<noteq> (\<pi> ` R)" 
      using * bij 
      by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_imp_surj_on inj_imp_bij_betw_inv)
    hence "(elimination_set e ?max' (<) V (\<pi> ` R) q) \<noteq> (\<pi> ` R)" 
      using set_eq 
      by argo
    hence "defer (max_eliminator e) V (\<pi> ` R) q = (\<pi> ` R) - (elimination_set e ?max' (<) V (\<pi> ` R) q)"
      by simp
    moreover have "\<pi> ` (R - (elimination_set e ?max (<) V R p)) =
      (\<pi> ` R) - (elimination_set e ?max' (<) V (\<pi> ` R) q)" 
      using set_eq bij 
      by (metis (no_types, lifting) bij_betw_imp_inj_on image_set_diff)
    thus ?thesis by auto
    qed
  have "well_formed_result R (max_eliminator e V R p)" 
    using max_elim_sound wf
    by auto
  hence "well_formed_result (\<pi> ` R) ?renamed"
    using bij bij_preserves_result
    by (metis rename_result.elims)
  hence "reject_r ?renamed = (\<pi> ` R) -(elect_r ?renamed \<union> defer_r ?renamed)"
    using result_imp_rej
    by (metis prod.collapse)
  moreover have "reject (max_eliminator e) V (\<pi> ` R) q = (\<pi> ` R) - 
    (elect (max_eliminator e) V (\<pi> ` R) q \<union> defer (max_eliminator e) V (\<pi> ` R) q)" by auto
  ultimately have "reject (max_eliminator e) V (\<pi> ` R) q = reject_r ?renamed"
    using elect_eq defer_eq 
    by simp
  thus "?renamed = (max_eliminator e) V (\<pi> ` R) q" 
    using elect_eq defer_eq
    by (metis prod.expand)
qed


lemma defer_of_max_elim[simp]:
fixes 
  e :: "('r, 'v, 'b) Evaluation_Function" and
  R :: "'r set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile" and
  r :: "'r"
assumes 
  fin: "finite R" and 
  wf: "well_formed_profile V (affected_alts R) p" and 
  elem: "r \<in> R"
shows "r \<in> defer (max_eliminator e) V R p \<longleftrightarrow> e V r R p = Max {e V x R p | x. x \<in> R}"
proof 
let ?max = "Max {e V x R p | x. x \<in> R}"
assume def: "r \<in> defer (max_eliminator e) V R p"
moreover have fin_img: "finite  {e V x R p | x. x \<in> R}" 
  using fin 
  by simp
ultimately have *: "\<forall>y \<in> R. e V y R p \<le> ?max"
  using Max_ge 
  by fastforce
have "?max \<in> {e V x R p |x. x \<in> R}"
  using fin_img Max_in elem 
  by auto
hence ex_max_arg: "\<exists>m \<in> R. e V m R p = ?max"
  using * fin 
  by auto
show "e V r R p = ?max"
proof (cases "(elimination_set e ?max (<) V R p) = R")
  case all_elim: True
  hence "\<forall>y \<in> R. e V y R p < ?max" by auto
  hence "False" 
    using ex_max_arg
    by auto
  thus ?thesis by simp
next
  case ex_def: False
  hence "r \<notin> (elimination_set e ?max (<) V R p)" 
    using def 
    by simp
  hence "\<not> (e V r R p < ?max)" 
    using elimination_set.simps elem
    by simp
  thus ?thesis
  using * elem nless_le 
  by blast
qed
next
let ?max = "Max {e V x R p | x. x \<in> R}"
assume max_eval: "e V r R p = ?max"
moreover have fin_img: "finite  {e V x R p | x. x \<in> R}" 
  using fin 
  by simp
ultimately have *: "\<forall>y \<in> R. e V y R p \<le> ?max"
  using Max_ge 
  by fastforce
have "?max \<in> {e V x R p |x. x \<in> R}"
  using fin_img Max_in elem 
  by auto
hence ex_max_arg: "\<exists>m \<in> R. e V m R p = ?max"
  using * fin 
  by auto
show "r \<in> defer (max_eliminator e) V R p"
proof (cases "(elimination_set e ?max (<) V R p) = R")
  case all_elim: True
  hence "\<forall>y \<in> R. e V y R p < ?max" by auto
  hence "False" 
    using ex_max_arg
    by auto
  thus ?thesis by simp
next
case ex_def: False
 have "\<not> (e V r R p < ?max)" 
    using max_eval by simp
  hence "r \<notin> (elimination_set e ?max (<) V R p)" 
    by simp
  thus ?thesis using elem by simp
qed
qed


end

end