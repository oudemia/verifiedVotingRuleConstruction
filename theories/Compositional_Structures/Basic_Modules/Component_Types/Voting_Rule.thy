section \<open>Voting Rules\<close>

theory Voting_Rule

imports
    Electoral_Module
    Evaluation_Function
begin

text \<open>
  Voting Rules are a special component type of the composable
  modules voting framework. In contrast to an electoral module, a voting rule
  is not composable. It does not abstract from voting rules in social choice,
  but aims to model them, therefore "making the final decision" that an electoral
  model does not make by design.

  A voting rule therefore receives a set of voters, a set of eligible alternatives
  and a profile. It returns a set of (tied) winners.
\<close>

subsection \<open>Definition\<close>

type_synonym ('a, 'v, 'b, 'r) Voting_Rule = "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'r set"

subsection \<open>Properties\<close>
         
context electoral_structure 
begin

definition vr_anonymity :: "('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool" where 
  "vr_anonymity r \<equiv>
      (\<forall> A V p \<pi>.
        bij \<pi> \<longrightarrow> (let (A', V', q) = (rename \<pi> (A, V, p)) in
            finite_profile V A p \<and> finite_profile V' A' q \<longrightarrow> r V A p = r V' A' q))"

(*            
definition coinciding_permutes :: "'r set \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool" where
   "coinciding_permutes R \<pi> \<rho> = (bij \<rho> \<and> (\<forall>S \<subseteq> R. \<forall> b. well_formed_ballot (affected_alts R) b 
    \<longrightarrow> limit_by_conts (\<pi> ` S) (\<rho> b) = \<rho> ( limit_by_conts S b)))"

definition neutrality' :: "('r \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('r, 'v, 'b) Electoral_Module \<Rightarrow> bool"  where
  "neutrality' \<rho> \<beta> m \<equiv> electoral_module m \<and> bij \<rho> \<and> bij \<beta> \<and>
      (\<forall> R V p. coinciding_permutes R \<rho> \<beta> \<longrightarrow> (let (R', V', q) = (\<rho> ` R, V, \<beta> \<circ> p) in
            finite_profile V (affected_alts R) p \<and> finite_profile V' (affected_alts R') q \<longrightarrow> 
              m V R p = m V' R' q))"
*)

definition coinciding_bal_permute :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool" where
   "coinciding_bal_permute A \<pi> \<beta> = (\<forall>S \<subseteq> A. \<forall> b. 
      well_formed_ballot A b \<longrightarrow> limit_ballot (\<pi> ` S) (\<beta> b) = \<beta> (limit_ballot S b))"

definition coinciding_cont_permute :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> bool" where
   "coinciding_cont_permute A \<pi> \<rho> = (\<forall>S \<subseteq> A. \<forall> c \<in> contenders A.
      limit_contenders (\<pi> ` S) {\<rho> c} = \<rho> ` (limit_contenders S {c}))"          
      
definition vr_neutrality :: "('a \<Rightarrow> 'a) \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> ('b \<Rightarrow> 'b)
                              \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool"  where
  "vr_neutrality \<pi> \<kappa> \<beta> r \<equiv>
      (\<forall> A V p. 
        bij \<pi> \<and> coinciding_bal_permute A \<pi> \<beta> \<and> coinciding_cont_permute A \<pi> \<kappa>
          \<longrightarrow> well_formed_profile V A p \<and> well_formed_profile V (\<pi> ` A) (\<beta> \<circ> p) \<longrightarrow> 
            (\<kappa> `(r V A p)) = r V (\<pi> ` A) (\<beta> \<circ> p))"

lemma vr_neutrality_prereq:
fixes 
  r :: "('a, 'v, 'b, 'r) Voting_Rule" and
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile" and
  \<alpha> :: "'a \<Rightarrow> 'a"  and
  \<kappa> :: "'r \<Rightarrow> 'r"  and
  \<beta> :: "'b \<Rightarrow> 'b" 
assumes 
  "bij \<pi>" and
  "vr_neutrality \<pi> \<kappa> \<beta> r" and
  "coinciding_bal_permute A \<pi> \<beta>" and
  "coinciding_cont_permute A \<pi> \<kappa>" and
  "well_formed_profile V A p" and
  "well_formed_profile V (\<pi> ` A) (\<beta> \<circ> p)"
shows "(\<kappa> `(r V A p)) = r V (\<pi> ` A) (\<beta> \<circ> p)"
  using assms vr_neutrality_def
  by blast

text \<open>
  Intuitively, continuity states that a large group of voters should be able to enforce that 
  some of its desired outcomes are chosen. More precisely, a voting rule is continuous 
  if for two election instances E, E' over the same set of alternatives there is a natural number n 
  such that the outcome of the election instance consisting of n copies of E together with E'
  contains the election outcome of E.
\<close>

definition vr_continuity :: "('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool"  where
  "vr_continuity r \<equiv>
      (\<forall> A V V' W p q s. finite_profile V A p \<and> finite_profile V' A q \<and> finite_profile W A s \<and> 
        V \<inter> V' = {} \<and> W \<inter> V' = {} \<longrightarrow> 
        (\<exists>n. n_copy n V W p s \<longrightarrow> (r (W \<union> V') A (joint_profile V' W q s) \<subseteq> r V A p)))"


lemma vr_continuity_prereq:
fixes 
  r :: "('a, 'v, 'b, 'r) Voting_Rule" and
  A :: "'a set" and
  V V' W :: "'v set" and
  p q s :: "('v, 'b) Profile"
assumes 
  cont: "vr_continuity r" and
  fp: "finite_profile V A p" and
  fq: "finite_profile V' A q" and
  disj: "V \<inter> V' = {}" and
  disj: "W \<inter> V' = {}" 
shows "\<exists>n. n_copy n V W p s \<longrightarrow> r (W \<union> V') A (joint_profile V' W q s) \<subseteq> r V A p" 
using vr_continuity_def assms 
by blast

text \<open>
  Consistency states that if some contenders are chosen for two disjoint elections, then precisely 
  those contenders are chosen in the joint election.
\<close>

definition vr_consistency :: "('a, 'v, 'b, 'r) Voting_Rule \<Rightarrow> bool"  where
  "vr_consistency r \<equiv> (\<forall> A V V' p q. 
    well_formed_profile V A p \<and> well_formed_profile V' A q \<and> V \<inter> V' = {} \<and> (r V A p \<inter> r V' A q \<noteq> {})
      \<longrightarrow> (r (V \<union> V') A (joint_profile V V' p q) = r V A p \<inter> r V' A q))"

subsubsection \<open>Independence of Losers\<close>

text \<open>TODO, maybe\<close>

end

subsection \<open>The Elector Voting Rule\<close>

text \<open>
  The elector voting rule elects exactly those contenders that a given electoral module elects.
  It therefore discards all deferred and rejected contenders.
\<close>

context electoral_structure 
begin

fun elector :: "('r, 'v, 'b) Electoral_Module \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule" where
"elector m V A p = elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"

text \<open>
  The following variant of the  elector voting rule elects elected and deferred contenders,
  therefore discarding exactly the rejected contenders.
\<close>
fun elector\<^sub>d :: "('r, 'v, 'b) Electoral_Module \<Rightarrow> ('a, 'v, 'b, 'r) Voting_Rule" where
"elector\<^sub>d m V A p = ((elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p))
        \<union> (defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)))"

        
lemma elector_inherits_anonymity:   
fixes m :: "('r, 'v, 'b) Electoral_Module"
assumes anon: "anonymity m"
shows "vr_anonymity (elector m)"
proof (unfold vr_anonymity_def, simp add: Let_def, safe)
fix 
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
let ?V = "(\<pi> ` V)"
let ?p = "(limit_by_conts (contenders A) \<circ> p)"
let ?q = "(p \<circ> the_inv \<pi>)"
assume 
  bij: "bij \<pi>" and
  finA: "finite A" and
  finV: "finite V" and
  wfp: "well_formed_profile V A p" and
  finV': "finite ?V" and
  wfp': "well_formed_profile ?V A ?q" and
  win: "c \<in> elect m V (contenders A) ?p"
  have "(A, ?V, ?q) = rename \<pi> (A, V, p)" by simp
  thus "c \<in> elect m ?V (contenders A) (limit_by_conts (contenders A) \<circ> ?q)"
  using anon bij finA finV finV' wfp wfp' win permute_V_preserves_result
  by metis
next
fix 
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
  let ?V = "(\<pi> ` V)"
  let ?p = "(limit_by_conts (contenders A) \<circ> p)"
  let ?q = "(p \<circ> the_inv \<pi>)"
assume 
  bij: "bij \<pi>" and
  finA: "finite A" and
  finV: "finite V" and
  wfp: "well_formed_profile V A p" and
  finV': "finite ?V" and
  wfp': "well_formed_profile ?V A ?q" and
  win: "c \<in> elect m ?V (contenders A) (limit_by_conts (contenders A) \<circ> ?q)"
  have inv_bij: "bij (the_inv \<pi>)"
    using bij
    by (simp add: bij_betw_the_inv_into)
  have inv_inv: "the_inv (the_inv \<pi>) = \<pi>" 
    using bij bij_inv_inv 
    by auto
  have *: "V = ((the_inv \<pi>) \<circ> \<pi>) ` V"
    using bij
    by (simp add: bij_betw_def the_inv_f_f)
  hence "V = (the_inv \<pi>) ` ?V" by auto
  have "p = p \<circ> the_inv \<pi> \<circ> \<pi>" 
    using inv_bij inv_inv
    by (metis comp_assoc comp_id bij_id)
  hence "p = ?q \<circ> \<pi>" by simp
  hence "p = (?q \<circ> the_inv (the_inv \<pi>))" 
    using inv_inv by presburger
  hence "(A, V, p) = rename (the_inv \<pi>) (A, ?V, ?q)"
    using * 
    by fastforce
  thus "c \<in> elect m V (contenders A) ?p"
    using anon inv_bij finA finV finV' wfp wfp' win permute_V_preserves_result
    by metis
qed

lemma elector\<^sub>d_inherits_anonymity:   
fixes m :: "('r, 'v, 'b) Electoral_Module"
assumes anon: "anonymity m"
shows "vr_anonymity (elector\<^sub>d m)"
proof (unfold vr_anonymity_def Let_def, safe)
fix 
  A A' :: "'a set" and
  V V' :: "'v set" and
  p q :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
assume 
  bij: "bij \<pi>" and
  rename: "rename \<pi> (A, V, p) = (A', V', q)" and
  finA: "finite A" and
  finV: "finite V" and
  finV': "finite V'" and
  wfp: "well_formed_profile V A p" and
  wfp': "well_formed_profile V' A' q" and
  win: "c \<in> elector\<^sub>d m V A p"
  have "V' = (\<pi> ` V)" using rename by simp
  have A_id: "A' = A" using rename by simp
  have "q = (p \<circ> the_inv \<pi>)" using rename by simp
  have *: "c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p) \<union>
         defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)" 
    using win elector\<^sub>d.simps 
    by simp
  thus "c \<in> elector\<^sub>d m V' A' q"
  proof (cases)
    assume "c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)" 
    hence "c \<in> elect m V' (contenders A') (limit_by_conts (contenders A) \<circ> q)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V' A' q" by (simp add: A_id)
  next
    assume "\<not> c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
    hence "c \<in> defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
      using * by blast
    hence "c \<in> defer m V' (contenders A') (limit_by_conts (contenders A) \<circ> q)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V' A' q" by (simp add: A_id)
  qed
next
fix 
  A A' :: "'a set" and
  V V' :: "'v set" and
  p q :: "('v, 'b) Profile" and
  \<pi> :: "'v \<Rightarrow> 'v" and
  c :: 'r
assume 
  bij: "bij \<pi>" and
  rename: "rename \<pi> (A, V, p) = (A', V', q)" and
  finA: "finite A" and
  finV: "finite V" and
  finV': "finite V'" and
  wfp: "well_formed_profile V A p" and
  wfp': "well_formed_profile V' A' q" and
  win: "c \<in> elector\<^sub>d m V' A' q"
  have "V' = (\<pi> ` V)" using rename by simp
  have A_id: "A' = A" using rename by simp
  have "q = (p \<circ> the_inv \<pi>)" using rename by simp
  have *: "c \<in> elect m V' (contenders A') (limit_by_conts (contenders A') \<circ> q) \<union>
         defer m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)" 
    using win elector\<^sub>d.simps 
    by simp
  thus "c \<in> elector\<^sub>d m V A p"
  proof (cases)
    assume "c \<in> elect m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)" 
    hence "c \<in> elect m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V A p" by (simp add: A_id)
  next
    assume "\<not> c \<in> elect m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)"
    hence "c \<in> defer m V' (contenders A') (limit_by_conts (contenders A') \<circ> q)"
      using * by blast
    hence "c \<in> defer m V (contenders A) (limit_by_conts (contenders A) \<circ> p)"
      using A_id assms bij finA finV finV' permute_V_preserves_result rename wfp wfp'
      by metis
    thus "c \<in> elector\<^sub>d m V A p" by (simp add: A_id)
    qed
qed

lemma elector\<^sub>d_simp [simp]:
fixes 
  m :: "('r, 'v, 'b) Electoral_Module" and
  A :: "'a set" and
  V :: "'v set" and
  p :: "('v, 'b) Profile"
assumes 
  mod: "electoral_module m" and 
  p_id: "p = (limit_by_conts (contenders A)) \<circ> p"
shows "(elector\<^sub>d m) V A p = (elect m V (contenders A) p) \<union> (defer m V (contenders A) p)" 
using mod p_id 
by  simp
   
end
end