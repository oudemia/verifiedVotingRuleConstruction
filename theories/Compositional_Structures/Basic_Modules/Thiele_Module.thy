section \<open>Thiele Module\<close>

theory Thiele_Module
  imports 
      "Component_Types/Voting_Rule"      
      "Component_Types/Elimination_Module"
      "Component_Types/Social_Choice_Types/Aggregate_Profile"
      "Component_Types/Social_Choice_Types/Electoral_Structure"
begin

subsection \<open>Aggregated Profiles for Thiele Methods\<close>

fun thiele_ballot :: "('a Committee) set \<Rightarrow> (('a Committee) \<Rightarrow> nat) \<Rightarrow> bool" where
"thiele_ballot R b = (\<forall> r \<in> R. b r \<ge> 0)"

fun thiele_result :: "('a Committee) set \<Rightarrow> ('a Committee) Result \<Rightarrow> bool" where
"thiele_result R r = (disjoint3 r \<and> set_equals_partition R r)"

fun (in committee_result) thiele_aggregate :: "('a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate b W = (card (W \<inter> b))"


sublocale committee_result \<subseteq> aggregate_structure
    "\<lambda> b c d. (b c > b d)" (*prefers*)
    "\<lambda> b c. (\<forall> d. b c \<ge> b d)" (*wins*)
    "\<lambda> C b. b" (* "\<lambda> C b c. if c \<in> C then b c else 0" limit_ballot*)
    "\<lambda> C D. C \<inter> D"(*limit contenders*)
    thiele_ballot (*well formed ballot*)
    thiele_result (*well formed result*)
    "\<lambda> C b. b" (* "\<lambda> C b c. if c \<in> C then b c else 0" limit_ballot*)
    "default_ballot_\<A>\<V>" (*empty base*)
    "prefers_\<A>\<V>" (*prefers base*) 
    "wins_\<A>\<V>" (*wins base*)
    "limit_\<A>\<V>_ballot" (*limit base*)
    "\<lambda> A rs. {r \<inter> A | r. r \<in> rs}" (*limit contenders base*)
    "\<lambda> rs. \<Union> rs" (*affected alts base*)
    "ballot_\<A>\<V>" (*base ballot*)
    "\<lambda> A r. disjoint3 r" (*base result*)
    "limit_app_to_comm" (*base limit by conts*)
    "\<lambda> c. 0" (*empty ballot*) 
    "\<lambda> x. x"(*affected alts*)
    committee_contenders 
    thiele_aggregate
proof (unfold_locales)
  fix 
    b :: "'a Committee \<Rightarrow> nat" and
    c :: "'a Committee" and
    d :: "'a Committee"
  assume
    assm: "c \<noteq> d \<and> b d < b c"
  hence "b d < b c" by simp
  thus " \<not>(\<forall>e. b e \<le> b d)" using leD by auto
next
  fix
    C :: "('a Committee) set" and
    b :: "'a Committee \<Rightarrow> nat"
  assume "thiele_ballot C b"
  thus "b = b" by simp
next
fix
    C :: "('a Committee) set" and
    D :: "('a Committee) set" and
    b :: "'a Committee \<Rightarrow> nat"
  assume "C \<subseteq> D"
  thus "b = b" by simp
next
fix
    C :: "('a Committee) set" and
    D :: "('a Committee) set" and
    b :: "'a Committee \<Rightarrow> nat"
  assume "thiele_ballot D b \<and> C \<subseteq> D"
  thus "thiele_ballot C b" by simp
next
 fix
    C :: "('a Committee) set" and
    r :: "('a Committee) Result"
  assume " set_equals_partition (C \<inter> UNIV) r \<and> disjoint3 r"
  thus "thiele_result C r" by simp
next
  fix
    C :: "('a Committee) set" and
    D :: "('a Committee) set"
  show "C \<inter> D \<subseteq> C" by simp
next
  fix b :: "('a Committee) \<Rightarrow> nat"
  show "b = b" by simp
next
  fix C :: "('a Committee) set"
  show "C = C" by simp
next
  have "\<forall> W. W \<inter> default_ballot_\<A>\<V> = {}" by (simp add: default_ballot_\<A>\<V>_def)
  hence "\<forall> W. (card (W \<inter> default_ballot_\<A>\<V>)) = 0" by (metis card.empty)
  thus "thiele_aggregate default_ballot_\<A>\<V> = (\<lambda>c. 0)" by (metis thiele_aggregate.simps)
next
  fix A :: "'a set"
  have " \<Union> (committees A) \<subseteq> A"
    proof
      fix a :: "'a"
      assume "a \<in> (\<Union> (committees A))"
      hence "\<exists> C. C \<subseteq> A \<and> card C = k \<and> a \<in> C" by simp
      thus "a \<in> A" by blast
    qed
    thus "\<Union> (committee_contenders A) \<subseteq> A" by simp
next
 fix
    A :: "'a set" and
    b :: "'a Approval_Set"
  assume "ballot_\<A>\<V> A b"
  thus "thiele_ballot (committee_contenders A) (thiele_aggregate b)" by simp
next
 fix
    A :: "'a set" and
    B :: "'a set" and
    b :: "'a Approval_Set"
  assume "A \<subseteq> B \<and> ballot_\<A>\<V> A b"
  thus "thiele_ballot (committee_contenders B) (thiele_aggregate b)" by simp
qed


sublocale committee_result \<subseteq> aggregate_ballot
"\<lambda> c. 0" (*empty ballot*) 
"\<lambda> b c d. (b c > b d)" (*prefers*)
"\<lambda> b c. (\<forall> d. b c \<ge> b d)" (*wins*)
"\<lambda> C b. b" (* "\<lambda> C b c. if c \<in> C then b c else 0" limit_ballot*)
"ballot_\<A>\<V>" (*base ballot*)
"default_ballot_\<A>\<V>" (*empty base*)
"prefers_\<A>\<V>" (*prefers base*) 
"wins_\<A>\<V>" (*wins base*)
"limit_\<A>\<V>_ballot" (*limit base*)
thiele_ballot (*well formed ballot*)
committee_contenders 
thiele_aggregate
proof (unfold_locales)
 fix
    A :: "'a set" and
    b :: "'a Approval_Set"
  assume "ballot_\<A>\<V> A b"
  thus "thiele_ballot (committee_contenders A) (thiele_aggregate b)" by simp
next
 fix
    A :: "'a set" and
    B :: "'a set" and
    b :: "'a Approval_Set"
  assume "A \<subseteq> B \<and> ballot_\<A>\<V> A b"
  thus "thiele_ballot (committee_contenders B) (thiele_aggregate b)" by simp
qed

fun (in committee_result) thiele_agg_profile :: "('v, 'a Approval_Set, 'a Committee, nat) Profile_Aggregation" where
"thiele_agg_profile p v W = thiele_aggregate (p v) W"


subsection \<open>Definition\<close>

type_synonym Thiele_Score = "nat => nat"

type_synonym Thiele_Score' = "nat => real"

fun thiele_module :: "(nat \<Rightarrow> nat) \<Rightarrow> ('a Committee, 'v, ('a Committee \<Rightarrow> nat)) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R p. (\<Sum> v \<in> V.  s (p v r)))) V C p"

fun (in committee_result) thiele_family :: "('v, 'a, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where 
"thiele_family w V A p =
	elect (thiele_module w) V (committees A) (thiele_agg_profile p)"

subsection \<open>Sequential Thiele Methods\<close>

subsection \<open>Reverse-Sequential Thiele Methods\<close>

end