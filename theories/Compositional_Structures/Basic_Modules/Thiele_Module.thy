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

fun (in committee_result) thiele_aggregate :: "('a Approval_Set, 'a Committee, nat) Ballot_Aggregation" where
"thiele_aggregate b W = (card (W \<inter> b))"

global_interpretation (in committee_result) thiele_profile:
  aggregate_profile
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

type_synonym ('v, 'a, 'b, 'r, 'i) Voting_Rule_Family = 
	"('v, 'b, 'r, 'i) Profile_Aggregation \<Rightarrow>  ('i \<Rightarrow> 'i)  \<Rightarrow> ('v, 'a, 'b, 'r) Voting_Rule"


type_synonym Thiele_Score = "nat => nat"

type_synonym Thiele_Score' = "nat => real"

fun thiele_module :: "('a Committee \<Rightarrow> nat) \<Rightarrow> ('a Committee, 'v, ('a Committee \<Rightarrow> nat)) Electoral_Module" where
"thiele_module s V C p = (max_eliminator (\<lambda> V r R p. (\<Sum> v \<in> V.  s (p v r)))) V C p"

fun (in committee_result) thiele_family :: "('v, 'a, 'a Approval_Set, 'a Committee, nat) Voting_Rule_Family" where 
"thiele_family w V A p =
	elect (thiele_module w) V (committees A) (thiele_agg_profile p)"

subsection \<open>Sequential Thiele Methods\<close>


subsection \<open>Reverse-Sequential Thiele Methods\<close>

end