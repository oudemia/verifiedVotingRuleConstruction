section \<open> Ballot Styles\<close>

theory Ballots
  imports Preference_Relation
begin

text \<open>
  A ballot contains information about the preferences of a single voter towards electable
  alternatives. There is exactly one ballot per voter in an election.
  As of now, we distinguish between preference based and approval based ballots
\<close>

subsection \<open>Definition\<close>

text \<open> There is exactly one ballot per voter. \<close>

locale general_election = 
  fixes is_ballot:: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
end

locale preference_based
begin
type_synonym 'a Preference_Relation = "'a rel"
type_synonym 'a Profile = "('a Preference_Relation) list"

definition profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> linear_order_on A (p!i)"

definition is_ballot:: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"is_ballot A b \<equiv> linear_order_on A b"
end

locale approval_based
begin
type_synonym 'a Approval_Set = "'a set"
type_synonym 'a Profile = "('a Approval_Set) list"

definition profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> subset A (p!i)"

definition is_ballot:: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> bool" where
"is_ballot A b \<equiv> subset A b"
end

sublocale preference_based \<subseteq> general_election
  done
sublocale approval_based \<subseteq> general_election
  done
