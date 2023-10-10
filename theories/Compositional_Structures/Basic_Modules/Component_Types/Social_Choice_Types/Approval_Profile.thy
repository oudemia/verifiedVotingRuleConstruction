section \<open>Approval Profile\<close>

theory Approval_Profile
  imports Approval_Sets
begin

text \<open>
  Approval profiles denote the decisions made by the individual voters on
  the eligible alternatives. They are represented in the form of one set of 
  approvaed alternatives (e.g., selected on a ballot) per voter, collectively 
  captured in a list of such approval sets.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A profile contains one ballot for each voter.
\<close>

type_synonym 'a Approval_Profile = "('a Approval) list"

type_synonym 'a Election = "'a set \<times> 'a Approval_Profile"

fun alts_\<E> :: "'a Election \<Rightarrow> 'a set" where "alts_\<E> E = fst E"

fun prof_\<E> :: "'a Election \<Rightarrow> 'a Approval_Profile" where "prof_\<E> E = snd E"

text \<open>
  A profile on a finite set of alternatives A contains only ballots that are
  (possibly empty) subsets of A.
\<close>

definition profile :: "'a set \<Rightarrow> 'a Approval_Profile \<Rightarrow> bool" where
  "profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> (p!i) \<subseteq> A"

lemma profile_set :
  fixes
    A :: "'a set" and
    p :: "'a Approval_Profile"
  shows "profile A p \<equiv> (\<forall> b \<in> (set p). b \<subseteq> A)"
  unfolding profile_def all_set_conv_all_nth
  by simp

abbreviation finite_profile :: "'a set \<Rightarrow> 'a Approval_Profile \<Rightarrow> bool" where
  "finite_profile A p \<equiv> finite A \<and> profile A p"
