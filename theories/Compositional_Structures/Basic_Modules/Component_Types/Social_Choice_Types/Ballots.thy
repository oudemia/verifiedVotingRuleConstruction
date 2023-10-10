 section \<open>Ballots and Ballot Types\<close>

theory Ballots
  imports Preference_Relation Approval_Set
begin

text \<open>
  A ballot contains information about the preferences of a single voter towards electable
  alternatives. There is exactly one ballot per voter in an election.
  As of now, we distinguish between preference based and approval based ballots.
\<close>

subsection \<open>Definition\<close>

text \<open>
  The definition of profiles, elections etc. should not depend on a concrete ballot type but only
  rely on exactly one valid ballot per voter. Whether a ballot is valid depends on the ballot type
  (e.g. a subset of alternatives in the case of approval based ballots).
 \<close>

(*
locale general_election = 
  fixes is_ballot:: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
end
*)

locale preference_based
begin
type_synonym 'a Ballot = "'a Preference_Relation"
type_synonym 'a Profile = "('a Ballot) list"

definition is_ballot:: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"is_ballot A b \<equiv> linear_order_on A b"

definition is_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"is_profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> is_ballot A (p!i)"
end

(*
sublocale preference_based \<subseteq> general_election
  done
*)

locale approval_based
begin
type_synonym 'a Ballot = "'a Approval_Set"

type_synonym 'a Profile = "('a Ballot) list"

definition is_ballot:: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> bool" where
"is_ballot A b \<equiv> b \<subseteq> A"

definition is_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"is_profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> is_ballot A (p!i)"
end

(*
sublocale approval_based \<subseteq> general_election
  done
*)

(* test*)
context approval_based
begin
lemma profile_set :
  fixes
    A :: "'a set" and
    p :: "'a Profile"
  shows "is_profile A p \<equiv> (\<forall> b \<in> (set p). b \<subseteq> A)"
  unfolding is_profile_def all_set_conv_all_nth is_ballot_def
  by simp
end

