\<^marker>\<open>creator "Henriette Färber, Karlsruhe Institute of Technology (KIT)"\<close>

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


locale general_election = 
  fixes is_ballot:: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
end

text \<open>
  In a preference-based context, a profile on a finite set of alternatives A contains 
  only ballots that are linear orders on A.
\<close>

locale preference_based
begin
type_synonym 'a Ballot = "'a Preference_Relation"
type_synonym 'a Profile = "('a Ballot) list"
type_synonym 'a Election = "'a set \<times> 'a Profile"
type_synonym 'a Vote = "'a set \<times> 'a Ballot"

definition is_ballot:: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"is_ballot A b \<equiv> linear_order_on A b"

definition is_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"is_profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> is_ballot A (p!i)"

fun alts_\<E> :: "'a Election \<Rightarrow> 'a set" where "alts_\<E> E = fst E"
fun prof_\<E> :: "'a Election \<Rightarrow> 'a Profile" where "prof_\<E> E = snd E"

fun alts_\<V> :: "'a Vote \<Rightarrow> 'a set" where "alts_\<V> V = fst V"
fun pref_\<V> :: "'a Vote \<Rightarrow> 'a Ballot" where "pref_\<V> V = snd V"
end

sublocale preference_based \<subseteq> general_election
  done

text \<open>
  In an approval-based context, a profile on a finite set of alternatives A contains only ballots 
  that are (possibly empty) on A.
\<close>

locale approval_based
begin
type_synonym 'a Ballot = "'a Approval_Set"
type_synonym 'a Profile = "('a Ballot) list"
type_synonym 'a Election = "'a set \<times> 'a Profile"

fun alts_\<E> :: "'a Election \<Rightarrow> 'a set" where "alts_\<E> E = fst E"
fun prof_\<E> :: "'a Election \<Rightarrow> 'a Profile" where "prof_\<E> E = snd E"

definition is_ballot:: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> bool" where
"is_ballot A b \<equiv> b \<subseteq> A"

definition is_profile :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"is_profile A p \<equiv> \<forall> i::nat. i < length p \<longrightarrow> is_ballot A (p!i)"
end

sublocale approval_based \<subseteq> general_election
  done

