theory Profile_Loc
  imports Main
          "HOL-Library.Extended_Nat"
begin

text \<open>
  A ballot contains information about the preferences of a single voter towards electable
  alternatives. There is exactly one ballot per voter in an election.
  As of now, we distinguish between preference based and approval based ballots.
\<close>

subsection \<open>Auxiliary Functions\<close>

text \<open>
  A profile is a function that assigns a ballot to each voter in the election. The ballot type
  depends on the election setting.
\<close>
type_synonym ('v, 'b) Profile = "'v \<Rightarrow> 'b"

type_synonym ('a, 'v, 'b) Election = "'a set \<times> 'v set \<times> ('v, 'b) Profile"

fun alternatives_\<E> :: "('a, 'v, 'b) Election \<Rightarrow> 'a set" where
  "alternatives_\<E> E = fst E"

fun voters_\<E> :: "('a, 'v, 'b) Election \<Rightarrow> 'v set" where
  "voters_\<E> E = fst (snd E)"

fun profile_\<E> :: "('a, 'v, 'b) Election \<Rightarrow> ('v, 'b) Profile" where
  "profile_\<E> E = snd (snd E)"

fun election_equality :: "('a, 'v, 'b) Election \<Rightarrow> ('a, 'v, 'b) Election \<Rightarrow> bool" where
  "election_equality (A, V, p) (A', V', p') =
        (A = A' \<and> V = V' \<and> (\<forall> v \<in> V. p v = p' v))"


subsection \<open>Definition\<close>

text \<open>
  A result generally is related to the alternative set A (of type 'a).
  A result should be well-formed on the alternatives.
  Also it should be possible to limit a well-formed result to a subset of the alternatives.

  Specific result types like social choice results (sets of alternatives) can be realized
  via sublocales of the result locale.
\<close>

locale profile =
  fixes
    well_formed :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" and
    well_formed_bal :: "'a set \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "\<And> (A::('a set)) (V::('v set)) (p::(('v, 'b) Profile)).
    (\<forall> v \<in> V. (well_formed_bal A (p v))) \<Longrightarrow> well_formed V A p "

(*  win_count :: "'v set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'a \<Rightarrow> enat" *)

context profile 
begin

text \<open>
  A profile on a set of alternatives A and a voter set V consists of ballots
  that are well formed on A for all voters in V.
  A finite profile is one with finitely many alternatives and voters.
\<close>
abbreviation  finite_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "finite_profile V A p \<equiv> finite A \<and> finite V \<and> well_formed V A p"

abbreviation finite_election :: "('a,'v,'b) Election \<Rightarrow> bool" where
  "finite_election E \<equiv> finite_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)"

definition finite_elections_\<V> :: "('a, 'v, 'b) Election set" where
  "finite_elections_\<V> = {E :: ('a, 'v, 'b) Election. finite (voters_\<E> E)}"

definition finite_elections :: "('a, 'v, 'b) Election set" where
  "finite_elections = {E :: ('a, 'v, 'b) Election. finite_election E}"

definition valid_elections :: "('a,'v, 'b) Election set" where
  "valid_elections = {E. well_formed (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)}"

end

locale ballots = 
  fixes ballot:: "'alt set \<Rightarrow> 'bal \<Rightarrow> bool"
    and winner:: "'alt \<Rightarrow> 'bal \<Rightarrow> bool" 
begin
end


text \<open>
  In a preference-based context, a profile on a finite set of alternatives A contains 
  only ballots that are linear orders on A.
\<close>

(*
locale preference_ballots =
  fixes ballot:: "'alt set \<Rightarrow> 'alt Preference_Relation \<Rightarrow> bool"
  assumes ballot_def: "ballot A b \<equiv> linear_order_on A b"
begin
end

sublocale preference_ballots \<subseteq> ballots
  done

definition pref_ballot :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"pref_ballot A b \<equiv> linear_order_on A b "

definition pref_winner :: "'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"pref_winner a b \<equiv> above b a = {a}"

global_interpretation pref_ballots:
  ballots "pref_ballot" "pref_winner"
done

*)
end