theory Profile_Loc
  imports Main
          "HOL-Library.Extended_Nat"
begin

subsection \<open>Definition\<close>

text \<open>
  A ballot contains information about the preferences of a single voter towards electable
  alternatives.
\<close>

locale ballot =
  fixes 
    well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    default_ballot :: "'b" and
    prefers :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and
    wins :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<And> (b::'b) (a1::'a) (a2::'a). (a1 \<noteq> a2 \<and> prefers b a1 a2) \<Longrightarrow> \<not> wins b a2"


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


locale profile = ballot +
  fixes
    well_formed_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" and
    win_count :: "'v set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'a \<Rightarrow> enat" 
  assumes "\<And> (A::('a set)) (V::('v set)) (p::(('v, 'b) Profile)).
    (\<forall> v \<in> V. (well_formed_ballot A (p v))) \<Longrightarrow> well_formed_profile V A p "


text \<open>
  A profile on a set of alternatives A and a voter set V consists of ballots
  that are well formed on A for all voters in V.
  A finite profile is one with finitely many alternatives and voters.
\<close>

context profile 
begin

abbreviation  finite_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "finite_profile V A p \<equiv> finite A \<and> finite V \<and> well_formed_profile V A p"

abbreviation finite_election :: "('a, 'v, 'b) Election \<Rightarrow> bool" where
  "finite_election E \<equiv> finite_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)"

definition finite_elections_\<V> :: "('a, 'v, 'b) Election set" where
  "finite_elections_\<V> = {E :: ('a, 'v, 'b) Election. finite (voters_\<E> E)}"

definition finite_elections :: "('a, 'v, 'b) Election set" where
  "finite_elections = {E :: ('a, 'v, 'b) Election. finite_election E}"

definition valid_elections :: "('a, 'v, 'b) Election set" where
  "valid_elections = {E. well_formed_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)}"

\<comment> \<open>This function subsumes elections with fixed alternatives, finite voters, and
    a default value for the profile value on non-voters.\<close>
fun elections_\<A> :: "'a set \<Rightarrow> ('a, 'v, 'b) Election set" where
  "elections_\<A> A =
        valid_elections
      \<inter> {E. alternatives_\<E> E = A \<and> finite (voters_\<E> E)
            \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = default_ballot)}"
end

end