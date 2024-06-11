theory Preference_Profile
  imports Profile Preference_Relation
begin

text \<open>
  Preference profiles denote the decisions made by the individual voters on
  the eligible alternatives. They are represented in the form of one preference
  relation (e.g., selected on a ballot) per voter, collectively captured in a
  mapping of voters onto their respective preference relations.
  If there are finitely many voters, they can be enumerated and the mapping can
  be interpreted as a list of preference relations.
  Unlike the common preference profiles in the social-choice sense, the
  profiles described here consider only the (sub-)set of alternatives that are
  received.
\<close>

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses their preferences by indicating a linear order on the alternatives A.
\<close>

type_synonym ('a, 'v) Preference_Profile = "'v \<Rightarrow> ('a Preference_Relation)"

fun ballot_\<P>\<V> :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"ballot_\<P>\<V> A b = linear_order_on A b"

definition default_ballot_\<P>\<V> :: "'a Preference_Relation" where
"default_ballot_\<P>\<V> = {}"

fun prefers_\<P>\<V> :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"prefers_\<P>\<V> b a1 a2 = (a1 \<in> (above b a2))"

fun wins_\<P>\<V> :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" where
"wins_\<P>\<V> b a = (above b a = {a})"

fun limit_\<P>\<V>_ballot :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Preference_Relation" where
"limit_\<P>\<V>_ballot A b = (A \<times> A) \<inter> b"

end
