theory Approval_Profile
  imports Profile
begin

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses their preferences by indicating a set of alternatives that they approve of.
\<close>

type_synonym 'a Approval_Set = "'a set"

type_synonym ('v, 'a) Approval_Profile = "('v, 'a Approval_Set) Profile"

fun ballot_\<A>\<V> :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> bool" where
"ballot_\<A>\<V> A b = (b \<subseteq> A)"

definition default_ballot_\<A>\<V> :: "'a Approval_Set" where
"default_ballot_\<A>\<V> = {}"

fun prefers_\<A>\<V> :: "'a Approval_Set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"prefers_\<A>\<V> A a1 a2 = ((a1 \<in> A) \<and> (a2 \<notin> A))"

fun wins_\<A>\<V> :: "'a Approval_Set \<Rightarrow> 'a \<Rightarrow> bool" where
"wins_\<A>\<V> A a = (a \<in> A)"

fun limit_\<A>\<V>_ballot :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> 'a Approval_Set" where
"limit_\<A>\<V>_ballot A b = A \<inter> b"

end