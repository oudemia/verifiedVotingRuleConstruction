chapter \<open>Social-Choice Types\<close>

section \<open>Approval Set\<close>

theory Approval_Set
  imports Main
begin

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses their preferences by listing the alternatives that they approve of.
\<close>

type_synonym 'a Approval = "'a set"


type_synonym 'a Vote = "'a set \<times> 'a Approval"

fun is_approved :: "'a \<Rightarrow> 'a Approval \<Rightarrow> bool" where
    "is_approved a s = (a \<in> s)"

fun alts_\<V> :: "'a Vote \<Rightarrow> 'a set" where "alts_\<V> V = fst V"

fun pref_\<V> :: "'a Vote \<Rightarrow> 'a Approval" where "pref_\<V> V = snd V"

end
