chapter \<open>Social-Choice Types\<close>

section \<open>Approval Set\<close>

theory Approval_Set
  imports Main
begin

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses their preferences by listing the alternatives that they approve of.
\<close>

type_synonym 'a Approval_Set = "'a set"

fun is_approved :: "'a \<Rightarrow> 'a Approval_Set \<Rightarrow> bool" where
    "is_approved a s = (a \<in> s)"
end
