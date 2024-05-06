theory Approval_Profile
  imports Profile_Loc
begin

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses their preferences by indicating a set of alternatives that they approve of.
\<close>

type_synonym 'a Approval_Set = "'a set"

type_synonym 'a Vote = "'a set \<times> 'a Approval_Set"

type_synonym ('v, 'a) Approval_Profile = "('v, 'a Approval_Set) Profile"

fun alts_\<V> :: "'a Vote \<Rightarrow> 'a set" where
  "alts_\<V> V = fst V"

fun appr_\<V> :: "'a Vote \<Rightarrow> 'a Approval_Set" where
  "appr_\<V> V = snd V"


fun well_formed_AV :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'a) Approval_Profile \<Rightarrow> bool" where
"well_formed_AV V A p = (\<forall> v \<in> V. (p v) \<subseteq> A)"

fun well_formed_bal_AV :: "'a set \<Rightarrow> 'a Approval_Set \<Rightarrow> bool" where
"well_formed_bal_AV A b = (b  \<subseteq> A)"

fun win_count_AV :: "'v set \<Rightarrow> ('v, 'a) Approval_Profile \<Rightarrow> 'a \<Rightarrow> enat" where
"win_count_AV V p a = card {v \<in> V. a \<in> (p v)}"



end