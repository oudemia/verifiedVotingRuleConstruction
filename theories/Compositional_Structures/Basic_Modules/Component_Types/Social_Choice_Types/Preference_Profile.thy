theory Preference_Profile
  imports Profile_Loc Preference_Relation
begin

subsection \<open>Definition\<close>

text \<open>
  Each voter expresses their preferences by indicating a linear order on the alternatives A.
\<close>

type_synonym ('a, 'v) Preference_Profile = "'v \<Rightarrow> ('a Preference_Relation)"

fun well_formed_PV_ballot :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
"well_formed_PV_ballot A b = linear_order_on A b"

definition default_PV_ballot :: "'a Preference_Relation" where
"default_PV_ballot = {}"

fun prefers_PV :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"prefers_PV b a1 a2 = (a1 \<in> (above b a2))"

fun wins_PV :: "'a Preference_Relation \<Rightarrow> 'a \<Rightarrow> bool" where
"wins_PV b a = (above b a = {a})"

fun well_formed_PV_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Preference_Profile \<Rightarrow> bool" where
"well_formed_PV_profile V A p = (\<forall> v \<in> V. linear_order_on A (p v))"

fun win_count_PV :: "'v set \<Rightarrow> ('a, 'v) Preference_Profile \<Rightarrow> 'a \<Rightarrow> enat" where
  "win_count_PV V p a = (if (finite V)
    then card {v \<in> V. above (p v) a = {a}} else infinity)"

fun prefer_count_PV :: "'v set \<Rightarrow> ('a, 'v) Preference_Profile \<Rightarrow> 'a \<Rightarrow>'a \<Rightarrow> enat" where
  "prefer_count_PV V p x y = (if (finite V)
      then card {v \<in> V. (let r = (p v) in (y \<preceq>\<^sub>r x))} else infinity)"

end
