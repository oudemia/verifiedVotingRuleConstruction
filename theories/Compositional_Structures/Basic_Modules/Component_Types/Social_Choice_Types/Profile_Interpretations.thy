theory Profile_Interpretations
  imports Profile
          Approval_Profile
          Preference_Profile
          Collections.Locale_Code
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale-Code block
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale-Code block as well.
\<close>

setup Locale_Code.open_block

subsection \<open>Approval Profiles\<close>

global_interpretation \<A>\<V>_profile:
  profile "ballot_\<A>\<V>" "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot"
proof (unfold_locales)
  fix
    A :: "'a Approval_Set" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_\<A>\<V> A a1 a2"
  thus "\<not> wins_\<A>\<V> A a2" by simp
  next
  fix
    A :: "'a set" and
    b :: "'a Approval_Set"
    assume "ballot_\<A>\<V> A b"
    hence "(b  \<subseteq> A)" by simp
  thus "limit_\<A>\<V>_ballot A b = b" by (simp add: Int_commute inf.order_iff)
qed
  

subsection \<open>Preference Profiles\<close>

global_interpretation \<P>\<V>_profile:
  profile "ballot_\<P>\<V>" "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot"
proof (unfold_locales)
  fix
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_\<P>\<V> b a1 a2"
  thus "\<not> wins_\<P>\<V> b a2" by auto
  next
  fix
    A :: "'a set" and
    b :: "'a Preference_Relation"
    assume "ballot_\<P>\<V> A b"
    hence "linear_order_on A b" by simp
    hence "b \<subseteq> A \<times> A" by (simp add: order_on_defs refl_on_def)
  thus "limit_\<P>\<V>_ballot A b = b" by auto
qed

setup Locale_Code.close_block

end