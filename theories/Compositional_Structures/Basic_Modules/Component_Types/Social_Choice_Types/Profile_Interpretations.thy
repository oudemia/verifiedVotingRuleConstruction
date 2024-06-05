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
  profile "ballot_\<A>\<V>" "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>"
proof (unfold_locales)
  fix
    A :: "'a Approval_Set" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_\<A>\<V> A a1 a2"
  thus "\<not> wins_\<A>\<V> A a2" by simp
  qed
  

subsection \<open>Preference Profiles\<close>

global_interpretation \<P>\<V>_profile:
  profile "ballot_\<P>\<V>" "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>"
proof (unfold_locales)
  fix
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_\<P>\<V> b a1 a2"
  thus "\<not> wins_\<P>\<V> b a2" by auto
  qed

setup Locale_Code.close_block

end