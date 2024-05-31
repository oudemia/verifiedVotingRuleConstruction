theory Profile_Interpretations
  imports Profile_Loc
          Approval_Profile
          Preference_Profile
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale-Code block
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale-Code block as well.
\<close>

(* setup Locale_Code.open_block *)

subsection \<open>Approval Profiles\<close>

global_interpretation approval_ballot:
  ballot "well_formed_AV_ballot" "default_AV_ballot" "prefers_AV" "wins_AV"
proof (unfold_locales)
  fix
    A :: "'a Approval_Set" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_AV A a1 a2"
  thus "\<not> wins_AV A a2" by simp
qed

global_interpretation approval_profile:
   profile "well_formed_AV_ballot" "default_AV_ballot" "prefers_AV" "wins_AV" "well_formed_AV_profile" "win_count_AV"
proof (unfold_locales) 
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a) Approval_Profile"
  assume "\<forall> v \<in> V. well_formed_AV_ballot A (p v)"
  thus " well_formed_AV_profile V A p" by simp
qed

subsection \<open>Preference Profiles\<close>

global_interpretation preference_ballot:
  ballot "well_formed_PV_ballot" "default_PV_ballot" "prefers_PV" "wins_PV"
proof (unfold_locales)
  fix
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_PV b a1 a2"
  thus "\<not> wins_PV b a2" by auto
qed

global_interpretation preference_profile:
   profile "well_formed_PV_ballot" "default_PV_ballot" "prefers_PV" "wins_PV" "well_formed_PV_profile" "win_count_PV"
proof (unfold_locales) 
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Preference_Profile"
  assume "\<forall> v \<in> V. well_formed_PV_ballot A (p v)"
  thus " well_formed_PV_profile V A p" by simp
qed

(* setup Locale_Code.close_block *)

end