theory Profile_Interpretations
  imports Profile_Loc
          Approval_Profile
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale-Code block
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale-Code block as well.
\<close>

(* setup Locale_Code.open_block *)

global_interpretation approval_ballot:
  ballot "well_formed_AV_ballot" "prefers_AV" "wins_AV"
proof (unfold_locales)
  fix
    A :: "'a Approval_Set" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "prefers_AV A a1 a2"
  thus "\<not> wins_AV A a2" by simp
qed


global_interpretation approval_profile:
  profile "well_formed_AV" "well_formed_bal_AV"
proof (unfold_locales) 
  show "\<And> A V p . \<forall> v \<in> V. well_formed_bal_AV A (p v) \<Longrightarrow> well_formed_AV V A p" by simp
qed


text \<open>
  In a preference-based context, a profile on a finite set of alternatives A contains 
  only ballots that are linear orders on A.
\<close>
(* setup Locale_Code.close_block *)

end