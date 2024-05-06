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

global_interpretation approval_profile:
  profile "well_formed_AV" "well_formed_bal_AV"
proof (unfold_locales) 
  fix
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a) Approval_Profile"
  assume "\<forall> v \<in> V. well_formed_bal_AV A (p v)"
  show "well_formed_AV V A p" by auto
qed

(* setup Locale_Code.close_block *)

end