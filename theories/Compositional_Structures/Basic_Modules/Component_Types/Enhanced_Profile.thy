theory Enhanced_Profile
imports
    "Social_Choice_Types/Profile_Interpretations"
    "Social_Choice_Types/Result"
    "HOL-Library.Extended_Real"
begin

section \<open>Choice Schemata\<close>
text \<open>
  While a voting rule receives an alternative, electoral modules operate on choices,
  which are of the same type as the results of an election.

  A choice schema is a generalization of a profile and aims to capture information
  about the preference of voters on choices (in contrast to profiles, which capture
  the preferences of voters on alternatives).
  For the sake of clarity, an abstract profile should always store minimally complex data.
\<close>

subsection \<open>Choices\<close>
text \<open>
  Choices are of the same type as election results and represent possible or incomplete
  results that are part of the computation of a final result.
\<close>

fun single_winner_choices :: "'a set \<Rightarrow> 'a set" where
"single_winner_choices A = A"

fun committee_choices :: "'a set \<Rightarrow> nat \<Rightarrow> ('a Committee) set" where
"committee_choices A k = {C. C \<subseteq> A \<and> card C = k}"

subsection \<open>Defintion\<close>

type_synonym ('v, 'r, 'i) Enhanced_Profile = "'v => 'r => 'i"


subsubsection \<open>Contender Scores\<close>


subsection \<open>Enhanced Profile Transformations\<close>

end