theory Choice_Schema
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

type_synonym ('v, 'r, 'i) Choice_Schema = "'v \<Rightarrow> 'r \<Rightarrow> 'i"


subsubsection \<open>Choice Scores\<close>

type_synonym Thiele_ID = "nat \<Rightarrow> ereal"

text \<open>
  The choice schema for a Thiele method has a specific shape: For any voter v and any
  committee W, the schema returns the Thiele score of the ballot of v and W.
\<close>

fun thiele_score :: "Thiele_ID \<Rightarrow> 'a Committee \<Rightarrow> 'a Committee \<Rightarrow> ereal" where
  "thiele_score i W B = i (card (W \<inter> B))"

fun thiele_choice_schema :: " Thiele_ID \<Rightarrow> ('v, 'a Approval_Set) Profile \<Rightarrow> ('v, 'a Committee, ereal) Choice_Schema" where
"thiele_choice_schema i p v c = thiele_score i c (p v)"


fun av_score :: "Thiele_ID" where
"av_score n = n"

fun av_schema :: "('v, 'a Approval_Set) Profile \<Rightarrow> ('v, 'a Committee, ereal) Choice_Schema" where
"av_schema p = thiele_choice_schema av_score p"

fun harmonic :: "nat \<Rightarrow> ereal" where
"harmonic n = sum (\<lambda>x. 1/x) {1..n::nat}"

fun pav_score :: "Thiele_ID" where
"pav_score n = harmonic n"

subsection \<open>Schema Transformations\<close>

end