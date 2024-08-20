section \<open>Properties and Property Families\<close>

theory Properties

imports
    Electoral_Module
    Enhanced_Profile
begin

text \<open>
  The description of properties for voting rules may be arbitrarily complex and therefore more
  difficult to understand. This is especially relevant for multiwinner voting rules, where properties
  may refer to subsets of results. 
  Complex properties may benefit from a component-based description. This also allows us to simplify
  proofs on implication relations between properties.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A property states a postcondition on the results of a given voting rule for elections satisfying 
  a precondition. A family of properties
\<close>

type_synonym ('v, 'a, 'b, 'r, 'i, 'p) Property_Family = "('v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b set) \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow>
  ('v set \<Rightarrow> 'r set \<Rightarrow> ('v, 'b set) \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> (('v, 'a, 'b, 'r) Voting_Rule \<Rightarrow> bool)"

text \<open>
  Instances of a property family are obtained by providing parameters for the pre- and postconditions.
  A property family is valid if there is a weak ordering on the parameters such that if
  p \<le> p', then the property for parameter p' implies the property for parameters p.
\<close>
fun property_family :: "('v, 'a, 'b, 'r, 'i) Voting_Rule_Family => bool" where
"voting_rule_family f = True"

end