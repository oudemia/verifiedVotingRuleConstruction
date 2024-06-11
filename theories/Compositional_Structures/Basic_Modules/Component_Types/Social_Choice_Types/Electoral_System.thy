theory Electoral_System 
imports Profile Result
begin

print_locale result
print_locale profile

locale electoral_system = 
  result well_formed_result limit_set + 
  profile well_formed_ballot empty_ballot prefers wins limit_ballot
  for 
    well_formed_result :: "'a set \<Rightarrow> 'r Result \<Rightarrow> bool" and 
    limit_set :: "'a set \<Rightarrow> 'r set \<Rightarrow> 'r set" and
    well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool"
    and empty_ballot :: "'b"
    and prefers :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and wins :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
    and limit_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b"

(* TODO: win counts etc. for different result types *)

(* TODO: How to do this without unneccessary code duplication? *)
    
end