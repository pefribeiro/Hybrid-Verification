theory Minimal
  imports "Hybrid-Verification.Hybrid_Verification"
begin

lit_vars

dataspace Minimal =
  constants
    W :: real
  variables
    y :: real
    x :: real
    z :: real

context Minimal
begin

abbreviation 
  "evo \<equiv>
  {z` = x-y,
   x` = W,
   y` = W
  }"

lemma never_turn: 
  "\<^bold>{x = y \<and> z = X\<^bold>}
    evo
   \<^bold>{x = y \<and> z = X\<^bold>}"
  apply (rule_tac diff_cut_on_split)
  apply (dInduct)
  apply (dInduct)
  done

lemma never_turn'': 
  "\<^bold>{z = X \<and> x = y\<^bold>}
    evo
   \<^bold>{z = X \<and> x = y\<^bold>}"
  apply (rule_tac diff_cut_on_split)
  apply dInduct
  oops

end