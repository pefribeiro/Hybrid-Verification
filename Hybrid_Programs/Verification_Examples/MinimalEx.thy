theory MinimalEx

imports 
  "Hybrid-Verification.Hybrid_Verification"
begin

expr_vars

dataspace robosim = 
  variables
    timer :: real

context robosim
begin
  abbreviation (input) "Example \<delta> \<equiv> ($timer \<le> \<delta>)\<^sub>e"
end

dataspace ex = robosim +
  constants 
    yolo::bool

end