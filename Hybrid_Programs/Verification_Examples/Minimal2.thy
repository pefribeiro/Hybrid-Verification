theory Minimal2

imports 
  "Hybrid-Verification.Hybrid_Verification"
begin

lit_vars

dataspace wmr = 
   variables
    po :: real
    ve :: real
    ti :: real

context wmr
begin

abbreviation 
  "mini_evolution \<equiv> 
  {
  po` = ve,
  ve` = 0,
  ti` = 1
  }"

abbreviation 
  "mini_evolve \<equiv> 
  [po \<leadsto> ve,
   ve \<leadsto> 0,
   ti \<leadsto> 1]"

abbreviation "mini_wmr_flow \<tau> \<equiv> [
  po \<leadsto> ve*\<tau> + po,
  ve \<leadsto> ve,
  ti \<leadsto> \<tau> + ti]"

lemma mini_wmr_flow_exp:
  "local_flow_on mini_evolve (po +\<^sub>L ve +\<^sub>L ti) UNIV UNIV mini_wmr_flow"
  apply (auto simp add: local_flow_on_def)
  apply (unfold_locales, auto, lipschitz "1")
    defer
    apply vderiv
  apply expr_auto
  by (metis norm_fst_le norm_snd_le order_trans real_norm_def)

lemma res1:"\<^bold>{ve = 1\<^bold>} mini_evolution \<^bold>{ve = 1\<^bold>}"
  by dInduct

lemma res2:"\<^bold>{ve = 1\<^bold>} mini_evolution \<^bold>{ve \<ge> 0\<^bold>}"
  apply (hoare_wp_auto local_flow: mini_wmr_flow_exp)
  oops (* goes through if 'ti' is removed from system of equations, 
          and order of lens composition above in mini_wmr_flow_exp
          is 'po +\<^sub>L ve', but not if it is 've +\<^sub>L po' *)

end

end