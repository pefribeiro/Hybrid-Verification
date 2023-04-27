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

abbreviation (input) 
  "mini_evolution \<equiv> 
  {
  po` = ve,
  ve` = 0,
  ti` = 1
  }"

abbreviation
  (input)
  "mini_evolve \<equiv> 
  [po \<leadsto> ve,
   ve \<leadsto> 0,
   ti \<leadsto> 1]"


term mini_evolve

abbreviation (input) "mini_wmr_flow \<tau> \<equiv> [
  po \<leadsto> ve*\<tau> + po,
  ti \<leadsto> \<tau> + ti,
  ve \<leadsto> ve]"

lemma mini_wmr_flow_exp:
  "local_flow_on mini_evolve (po +\<^sub>L ve +\<^sub>L ti) UNIV UNIV mini_wmr_flow"
  apply (auto simp add: local_flow_on_def)
  apply (unfold_locales, auto, lipschitz_const "1")
    defer
    apply vderiv
  apply expr_auto
  by (metis norm_fst_le norm_snd_le order_trans real_norm_def)

lemma res1:"\<^bold>{ve = 1\<^bold>} mini_evolution \<^bold>{ve = 1\<^bold>}"
  by dInduct

thm fbox_solve[OF mini_wmr_flow_exp]

method hoare_wp_auto uses local_flow = (hoare_wp_simp local_flow: local_flow[simplified]; expr_auto)


lemma res2:"\<^bold>{ve = 1\<^bold>} mini_evolution \<^bold>{ve \<ge> 0\<^bold>}"
  apply (hoare_wp_auto local_flow: mini_wmr_flow_exp)
  oops (* goes through if 'ti' is removed from system of equations, 
          and order of lens composition above in mini_wmr_flow_exp
          is 'po +\<^sub>L ve', but not if it is 've +\<^sub>L po' *)

end

end