theory Simple
  imports 
  "Hybrid-Verification.Hybrid_Verification"
  "Z_Toolkit.Trace_Algebra"
begin

lit_vars

dataspace wmr = 
  variables
  ty :: real
  mx :: real
  t :: real
  tx :: real

context wmr 
begin

abbreviation 
  "simple \<equiv> 
  {
   mx` = 1,
   t` = 1
  }"

abbreviation  "exp_f \<equiv> [mx \<leadsto> 1, t \<leadsto> 1]" (* x>0 -> [{x'=-x}](x>0) *)
abbreviation  "exp_flow \<tau> \<equiv> [mx \<leadsto> 1*\<tau> + mx, t \<leadsto> \<tau> + t]"


term exp_f 
term exp_flow

lemma local_flow_exp_flow: "local_flow_on exp_f (mx+\<^sub>Lt) UNIV UNIV (exp_flow)"
  apply (auto simp add: local_flow_on_def)?
  apply (unfold_locales, auto)
    apply (lipschitz_const "1")
   apply (vderiv)
  by expr_auto



lemma passes_d: 
  "\<^bold>{mx = 0 \<and> t = 0\<^bold>}
    simple
   \<^bold>{t > 0 \<longrightarrow> mx > 0\<^bold>}"
  apply (simp add: 
        
    refine_iff_implies)
    apply (simp add:fbox_g_dL_easiest[OF local_flow_exp_flow])
  by (hoare_wp_simp local_flow: local_flow_exp_flow)

end

end