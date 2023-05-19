theory RoboSim

imports 
  "Hybrid-Verification.Hybrid_Verification"
begin

expr_vars

method hoare_help =
  (
    (
      (simp only:kcomp_assoc)?, 
      (   (rule hoare_else_kcomp, force) 
        | (rule hoare_floyd_kcomp, simp, simp add: usubst_eval usubst unrest)
        | (rule hoare_if_kcomp, force) 
        | (rule hoare_ifte_kcomp)
        | (rule hoare_pre_not_while_seq, simp, hoare_wp_auto)
        | (simp only:kcomp_skip)
        | (dInduct_mega)
        | (rule nmods_invariant, (clarify intro!:closure, subst_eval))
       )
     )+, 
   (subst WHILE_unroll_IF[symmetric])?
  )+

text \<open> Modelling components that are common to all RoboSim models. \<close>

dataspace robosim = 
  constants
    Cycle :: nat
    TimeScale :: real
  variables
    executing :: bool
    timer :: real
    t     :: real

context robosim
begin

lemma ini_cycle_loop:
  assumes "\<^bold>{P\<^bold>} I \<^bold>{P\<^bold>}" "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>}" "\<^bold>{Q\<^bold>} C \<^bold>{Q\<^bold>}" "\<^bold>{Q\<^bold>} E \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} I ; C ; ((IF \<guillemotleft>TimeScale\<guillemotright>*\<guillemotleft>Cycle\<guillemotright> \<le> timer THEN C ELSE skip) ; E)\<^sup>* \<^bold>{Q\<^bold>}"
  apply (rule hoare_kcomp[where R="(Q)\<^sup>e"])
   apply (rule hoare_kcomp[where R="(P)\<^sup>e"])
    apply (simp add:assms(1))
   apply (simp add:assms(2))
  apply (rule hoare_kstar_inv)
  apply (rule hoare_kcomp[where R="(Q)\<^sup>e"])
   apply (rule hoare_if_then_else')
    apply (simp add:assms(3))
  apply (rule hoare_skip)
  by (simp add:assms(4))

lemma ini_cycle_loop':
  assumes "\<^bold>{P\<^bold>} I \<^bold>{Q\<^bold>}" "\<^bold>{Q\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} E \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} I ; C ; ((IF \<guillemotleft>TimeScale\<guillemotright>*\<guillemotleft>Cycle\<guillemotright> \<le> timer THEN C ELSE skip) ; E)\<^sup>* \<^bold>{R\<^bold>}"
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
   apply (rule hoare_kcomp[where R="(Q)\<^sup>e"])
    apply (simp add:assms(1))
   apply (simp add:assms(2))
  apply (rule hoare_kstar_inv)
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
   apply (rule hoare_if_then_else')
    apply (simp add:assms(3))
  apply (rule hoare_skip)
  by (simp add:assms(4))

thm hoare_skip
thm hoare_while

lemma cycle_loop:
  assumes "\<^bold>{P\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} E \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} C ; ((IF \<guillemotleft>TimeScale\<guillemotright>*\<guillemotleft>Cycle\<guillemotright> \<le> timer THEN C ELSE skip) ; E)\<^sup>* \<^bold>{R\<^bold>}"
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
    apply (simp add:assms(1))
  apply (rule hoare_kstar_inv)
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
   apply (rule hoare_if_then_else')
    apply (simp add:assms(2))
  apply (rule hoare_skip)
  by (simp add:assms(3))

lemma cycle_loop_ini:
  assumes "\<^bold>{P\<^bold>} I \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} E \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} I ; ((IF \<guillemotleft>TimeScale\<guillemotright>*\<guillemotleft>Cycle\<guillemotright> \<le> timer THEN C ELSE skip) ; E)\<^sup>* \<^bold>{R\<^bold>}"
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
    apply (simp add:assms(1))
  apply (rule hoare_kstar_inv)
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
   apply (rule hoare_if_then_else')
    apply (simp add:assms(2))
  apply (rule hoare_skip)
  by (simp add:assms(3))

lemma cycle_loop':
  assumes "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} E \<^bold>{R\<^bold>}"
  shows "\<^bold>{R\<^bold>} ((IF \<guillemotleft>TimeScale\<guillemotright>*\<guillemotleft>Cycle\<guillemotright> \<le> timer THEN C ELSE skip) ; E)\<^sup>* \<^bold>{R\<^bold>}"
  apply (rule hoare_kstar_inv)
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
   apply (rule hoare_if_then_else')
    apply (simp add:assms(1))
  apply (rule hoare_skip)
  by (simp add:assms(2))

method hoare_cycle =
  (((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, subst_eval)+, subst_eval?, rule cycle_loop; hoare_help; hoare_help?)

end

end