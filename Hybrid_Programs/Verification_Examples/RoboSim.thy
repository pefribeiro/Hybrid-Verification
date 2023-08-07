theory RoboSim

imports 
  "Hybrid-Verification.Hybrid_Verification"
begin

expr_vars

(*
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
  )+*)

section \<open> RoboSim \<close>

text \<open> Modelling components that are common to all RoboSim models. \<close>

dataspace robosim = 
  constants
    Cycle :: nat
    TimeScale :: real
  variables
    executing :: bool
    wait  :: bool
    timer :: real
    t     :: real

context robosim
begin

subsection \<open> Time modelling \<close>

text \<open> Every ODE will contain both a timer and a t variable for specification purposes,
       so below we define TimerEvo that includes the lenses for t and timer, and moreover
       specifies that these evolve at rate 1. The overall ODE system is then evolved within
       timer \<le> \<delta> time, assuming timer has been set to 0 initially.  \<close>

subsubsection \<open> TimerEvo \<close>

definition "TimerEvo \<delta> a \<sigma> B \<equiv> g_dl_ode_frame (t +\<^sub>L timer +\<^sub>L a) (\<sigma>(t  \<leadsto> 1, timer \<leadsto> 1)) (@B \<and> $timer \<le> \<guillemotleft>\<delta>\<guillemotright>)\<^sub>e"

lemma TimerEvo_delta_nmods:
  assumes "TimerEvo \<delta> a \<sigma> B nmods P"
  shows "\<^bold>{ P \<^bold>} TimerEvo \<delta> a \<sigma> B \<^bold>{ P \<and> $timer \<le> \<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
  apply (simp only:hoare_conj_pos, auto)
  using assms nmods_invariant apply fastforce
  using TimerEvo_def by (smt (verit, del_insts) SEXP_def fbox_g_orbital_on)

lemma TimerEvo_pos_timer_delta:
  shows "\<^bold>{ P \<^bold>} TimerEvo \<delta> a \<sigma> B \<^bold>{ $timer \<le> \<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
  using TimerEvo_def
  by (smt (verit, best) SEXP_def fbox_g_orbital_on predicate1I)

subsubsection \<open> EvolveUntil \<close>

text \<open> Having defined the above, we are now in a position to specify a program that evolves
       exactly until \<delta>. To ensure that sequential composition has the correct meaning, we 
       introduce the function T(_) that behaves like healthiness condition R3 of the
       theory of reactive processes. \<close>

definition "T(P) \<equiv> IF \<not> wait THEN P ELSE skip"

lemma hoare_T_wait:
  assumes "\<^bold>{P \<and> \<not> wait\<^bold>} C \<^bold>{Q\<^bold>}" "`(P \<and> wait) \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} T C \<^bold>{Q\<^bold>}"
  unfolding T_def apply (rule hoare_if_then_else)
  using assms apply simp
  by (metis (mono_tags, lifting) SEXP_def assms(2) fbox_skip predicate1I taut_def)

lemma hoare_T_wait':
  assumes "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> \<not> wait\<^bold>} T C \<^bold>{Q\<^bold>}"
  unfolding T_def
  using assms by fastforce

lemma T_idempotent:"T(T(P)) = T(P)"
  unfolding T_def
  unfolding ifthenelse_def apply auto
  by wlp_full

text \<open> EvolveUntil is then defined using wait as follows. Initially timer is set to 0, wait
       is set to true, and then it behaves as TimerEvo, with wait set to false once timer = \<delta>. \<close>

definition 
  "EvolveUntil \<delta> a \<sigma> \<equiv> 
    T(timer ::= 0 ; wait ::= True ; TimerEvo \<delta> a \<sigma> (True)\<^sup>e ; 
      (IF timer \<ge> \<guillemotleft>\<delta>\<guillemotright> THEN wait ::= False ELSE skip)
     )"

text \<open> We now prove several useful results about EvolveUntil \<close>

lemma
  assumes "vwb_lens a" "$t \<sharp> e" "$timer \<sharp> e" "$a \<sharp> e" "$wait \<sharp> e" 
  shows "EvolveUntil \<delta> a \<sigma> nmods e"
  using assms
  apply (simp add: EvolveUntil_def TimerEvo_def T_def)
  apply (auto intro!: closure)
     apply (expr_auto)+
  done

lemma lens_indep_no_change:
  assumes "x \<bowtie> y" 
  shows "($y\<lbrakk>v/x\<rbrakk>)\<^sub>e = ($y)\<^sub>e"
  by (simp add: assms lens_indep.lens_put_irr2 subst_app_def subst_id_def subst_upd_def)

lemma lens_indep_no_change'[simp]:
  assumes "y \<bowtie> x" 
  shows "get\<^bsub>x\<^esub> ([y \<leadsto> b] d) = get\<^bsub>x\<^esub> d"
  by (simp add: assms get_subst_upd_indep subst_id_def lens_indep_sym)

(* The above is a notion weaker than lens independence, as can be seen from the unfinished proof, 
   but I'm not sure if it's worth working with it! *)
lemma 
  assumes "(\<And>v. ($y\<lbrakk>v/x\<rbrakk>)\<^sub>e = ($y)\<^sub>e)"
  shows "x \<bowtie> y"
  apply (rule lens_indepI)
  defer defer
  using assms apply expr_auto 
     apply meson+
  oops

lemma 
  assumes "(\<And>v. ($y\<lbrakk>v/x\<rbrakk>)\<^sub>e = ($y)\<^sub>e)"
  shows "x ##\<^sub>L y"
  unfolding lens_compat_def
  unfolding lens_override_def
  using assms apply auto 
  apply expr_auto
  oops

text \<open> The following lemma confirms our intuition that provided EvolveUntil is started from a
       state in which wait is not true, then when it terminates (\<not> wait) then timer = \<delta>. For
       this result to hold we need to know that the lens a is independent from wait, so that
       it does not modify it.

       In general this should always be the case, as ODEs should not be talking about wait.
       Perhaps there could be a way to restrict the frame type? \<close>

lemma EvolveUntil_not_wait:
   (* I've removed the assumption: (\<And>v. ($wait\<lbrakk>v/a\<rbrakk>)\<^sub>e = ($wait)\<^sub>e) in favour of lens independence,
     which is stronger, but practically I think nearly always wanted for this result. *)
  assumes "a \<bowtie> wait"
  shows "\<^bold>{ \<not> wait \<^bold>} EvolveUntil \<delta> a \<sigma> \<^bold>{ \<not> wait \<longrightarrow> timer = \<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
  unfolding EvolveUntil_def T_def
  apply (rule hoare_if_then_else)
  apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp)
   apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp, subst_eval)
   apply (rule hoare_kcomp[where R="($wait \<and> $timer \<le> \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"])
    apply (rule hoare_weaken_pre_conj[where P="($wait)\<^sup>e"], simp)
    apply (rule TimerEvo_delta_nmods)
  unfolding TimerEvo_def apply (auto intro!:closure; subst_eval)
  using assms apply simp
    apply wlp_full+
  done

(* Need a lemma that states: if the rate of change of a variable is
   the same as another, then they are changed by the same amount.*) 

lemma "vwb_lens a \<Longrightarrow> a \<bowtie> t \<Longrightarrow> a \<bowtie> timer \<Longrightarrow> vwb_lens (timer +\<^sub>L t +\<^sub>L a)"
  by (meson indeps(11) lens_indep_sym plus_pres_lens_indep' plus_vwb_lens vwbs(3) vwbs(4))

thm differentiable_dvar

(* The following is useful when there is an explicit lens composition.
   FIXME: Move to Framed_Derivatives.thy. *)
lemma differentiable_cvar_explicit[ldifferentiable]:
  assumes "vwb_lens X" "vwb_lens x" "X \<bowtie> x"
  shows "differentiable\<^bsub>x +\<^sub>L X\<^esub> $x within S when G"
  apply (rule differentiable_cvar)
  using assms lens_indep_sym plus_vwb_lens vwbs(4) apply blast
   apply (simp add: assms(1))
  by (simp add: assms(1) assms(2) assms(3) lens_indep_sym)  

lemma "vwb_lens x \<Longrightarrow> vwb_lens y \<Longrightarrow> x \<bowtie> y \<Longrightarrow> vwb_lens (y +\<^sub>L x)"
  using lens_indep_sym plus_vwb_lens by blast

(* The following is useful when the lens independence is stated in the opposite
   way to the lens composition. FIXME: add to Lens_Algebra.thy ? *)
lemma plus_vwb_lens' [simp]:
  assumes "vwb_lens x" "vwb_lens y" "y \<bowtie> x"
  shows "vwb_lens (x +\<^sub>L y)"
  using assms
  by (meson lens_indep_sym plus_vwb_lens)

lemma TimerEvo_t_increasing:
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  unfolding TimerEvo_def T_def (* despite the above dInduct can fail if t \<bowtie> a is swapped by a \<bowtie> t *)
  using assms by (dInduct)
 
lemma TimerEvo_t_increasing':
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> = t \<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  using assms TimerEvo_t_increasing 
  by fastforce

lemma TimerEvo_timer_sum_invariant:
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows " \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> + timer \<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> + timer \<^bold>}"
  using assms unfolding TimerEvo_def 
  by (dInduct)

lemma T_increasing_t:
  assumes "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} X \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} T(X) \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  unfolding T_def 
  apply (rule hoare_if_then_else)
  using assms by wlp_full+  

lemma T_kcomp_increasing_t:
  assumes "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> = t \<^bold>} X \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}" "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} Y \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}" 
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> = t \<^bold>} T(X ; Y) \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  unfolding T_def 
  apply (rule hoare_if_then_else)
   defer
   apply (smt (verit, best) SEXP_def fbox_skip predicate1I)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"])
  using assms by auto

lemma T_kcomp_increasing_t':
  assumes "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} X \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}" "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} Y \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}" 
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} T(X ; Y) \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  unfolding T_def 
  apply (rule hoare_if_then_else)
   defer
   apply (smt (verit, best) SEXP_def fbox_skip predicate1I)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"])
  using assms by auto
  
lemma EvolveUntil_increasing_t:
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> = t \<^bold>} EvolveUntil \<delta>\<^sub>c a \<sigma> \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  unfolding EvolveUntil_def
  apply (rule T_kcomp_increasing_t)
   apply (subst kcomp_assoc)
   apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"], wlp_full)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"], wlp_full)
  using assms apply (simp add: TimerEvo_t_increasing)
  apply (rule hoare_if_then_else, wlp_full)
  by (wlp_full)

lemma EvolveUntil_increasing_t':
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} EvolveUntil \<delta>\<^sub>c a \<sigma> \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  unfolding EvolveUntil_def
  apply (rule T_kcomp_increasing_t')
   apply (subst kcomp_assoc)
   apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"], wlp_full)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"], wlp_full)
  using assms apply (simp add: TimerEvo_t_increasing)
  apply (rule hoare_if_then_else, wlp_full)
  by (wlp_full)


lemma kstar_increasing_t:
  assumes "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} X \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> = t \<^bold>} X\<^sup>* \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  apply (subst kstar_zero_or_one_or_more)
  apply (rule hoare_choice, wlp_full)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"])
   apply (rule hoare_weaken_pre_conj[where P="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"], simp)
  using assms apply simp
  apply (rule hoare_kstar_inv)
  using assms by auto

lemma kstar_increasing_t':
  assumes "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} X \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  shows "\<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} X\<^sup>* \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
  apply (subst kstar_zero_or_one_or_more)
  apply (rule hoare_choice, wlp_full)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"])
   apply (rule hoare_weaken_pre_conj[where P="(\<guillemotleft>t\<^sub>1\<guillemotright> \<le> t)\<^sup>e"], simp)
  using assms apply simp
  apply (rule hoare_kstar_inv)
  using assms by auto

lemma T_EvolveUntil_kstar_increasting_t:
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a" "\<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>} T C \<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>}"
  shows "\<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> = t\<^bold>} (T C ; EvolveUntil \<delta> a \<sigma>)\<^sup>* \<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>}"
  apply (rule kstar_increasing_t)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t)\<^sup>e"])
   defer
  using assms(1-3) apply (rule EvolveUntil_increasing_t')
  using assms(4) by auto

lemma T_EvolveUntil_kstar_increasting_t':
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a" "\<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>} T C \<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>}"
  shows "\<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>} (T C ; EvolveUntil \<delta> a \<sigma>)\<^sup>* \<^bold>{\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t\<^bold>}"
  apply (rule kstar_increasing_t')
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t)\<^sup>e"])
   defer
  using assms(1-3) apply (rule EvolveUntil_increasing_t')
  using assms(4) by auto

lemma TimerEvo_timer_sum_invariant':
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows " \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> timer = 0 \<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> + timer \<^bold>}"
  using assms 
  apply (hoare_wp_auto)
  by (smt (verit, best) SEXP_def TimerEvo_timer_sum_invariant fbox_iso predicate1D predicate1I)
  (* FIXME: There ought to be a better non-SMT proof for the above. *)

lemma hoare_weaken_pre:
  assumes "`P \<longrightarrow> Q`" and "\<^bold>{Q\<^bold>} G \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} G \<^bold>{R\<^bold>}"
  using assms oops

lemma hoare_stengthen_post:
  assumes "`Q \<longrightarrow> R`" and "\<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} G \<^bold>{R\<^bold>}"
  using assms Diff_Dyn_Logic.strengthen by blast

thm nmods_frame_law



lemma g_dl_ode_frame_nmods:
  assumes "a \<bowtie> x" "vwb_lens x"
  shows "g_dl_ode_frame a \<sigma> B nmods $x"
  using assms unfolding not_modifies_def apply auto
  using g_orbital_on_def   
  by (smt (verit, del_insts) g_orbital_on_eq lens_indep.lens_put_irr2 mem_Collect_eq)

lemma TimerEvo_nmods_lens:
  assumes "a \<bowtie> x" "timer \<bowtie> x" "t \<bowtie> x" "vwb_lens x"
  shows "TimerEvo \<delta> a \<sigma> B nmods $x"
proof -
  have "(t +\<^sub>L timer +\<^sub>L a) \<bowtie> x"
    using assms 
    by force
  then show ?thesis
    unfolding TimerEvo_def using assms g_dl_ode_frame_nmods
    by blast
qed

lemma EvolveUntil_t_not_wait:
  (* Need assumption that a does not modify wait. Stated below using substitution:
     essentially, it must be the case that for every possible state v, when
     a is substituted in $wait by v, then its value doesn't change. *)
  assumes "a \<bowtie> wait" "\<^bold>{P\<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{P\<^bold>}" "$wait \<sharp> P" "$timer \<sharp> P" "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
  shows "\<^bold>{ P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> \<not> wait \<^bold>} EvolveUntil \<delta> a \<sigma> \<^bold>{ P \<and> (\<not> wait \<longleftrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<and> (wait \<longleftrightarrow> t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^bold>}"
  unfolding EvolveUntil_def T_def
   apply (rule hoare_if_then_else)
    apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp)
   apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp, subst_eval)
  defer
   apply expr_auto
  apply (rule hoare_kcomp[where R="(P \<and> wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + timer \<and> timer \<le> \<guillemotleft>\<delta>\<guillemotright> )\<^sup>e"])
   defer
   apply (rule hoare_if_then_else)
  using assms apply (hoare_wp_auto)
  using assms apply (hoare_wp_auto)
  apply (rule hoare_weaken_pre_conj[where P="(P \<and> wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + timer)\<^sup>e"])
  using assms(3,4) apply expr_auto
  apply (rule hoare_conj_posI[where a="(P \<and> wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + timer)\<^sup>e" and b="(timer \<le> \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"])
    defer
    apply (simp add: TimerEvo_pos_timer_delta)
   apply expr_auto
  apply (rule hoare_conj_inv)
  apply (simp add:assms) 
  apply (rule nmods_frame_law'', simp add:assms TimerEvo_nmods_lens)
  by (simp add:assms TimerEvo_timer_sum_invariant)

(*
lemma 
  assumes "a \<bowtie> wait" 
          "\<^bold>{P\<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{P\<^bold>}" (* Might want to relax this assumption. *)
          "$wait \<sharp> P" "$timer \<sharp> P" "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
          "`(P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<longrightarrow> R`"
         (* "\<^bold>{ t = \<guillemotleft>t\<^sub>1\<guillemotright> \<^bold>} C \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}" *)
          "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}"
    (* What we want: 
        * P is an invariant over EvolveUntil, and so:
           * it holds at t = t\<^sub>0 and at t = t\<^sub>0 + \<delta>
        * R is an invariant over C, and so:
           * it holds at t = t\<^sub>0 + \<delta> as established by EvolveUntil at t = t\<^sub>0 + \<delta>,
             so perhaps it is sufficient to show that `P \<and> t = t\<^sub>0 + \<delta> \<longrightarrow> R` ?
    *)
  shows "\<^bold>{P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> \<not> wait\<^bold>} EvolveUntil \<delta> a \<sigma> ; T(C) \<^bold>{(t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<longrightarrow> P) \<and> (\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<longrightarrow> R)\<^bold>}"
  apply (rule hoare_kcomp[where R="(P \<and> (\<not> wait \<longleftrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<and> (wait \<longleftrightarrow> t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>))\<^sup>e"])
  using assms apply (simp only:EvolveUntil_t_not_wait) (* Tentative *)
  apply (rule hoare_T_wait) (* Need C to be monotonically increasing on t *)
   defer
  apply expr_auto
  apply (rule hoare_weaken_pre_conj[where P="(P \<and> \<not> wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<and> R)\<^sup>e"])
  using assms apply expr_auto
  apply (rule hoare_weaken_pre_conj[where P="(R \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"], expr_auto)
  apply (rule hoare_stengthen_post[where Q="(R)\<^sup>e"])
  using assms apply simp
  using assms by auto *)

lemma 
  assumes "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a" "\<^bold>{$a = a\<^sub>0\<^bold>} TimerEvo \<delta>\<^sub>s a \<sigma> (True)\<^sup>e \<^bold>{$a = a\<^sub>0\<^bold>}"
  shows "TimerEvo \<delta>\<^sub>s a \<sigma> (True)\<^sup>e = {timer` = 1, t` = 1 | timer \<le> \<delta>}"
  using assms unfolding TimerEvo_def oops

lemma T_kcomp_fixpoint:
  shows "T(T(P) ; T(Q)) = T(P) ; T(Q)"
  unfolding T_def ifthenelse_def skip_def kcomp_def by expr_auto

lemma T_kstar_fixpoint:
  shows "T((T(P))\<^sup>*) = (T(P))\<^sup>*"
  unfolding T_def ifthenelse_def skip_def kstar_def apply expr_auto
   apply (metis (full_types) kpower_0 singletonI)
  by (smt (verit, ccfv_SIG) Collect_conv_if2 kpower_inv mem_Collect_eq)

lemma T_EvolveUntil_fixpoint:
  shows "(T C ; EvolveUntil \<delta>\<^sub>c a \<sigma>)\<^sup>* = T((T C ; EvolveUntil \<delta>\<^sub>c a \<sigma>)\<^sup>*)"
  using T_kstar_fixpoint 
  by (smt (verit, ccfv_threshold) EvolveUntil_def T_kcomp_fixpoint)

lemma T_EvolveUntil_plus_fixpoint:
  shows "(T C ; EvolveUntil \<delta>\<^sub>c a \<sigma>)\<^sup>+ = T((T C ; EvolveUntil \<delta>\<^sub>c a \<sigma>)\<^sup>+)"
  using T_kstar_fixpoint unfolding kstar_one_def
  by (smt (verit, ccfv_threshold) EvolveUntil_def T_kcomp_fixpoint)

lemma T_invariant:
  assumes "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}"
  shows "\<^bold>{R\<^bold>} T C \<^bold>{R\<^bold>}"
  unfolding T_def 
  apply (rule hoare_if_then_else')
  using assms apply simp
  by (simp add: hoare_skip)

lemma hoare_pre_eq:
  assumes "\<^bold>{Q\<^bold>} X \<^bold>{S\<^bold>}" "R = Q"
  shows "\<^bold>{R\<^bold>} X \<^bold>{S\<^bold>}"
  using assms by auto

lemma EvolveUntil_two_post:
  assumes "a \<bowtie> wait" 
          "\<^bold>{P\<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{P\<^bold>}" (* Might want to relax this assumption. *)
          "$wait \<sharp> P" "$timer \<sharp> P" "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
          (* "\<^bold>{P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>} C \<^bold>{R\<^bold>}"*) "`(P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<longrightarrow> R`" (* This may a little too strong *)
          "\<And>t\<^sub>1. \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} C \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
          "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}"
          "\<^bold>{R\<^bold>} EvolveUntil \<delta>\<^sub>c a \<sigma> \<^bold>{R\<^bold>}"
  shows "\<^bold>{P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> \<not> wait\<^bold>}
         EvolveUntil \<delta> a \<sigma> ; (T(C) ; EvolveUntil \<delta>\<^sub>c a \<sigma>)\<^sup>*
         \<^bold>{(t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<longrightarrow> P) \<and> (\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<longrightarrow> R)\<^bold>}"
  apply (rule hoare_kcomp[where R="(P \<and> (\<not> wait \<longleftrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<and> (wait \<longleftrightarrow> t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>))\<^sup>e"])
  using assms apply (simp only:EvolveUntil_t_not_wait) (* Tentative *)
  apply (subst T_EvolveUntil_fixpoint)
  apply (rule hoare_T_wait) (* Need C to be monotonically increasing on t *)
   defer
  apply expr_auto
  apply (rule hoare_weaken_pre_conj[where P="(P \<and> \<not> wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"])
  using assms apply expr_auto
(* Use: T_EvolveUntil_kstar_increasting_t *)
  using assms apply (insert T_increasing_t[where t\<^sub>1="t\<^sub>0 + \<delta>" and X="C"])
  apply (insert T_EvolveUntil_kstar_increasting_t[where C="C" and t\<^sub>0="t\<^sub>0 + \<delta>" and \<delta>="\<delta>\<^sub>c" and a="a" and \<sigma>="\<sigma>"])
  using assms apply simp
  apply (rule hoare_stengthen_post[where Q="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<and> R)\<^sup>e"], expr_simp)
  thm hoare_conj_posI
  apply (rule hoare_conj_posI[where a="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t)\<^sup>e" and b="R"])
    defer
    defer
  apply expr_simp
  apply (rule hoare_weaken_pre_conj[where P="(t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"], expr_auto)
    apply (smt (verit, best) SEXP_def le_fun_def)
      apply (rule hoare_weaken_pre_conj[where P="(R \<and> \<not> wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"], expr_auto)
(*  apply (rule hoare_stengthen_post[where Q="(R)\<^sup>e"])
  using assms apply simp*)
  apply (subst kstar_zero_or_one_or_more)
  apply (rule hoare_choice)
   apply (simp add:fbox_skip, expr_auto)
  apply (subst kcomp_assoc)
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
   apply (rule hoare_T_wait, simp)
    apply (rule hoare_weaken_pre_conj[where P="(R)\<^sup>e"], expr_auto)
  using assms apply simp
   apply expr_auto
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
  using assms apply simp
  apply (rule hoare_kstar_inv)
  apply (rule hoare_kcomp[where R="(R)\<^sup>e"])
  using assms by (auto simp add:T_invariant)

lemma EvolveUntil_two_post_plus:
  assumes "a \<bowtie> wait" 
          "\<^bold>{P\<^bold>} TimerEvo \<delta> a \<sigma> (True)\<^sup>e \<^bold>{P\<^bold>}" (* Might want to relax this assumption. *)
          "$wait \<sharp> P" "$timer \<sharp> P" "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
          "\<^bold>{P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>} C \<^bold>{R \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>}" (*"`(P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<longrightarrow> R`"*) (* This may a little too strong *)
          "\<And>t\<^sub>1. \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>} C \<^bold>{ \<guillemotleft>t\<^sub>1\<guillemotright> \<le> t \<^bold>}"
          "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}"
          "\<^bold>{R\<^bold>} EvolveUntil \<delta>\<^sub>c a \<sigma> \<^bold>{R\<^bold>}"
  shows "\<^bold>{P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> \<not> wait\<^bold>}
         EvolveUntil \<delta> a \<sigma> ; (T(C) ; EvolveUntil \<delta>\<^sub>c a \<sigma>)\<^sup>+
         \<^bold>{(t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<longrightarrow> P) \<and> (\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<longrightarrow> R)\<^bold>}"
  apply (rule hoare_kcomp[where R="(P \<and> (\<not> wait \<longleftrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<and> (wait \<longleftrightarrow> t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>))\<^sup>e"])
  using assms apply (simp only:EvolveUntil_t_not_wait) (* Tentative *)
  apply (subst T_EvolveUntil_plus_fixpoint)
  apply (rule hoare_T_wait) (* Need C to be monotonically increasing on t *)
   defer
  apply expr_auto
  apply (rule hoare_weaken_pre_conj[where P="((P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>) \<and> \<not> wait )\<^sup>e"])
  using assms apply expr_auto
  unfolding kstar_one_def
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<and> R)\<^sup>e"])
  defer
(* Proof steps unchanged below *)
(* Use: T_EvolveUntil_kstar_increasting_t *)
  using assms apply (insert T_increasing_t[where t\<^sub>1="t\<^sub>0 + \<delta>" and X="C"])
  apply (insert T_EvolveUntil_kstar_increasting_t'[where C="C" and t\<^sub>0="t\<^sub>0 + \<delta>" and \<delta>="\<delta>\<^sub>c" and a="a" and \<sigma>="\<sigma>"])
  using assms apply simp
  apply (rule hoare_stengthen_post[where Q="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<and> R)\<^sup>e"], expr_simp)
  thm hoare_conj_posI
   apply (rule hoare_conj_posI[where a="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t)\<^sup>e" and b="R"])
     apply (rule hoare_weaken_pre_conj[where P="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t)\<^sup>e"], expr_auto, simp)
    defer
    apply expr_simp
  defer
   apply (rule hoare_weaken_pre_conj[where P="(R)\<^sup>e"], simp)
   apply (meson hoare_kcomp hoare_kstar_inv robosim.T_invariant robosim_axioms)
  apply (rule hoare_kcomp[where R="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t \<and> R)\<^sup>e"])
   apply (rule hoare_T_wait')
   defer
   apply (rule hoare_conj_inv)
  using EvolveUntil_increasing_t' assms(5) assms(6) assms(7) apply blast
  using assms apply blast
  apply (rule hoare_stengthen_post[where Q="(R \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"], expr_simp)
  using assms by auto
  (*apply (rule hoare_conj_pos')
  apply (rule hoare_weaken_pre_conj[where P="(\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<le> t)\<^sup>e"], simp)
  using assms(9) apply fastforce
  using assms by auto*)

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

lemma cycle_loop'':
  assumes "\<^bold>{P\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} C \<^bold>{R\<^bold>}" "\<^bold>{R\<^bold>} E \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} (C ; E)\<^sup>* \<^bold>{R\<^bold>}"
  oops (* TBC *)

lemma exists_subst [usubst_eval]:
  "(Q \<and> R \<and> S \<and> (\<exists>v. v \<and> P))\<^sub>e = (Q \<and> R \<and> S \<and> P)\<^sub>e"
  by wlp_full

lemma exists_subst' [usubst_eval]:
  "(Q \<and> (\<exists>v. v \<and> P))\<^sub>e = (Q \<and> P)\<^sub>e"
  by wlp_full

lemma exists_true [usubst_eval]:
  "(\<exists>v. v)"
  by wlp_full

lemma exists_move [usubst_eval]:
  "(Q \<and> (\<exists>v. v \<and> P))\<^sub>e = (Q \<and> (\<exists>v. P))\<^sub>e"
  by wlp_full

lemma EvolveUntil_TimerEvo:
  assumes "$timer \<sharp> I" "$wait \<sharp> I" "\<^bold>{ I \<^bold>} TimerEvo \<delta> a \<sigma> (\<lambda>\<s>. True) \<^bold>{ I \<^bold>}"
  shows "\<^bold>{ I \<^bold>} EvolveUntil \<delta> a \<sigma> \<^bold>{ I \<^bold>}"
  unfolding EvolveUntil_def T_def
  apply (rule hoare_if_then_else)
   defer
   apply wlp_full
  thm nmods_invariant
  apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp, simp add:unrest usubst assms)
  apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp, simp add:unrest usubst assms)
  apply (rule hoare_weaken_pre_conj[where P="I"], simp)
  apply (rule hoare_kcomp[where R="I"])
  using assms apply simp
  apply (rule hoare_if_then_else)
  using assms apply wlp_full
  by wlp_full
  
end

term "[\<leadsto>] \<circ>\<^sub>s \<sigma>(x \<leadsto> u, x \<leadsto> v)"
term "\<langle>\<sigma>(x \<leadsto> v, y \<leadsto> v)\<rangle>"
term "\<langle>\<sigma>(x \<leadsto> v)\<rangle>"
term "\<langle>CONST subst_upd [\<leadsto>] x (e)\<^sub>e\<rangle>"

term "[\<leadsto>]"
term "(subst_upd [\<leadsto>] x (e)\<^sub>e)"

context robosim
begin

(* abbreviation (input) "TimerEvo \<delta> a \<sigma> B \<equiv> g_dl_ode_frame a \<sigma> (@B \<and> $timer \<le> \<delta>)\<^sub>e" *)

end

method hoare_help uses add = ( 
    (
      (simp only:kcomp_assoc)?, 
      (   (rule hoare_else_kcomp, force) 
        | (rule hoare_floyd_kcomp, simp, simp add: usubst_eval usubst unrest)
        | (rule hoare_if_kcomp, force) 
        | (rule hoare_ifte_kcomp)
        | (rule hoare_pre_not_while_seq, simp, hoare_wp_auto)
        | (rule hoare_pre_not_while, simp, hoare_wp_auto)
        | (simp only:kcomp_skip)
        | (dInduct_mega)
        | (rule nmods_invariant, (clarify intro!:closure, subst_eval))
        | (rule hoare_false, subst_eval)
        | (simp add:unrest usubst expr_simps add)
       )
     )+, 
   (subst WHILE_unroll_IF[symmetric])?
  )+

end
