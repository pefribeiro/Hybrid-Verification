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
    \<epsilon>\<^sub>s        :: real \<comment> \<open> Initial delay before simulation starts. \<close>
  variables
    executing :: bool \<comment> \<open> Used to model 'exec'. \<close>
    wait  :: bool \<comment> \<open> Used for modelling reactive termination. \<close>
    timer :: real \<comment> \<open> Continuous time within each simulation cycle. \<close>
    t     :: real \<comment> \<open> Global time. \<close>

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

lemma hoare_T_wait_skip:
  assumes "`P \<longrightarrow> wait`" "\<^bold>{ P \<^bold>} skip \<^bold>{ Q \<^bold>}"
  shows "\<^bold>{ P \<^bold>} T X \<^bold>{ Q \<^bold>}"
  unfolding T_def
  by (smt (verit, del_insts) SEXP_def assms(1) assms(2) fbox_if_then_else predicate1D predicate1I taut_def)

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

lemma EvoleUntil_wait_skip:
  assumes "`P \<longrightarrow> wait`" "\<^bold>{ P \<^bold>} skip \<^bold>{ Q \<^bold>}"
  shows "\<^bold>{ P \<^bold>} EvolveUntil \<delta> a \<sigma> \<^bold>{ Q \<^bold>}"
  apply (rule hoare_weaken_pre_conj[where P="(P)\<^sup>e"])
  using assms apply expr_simp
  unfolding EvolveUntil_def
  using hoare_T_wait_skip assms by blast

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

lemma hoare_post_eq:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{R\<^bold>}" "R = S"
  shows "\<^bold>{P\<^bold>} X \<^bold>{S\<^bold>}"
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

(* Wouldn't it be nice to be able to have derivatives in the pre/post-conditions?
   Or how about a hybrid refinement checker? *)


definition kstar_fixed :: "('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^bsup>_\<^esup>)" [1000] 999)
  where [prog_defs]: "(f\<^bsup>n\<^esup>) = (\<Sqinter>i\<in>{0..n}. kpower f i)"

lemma kstar_0[simp]: "(P\<^bsup>0\<^esup>) = skip"
  unfolding kstar_fixed_def skip_def Nondet_choice_def kpower_def by auto

lemma kstar_1: "(P\<^bsup>1\<^esup>) = P \<sqinter> skip"
  unfolding kstar_fixed_def skip_def Nondet_choice_def nondet_choice_def kpower_def
  apply (auto simp add:fun_eq_iff)
  apply (metis One_nat_def Suc_eq_plus1 empty_iff funpow_0 insert_iff kcomp_id(2) kcomp_skip(1) kpower_Suc kpower_def le_add2 le_antisym list_decode.cases)
  by (metis Suc_le_mono atLeast0AtMost atMost_iff kcomp_id(2) kcomp_skip(1) kpower_Suc_0 kpower_def zero_le)

lemma kstar_fixed_comp_rhs: "(P\<^bsup>n\<^esup>) ; P = (\<Sqinter>i\<in>{1..Suc n}. (kpower P i))"
proof -
  have "(P\<^bsup>n\<^esup>) ; P = (\<Sqinter>i\<in>{0..n}. kpower P i) ; P"
    unfolding kstar_fixed_def by auto
  also have "... = (\<Sqinter>i\<in>{0..n}. (kpower P i ; P))"
    unfolding Nondet_choice_def 
    by (auto simp add:fun_eq_iff kcomp_def)
  also have "... = (\<Sqinter>i\<in>{0..n}. (kpower P (Suc i)))"
    by (auto simp add:kpower_Suc')
  also have "... = (\<Sqinter>i\<in>{1..Suc n}. (kpower P i))"
    apply (auto simp add:Nondet_choice_def fun_eq_iff)
     apply (meson Suc_leI Suc_le_mono atLeastAtMost_iff zero_less_Suc)
    by (metis intervalE less_Suc_eq_0_disj less_Suc_eq_le linorder_not_le)
  finally show ?thesis .
qed

lemma kstar_fixed_comp_lhs: "P ; (P\<^bsup>n\<^esup>) = (\<Sqinter>i\<in>{1..Suc n}. (kpower P i))"
proof -
  have "P ; (P\<^bsup>n\<^esup>) = P ; (\<Sqinter>i\<in>{0..n}. kpower P i)"
    unfolding kstar_fixed_def by auto
  also have "... = (\<Sqinter>i\<in>{0..n}. (P ; kpower P i))"
    unfolding Nondet_choice_def 
    by (auto simp add:fun_eq_iff kcomp_def)
  also have "... = (\<Sqinter>i\<in>{0..n}. (kpower P (Suc i)))"
    by (auto simp add:kpower_Suc)
  also have "... = (\<Sqinter>i\<in>{1..Suc n}. (kpower P i))"
    apply (auto simp add:Nondet_choice_def fun_eq_iff)
     apply (meson Suc_leI Suc_le_mono atLeastAtMost_iff zero_less_Suc)
    by (metis intervalE less_Suc_eq_0_disj less_Suc_eq_le linorder_not_le)
  finally show ?thesis .
qed

lemma kstar_plus: "P ; (P\<^bsup>n\<^esup>) = (P\<^bsup>n+1\<^esup>)"
  unfolding kstar_fixed_def Nondet_choice_def kcomp_def
  apply (auto simp add:fun_eq_iff)
   apply (smt (verit, ccfv_SIG) Suc_leI UN_I bot_nat_0.extremum comp_apply comp_apply intervalE kcomp_def kcomp_kpower kpower_Suc' le_imp_less_Suc)
  unfolding kpower_def
  oops

lemma kstar_fixed_comp_commute: "(P\<^bsup>n\<^esup>) ; P = P ; (P\<^bsup>n\<^esup>)"
  using kstar_fixed_comp_rhs kstar_fixed_comp_lhs by metis

lemma kpower_kcomp_sum: "kpower P y ; kpower P x = kpower P (y + x)"
proof (induct y)
  case 0
  then show ?case 
    by (simp add: kcomp_skip(2) kpower_0')
next
  case (Suc y)
  then show ?case
    by (simp add: kcomp_assoc kpower_Suc)
qed

lemma kstar_fixed_comp_eq_kstar:"(P\<^bsup>n\<^esup>) ; P\<^sup>* = P\<^sup>*"
proof(intro ext set_eqI iffI conjI impI, goal_cases "\<subseteq>" "\<supseteq>")
   case ("\<subseteq>" s s')
   then obtain y x where "s' \<in> (kpower P y ; kpower P x) s"
    unfolding kcomp_eq kstar_def kstar_fixed_def Nondet_choice_def
    by auto
  hence "s' \<in> kpower P (y + x) s"
    using kpower_kcomp_sum
    by metis
  then show ?case
    using kstar_def by fastforce
 next
   case (\<supseteq> s s') (* Just need a way to distribute the n between the composition. Case split maybe? *)
   then show ?case
    unfolding kcomp_def kstar_fixed_def kstar_def Nondet_choice_def apply auto
    by (metis atLeast0AtMost atMost_iff insertI1 kpower_0 zero_le)
qed

lemma kstar_fixed_comp_eq_kstar_one: "P\<^bsup>c\<^esup> ; P\<^sup>+ = P\<^sup>+"
  unfolding kstar_one_def
  by (metis kcomp_assoc kcomp_kstar kstar_fixed_comp_eq_kstar)

lemma kstar_one_def_alt:"P\<^sup>+ = P ; (\<Sqinter>i\<in>UNIV. P\<^bsup>i\<^esup>)"
  unfolding kstar_one_def Nondet_choice_def kcomp_def kstar_fixed_def
  apply (auto simp add:fun_eq_iff)
  apply (metis Nondet_choice_def UN_E atLeast0AtMost atMost_iff kstar_alt le_add2)
  using kstar_def by fastforce

lemma Nondet_choice_right_dist':
  "(\<Sqinter>i\<in>{0..n}. P i) ; R = (\<Sqinter>i\<in>{0..n}. (P i ; R))"
  unfolding Nondet_choice_def kcomp_def 
  by (auto simp add:fun_eq_iff)

lemma Nondet_choice_left_dist':
  "R ; (\<Sqinter>i\<in>{0..n}. P i) = (\<Sqinter>i\<in>{0..n}. (R ; P i))"
  unfolding Nondet_choice_def kcomp_def 
  by (auto simp add:fun_eq_iff)

lemma kstar_fixed_plus_kcomp: "(P\<^bsup>n\<^esup>) ; (P\<^bsup>m\<^esup>) = (P\<^bsup>n+m\<^esup>)"
proof -
  have "(P\<^bsup>n\<^esup>) ; (P\<^bsup>m\<^esup>) = ((\<Sqinter>i\<in>{0..n}. kpower P i) ; (\<Sqinter>j\<in>{0..m}. kpower P j))"
    unfolding kstar_fixed_def by auto
  also have "... = ((\<Sqinter>i\<in>{0..n}. (kpower P i ; (\<Sqinter>j\<in>{0..m}. kpower P j))))"
    using Nondet_choice_right_dist' by metis
  also have "... = ((\<Sqinter>i\<in>{0..n}. (\<Sqinter>j\<in>{0..m}. kpower P i ; kpower P j)))"
    by (auto simp add:Nondet_choice_left_dist')
  also have "... = (\<Sqinter>i\<in>{0..n}. (\<Sqinter>j\<in>{0..m}. kpower P (i + j)))"
    by (simp add: kpower_kcomp_sum)
  also have "... = (\<Sqinter>z\<in>{0..n+m}. kpower P z)"
    unfolding Nondet_choice_def
    apply (auto simp add:fun_eq_iff kcomp_def)
     apply fastforce
    by (metis add_cancel_right_left intervalE le_add1 le_add_diff_inverse le_diff_conv nat_le_linear)
  finally show ?thesis 
    by (auto simp add:kstar_fixed_def)
qed

(*
lemma kstar_fixed_comp_Suc:"(P\<^bsup>n\<^esup>) ; P = (P\<^bsup>Suc n\<^esup>)"
proof(intro ext set_eqI iffI conjI impI, goal_cases "\<subseteq>" "\<supseteq>")
  case ("\<subseteq>" x xa)
  (*then have "xa \<in> kpower P n x"
    unfolding kcomp_eq kstar_fixed_def Nondet_choice_def kpower_def apply auto
    *)
  then obtain y where y:"xa \<in> (kpower P y ; P) x \<and> y \<le> n"
    unfolding kcomp_eq kstar_def kstar_fixed_def Nondet_choice_def
    by auto+
  then show ?case
  proof (cases "y = n")
    case True
    then have "xa \<in> (kpower P n ; P) x"
      using y by blast
    then have "xa \<in> (kpower P n ; kpower P 1) x"
      using kpower_Suc_0
      by (metis One_nat_def)
    then have "xa \<in> (kpower P (Suc n)) x"
      by (metis True kpower_Suc' y)
    then show ?thesis
      unfolding kstar_fixed_def Nondet_choice_def by auto
  next
    case False
    then show ?thesis sorry
  qed
  then have "xa \<in> (kpower P y ; kpower P 1) x"
    using kpower_Suc_0
    by (metis One_nat_def)
  hence "xa \<in> kpower P (y + 1) x"
    using kpower_kcomp_sum
    by metis
  then show ?case 
    using kstar_def by fastforce
next
  case (\<supseteq> x xa)
  then show ?case sorry
qed
*)

(* The following lemma will get us to reason about the interval between
   st = DMoving and st = Waiting.*)
lemma
  fixes c::nat
  assumes "`t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<longrightarrow> I\<^sub>T`"
          "`t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<longrightarrow> Q`" (* no obstacle? before *)
          "a \<bowtie> wait" 
          "$wait \<sharp> I\<^sub>T" "$timer \<sharp> I\<^sub>T" "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
          (* P is an invariant before t\<^sub>0+c*tcycle *)
          "\<^bold>{ P \<and> Q \<^bold>} (T(C) ; EvolveUntil tcycle a \<sigma>) \<^bold>{ P \<^bold>}"
          (* From this we can deduce that P holds at t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c+1\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>? *)
          (* At t = t\<^sub>0 we have that I\<^sub>T holds, and between t\<^sub>0 \<le> t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>tcycle\<guillemotright> I\<^sub>R holds *)
          "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<and> P \<^bold>}
           (T(C) ; EvolveUntil tcycle a \<sigma>)
           \<^bold>{ (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<le> t \<and> t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c+1\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<longrightarrow> I\<^sub>R \<^bold>}"
          (* We can probably simplify this:*)
          "\<^bold>{ P \<and> I\<^sub>T \<^bold>} C \<^bold>{ I\<^sub>R \<^bold>}"
          (* I\<^sub>T is about continuous variables? *)
          "\<^bold>{ I\<^sub>R \<^bold>} TimerEvo tcycle a \<sigma> (True)\<^sup>e \<^bold>{ I\<^sub>R \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> P \<^bold>}
         (T(C) ; EvolveUntil tcycle a \<sigma>)\<^sup>+
         \<^bold>{ (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<le> t \<and> t < (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c+1\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>)) \<longrightarrow> I\<^sub>R \<^bold>}"
  oops
  (* Proof: need to 'unfold' the iteration 'c' times? ie.

    (T(C) ; EvolveUntil tcycle a \<sigma>)\<^sup>C ; (T(C) ; EvolveUntil tcycle a \<sigma>)\<^sup>+

     Then also need to show that for the above postcondition, we only
     need to look at the RHS of the composition for one iteration.

    ie. { t = t\<^sub>0 } (C ; EvolveUntil \<delta> a \<sigma>) { t < t\<^sub>0+\<delta>*c \<longrightarrow> Q } 
        \<longrightarrow> 
        { t = t\<^sub>0 } (C ; EvolveUntil \<delta> a \<sigma>)\<^sup>+ { t < t\<^sub>0+\<delta>*c \<longrightarrow> Q }
     *)

(* We need another, more generic, form of the above lemma, where we 
   prove that the invariant holds for a longer interval, so that we
   can state a result about the behaviour between st = STurning and
   st = DTurning. This will be between t and t+nat(PI/AV) *)

lemma "P\<^bsup>0\<^esup> = skip"

lemma
  assumes"\<^bold>{P\<^bold>} S \<^bold>{ Q \<and> R \<^bold>}"
  shows "\<^bold>{ P \<^bold>} S \<^bold>{ Q \<longrightarrow> R \<^bold>}"
  using assms
  oops

lemma 
  assumes "\<^bold>{P\<^bold>} (S)\<^bsup>c\<^esup> ; S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} (S)\<^bsup>Suc c\<^esup> \<^bold>{Q\<^bold>}"
  using assms
  unfolding kstar_fixed_def
  oops

lemma EvolveUntil_delta_cycles:
  assumes "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} C \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} kpower (T(C) ; EvolveUntil \<delta> a \<sigma>) c \<^bold>{ \<not> wait \<longrightarrow> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(real \<guillemotleft>c\<guillemotright>) \<le> t \<^bold>}"
  oops

lemma EvolveUntil_delta_cycles:
  assumes "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} C \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> \<^bold>{ \<not> wait \<longrightarrow> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(real \<guillemotleft>c\<guillemotright>) \<le> t \<^bold>}"
proof (induct c)
  case 0
  then show ?case
    apply (simp add:kstar_0)
    by (metis (mono_tags, lifting) SEXP_def dual_order.refl hoare_skip order.trans predicate1I)
next
  case (Suc c)
  then have "\<^bold>{$t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> \<^bold>{$wait \<or> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>c\<guillemotright> \<le> $t\<^bold>}"
    apply (wlp_full)
    by (smt (verit, del_insts) antisym le_boolI le_funI predicate1D)

  assume a1:"\<^bold>{$t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> \<^bold>{$wait\<^bold>}"
  then have "\<^bold>{$t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> ; (T(C) ; EvolveUntil \<delta> a \<sigma>) \<^bold>{$wait\<^bold>}"
    apply (rule hoare_kcomp)
    apply (rule hoare_kcomp[where R="($wait)\<^sup>e"])
    unfolding T_def apply (wlp_full)
    by (simp add: EvolveUntil_def hoare_T_wait le_funI)
  then have "\<^bold>{$t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^bsup>Suc c\<^esup> \<^bold>{$wait\<^bold>}"
    oops

  then show ?case
  proof (cases "\<^bold>{$t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} (C ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> \<^bold>{$wait\<^bold>}")
  assume ""
  then show ?case
    apply (simp; rule hoare_disj_posI)
    thm hoare_disj_posI
  (* Apply disjuntion on postcondition, then consider wait/not wait*)
    sorry
qed

  (* By induction? *)
  oops
lemma 
  assumes "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+(\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>) \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>+(\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>) \<^bold>}"
  using assms 
  sledgehammer (* I think we need a healthiness condition over P, such that it is insensitive to
    absolute time of t! *)

lemma 
  assumes "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> timer = 0 \<^bold>} {t` = 1, timer` = 1 | timer \<le> \<guillemotleft>\<delta>\<guillemotright>} \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+(\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>) \<and> timer = 0\<^bold>} {t` = 1, timer` = 1 | timer \<le> \<guillemotleft>\<delta>\<guillemotright>} \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>+(\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>) \<^bold>}"
  using assms unfolding TimerEvo_def
  apply (auto simp add:SEXP_def)
  oops

lemma bounded_time_lift_kstar_fixed:
  fixes c::"nat"
  assumes "0 \<le> \<delta>" "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
proof -
  have "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<sqinter> skip \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
    apply (rule hoare_choice)
    using assms apply simp
    apply (wlp_full)
    by (simp add: assms(1) mult_left_mono)
  then have "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
    by (metis kstar_1)
  then show ?thesis .
qed

lemma bounded_time_lift_kstar_fixed_leq:
  fixes c::"nat"
  assumes "0 \<le> \<delta>" "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
  shows "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
proof -
  have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<sqinter> skip \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
    apply (rule hoare_choice)
    using assms apply simp
    apply (wlp_full)
    using assms
    by (smt (verit, best) mult_left_mono)
  then have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}"
    by (metis kstar_1)
  then show ?thesis .
qed


lemma bounded_time_lift_kstar_fixed':
  fixes c::"nat"
  assumes "0 \<le> \<delta>" "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real (\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
  shows "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real (\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
proof -
  have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<sqinter> skip \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real (\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
    apply (rule hoare_choice)
    using assms apply simp
    apply (wlp_full)
    using assms
    by (smt (verit, ccfv_SIG) mult_left_mono)
  then have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
    by (metis kstar_1)
  then show ?thesis .
qed

lemma bounded_time_lift_kstar_fixed'':
  fixes c::"nat"
  assumes "0 \<le> \<delta>" "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>}"
  shows "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real (\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
proof -
  have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<sqinter> skip \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real (\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
    apply (rule hoare_stengthen_post[where Q="(t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright>)\<^sup>e"])
     apply wlp_full
    using assms apply (smt (verit, ccfv_SIG) mult_left_mono)
    apply (rule hoare_choice)
    using assms apply simp
    by (wlp_full)
  then have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
    by (metis kstar_1)
  then show ?thesis .
qed

(*
lemma bounded_time_lift_kstar_fixed':
  fixes c::"nat"
  assumes "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
  shows "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
proof -
  have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>} P \<sqinter> skip \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
    apply (rule hoare_choice)
    using assms apply simp
    by (wlp_full)
  then have "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>} P\<^bsup>1\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
    by (metis kstar_1)
  then show ?thesis .
qed
*)

(*
lemma 
  assumes "0 \<le> \<delta>" "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
  shows "\<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(\<guillemotleft>c\<guillemotright>+1) \<^bold>}"
  apply (rule Correctness_Specs.hoare_disj_preI[where a="(True)\<^sup>e" and b="(t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>)\<^sup>e" and c="(t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>)\<^sup>e"])
    apply simp_all
  using assms apply simp *)

lemma 
  assumes "0 \<le> \<delta>" "\<forall>c. \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<^bold>} P \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*(1+real \<guillemotleft>c\<guillemotright>) \<^bold>}" (* Is this assumption satisfied by the intended theorem?*)
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} P\<^bsup>c\<^esup> \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> \<^bold>}"
proof (induct c)
  case 0
  then show ?case
    unfolding Nondet_choice_def kpower_def kstar_fixed_def
    apply auto
    by (simp add:skip_def fbox_def)
next
  case (Suc c)
  then have suc_kstar_seq:"P\<^bsup>Suc c\<^esup> = P\<^bsup>c\<^esup> ; P\<^bsup>1\<^esup>"
    using kstar_fixed_plus_kcomp
    by (metis Suc_eq_plus1)
  have "\<^bold>{t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} P\<^bsup>c\<^esup> ; P\<^bsup>1\<^esup> \<^bold>{t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + (\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>Suc c\<guillemotright>)\<^bold>}"
   (* apply (rule hoare_kcomp[where R="(t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + (\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>))\<^sup>e"])
    using Suc apply blast
  apply (simp only:Nat.Suc_eq_plus1)
    apply (rule bounded_time_lift_kstar_fixed')
    using assms apply simp
    using assms sledgehammer
    using Suc apply blast
    using bounded_time_lift_kstar_fixed'*)
  proof (rule hoare_kcomp[where R="(t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + (\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>))\<^sup>e"], simp_all del:One_nat_def)
    show "\<^bold>{t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} P\<^bsup>c\<^esup> \<^bold>{t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>c\<guillemotright>\<^bold>}"
      using Suc by presburger
    show "\<^bold>{t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>c\<guillemotright>\<^bold>} P\<^bsup>1\<^esup> \<^bold>{t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * (1 + real \<guillemotleft>c\<guillemotright>)\<^bold>}"
      apply (rule bounded_time_lift_kstar_fixed_leq)
      using assms by simp+
  qed
   (* proof (rule hoare_disj_preI[where a="(True)\<^sup>e" and b="(t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>)\<^sup>e" and c="(t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright>)\<^sup>e"], simp_all del:One_nat_def)
      show "\<^bold>{t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>c\<guillemotright>\<^bold>} P\<^bsup>1\<^esup> \<^bold>{t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * (1 + real \<guillemotleft>c\<guillemotright>)\<^bold>}"
        thm bounded_time_lift_kstar_fixed
         apply (rule bounded_time_lift_kstar_fixed)
        using assms by simp+
      next
      show "\<^bold>{t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>c\<guillemotright>\<^bold>} P\<^bsup>1\<^esup> \<^bold>{t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * (1 + real \<guillemotleft>c\<guillemotright>)\<^bold>}"
    (* This won't work. *)
    using assms 
    sorry (* FIXME: Need assumption? *)*)
  (*then have "(\<Sqinter>i\<in>{0..c}. kpower f i) ; (\<Sqinter>i\<in>{0..1}. kpower f i) = "*)
  then show ?case
    using Suc suc_kstar_seq by presburger
qed

lemma 
  assumes "\<^bold>{ \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> = t \<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>) \<^bold>{ Q \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> \<not> $wait \<^bold>} (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^sup>+ \<^bold>{ \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*real \<guillemotleft>c\<guillemotright> \<le> t \<longrightarrow> Q \<^bold>}"
proof -
  have "((T(C) ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> ; (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^sup>+) = (T(C) ; EvolveUntil \<delta> a \<sigma>)\<^sup>+"
    using kstar_fixed_comp_eq_kstar_one by auto

  thm kstar_fixed_comp_eq_kstar_one

  (* Show that { t = \<guillemotleft>t\<^sub>0\<guillemotright> } (C ; EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> { t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>c\<guillemotright> } 
     and { Q } C { Q }
     and { Q } (EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> { Q }

     then use { Q } (EvolveUntil \<delta> a \<sigma>)\<^bsup>c\<^esup> { Q } \<longrightarrow> { Q } (EvolveUntil \<delta> a \<sigma>)\<^sup>+ { Q } 
  
     can use cases on wait after postcondition of LHS of composition:
     * If it is true, then it's the LHS behaviour, otherwise it is the composition.
   *)
  thm kstar_fixed_comp_eq_kstar_one
  oops

lemma
  assumes "\<^bold>{ I\<^sub>C \<^bold>} (T C ; EvolveUntil tcycle a \<sigma>)\<^bsup>c\<^esup> \<^bold>{ I\<^sub>C \<^bold>}"
          "\<^bold>{ I\<^sub>C \<^bold>} (T C ; EvolveUntil tcycle a \<sigma>) \<^bold>{ I\<^sub>K \<^bold>}"
          "\<^bold>{ I\<^sub>K \<^bold>} (T C ; EvolveUntil tcycle a \<sigma>)\<^bsup>k\<^esup> \<^bold>{ I\<^sub>K \<^bold>}"
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} 
         (T C ; EvolveUntil tcycle a \<sigma>)\<^bsup>k\<^esup> 
         \<^bold>{ (\<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>c\<guillemotright> * \<guillemotleft>tcycle\<guillemotright> \<le> t \<and> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>c+k\<guillemotright> * \<guillemotleft>tcycle\<guillemotright> < t) \<longrightarrow> I\<^sub>K\<^bold>}"
  oops

lemma
  assumes (*"\<^bold>{  \<^bold>} kpower (T C ; EvolveUntil tcycle a \<sigma>) \<guillemotleft>c\<guillemotright> \<^bold>{ Q \<^bold>}"*) (* ?? *)
          "\<^bold>{t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>c\<guillemotright> * \<guillemotleft>tcycle\<guillemotright> \<and> \<not>wait\<^bold>} (T C ; EvolveUntil tcycle a \<sigma>) \<^bold>{ (\<not>wait) \<longrightarrow> I \<^bold>}"
          "\<^bold>{ I \<^bold>} (T C ; EvolveUntil tcycle a \<sigma>)\<^bsup>k\<^esup> \<^bold>{ I \<^bold>}"
          (* \<longrightarrow> \<^bold>{ I\<^sub>R \<^bold>} (T C ; EvolveUntil tcycle a \<sigma>)\<^sup>* \<^bold>{ I\<^sub>R \<^bold>}*)
  shows "\<^bold>{t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>}
          (T C ; EvolveUntil tcycle a \<sigma>)\<^sup>+ 
         \<^bold>{((\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<le> t \<and> t < (\<guillemotleft>t\<^sub>0\<guillemotright>+(\<guillemotleft>c\<guillemotright>+\<guillemotleft>k\<^sub>1\<guillemotright>)*\<guillemotleft>tcycle\<guillemotright>)) \<longrightarrow> I\<^bold>}"
  oops

lemma
  fixes c::nat
  assumes "`t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<longrightarrow> I\<^sub>T`"
          "`t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<longrightarrow> Q`" (* no obstacle? before *)
          "a \<bowtie> wait" 
          "$wait \<sharp> I\<^sub>T" "$timer \<sharp> I\<^sub>T" "vwb_lens a" "t \<bowtie> a" "timer \<bowtie> a"
          (* P is an invariant before t\<^sub>0+c*tcycle*)
          "\<^bold>{ P \<and> Q \<^bold>} (T(C) ; EvolveUntil tcycle a \<sigma>) \<^bold>{ P \<^bold>}"
          (* From this we can deduce that P holds at t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c+1\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>? *)
          (* At t = t\<^sub>0 we have that I\<^sub>T holds, and between t\<^sub>0 \<le> t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>tcycle\<guillemotright> I\<^sub>R holds *)
          "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<and> P \<^bold>}
           (T(C) ; EvolveUntil tcycle a \<sigma>)\<^sup>+
           \<^bold>{ (t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<longrightarrow> I\<^sub>T) \<and> ((\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t \<and> t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c+1\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<longrightarrow> I\<^sub>T) \<^bold>}"
          (* We can probably simplify this:*)
          "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<and> I\<^sub>T \<^bold>} C \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright> \<and> I\<^sub>R \<^bold>}" 
          (* I\<^sub>T is about continuous variables? *)
          "\<^bold>{ I\<^sub>R \<^bold>} TimerEvo tcycle a \<sigma> (True)\<^sup>e \<^bold>{ I\<^sub>R \<^bold>}"
          (* P = state = DMoving ... \<and> *)
  shows "\<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<and> P \<^bold>} 
         (T(C) ; EvolveUntil tcycle a \<sigma>)\<^sup>+
         \<^bold>{ (t = (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<longrightarrow> I\<^sub>T) 
            \<and> 
           (((\<guillemotleft>t\<^sub>0\<guillemotright>+(\<guillemotleft>c\<guillemotright>+\<guillemotleft>k\<^sub>1\<guillemotright>)*\<guillemotleft>tcycle\<guillemotright>) \<le> t \<and> t < (\<guillemotleft>t\<^sub>0\<guillemotright>+(\<guillemotleft>c\<guillemotright>+\<guillemotleft>k\<^sub>1\<guillemotright>+\<guillemotleft>k\<^sub>2\<guillemotright>)*\<guillemotleft>tcycle\<guillemotright>)) \<longrightarrow> I\<^sub>R) \<^bold>}"
  apply (rule hoare_conj_pos')
  using assms(1)
  apply (simp add: fbox_def predicate1I taut_def)
  thm hoare_conj_pos
  
  (* We have the ability to tackle the design, rather than just specification. *)

  (* Key here is: c*tcycle controls how many times the loop gets unfolded, so need
     an inductive proof?

     We need a way to transform this into a proof of:

     \<^bold>{ t = (\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<and> I\<^sub>T \<^bold>} 
     (T(C) ; EvolveUntil tcycle a \<sigma>)
     \<^bold>{ (t = (\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<longrightarrow> I\<^sub>T) \<and> (((\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<le> t \<and> t < (2*\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>)) \<longrightarrow> I\<^sub>R) \<^bold>}
     \<Longrightarrow>
     \<^bold>{ t = (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<and> I\<^sub>T \<^bold>} 
     (T(C) ; EvolveUntil tcycle a \<sigma>)
     \<^bold>{ (t = (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<longrightarrow> I\<^sub>T) \<and> (((\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<le> t \<and> t < (\<guillemotleft>t\<^sub>0\<guillemotright>+2*\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>)) \<longrightarrow> I\<^sub>R) \<^bold>}
     \<Longrightarrow>
     \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} 
     (T(C) ; EvolveUntil tcycle a \<sigma>)\<^sup>+
     \<^bold>{ (t = (\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<longrightarrow> I\<^sub>T) \<and> (((\<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>) \<le> t \<and> t < (\<guillemotleft>t\<^sub>0\<guillemotright>+2*\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>)) \<longrightarrow> I\<^sub>R) \<^bold>}
      
     For any amount of time between t\<^sub>0 and \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>tcycle\<guillemotright>, we can unfold the computation 
     c times. Need to show this.

     Obs 1: Also it seems we may need a healthiness condition over the ODE system to state that 
            it is invariant to the choice of t value, so that t is only used for relative time?

     Obs 2: Should the auxiliary variable wait be named differently, eg. evolving, to distinguish
            it from the role played in the theory of reactive processes? 
  *)
  using assms 

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

lemma kpower_from_wait:
  assumes "`P \<longrightarrow> wait`"
  shows "\<^bold>{P\<^bold>} kpower (T X) k \<^bold>{\<not> wait \<longrightarrow> Q\<^bold>}"
proof (induct k)
  case 0
  then show ?case
    using assms kpower_0
    by (metis (mono_tags, lifting) SEXP_def fbox_kpower_0 predicate1I taut_def)
next
  case (Suc k)
  have p:"kpower (T X) (Suc k) = (T X) ; kpower (T X) k"
    using kpower_Suc by blast
  show ?case
    apply (simp only:p)
    apply (rule hoare_kcomp[where R="(P)\<^sup>e"])
    using assms
    apply (metis (mono_tags, lifting) SEXP_def hoare_T_wait predicate1I taut_def)
    using Suc by blast
qed

lemma kpower_decompose:
  assumes "k > 1" "\<^bold>{ P \<^bold>} X \<^bold>{ Q \<^bold>}" "\<^bold>{ Q \<^bold>} kpower X (k-1) \<^bold>{ R \<^bold>}"
  shows "\<^bold>{ P \<^bold>} kpower X k \<^bold>{ R \<^bold>}"
proof -
  from assms obtain c where c:"k = 1 + c"
    using less_imp_add_positive by blast
  then have "kpower X k = kpower X (1 + c)"
    by auto
  also have "... = X ; kpower X c"
    using kpower_kcomp_sum
    by (simp add: kpower_Suc)
  then show "\<^bold>{ P \<^bold>} kpower X k \<^bold>{ R \<^bold>}"
    using c apply (simp)
    apply (rule hoare_kcomp[where R="Q"])
    using assms apply blast
    using assms(3) by auto
qed

lemma kpower_cyclic:
  assumes "\<forall>t\<^sub>0. \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} X \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
  shows "\<^bold>{ P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} kpower X k \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>k\<guillemotright> \<^bold>}"
proof (induct k arbitrary:t\<^sub>0 P)
  case 0
  then show ?case
    using assms
    by (smt (verit, ccfv_threshold) SEXP_def fbox_kpower_0 mult_eq_0_iff of_nat_0 predicate1I taut_def)
next
  case (Suc k)
  then have noP:"\<And>t\<^sub>1. \<^bold>{$t = \<guillemotleft>t\<^sub>1\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
    by (simp add: SEXP_def le_fun_def)
  have SucP:"\<^bold>{P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * \<guillemotleft>k\<guillemotright>\<^bold>}"
    using assms(1)
    by (simp add: Suc)
  have p:"kpower X (Suc k) = X ; kpower X k"
    using kpower_Suc by blast
  show ?case
  proof (simp only:p, rule hoare_kcomp[where R="($t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"])
    show "\<^bold>{P \<and> $t = \<guillemotleft>t\<^sub>0\<guillemotright>\<^bold>} X \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>}"
      using assms by fastforce
  next
    show "\<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real (Suc \<guillemotleft>k\<guillemotright>)\<^bold>}"
    proof (rule hoare_post_eq[where R="(t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> *\<guillemotleft>k\<guillemotright>)\<^sup>e"])
      show " (\<lambda>\<s>. get\<^bsub>t\<^esub> \<s> \<le> t\<^sub>0 + \<delta> + \<delta> * real k) = (\<lambda>\<s>. get\<^bsub>t\<^esub> \<s> \<le> t\<^sub>0 + \<delta> * real (Suc k))"
        by (simp add: add.assoc distrib_left)
    next
      show "\<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
      (* Case split *)
      proof (rule hoare_disj_preI[where a="(True)\<^sup>e" and b="($t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e" and c="($t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sup>e"], simp_all)
        show "(\<lambda>\<s>. get\<^bsub>t\<^esub> \<s> \<le> t\<^sub>0 + \<delta>) = ($t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> \<or> $t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>)\<^sub>e"
          by expr_auto
      next
        show "\<^bold>{$t = \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
          by (simp add: noP)
      next
        show "\<^bold>{$t < \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
        proof -
           have "\<forall>c. \<^bold>{$t = \<guillemotleft>t\<^sub>0 + \<delta> - c\<guillemotright> \<and> \<guillemotleft>c\<guillemotright> > 0\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0 + \<delta> - c\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright> \<and> \<guillemotleft>c\<guillemotright> > 0\<^bold>}"
            using Suc noP apply expr_auto
            by blast
          then have pp:"\<forall>c. \<^bold>{$t = \<guillemotleft>t\<^sub>0 + \<delta> - c\<guillemotright> \<and> \<guillemotleft>c\<guillemotright> > 0\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0 + \<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
            apply expr_auto
            by (smt (verit) fbox_def le_bool_def le_fun_def)
          then have pp:"\<^bold>{\<exists>c. $t = \<guillemotleft>t\<^sub>0 + \<delta> - c\<guillemotright> \<and> \<guillemotleft>c\<guillemotright> > 0\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0 + \<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
            by (expr_auto)
          then have pp:"\<^bold>{$t < \<guillemotleft>t\<^sub>0 + \<delta>\<guillemotright>\<^bold>} kpower X k \<^bold>{$t \<le> \<guillemotleft>t\<^sub>0 + \<delta>\<guillemotright> + \<guillemotleft>\<delta>\<guillemotright> * real \<guillemotleft>k\<guillemotright>\<^bold>}"
            apply expr_auto
            by (smt (verit, best) predicate1D)
          then show ?thesis
            by auto
        qed
      qed
    qed
  qed
qed

lemma kpower_cyclic':
  assumes "\<forall>t\<^sub>0. \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} X \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright> \<^bold>}" "`P \<longrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright>`"
  shows "\<^bold>{ P \<^bold>} kpower X k \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>k\<guillemotright> \<^bold>}"
  apply (rule hoare_weaken_pre_conj[where P="(P \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright>)\<^sup>e"])
  using assms apply expr_auto
  using assms by (simp add:kpower_cyclic)

lemma
  assumes "`P \<longrightarrow> t = \<guillemotleft>\<epsilon>\<^sub>s\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>\<delta>\<guillemotright>`"
        "\<^bold>{ Q \<^bold>} X \<^bold>{ Q \<^bold>}" "\<forall>t\<^sub>0. \<^bold>{ t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} X \<^bold>{ t \<le> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>\<delta>\<guillemotright> \<^bold>}"
        "\<^bold>{ P \<^bold>} kpower X k \<^bold>{ (\<guillemotleft>\<epsilon>\<^sub>s\<guillemotright> + (\<guillemotleft>c\<guillemotright>+1)*\<guillemotleft>\<delta>\<guillemotright> \<le> t \<and> t < \<guillemotleft>\<epsilon>\<^sub>s\<guillemotright> + (\<guillemotleft>c\<guillemotright>+\<guillemotleft>k\<guillemotright>)*\<guillemotleft>\<delta>\<guillemotright>) \<longrightarrow> Q \<^bold>}"
      shows "\<^bold>{ P \<^bold>} X\<^sup>+ \<^bold>{ (\<guillemotleft>\<epsilon>\<^sub>s\<guillemotright> + (\<guillemotleft>c\<guillemotright>+1)*\<guillemotleft>\<delta>\<guillemotright> \<le> t \<and> t < \<guillemotleft>\<epsilon>\<^sub>s\<guillemotright> + (\<guillemotleft>c\<guillemotright>+\<guillemotleft>k\<guillemotright>)*\<guillemotleft>\<delta>\<guillemotright>) \<longrightarrow> Q  \<^bold>}"
proof -
  have "\<^bold>{ P \<^bold>} kpower X k \<^bold>{ t \<le> (\<guillemotleft>\<epsilon>\<^sub>s\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>\<delta>\<guillemotright>)+\<guillemotleft>\<delta>\<guillemotright>*\<guillemotleft>k\<guillemotright> \<^bold>}"
    using assms kpower_cyclic'
    by blast
  have "X\<^sup>+ = X\<^bsup>k\<^esup> ; X\<^sup>+"
    by (simp add: kstar_fixed_comp_eq_kstar_one)

end

term "[\<leadsto>] \<circ>\<^sub>s \<sigma>(x \<leadsto> u, x \<leadsto> v)"
term "\<langle>\<sigma>(x \<leadsto> v, y \<leadsto> v)\<rangle>"
term "\<langle>\<sigma>(x \<leadsto> v)\<rangle>"
term "\<langle>CONST subst_upd [\<leadsto>] x (e)\<^sub>e\<rangle>"

term "[\<leadsto>]"
term "(subst_upd [\<leadsto>] x (e)\<^sub>e)"

context robosim
begin

text \<open> To show that P is an invariant when X executed up to 'k' times from
 a state where F 0 holds, where 'k' is bounded by a constant 'e', it suffices to show the following? \<close>

lemma 
  assumes "k < e" "n < e/k" "\<^bold>{P \<and> F \<guillemotleft>n\<guillemotright>\<^bold>} X \<^bold>{P \<and> (F \<guillemotleft>n\<guillemotright> \<or> F (\<guillemotleft>n\<guillemotright> + 1))\<^bold>}"
  shows "\<^bold>{P \<and> F 0\<^bold>} X\<^bsup>k\<^esup> \<^bold>{ P \<^bold>}"
  using assms(2,3) 
proof(induct k arbitrary:n)
  case 0
  then show ?case sorry
next
  case (Suc k)
  then show ?case sorry
qed

lemma hoare_NonDet_index:
  assumes "\<forall>k\<le>m. \<^bold>{P\<^bold>} X k \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} \<Sqinter>i\<in>{0..m}. X i \<^bold>{Q\<^bold>}"
  using assms by (wlp_full)

lemma
  assumes "\<forall>k\<le>m. \<^bold>{P\<^bold>} kpower X k \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} X\<^bsup>m\<^esup> \<^bold>{Q\<^bold>}"
  apply (simp add:kstar_fixed_def)
  using assms by (rule hoare_NonDet_index)

(* abbreviation (input) "TimerEvo \<delta> a \<sigma> B \<equiv> g_dl_ode_frame a \<sigma> (@B \<and> $timer \<le> \<delta>)\<^sub>e" *)
method hoare_help_rs uses add = ( 
    (
      (simp only:kcomp_assoc kcomp_skip)?, 
      (   (rule hoare_else_kcomp, force) 
        | (rule hoare_floyd_kcomp, simp, simp add: usubst_eval usubst unrest)
        | (rule hoare_if_kcomp, force) 
        | (rule hoare_ifte_kcomp)
        | (rule hoare_pre_not_while_seq, simp, hoare_wp_auto)
        | (rule hoare_pre_not_while, simp, hoare_wp_auto)
        | (rule hoare_if_then_cond, simp)
        | (rule EvoleUntil_wait_skip, simp)
        | (rule hoare_skip_conjI, simp)
        | (rule hoare_skip)
        | (simp_all only:kcomp_skip)
        | (rule hoare_if_then_else, simp)
        | (rule hoare_false, subst_eval)
        | (rule hoare_kcomp_if_then_else_any)
        | ((rule hoare_kcomp_assign_unrest), simp add: expr_simps, simp add:expr_simps)
        | (simp add:unrest usubst expr_simps add)
        (*| (rule hoare_inv_post, expr_simp, (dInduct | (rule nmods_invariant, (clarify intro!:closure, subst_eval))))*) (* Attempt to use postcondition as invariant *)
        | (rule hoare_inv_post, expr_simp, dInduct_mega)
        | (rule nmods_invariant, (clarify intro!:closure, subst_eval))
        | (dInduct_mega)
       )
     )+, 
   (subst WHILE_unroll_IF[symmetric])?
  )+,(tactic distinct_subgoals_tac)?

lemma hoare_kcomp_nmods_rhs:
  assumes "Y nmods Q" "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} X ; Y \<^bold>{Q\<^bold>}"
  using assms(1) assms(2) hoare_kcomp_inv_rhs nmods_invariant by blast

end

method hoare_help uses add = ( 
    (
      (simp only:kcomp_assoc kcomp_skip)?, 
      (   (rule hoare_else_kcomp, force) 
        | (rule hoare_floyd_kcomp, simp, simp add: usubst_eval usubst unrest)
        | (rule hoare_if_kcomp, force) 
        | (rule hoare_ifte_kcomp)
        | (rule hoare_pre_not_while_seq, simp, hoare_wp_auto)
        | (rule hoare_pre_not_while, simp, hoare_wp_auto)
        | (rule hoare_if_then_cond, simp)
        | (simp_all only:kcomp_skip)
        | (dInduct_mega)
        | (rule nmods_invariant, (clarify intro!:closure, subst_eval))
        | (rule hoare_false, subst_eval)
        | (rule hoare_kcomp_if_then_else_any)
        | ((rule hoare_kcomp_assign_unrest), simp add: expr_simps, simp add:expr_simps)
        | (simp add:unrest usubst expr_simps add)
        | (rule hoare_inv_post, expr_simp, (dInduct | (rule nmods_invariant, (clarify intro!:closure, subst_eval)))) (* Attempt to use postcondition as invariant *)
       )
     )+, 
   (subst WHILE_unroll_IF[symmetric])?
  )+

end
