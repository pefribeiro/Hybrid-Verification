theory WMR

imports 
  "Hybrid-Verification.Hybrid_Verification"
  "Z_Toolkit.Trace_Algebra"
begin

term "D X \<mapsto> P F = (X has_derivative P) F"
term "DERIV f x :> k"
term "(\<And>x. x * X' = X x)"
term "(f has_derivative (*) X) F"
term "(X has_derivative (\<lambda>x. 0)) F"

lemma "(X has_derivative (\<lambda>x. 0)) F = (X has_field_derivative 0) F"
  by (simp add: has_field_derivative_def lambda_zero)

lemma "open {0::real<..}"
  by simp

lemma DERIV_isconst_all_gzero:
  fixes f :: "real \<Rightarrow> real"
  assumes "x \<ge> 0" "y \<ge> 0"
  shows "\<forall>x\<ge>0. DERIV f x :> 0 \<Longrightarrow> f x = f y"
  using assms 
  by (metis DERIV_nonneg_imp_nondecreasing DERIV_nonpos_imp_nonincreasing antisym order_refl)  

lemma DERIV_isconst_all_gt_zero:
  fixes f :: "real \<Rightarrow> real"
  assumes "x > 0" "y > 0"
  shows "\<forall>x>0. DERIV f x :> 0 \<Longrightarrow> f x = f y"
  using assms
  by (smt (verit) DERIV_nonneg_imp_nondecreasing DERIV_nonpos_imp_nonincreasing)

lemma 
  fixes X :: "real \<Rightarrow> real"
  assumes "\<forall>x\<ge>0. D X \<mapsto> (\<lambda>x. 0) at x" "X 0 = v" "0 \<le> xa" "xa \<le> t" 
  shows "v = (X xa)"
proof -
  have "(\<forall>x\<ge>0. (X has_field_derivative 0) (at x))"
    using assms by (simp add: has_field_derivative_def lambda_zero)
  then have "\<forall>x\<ge>0. DERIV X x :> 0"
    by blast
  then have "\<forall>x y. x \<ge> 0 \<and> y \<ge> 0 \<longrightarrow> X x = X y"
    using assms DERIV_isconst_all_gzero 
    by presburger
  then have "X 0 = X xa"
    using assms(3) by blast
  then show ?thesis using assms by auto
qed

lemma helpful_deriv:
  fixes X :: "real \<Rightarrow> real"
  assumes "\<forall>x\<ge>0. D X \<mapsto> (\<lambda>x. 0) at x within Collect ((\<le>) 0)"
  shows "\<forall>x\<ge>0. D X \<mapsto> (\<lambda>x. 0) at x within Collect ((<) 0)"
  by (metis assms dual_order.order_iff_strict has_derivative_subset mem_Collect_eq subsetI)

(* FIXME: I believe we need a generalisation of the below to arbitrary function X, where only
   one component is 0 *)
lemma deriv_0_same_value:
  fixes X :: "real \<Rightarrow> real"
  assumes "\<forall>x\<ge>0. D X \<mapsto> (\<lambda>x. 0) at x within Collect ((\<le>) 0)"
          (*"\<forall>x>0. D X \<mapsto> (\<lambda>x. 0) (at x within Collect ((<) (0::real)))"*) "X 0 = v" "0 \<le> xa" "xa \<le> t" 
  shows "v = (X xa)"
proof -
  have cont:"continuous_on (Collect ((\<le>) 0)) X"
    unfolding continuous_on_def
    by (metis assms(1) continuous_within has_derivative_continuous mem_Collect_eq)
  then have cont_on:"continuous_on {0..xa} X"
    by (metis atLeastAtMost_iff continuous_on_subset mem_Collect_eq subset_iff)

  have "\<forall>x\<ge>0. D X \<mapsto> (\<lambda>x. 0) at x within Collect ((<) 0)"
    using assms helpful_deriv by blast
  then have "(\<forall>x\<ge>0. (X has_field_derivative 0) (at x within Collect ((<) 0)))"
    using assms by (simp add: has_field_derivative_def lambda_zero)
  then have "(\<forall>x\<ge>0. (X has_field_derivative 0) (at x within {0<..}))"
    by (simp add: greaterThan_def)
  then have "(\<forall>x>0. (X has_field_derivative 0) (at x))"
    by (metis at_within_open greaterThan_iff less_le_not_le open_greaterThan)
  then have a:"\<forall>x>0. DERIV X x :> 0"
    by auto
  then have "\<forall>x y. x > 0 \<and> y > 0 \<longrightarrow> X x = X y"
    using assms DERIV_isconst_all_gt_zero
    by presburger
  then have "X 0 = X xa"
    using DERIV_isconst_end cont_on 
    by (smt (verit) a assms(3))
  then show ?thesis
    using assms(2) by blast
  (* Problem with this approach is that we do not have any witness at a value xa > 0
     such that X xa = X 0. If we did, then the above would follow.

     Err. It just turns out we needed to demonstrate continuity of X. *)
qed

lit_vars


lemma 
  fixes avLW :: "real \<Longrightarrow> 'st"
  shows "{avLW` = \<guillemotleft>k\<guillemotright> | \<guillemotleft>k\<guillemotright> = 0} = {avLW` = 0 | \<guillemotleft>k\<guillemotright> = 0}"
  unfolding g_orbital_on_def
  apply(clarsimp simp add: fun_eq_iff)
  (*apply (rule_tac x="[avLW \<leadsto> $avLW]" in arg_cong[symmetric])*)

  apply (cases "k = 0")
   apply expr_auto
  apply expr_auto
  by (smt (verit) g_orbital_eq image_le_pred mem_Collect_eq)+

thm lframe_set_def

lemma 
  fixes avLW :: "real \<Longrightarrow> 'st"
  assumes "k = 0"
  shows "{avLW` = 0 | \<guillemotleft>k\<guillemotright> = 0} = {avLW` = 0}"
  using assms by presburger

chantype ch_buffer =
  inp :: unit

term inp_C

thm g_orbital_on_def



datatype DIMENSION = OneD | TwoD | ThreeD

dataspace wmr = 
  constants
    \<comment> \<open> Robot d-model \<close>
    C      :: real
    LV     :: real
    \<comment> \<open> Robot p-model \<close>
    radius :: real
    mass   :: real
    W      :: real
    L      :: real
    \<comment> \<open> Arena \<close>
    size :: "real^3"
    dimension :: "DIMENSION"
    \<comment> \<open> Scenario: wheel inertias \<close>
    lwI :: real
    rwI :: real
    tcycle :: real
    tscale :: real
  assumes
    non_zeros: "lwI > 0" "rwI > 0" "radius > 0" "W > 0" "L > 0"
  variables
    (*trace :: "'t::trace"
    wait :: "bool"*)
    \<comment> \<open> Timer \<close>
    t :: "real"
    \<comment> \<open> P-model: torques \<close>
    LMotorT :: real
    RMotorT :: real
    \<comment> \<open> Scenario mapping \<close>
    robotPose :: "real^6"
    (* How about local variables? I suppose for now need all of them visible/declared here. *)
    \<comment> \<open> Scenario: robot position (px,py) and yaw (yw) \<close>
    px :: "real"
    py :: "real"
    yw :: "real"
    \<comment> \<open> Scenario: middle point between wheels (mx,my) \<close>
    mx :: "real"
    my :: "real"
    \<comment> \<open> Scenario: wheel velocities \<close>
    avLW :: "real"
    avRW :: "real"

context wmr
begin

lemma deriv_0_imp_nmods:
  shows "{yw` = 0} nmods {yw}" 
  apply (simp add: not_modifies_def scene_equiv_def lens_override_def )
  unfolding g_orbital_on_def
  apply expr_auto
  unfolding g_orbital_def g_orbit_def ivp_sols_def has_vderiv_on_def has_vector_derivative_def
  apply auto (* Doesn't seem provable? It is! *)
  using deriv_0_same_value
  by (metis vwb_lens.put_eq vwbs(7))

lemma deriv_0_some_nmods:
  shows "{mx` = 1, yw`= 0} nmods {yw}"
  apply (simp add: not_modifies_def scene_equiv_def lens_override_def )
  unfolding g_orbital_on_def
  apply expr_auto
  unfolding g_orbital_def g_orbit_def ivp_sols_def has_vderiv_on_def has_vector_derivative_def
  apply auto
  using deriv_0_same_value 
  sorry

lemma
  shows "{mx` = 1} = {mx` = 1, yw`= 0}"
  using deriv_0_some_nmods
(*
  unfolding g_orbital_on_def
  apply(clarsimp simp add: fun_eq_iff g_orbital_eq )
  apply expr_auto
   apply(simp_all add:image_def)
  defer
  
  apply (rule_tac x="a" in exI, auto)
   apply (rule_tac x="X t" in exI)
   apply (rule_tac x="t" in exI, auto)
    apply (rule_tac x="t" in exI)
    apply (rule_tac x="\<lambda>y. (X t, y)" in exI, auto)
   *)

abbreviation 
  "evolve \<equiv> 
  {yw` = (radius/W*avRW)-(radius/W*avLW),
   mx` = (radius/2 * cos(yw) * avLW)+(radius/2 * cos(yw) * avRW),
   my` = (radius/2 * sin(yw) * avLW)+(radius/2 * sin(yw) * avRW),
   avLW` = LMotorT/lwI,
   avRW` = RMotorT/rwI,
   t` = 1
  }"

(*| px = mx \<and> 
     py = my+L/4 \<and> 
     yw = robotPose$5 \<and> 
     px = robotPose$0 \<and> 
     py = robotPose$1 \<and> 
     robotPose$2 = 0 \<and> 
     robotPose$3 = 0 \<and> 
     robotPose$4 = 0*)

text \<open> The above is fine, but note that because avLW/avRW can change over time,
       then we have a problem with solving the above system for mx/my via 
       integration. This is expected of a non-holonomic system. \<close>

text \<open> Properties I would like to explore. \<close>

text \<open> If there is no obstacle, then given the initial pose of the robot,
       where p=(px,py) is the 2D coordinate, with yaw YW, and linear velocity 
       set by the controller at LV, then we have the following: 

       p' = p+rot((t*LV,0),yw)

       where LV = radius*(avLW+avRW)/2

       For straight-line we have that avLW=avRW, so:

       LV = radius*avLW so have that: avLW = LV/radius
     \<close>

lemma no_yaw_change:
  "\<^bold>{LMotorT = RMotorT \<and> lwI = rwI \<and> avRW = avLW \<and> yw = yw\<^sub>0\<^bold>}
    evolve
   \<^bold>{LMotorT = RMotorT \<and> lwI = rwI \<and> avRW = avLW \<and> yw = yw\<^sub>0\<^bold>}"
  apply (rule_tac diff_cut_on_split)
   apply (dInduct)
  apply (rule_tac diff_cut_on_split)
   apply (dInduct)
  apply (rule_tac diff_cut_on_split)
   apply (dInduct)
  apply (dInduct)
  done

lemma no_yaw_change_zero_torque:
  "\<^bold>{LMotorT = 0 \<and> RMotorT = 0 \<and> avLW = avRW \<and> yw = yw\<^sub>0\<^bold>}
    evolve
   \<^bold>{LMotorT = 0 \<and> RMotorT = 0 \<and> avLW = avRW \<and> yw = yw\<^sub>0\<^bold>}"
  apply (rule_tac diff_cut_on_split)
     apply (dInduct)
  apply (rule_tac diff_cut_on_split)
     apply (dInduct)
  apply (rule_tac diff_cut_on_split)
     apply (dInduct)
  by (dInduct)

text \<open> The above can be expressed as an invariant over the position mx/my wrt. t, yw and LV,
       where mx_i and my_i are the initial coordinates. \<close>

lemma linear_motion:
  assumes "LV > 0"
  shows "\<^bold>{LMotorT = 0 \<and> RMotorT = 0 
        \<and> avLW = LV/radius \<and> avRW = LV/radius 
        \<and> yw = yw\<^sub>0
        \<and> mx = mx\<^sub>i + t*LV * cos(yw) 
        \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
       (evolve)
      \<^bold>{LMotorT = 0 \<and> RMotorT = 0 
        \<and> avLW = LV/radius \<and> avRW = LV/radius
        \<and> yw = yw\<^sub>0
        \<and> mx = mx\<^sub>i + t*LV * cos(yw) 
        \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (dInduct_mega)
  (* This nearly works, but then need to incorporate this result into system:

      "$avLW = LV / radius \<and> $avRW = LV / radius \<longrightarrow> radius / 2 * cos ($yw) * $avLW + radius / 2 * cos ($yw) * $avRW = cos ($yw) * LV"
      "$avLW = LV / radius \<and> $avRW = LV / radius \<longrightarrow> radius / 2 * sin ($yw) * $avLW + radius / 2 * sin ($yw) * $avRW = sin ($yw) * LV"

    after which, it should be possible to show it holds.

    See below for an equivalent ODE system / property. *)
  oops

abbreviation 
  "evolve_simp \<equiv> 
  {mx` = cos(yw) * LV,
   my` = sin(yw) * LV,
   t` = 1
  }" (* Cannot have eq. yw` = 0 in system, otherwise tactic no longer works. *)

lemma linear_motion:
  shows "\<^bold>{mx = mx\<^sub>i + t*LV * cos(yw) 
        \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
       (evolve_simp)
      \<^bold>{mx = mx\<^sub>i + t*LV * cos(yw) 
        \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule_tac diff_cut_on_split)
   apply (dInduct)
  by (dInduct)

lemma linear_motion_1:
  "\<^bold>{$mx = mx\<^sub>i + $t * LV * cos ($yw)\<^bold>} evolve_simp \<^bold>{$mx = mx\<^sub>i + $t * LV * cos ($yw)\<^bold>}"
  by (dInduct)




lemma g_ode_frame_prod_sugar:
  "h \<bowtie> t \<Longrightarrow> {h` = \<guillemotleft>k\<guillemotright>, t` = 1 | $t \<le> (H\<^sub>u - h\<^sub>m)/\<guillemotleft>k\<guillemotright>} = {(h, t)` = (\<guillemotleft>k\<guillemotright>, 1) | $t \<le> (H\<^sub>u - h\<^sub>m)/\<guillemotleft>k\<guillemotright>}"
  unfolding g_orbital_on_def apply(clarsimp simp add: fun_eq_iff)
  apply (rule_tac x="[h \<leadsto> \<guillemotleft>k\<guillemotright>, t \<leadsto> 1]" in arg_cong)
  apply  (expr_simp add: lens_indep.lens_put_comm)
  oops

lemma eq_evolutions:
  "{avLW` = $LMotorT / lwI, avRW` = $RMotorT / lwI,
     mx` = radius * cos ($yw) * $avLW / 2 + radius * cos ($yw) * $avRW / 2,
     my` = radius * sin ($yw) * $avLW / 2 + radius * sin ($yw) * $avRW / 2, t` = 1,
     yw` = radius * $avRW / W -
           radius * $avLW / W | $LMotorT = 0 \<and> $RMotorT = 0}
  =
  {avLW` = 0, avRW` = 0,
     mx` = radius * cos ($yw) * $avLW / 2 + radius * cos ($yw) * $avRW / 2,
     my` = radius * sin ($yw) * $avLW / 2 + radius * sin ($yw) * $avRW / 2, t` = 1,
     yw` = radius * $avRW / W -
           radius * $avLW / W | $LMotorT = 0 \<and> $RMotorT = 0}"
   unfolding g_orbital_on_def
   apply(clarsimp simp add: fun_eq_iff)
  apply (case_tac "(get\<^bsub>LMotorT\<^esub> x) = 0 \<and> (get\<^bsub>RMotorT\<^esub> x) = 0")
   apply expr_auto
  apply expr_auto
  by (smt (verit) g_orbital_eq image_le_pred mem_Collect_eq)+

lemma "{mx` = cos(yw) * LV} = {mx` = cos(yw) * LV, yw`= 0}"
  unfolding g_orbital_on_def
  apply(clarsimp simp add: fun_eq_iff)
  apply expr_auto
  sledgehammer
  apply (rule_tac x="[mx \<leadsto> cos ($yw) * LV, yw \<leadsto> $yw]" in arg_cong)
  apply (case_tac "(get\<^bsub>LMotorT\<^esub> x) = 0 \<and> (get\<^bsub>RMotorT\<^esub> x) = 0", auto)

lemma eq_box_imp:
  assumes "Q = R"
  shows "`P \<longrightarrow> |Q] P` = `P \<longrightarrow> |R] P`"
  using assms by auto


lemma angular_motion:
  assumes "LV > 0" "lwI = rwI"
  shows "\<^bold>{LMotorT = 0 \<and> RMotorT = 0
        \<and> avLW = -avRW 
        \<and> mx = mx\<^sub>i 
        \<and> my = my\<^sub>i\<^bold>}
       (evolve)
      \<^bold>{LMotorT = 0 \<and> RMotorT = 0
        \<and> avLW = -avRW
        \<and> mx = mx\<^sub>i 
        \<and> my = my\<^sub>i\<^bold>}"
    apply (rule_tac diff_cut_on_split)
     apply (dInduct)
  apply (rule_tac diff_cut_on_split)
     apply (dInduct)
  apply (rule_tac diff_cut_on_split)
   defer
   apply (rule_tac diff_cut_on_split)
    apply (dInduct)
   apply (dInduct)
  apply (hoare_wp_simp)
  using eq_evolutions eq_box_imp (* Hmmm *)
 apply (auto simp only: expr_defs  )
  oops

lemma linear_motion_forever:
  shows "\<^bold>{mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
       (evolve_simp\<^sup>*)
      \<^bold>{mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  using kstar_inv_rule linear_motion
  by fastforce

(* stepwise attempt below

  apply (rule_tac diff_cut_on_split)
   apply dInduct
  apply (rule_tac diff_cut_on_split)
   apply dInduct
  apply (rule_tac diff_cut_on_split)
   apply dInduct
apply (rule_tac diff_cut_on_split)
   apply dInduct
apply (rule_tac diff_cut_on_split)
   apply dInduct
apply (rule_tac diff_cut_on_split)
   apply dInduct *)

(*
  apply (auto intro!:derivative_intros)
  using assms  apply auto 
  apply (auto simp add: field_differentiable_at_cos field_differentiable_imp_differentiable)
  apply expr_simp
  oops

  thm "ldifferentiable"
*)

lemma 
  fixes s :: "'a::{banach,real_normed_field}"
  shows "cos differentiable at s"
proof -
  have "cos field_differentiable at s"
    by (simp add: field_differentiable_at_cos)
  then show ?thesis by (simp add:field_differentiable_imp_differentiable)
qed

text \<open> Second property: if there is an obstacle  \<close>

named_theorems local_flow

abbreviation "ratio \<equiv> radius/W"

text \<open> If we ignore position and focus just on velocities, then we can obtain
       a complete solution rather easily. \<close>

abbreviation 
  "mini_evolution \<equiv> 
  {yw`   = ratio*(avRW-avLW),
   avLW` = LMotorT,
   avRW` = RMotorT,
   t` = 1
  }"

abbreviation 
  "mini_evolve \<equiv> 
  [yw \<leadsto> ratio*(avRW-avLW),
   avLW \<leadsto> LMotorT,
   avRW \<leadsto> RMotorT,
   t \<leadsto> 1]"

abbreviation "mini_wmr_flow \<tau> \<equiv> [
  yw \<leadsto> ratio*(((RMotorT)*(\<tau>^2/2) + avRW*\<tau>) - ((LMotorT)*(\<tau>^2/2) + avLW*\<tau>)) + yw,
  avLW \<leadsto> (LMotorT) * \<tau> + avLW,
  avRW \<leadsto> (RMotorT) * \<tau> + avRW,
  t \<leadsto> \<tau> + t]"

abbreviation "Init \<equiv> LMotorT ::= C ; RMotorT ::= C ; avLW ::= 0; avRW ::= 0 ; t ::= 0"

abbreviation "Ctrl \<equiv> LMotorT ::= 0 ; RMotorT ::= 0 ; t ::= 0"

abbreviation "Cycle \<equiv> IF t \<ge> (tcycle*tscale) THEN Ctrl ELSE skip"

text \<open> We need to certify the solution. \<close>

lemma mini_wmr_flow_exp:
  "local_flow_on mini_evolve (yw+\<^sub>LavLW+\<^sub>LavRW+\<^sub>Lt) UNIV UNIV mini_wmr_flow"
  using non_zeros apply (auto simp add: local_flow_on_def)
  apply (unfold_locales, auto, lipschitz "ratio")
    defer
  apply vderiv
   apply expr_auto
  sorry (* Cannot easily establish Lipschitz continuity *)

lemma
  assumes "lwI = rwI" "lwI > 0" "rwI > 0" "W > 0" "radius > 0"
  shows "\<^bold>{True\<^bold>} Init ; (Cycle ; mini_evolution)\<^sup>* \<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}"
proof -
  have "\<^bold>{True\<^bold>} Init \<^bold>{LMotorT = C \<and> RMotorT = C \<and> avRW = 0 \<and> avLW = 0 \<and> t = 0\<^bold>}"
    by hoare_wp_auto
  have 
    "\<^bold>{LMotorT = C \<and> RMotorT = C \<and> avRW = v \<and> avLW = v \<and> t \<ge> (tcycle*tscale)\<^bold>} 
      Cycle
     \<^bold>{t = 0 \<and> LMotorT = 0 \<and> RMotorT = 0 \<and> avRW = v \<and> avLW = v\<^bold>}"
    by hoare_wp_auto  

  have "vwb_lens (yw+\<^sub>LavLW+\<^sub>LavRW+\<^sub>Lt)"
    by auto

  have
    "\<^bold>{True\<^bold>} 
      mini_evolution
     \<^bold>{avRW \<ge> 0\<^bold>}"
    apply (hoare_wp_auto local_flow: mini_wmr_flow_exp)
  proof -
    have "\<^bold>{0 < rwI \<and> 0 < lwI \<and> 0 < W \<and> 0 < radius \<and> avRW = 0 \<and> t = 0\<^bold>} 
      mini_evolution
     \<^bold>{avRW = t*RMotorT/rwI\<^bold>} = `0 < rwI \<and> 0 < lwI \<and> 0 < W \<and> 0 < radius \<and> $avRW = 0 \<and> $t = 0 \<longrightarrow> 
          |g_dl_ode_frame (yw+\<^sub>LavLW+\<^sub>LavRW+\<^sub>Lt) mini_evolve (True)\<^sub>e] ($avRW = $t * $RMotorT / rwI)`"
      by (simp add: refine_iff_implies)
    
    also have "...
          =
          `0 < rwI \<and> 0 < lwI \<and> 0 < W \<and> 0 < radius \<and> $avRW = 0 \<and> $t = 0 \<longrightarrow>
          |g_evol_on (yw+\<^sub>LavLW+\<^sub>LavRW+\<^sub>Lt) mini_wmr_flow (True)\<^sub>e ({0..})\<^sub>e] ($avRW = $t * $RMotorT / rwI)`
          "
      apply (subst fbox_g_dL_easiest[OF mini_wmr_flow_exp])
    apply (simp add: unrest_ssubst
    var_alpha_combine wp usubst usubst_eval 
    refine_iff_implies )
    thm fbox_g_dL_easiest mini_wmr_flow_exp
    by blast
  also have "... = True"
    apply expr_auto
    thm mini_wmr_flow_exp 
    oops




text \<open> This works, however, for a simplified version, without the difference in yw, as follows. \<close>

abbreviation 
  "mini_evolve_2 \<equiv> 
  [
   yw \<leadsto> ratio*avRW,
   avLW \<leadsto> LMotorT/lwI,
   avRW \<leadsto> RMotorT/rwI,
   t \<leadsto> 1
   ]"

abbreviation "mini_wmr_flow_2 \<tau> \<equiv> [
  yw \<leadsto> ratio*((RMotorT/rwI)*(\<tau>^2/2) + avRW*\<tau>) + yw,
  avLW \<leadsto> (LMotorT/lwI) * \<tau> + avLW,
  avRW \<leadsto> (RMotorT/rwI) * \<tau> + avRW,
  t \<leadsto> \<tau> + t]"

lemma mini_wmr_flow_2_exp [local_flow]:
  assumes "lwI > 0" "rwI > 0" "W > 0" "ratio > 0" "radius > 0"
  shows "local_flow_on (mini_evolve_2) (yw+\<^sub>LavLW+\<^sub>LavRW+\<^sub>Lt) UNIV UNIV (mini_wmr_flow_2)"
  using assms apply (auto simp add: local_flow_on_def)
  apply (unfold_locales, auto, lipschitz "ratio")
    (* Following step not able to be found by Sledgehammer directly, detailed proof needed to get it. *)
  using mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le norm_Pair2 norm_eq_zero right_diff_distrib' norm_mult real_norm_def
    apply (smt (verit) mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le)
   apply vderiv
  by expr_auto



proof (unfold_locales, auto, lipschitz "ratio")
  fix a aa ab b t ta ac ad ae ba af ag ah bb::real
  assume assms:"0 < lwI"
       "0 < rwI"
       "0 < W"
       "0 < ratio"
       "dist t ta \<le> ratio"
       "dist (a, aa, ab, b) (ac, ad, ae, ba) \<le> ratio"
       "dist (a, aa, ab, b) (af, ag, ah, bb) \<le> ratio"
  show "\<parallel>(ratio * ae - ratio * ad - (ratio * ah - ratio * ag), 0, 0, 0)\<parallel>
       \<le> ratio * \<parallel>(ac - af, ad - ag, ae - ah, ba - bb)\<parallel>"
    sorry
next
  show "?thesis"
  
  

  using mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le norm_Pair2 norm_eq_zero right_diff_distrib' norm_mult real_norm_def
    apply (smt (verit) mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le)

lemma "\<parallel>(a - af, aa - ag, ab - ah, b - bb)\<parallel> \<le> radius \<Longrightarrow> 0 \<le> (2 * ad - 2 * ag) * (ae - ah)"
  unfolding norm_Pair 
  apply auto
  oops

lemma mini_wmr_flow_exp [local_flow]:
  assumes "lwI > 0" "rwI > 0" "W > 0" "radius > 0"
  shows "local_flow_on (miniEvolve) (yw+\<^sub>LavLW+\<^sub>LavRW+\<^sub>Lt) UNIV UNIV (mini_wmr_flow)"
  (*apply local_flow_auto*)
  using assms apply (auto simp add: local_flow_on_def)
  apply (unfold_locales, auto, lipschitz "radius")
  (* Following step not able to be found by Sledgehammer *)
  using mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le norm_Pair2 norm_eq_zero right_diff_distrib' norm_mult real_norm_def
    apply (smt (verit) mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le)
   apply vderiv
  apply expr_simp
  done
*)
proof (unfold_locales, auto, lipschitz "radius")
  fix a aa ab b t ta af ag ah bb and ba ac ae ad::real
  assume assms:"0 < lwI" "0 < rwI" "0 < W" "0 < radius" "dist t ta \<le> radius"
          "dist (a, aa, ab, b) (ac, ad, ae, ba) \<le> radius"
          "dist (a, aa, ab, b) (af, ag, ah, bb) \<le> radius"
  show "
       \<parallel>(radius * ae - radius * ad - (radius * ah - radius * ag), 0, 0, 0)\<parallel>
       \<le> radius * \<parallel>(ac - af, ad - ag, ae - ah, ba - bb)\<parallel>"
  proof -
    have "\<parallel>(radius * ae - radius * ad - (radius * ah - radius * ag), 0, 0, 0)\<parallel> = \<parallel>radius * ((ae - ad) - (ah - ag))\<parallel>"
    proof -
      have "radius * ae - radius * ad - (radius * ah - radius * ag) = (radius * ((ae - ad) - (ah - ag)))"
        by (simp add: right_diff_distrib')
      then show ?thesis
        by (metis norm_Pair2 zero_prod_def)
    qed
    also have "... = radius * \<parallel>(ae - ah - (ad - ag))\<parallel>"
      by (smt (verit, del_insts) non_zeros(3) norm_mult real_norm_def)
    also have "... = radius * \<parallel>(ad - ag) - (ae - ah)\<parallel>"
      apply ( simp add: abs_minus_commute norm_Pair dist_norm)
      done
    have "((ad - ag) - (ae - ah))\<^sup>2 \<le> (ad - ag)\<^sup>2 + (ae - ah)\<^sup>2 "
    proof -
      have "((ad - ag) - (ae - ah))\<^sup>2 = (ad - ag)\<^sup>2 - 2*(ad-ag)*(ae-ah) + (ae - ah)\<^sup>2"
        apply auto
        by (simp add: power2_diff)
      have "(ad-ag) < 0 \<longrightarrow> (ae-ah) < 0"
        
        using assms unfolding dist_norm apply auto
        nitpick
      thm dist_norm real_abs_dist real_abs_infnorm zero_prod_def norm_Pair2 real_norm_def norm_mult norm_Pair norm_prod_def
      unfolding   norm_Pair
      apply auto
      unfolding norm_prod_def
      using non_zeros(3) apply blast
      
      using assms apply (simp add:real_norm_def) sledgehammer
      by (smt (verit) mult_le_cancel_left non_zeros(3) norm_fst_le norm_snd_le)
    then show ?thesis 
    by (metis norm_Pair2 norm_eq_zero)
    apply (lipschitz "radius")
    apply (auto simp add:norm_Pair2 norm_fst_le dist_scaleR)
    using norm_Pair2 norm_fst_le norm_snd_le zero_prod_def 
    apply (smt (verit) norm_Pair2 norm_fst_le norm_snd_le zero_prod_def)
    apply vderiv
  apply expr_auto

lemma "local_flow f9 UNIV UNIV flow9"

abbreviation "Init \<equiv> LMotorT ::= C ; RMotorT ::= C ; avLW ::= 0; avRW ::= 0 ; t ::= 0"

abbreviation "Ctrl \<equiv> LMotorT ::= 0 ; RMotorT ::= 0 ; t ::= 0"

abbreviation "Cycle \<equiv> IF t \<ge> (tcycle*tscale) THEN Ctrl ELSE skip"

abbreviation 
  "evolve2 \<equiv>
  {yw`   = avRW-avLW,
   avLW` = \<guillemotleft>W\<guillemotright>,
   avRW` = \<guillemotleft>W\<guillemotright>
  }"

lemma never_turn: 
  
    (*and Is:"`$avRW = $avLW`"*)
  shows
  "\<^bold>{avRW = avLW \<and> yw = \<guillemotleft>X\<guillemotright>\<^bold>}
    evolve2
   \<^bold>{avRW = avLW \<and> yw = \<guillemotleft>X\<guillemotright>\<^bold>}"
  by (dInduct_mega)

lemma never_turn'': 
  
    (*and Is:"`$avRW = $avLW`"*)
  shows
  "\<^bold>{yw = \<guillemotleft>X\<guillemotright> \<and> avRW = avLW\<^bold>}
    evolve2
   \<^bold>{yw = \<guillemotleft>X\<guillemotright> \<and> avRW = avLW\<^bold>}"
  apply (dInduct_mega)
  oops

text \<open> Given the same inertia and equal torque, then if angular
  velocity is equal at the beginning, then it stays constant 
  without changing yaw (heading). \<close>

lemma never_turn': 
  "\<^bold>{\<guillemotleft>lwI\<guillemotright> = \<guillemotleft>rwI\<guillemotright> \<and> LMotorT = RMotorT \<and> avRW = avLW \<and> yw = \<guillemotleft>Y\<guillemotright>\<^bold>}
    evolve
   \<^bold>{\<guillemotleft>lwI\<guillemotright> = \<guillemotleft>rwI\<guillemotright> \<and> LMotorT = RMotorT \<and> avRW = avLW \<and> yw = \<guillemotleft>Y\<guillemotright>\<^bold>}"
  by (dInduct_mega) (* Interesting: order of conjunctions matters, a lot! *)

lemma same_T: 
  "\<^bold>{True\<^bold>}
    LMotorT ::= Y ; RMotorT ::= Y
   \<^bold>{LMotorT = RMotorT\<^bold>}"
  by (hoare_wp_simp)

lemma same_AV:
  assumes "lwI = rwI"
  shows
  "\<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}
   evolve
   \<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}"
  using assms by dInduct_mega

lemma same_AV_after:
  "\<^bold>{True\<^bold>}
   avRW ::= X; avLW ::= X
   \<^bold>{avRW = avLW\<^bold>}"
  by hoare_wp_auto

lemma seq_hoare_rule:
  assumes "\<^bold>{P\<^bold>} P1 \<^bold>{Q\<^bold>}" "\<^bold>{Q\<^bold>} P2 \<^bold>{R\<^bold>}"
  shows "\<^bold>{P\<^bold>} P1 ; P2 \<^bold>{Q \<and> R\<^bold>}"
  using assms apply hoare_wp_auto
  by (metis fbox_def)+

lemma same_evolve:
  assumes "lwI = rwI"
  shows "\<^bold>{True\<^bold>} LMotorT ::= Y ; RMotorT ::= Y ; avRW ::= X; avLW ::= X ; evolve \<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}"
proof -
  have "\<^bold>{True\<^bold>} LMotorT ::= Y ; RMotorT ::= Y ; avRW ::= X; avLW ::= X \<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}"
    by hoare_wp_auto
  then show ?thesis 
    using assms same_AV
    by (meson hoare_kcomp)
qed

lemma
  assumes "lwI = rwI"
  shows "\<^bold>{True\<^bold>} Init ; (Cycle ; evolve)\<^sup>* \<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}"
proof -
  have "\<^bold>{True\<^bold>} Init \<^bold>{LMotorT = C \<and> RMotorT = C \<and> avRW = 0 \<and> avLW = 0 \<and> t = 0\<^bold>}"
    by hoare_wp_auto
  have 
    "\<^bold>{LMotorT = C \<and> RMotorT = C \<and> avRW = v \<and> avLW = v \<and> t \<ge> (tcycle*tscale)\<^bold>} 
      Cycle
     \<^bold>{t = 0 \<and> LMotorT = 0 \<and> RMotorT = 0 \<and> avRW = v \<and> avLW = v\<^bold>}"
    by hoare_wp_auto  
  have 
    "\<^bold>{LMotorT = C \<and> RMotorT = C \<and> avRW = v \<and> avLW = v\<^bold>} 
      (Cycle ; evolve)\<^sup>*
     \<^bold>{avRW = v+tcycle*tscale*C/rwI \<and> avLW = v+tcycle*tscale*C/lwI\<^bold>}"
    apply hoare_wp_simp

(*  \<^bold>{t \<ge> (tcycle*tscale) \<longrightarrow> LMotorT = 0 \<and> RMotorT = 0 \<and> avRW = 0 \<and> avLW = 0\<^bold>}" *)
  
lemma never_turn'': 
  "\<^bold>{yw = Y\<^bold>}
    LMotorT ::= C ; RMotorT ::= C ; evolve
   \<^bold>{yw = Y\<^bold>}"
  apply (dInduct)
  apply expr_auto

  thm dInduct_hoare_diff_inv_on
abbreviation 
  "simple \<equiv> 
  {
   mx` = 1,
   t` = 1
  }"




lemma evolve_never_turn: 
  shows
  "\<^bold>{avRW = avLW \<and> yw = \<guillemotleft>X\<guillemotright>\<^bold>}
    evolve
   \<^bold>{avRW = avLW \<and> yw = \<guillemotleft>X\<guillemotright>\<^bold>}"
  apply (dInduct_mega)
  oops
(*  apply (subst dInduct_hoare_diff_inv_on fbox_diff_inv_on)
  apply (rule_tac lderiv_rules)
  apply (simp add: framed_derivs ldifferentiable closure usubst unrest_ssubst unrest usubst_eval)+

  apply (dInduct)
  
  using assms apply auto
  sledgehammer
  apply (simp add: taut_def)
  apply (subst dInduct_hoare_diff_inv_on fbox_diff_inv_on)
  apply (rule_tac lderiv_rules)
  apply (simp add: framed_derivs ldifferentiable closure usubst unrest_ssubst unrest usubst_eval)+
  apply (expr_simp)
  apply (auto simp add: field_simps)
  apply (rule_tac diff_cut_on_split')*)



abbreviation (input) "exp_f \<equiv> [mx \<leadsto> 1, t \<leadsto> 1]" (* x>0 -> [{x'=-x}](x>0) *)
abbreviation (input) "exp_flow \<tau> \<equiv> [mx \<leadsto> 1*\<tau> + mx, t \<leadsto> \<tau> + t]"


term exp_f 
term exp_flow



lemma local_flow_exp_flow [local_flow]: "local_flow_on exp_f (mx+\<^sub>Lt) UNIV UNIV (exp_flow)"
  apply (auto simp add: local_flow_on_def)?
  apply (unfold_locales, auto)
    apply (lipschitz "1")
   apply (vderiv)
  apply expr_auto
  by (local_flow_auto)

thm fbox_solve
find_local_flow "simple"

lemma passes_d: 
  "\<^bold>{mx = 0 \<and> t = 0\<^bold>}
    simple
   \<^bold>{t > 0 \<longrightarrow> mx > 0\<^bold>}"
  
  by (hoare_wp_simp local_flow: local_flow_exp_flow)

(* How do we prove this without explicit solutions? *)

end


end