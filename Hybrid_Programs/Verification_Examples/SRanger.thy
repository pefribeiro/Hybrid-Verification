theory SRanger

imports 
  "Hybrid-Verification.Hybrid_Verification"
  "Z_Toolkit.Trace_Algebra"
begin

lit_vars

chantype ch_buffer =
  inp :: unit

term inp_C


datatype DIMENSION = OneD | TwoD | ThreeD

dataspace wmr = 
  constants
    \<comment> \<open> Robot d-model \<close>
    C      :: real
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
    non_zeros: "lwI > 0" "rwI > 0"
    "radius > 0" "W > 0" "L > 0" "lwI = rwI"
  variables
    (*trace :: "'t::trace"
    wait :: "bool"*)
    \<comment> \<open> Timer \<close>
    timer :: "real"
    \<comment> \<open> P-model: torques \<close>
    LMotorT :: real
    \<comment> \<open> P-model: Left Hinge / Motor \<close>
    LHinge_tau         :: real \<comment> \<open> Hinge torque? \<close>
    LHinge_pV          :: "real^6"
    LHinge_pA          :: "real^6"
    LHinge_F           :: "real^6"
    LHinge_fV          :: "real^6"
    LHinge_fA          :: "real^6"
    LHinge_LMotor_T    :: real \<comment> \<open> Motor torque output \<close>
    LHinge_theta       :: real \<comment> \<open> Hinge angle \<close>
    LHinge_v           :: real \<comment> \<open> Hinge velocity? \<close>
    LHinge_a           :: real \<comment> \<open> Hinge acceleration? \<close>
    LHinge_LMotor_das  :: real \<comment> \<open> Desired angular speed \<close>
    LHinge_LMotor_Tm   :: real \<comment> \<open> Motor torque \<close>
    LHinge_LMotor_Vemf :: real \<comment> \<open> Back electromotive force \<close>
    LHinge_LMotor_Tf   :: real \<comment> \<open> Torque due to friction \<close>
    LHinge_LMotor_V    :: real \<comment> \<open> Voltage supplied to motor \<close>
    LHinge_LMotor_i    :: real \<comment> \<open> Current \<close>
    LHinge_LMotor_theta:: real \<comment> \<open> Angular position \<close>
    LHinge_LMotor_av   :: real \<comment> \<open> Angular speed \<close>
    LHinge_LMotor_e    :: real \<comment> \<open> Angular speed error \<close>
    \<comment> \<open> P-model: Right Hinge / Motor \<close>
    RHinge_tau         :: real \<comment> \<open> Hinge torque? \<close>
    RHinge_pV          :: "real^6"
    RHinge_pA          :: "real^6"
    RHinge_F           :: "real^6"
    RHinge_fV          :: "real^6"
    RHinge_fA          :: "real^6"
    RHinge_RMotor_T    :: real \<comment> \<open> Motor torque output \<close>
    RHinge_theta       :: real \<comment> \<open> Hinge angle \<close>
    RHinge_v           :: real \<comment> \<open> Hinge velocity? \<close>
    RHinge_a           :: real \<comment> \<open> Hinge acceleration? \<close>
    RHinge_RMotor_das  :: real \<comment> \<open> Desired angular speed \<close>
    RHinge_RMotor_Tm   :: real \<comment> \<open> Motor torque \<close>
    RHinge_RMotor_Vemf :: real \<comment> \<open> Back electromotive force \<close>
    RHinge_RMotor_Tf   :: real \<comment> \<open> Torque due to friction \<close>
    RHinge_RMotor_V    :: real \<comment> \<open> Voltage supplied to motor \<close>
    RHinge_RMotor_i    :: real \<comment> \<open> Current \<close>
    RHinge_RMotor_theta:: real \<comment> \<open> Angular position \<close>
    RHinge_RMotor_av   :: real \<comment> \<open> Angular speed \<close>
    RHinge_RMotor_e    :: real \<comment> \<open> Angular speed error \<close>
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

datatype Pitch = FinitePitch real | InfinitePitch

abbreviation "LHinge_AXIS \<equiv> \<^bold>[[0,1,0]\<^bold>]"

(* const S: vector(real,6) = ScrewAxis(AXIS,Pitch::Finite(0)) *)
definition ScrewAxis :: "real vec[3] \<Rightarrow> Pitch \<Rightarrow> real vec[6]" where
  "ScrewAxis AXIS PITCH = undefined"

abbreviation "LHinge_S \<equiv> ScrewAxis LHinge_AXIS (FinitePitch 0)"

abbreviation "LHinge_A \<equiv> transpose ((Adjoint (matrix_inv (AbsTransform child))) ** (transpose (ScrewAxis AXIS (FinitePitch 0))))"

(* const A: vector(real,6) = Adjoint(inverse(AbsTransform(child)))*S *)
definition A :: "real vec[3] \<Rightarrow> LINK \<Rightarrow> real vec[6]" where
  "A AXIS child = transpose ((Adjoint (matrix_inv (AbsTransform child))) ** (transpose (ScrewAxis AXIS (FinitePitch 0))))"

(* T(theta) = exp(TwistToSe3(A)*(-theta))*Transform(child,parent) *)
definition T :: "LINK \<Rightarrow> LINK \<Rightarrow> real vec[3] \<Rightarrow> real \<Rightarrow> real mat[4,4]" where
  "T parent child AXIS theta =
    (mat_exp (-theta *\<^sub>R (TwistToSE3 (A AXIS child)))) ** (Transform child parent)"

(* const AdT: real -> matrix(real,6,6) = lambda theta: real @ Adjoint(T(theta)) *)
definition AdT :: "LINK \<Rightarrow> LINK \<Rightarrow> real vec[3] \<Rightarrow> real \<Rightarrow> real mat[6,6]" where
  "AdT parent child AXIS theta = Adjoint (T parent child AXIS theta)"

abbreviation "LHinge_AdT \<equiv> \<lambda>\<theta>::real. Adjoint(1)"

term "cos"

abbreviation 
  "evolve \<equiv> 
  {yw` = (\<guillemotleft>radius\<guillemotright>/W*avRW)-(\<guillemotleft>radius\<guillemotright>/W*avLW),
   mx` = (\<guillemotleft>radius\<guillemotright>/2 * cos(yw) * avLW)+(\<guillemotleft>radius\<guillemotright>/2 * cos(yw) * avRW),
   my` = (\<guillemotleft>radius\<guillemotright>/2 * sin(yw) * avLW)+(\<guillemotleft>radius\<guillemotright>/2 * sin(yw) * avRW),
   avLW` = LHinge_LMotor_T/\<guillemotleft>lwI\<guillemotright>,
   avRW` = RHinge_RMotor_T/\<guillemotleft>rwI\<guillemotright>,
   timer` = 1 
   | 
     LHinge_fV = LHinge_AdT(LHinge_theta) \<and>
      px = mx \<and>
     py = my+L/4 \<and> 
     yw = robotPose$5 \<and> 
     px = robotPose$0 \<and> 
     py = robotPose$1 \<and> 
     robotPose$2 = 0 \<and> 
     robotPose$3 = 0 \<and> 
     robotPose$4 = 0
  }"

abbreviation "Init \<equiv> LMotorT ::= 0 ; RMotorT ::= 0 ; avLW ::= 0; avRW ::= 0"

abbreviation "Ctrl \<equiv> LMotorT ::= C ; RMotorT ::= C"

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
  shows "\<^bold>{True\<^bold>} Init ; (Ctrl ; Cycle)\<^sup>* \<^bold>{LMotorT = RMotorT \<and> avRW = avLW\<^bold>}"
proof -
  have "\<^bold>{True\<^bold>} Init \<^bold>{LMotorT = 0 \<and> RMotorT = 0 \<and> avRW = 0 \<and> avLW = 0\<^bold>}"
    by hoare_wp_auto
  then have "

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

named_theorems local_flow

lemma local_flow_exp_flow [local_flow]: "local_flow_on exp_f (mx+\<^sub>Lt) UNIV UNIV (exp_flow)"
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