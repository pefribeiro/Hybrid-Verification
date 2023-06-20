theory WMR1

imports 
  "Hybrid-Verification.Hybrid_Verification"
  "Hoare_Help"
  "RoboSim"
begin

lit_vars

section \<open> Dataspace definition. \<close>

text \<open> Version of the model where we do not consider torque. \<close>

datatype STATE = 
  Initial | SMoving | DMoving | Waiting | STurning | DTurning | 
  DMovingJunction | DTurningJunction

dataspace wmr_state = robosim +
  constants
    \<comment> \<open> Robot d-model \<close>
    LV     :: real
    AV     :: real
    \<comment> \<open> Robot p-model \<close>
    RADIUS :: real
    mass   :: real
    WIDTH  :: real
    LENGTH :: real
  assumes
    non_zeros: "RADIUS > 0" "WIDTH > 0" "LENGTH > 0"
  variables
    \<comment> \<open> State machine variables and inputs/outputs \<close>
    state     :: STATE
    obstacle  :: bool
    MBC       :: nat
    \<comment> \<open> P-model: torques and sensor input \<close>
    IRVoltage :: real
    IRDistance:: real
    \<comment> \<open> Scenario mapping \<close>
    \<comment> \<open> Scenario: robot yaw (yw) \<close>
    yw :: "real"
    \<comment> \<open> Scenario: middle point between wheels (mx,my) \<close>
    mx :: "real"
    my :: "real"
    \<comment> \<open> Scenario: wheel velocities \<close>
    avLW :: "real"
    avRW :: "real"

dataspace wmr = wmr_state +
  assumes
    eq_IRVoltage_IRDistance: "$IRVoltage = 4*exp(-0.028784*$IRDistance)"
  (* Not quite sure whether this is a good way to introduce algebraic equations. *)

dataspace wmr_no_obstacle = wmr +
  assumes
    no_obstacle: "$IRDistance > - ln(3/4)/0.028784"

context wmr
begin

lemma 
  fixes IRD :: real
  assumes "IRV = 4*exp(-0.028784*IRD)"
  shows "IRD = - ln(IRV/4)/0.028784"
  using assms by auto

lemma IRDistance_no_detect:
  fixes IRD :: real
  assumes "4*exp(-0.028784*IRD) < K"
  shows "IRD > - ln(K/4)/0.028784"
proof -
  have "exp(-0.028784*IRD) < K/4"
    using assms by auto
  then have "ln (exp(-0.028784*IRD)) < ln(K/4)"
    by (metis dual_order.strict_trans exp_gt_zero exp_less_cancel_iff exp_ln)
  then have "-0.028784*IRD < ln(K/4)"
    by auto
  then have "- IRD < ln(K/4)/0.028784"
    by auto
  then show ?thesis
    by auto
qed

lemma IRDistance_no_detect_imp:
  fixes IRD :: real
  assumes "IRD > - ln(K/4)/0.028784" "K>0"
  shows "4*exp(-0.028784*IRD) < K"
proof -
  have "-IRD < ln(K/4)/0.028784"
    using assms by linarith
  then have "-0.028784*IRD < ln(K/4)"
    by auto
  then have "exp(-0.028784*IRD) < exp(ln(K/4))"
    by auto
  then have "exp(-0.028784*IRD) < K/4"
    using assms by auto
  then show ?thesis by auto
qed
  
lemma IRDistance_no_detect_iff:
  fixes IRD :: real
  assumes"K>0"
  shows "IRD > - ln(K/4)/0.028784 \<longleftrightarrow> 4*exp(-0.028784*IRD) < K"
  using IRDistance_no_detect IRDistance_no_detect_imp assms by blast
  
abbreviation "axisLength \<equiv> WIDTH+2*(RADIUS/4+0.5)"

lemma avLW_avRW_dsl_dsr:
  assumes "RADIUS > 0" "WIDTH > 0" "lv = RADIUS*(dsl+dsr)/2" "av = RADIUS*(dsl-dsr)/axisLength"
  shows "dsl = (2*lv+av*axisLength)/(2*RADIUS)" "dsr = (2*lv-av*axisLength)/(2*RADIUS)"
proof - 
  obtain K1 K2 where K1_def:"K1 = 2*lv/RADIUS" and K2_def:"K2 = av*axisLength/RADIUS" by auto
  from assms(1,3) K1_def have K1_eq:"K1 = dsl+dsr"
    by force
  from assms(1,2,4) K2_def have K2_eq: "K2 = dsl-dsr"
    by auto

  from K1_eq have dsl_eq_diff:"dsl = K1-dsr" by auto
  then have dsr_K1_K2:"dsr = - (K2-K1)/2"
    using K2_eq by simp
  
  then have dsl_K1_K2:"dsl = (K1+K2)/2"
    using dsl_eq_diff by simp
  also have "... = ((2*lv+av*axisLength)/RADIUS)/2"
    by (simp add: K1_def K2_def add_divide_distrib)
  also have "... = (2*lv+av*axisLength)/(2*RADIUS)"
    using divide_divide_eq_left' by blast
  then show "dsl = (2 * lv + av * axisLength) / (2 * RADIUS)"
    using calculation by blast

  then show "dsr = (2*lv-av*axisLength)/(2*RADIUS)"
    by (metis K2_def dsl_K1_K2 dsr_K1_K2 diff_divide_distrib divide_divide_eq_left' minus_diff_eq mult.commute real_average_minus_second)
qed

text \<open> Platform operation mappings \<close>

abbreviation "Move lv av \<equiv> avLW ::= (2*lv+av*axisLength)/(2*RADIUS) ; avRW ::= (2*lv-av*axisLength)/(2*RADIUS)"
abbreviation "Stop \<equiv> avLW ::= 0 ; avRW ::= 0"

(*abbreviation "exec P \<equiv> 
  IF startexec \<and> \<not> endexec THEN endexec ::= True ; startexec ::= False ELSE
  IF startexec \<and> endexec THEN endexec ::= False ; P ELSE skip"*)

abbreviation "exec P \<equiv> 
  IF executing THEN MBC ::= MBC + Cycle ; executing ::= False ELSE (executing ::= True ; P)"

text \<open> The state machine is defined below in a style that lends itself to being executed N 
       times till it reaches an exec. This helps with writing of the state machine. \<close>

definition[simp]: "SimSMovement \<equiv> 
  IF state = Initial THEN MBC ::= 0 ; state ::= SMoving ELSE
  IF state = SMoving THEN Move LV 0 ; state ::= DMoving ELSE
  IF state = DMoving THEN exec (state ::= DMovingJunction) ELSE 
  IF state = DMovingJunction \<and> obstacle THEN exec (MBC ::= 0 ; Stop ; state ::= Waiting) ELSE
  IF state = DMovingJunction \<and> \<not>obstacle THEN state ::= DMoving ELSE
  IF state = Waiting THEN exec (state ::= STurning) ELSE
  IF state = STurning THEN Move 0 AV ; state ::= DTurning ELSE
  IF state = DTurning THEN exec (state ::= DTurningJunction) ELSE
  IF state = DTurningJunction \<and> MBC < pi/AV THEN state ::= DTurning ELSE
  IF state = DTurningJunction \<and> MBC \<ge> pi/AV THEN state ::= SMoving ELSE skip" 

text \<open> Checks that SimSMovement behaves as expected. \<close>

lemma simS1: "\<^bold>{state = Initial \<and> executing\<^bold>} SimSMovement \<^bold>{state = SMoving \<and> executing\<^bold>}"
  by (hoare_wp_simp)

lemma simS1': "\<^bold>{state = Initial \<and> executing\<^bold>} SimSMovement ; SimSMovement \<^bold>{state = DMoving \<and> executing\<^bold>}"
  by (hoare_wp_simp)

lemma simS1'': "\<^bold>{state = DMoving \<and> executing\<^bold>} SimSMovement \<^bold>{state = DMoving \<and> \<not>executing\<^bold>}"
  by (hoare_wp_auto)

lemma simS1''': "\<^bold>{state = Initial \<and> executing\<^bold>} SimSMovement ; SimSMovement ; SimSMovement \<^bold>{state = DMoving \<and> \<not> executing\<^bold>}"
  by (hoare_wp_auto)

(*lemma simS2: "\<^bold>{state = DMoving \<and> \<not> startexec \<and> endexec\<^bold>} SimSMovement \<^bold>{state = DMoving \<and> \<not> startexec \<and> endexec\<^bold>}"
  by hoare_wp_auto

lemma simS3: "\<^bold>{state = DMoving \<and> \<not> startexec \<and> endexec\<^bold>} SimSMovement\<^sup>* \<^bold>{state = DMoving \<and> \<not> startexec \<and> endexec\<^bold>}"
  using hoare_kstar_inv simS2 by blast*)

lemma SimSMovement_DMoving_no_exe_obstacle_spec:
  "\<^bold>{state = DMoving \<and> \<not> executing \<and> \<not> obstacle\<^bold>}
   SimSMovement
   \<^bold>{state = DMovingJunction \<and> executing\<^bold>}"
  by hoare_wp_auto

lemma
  "\<^bold>{state = DMoving \<and> \<not> executing \<and> \<not> obstacle\<^bold>}
   SimSMovement ; SimSMovement ; SimSMovement
   \<^bold>{state = DMoving \<and> \<not> executing \<and> \<not> obstacle\<^bold>}"
   by hoare_wp_auto

lemma SimSMovement_obs_executing:
  "\<^bold>{\<not> obstacle \<and> state \<notin> {Initial,SMoving,DMovingJunction,Waiting,STurning,DTurning,DTurningJunction} \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>} 
    SimSMovement
   \<^bold>{\<not> obstacle \<and> state \<notin> {Initial,SMoving,DMovingJunction,Waiting,STurning,DTurning,DTurningJunction} \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS\<^bold>}"
  by hoare_wp_auto

lemma SimSMovement_obs_executing':
  "\<^bold>{\<not> obstacle \<and> state = DMovingJunction \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>} 
    SimSMovement
   \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>}"
  by hoare_wp_auto

lemma SimSMovement_DMoving_IF_executing:
  "\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> \<not> executing\<^bold>} 
    SimSMovement ; IF executing THEN SimSMovement ELSE skip
   \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>}"
  by hoare_wp_auto

lemma SimSMovement_DMoving_executing_need:
  "\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>} 
    SimSMovement
   \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> \<not> executing\<^bold>}"
  by hoare_wp_auto

lemma SimSMovement_obs_executing_need:
  "\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> \<not> executing\<^bold>} 
    DO SimSMovement WHILE executing
   \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> \<not> executing\<^bold>}"
proof -
  have decomp:
      "SimSMovement ; (WHILE executing DO SimSMovement) 
       =
       SimSMovement ; IF executing THEN SimSMovement ELSE skip ; (WHILE executing DO SimSMovement)
      "
      using WHILE_unroll_IF SimSMovement_DMoving_IF_executing
      by (metis kcomp_assoc)

    have a:"\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> \<not> executing\<^bold>} 
          SimSMovement ; IF executing THEN SimSMovement ELSE skip
          \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>}"
      by hoare_wp_auto

    have "\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>} 
          SimSMovement 
        \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS\<^bold>}"
      by hoare_wp_auto
    then have "\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS\<^bold>}
          (WHILE executing DO SimSMovement) 
          \<^bold>{\<not> executing \<and> \<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS\<^bold>}"
      by (simp add: hoare_while)
    then have b:"\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>}
          (WHILE executing DO SimSMovement) 
          \<^bold>{\<not> executing \<and> \<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS\<^bold>}"
      using SEXP_def predicate1D by auto

    from a b show ?thesis 
      by (smt (verit, ccfv_threshold) SEXP_def decomp fbox_def hoare_kcomp le_fun_def)
  (* This is not an invariant of WHILE _ DO _, but of DO _ WHILE _.
     Proving it relies on being able to unroll the WHILE. *)
  qed

lemma SimSMovement_obs_not_executing_from_DMoving:
  "\<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> \<not> executing\<^bold>} 
    SimSMovement
   \<^bold>{\<not> obstacle \<and> state \<noteq> STurning \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS \<and> executing\<^bold>}"
  by hoare_wp_auto

lemma simS4: "\<^bold>{True\<^bold>} (timer ::= y) \<^bold>{timer = y\<^bold>}"
  by hoare_wp_auto

text \<open> Therefore, we could have the following software controller. \<close>

definition[simp]: "Init \<equiv> executing ::= True ; obstacle ::= False ; state ::= Initial"
definition[simp]: "SendToSoftware \<equiv> IF IRVoltage \<ge> 3.0 THEN obstacle ::= True ELSE obstacle ::= False"
definition[simp]: "Ctrl \<equiv> SendToSoftware ; DO SimSMovement WHILE executing ; timer ::= 0"

lemma SendToSoftware_spec:
  "\<^bold>{IRVoltage < 3\<^bold>} SendToSoftware \<^bold>{ \<not> obstacle \<^bold>}"
  by (hoare_wp_auto)

lemma Ctrl_DMoving_inv:
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
   Ctrl
   \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
  unfolding Ctrl_def
  apply (rule hoare_kcomp_inv_rhs)
   apply (rule hoare_kcomp[where R="(\<not> obstacle \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing )\<^sub>e"])
    apply (hoare_wp_simp, simp del:SendToSoftware_def SimSMovement_def)
  using SimSMovement_obs_executing_need apply metis 
  by hoare_wp_simp

lemma Ctrl_IF:
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
   (IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip)
   \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
proof -
  have 
    "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
     Ctrl
     \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
    using Ctrl_DMoving_inv by blast
  then have 
    "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
     Ctrl
     \<^bold>{state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
    by (simp add: hoare_conj_pos)
  then have 
    "\<^bold>{state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> IRVoltage < 3\<^bold>}
     Ctrl
     \<^bold>{state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
    by auto
  then have 
    "\<^bold>{(state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing) \<and> IRVoltage < 3\<^bold>}
     Ctrl
     \<^bold>{(state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing) \<and> IRVoltage < 3\<^bold>}"
    apply (rule_tac nmods_frame_law')
    apply (simp)
     apply nmods_auto
    by presburger
  then have 
    "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
     Ctrl
     \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
    by (smt (verit) SEXP_def fbox_inv predicate1I)
  then have
    "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
     (IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip)
     \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
    apply (rule hoare_if_then_else')
    by (rule hoare_skip)
  then show ?thesis .
  (* Not sure whether this is sufficiently strong as an invariant *)
qed

lemma Ctrl_IF':
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   (IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip)
   \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
proof -
  have
  "\<^bold>{(IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing) \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   (IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip)
   \<^bold>{(IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing) \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule nmods_frame_law)
   apply nmods_auto
    using Ctrl_IF by blast
  then show ?thesis
    by presburger
qed

lemma SimSMovement_Initial_to_DMoving:
  "\<^bold>{executing \<and> state = Initial\<^bold>} 
   DO SimSMovement WHILE executing
   \<^bold>{\<not> executing \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS\<^bold>}"
  apply (rule hoare_kcomp[where R="(executing \<and> state = SMoving)\<^sup>e"], hoare_wp_simp)
  apply (rule hoare_while_unroll_kcomp[where Q="(state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> executing)\<^sup>e"])
   apply (hoare_wp_simp)
  apply (rule hoare_while_unroll_kcomp[where Q="(state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS)\<^sup>e"])
   apply (hoare_wp_simp)
  apply (rule hoare_while)
  by (hoare_wp_simp)

lemma Init_Ctrl:
  "\<^bold>{True\<^bold>}
   Init ; Ctrl
   \<^bold>{state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
  apply (rule hoare_kcomp[where R="(executing \<and> state = Initial)\<^sup>e"])
   apply hoare_wp_simp
  (*using IRDistance_no_detect_iff eq_IRVoltage_IRDistance no_obstacle apply simp*)
  unfolding Ctrl_def
  apply (rule hoare_kcomp[where R="(\<not> executing \<and> state = DMoving \<and> avLW = LV / RADIUS \<and> avRW = LV / RADIUS)\<^sup>e"])
  defer
   apply hoare_wp_simp
  apply (rule hoare_kcomp[where R="(executing \<and> state = Initial)\<^sup>e"])
  apply hoare_wp_simp
  using SimSMovement_Initial_to_DMoving by blast

section \<open> Platform and scenario modelling \<close>

subsection \<open> Version 0: no torque, assumes instantaneous change in velocity and no obstacles. \<close>

abbreviation 
  "PSEvolution \<equiv> 
  {yw` = (RADIUS/axisLength * avRW)-(RADIUS/axisLength * avLW),
   mx` = (RADIUS/2 * cos(yw) * avLW)+(RADIUS/2 * cos(yw) * avRW),
   my` = (RADIUS/2 * sin(yw) * avLW)+(RADIUS/2 * sin(yw) * avRW),
   timer` = 1,
   t` = 1 | timer \<le> TimeScale*Cycle
  }"

abbreviation (input) "startup \<epsilon> a \<sigma> B \<equiv> g_dl_ode_frame a \<sigma> (@B \<and> t < \<epsilon>)\<^sub>e"

term "startup 0.1 (yw +\<^sub>L t) [yw \<leadsto> 1, t \<leadsto> 1] (True)\<^sup>e"

term g_dl_ode_frame


term "g_dl_ode_frame (yw +\<^sub>L t) [yw \<leadsto> 1, t \<leadsto> 1] (t \<le> \<epsilon>)\<^sub>e"

ML \<open> @{term "{yw` = 1, t` = 1}"}\<close>

abbreviation "System0 \<equiv> Init ; Ctrl ; ((IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip) ; PSEvolution)\<^sup>*"

text \<open> In the first case, we show that if no obstacles => only linear behaviour relevant. \<close>

lemma PSE_no_yaw_change: "\<^bold>{avRW = avLW \<and> yw = yw\<^sub>0\<^bold>} PSEvolution \<^bold>{avRW = avLW \<and> yw = yw\<^sub>0\<^bold>}"
  by (dInduct_mega)

lemma PSE_linear_motion:
  "\<^bold>{avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
    PSEvolution
   \<^bold>{avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (dInduct_mega)
  using non_zeros apply blast
  apply (dInduct_mega)
  using non_zeros by blast

text \<open> Below the angular version. Note that AV is clockwise, ie. a positive velocity spins clockwise,
       whereas yaw is measured anti-clockwise, so a positive velocity decreases the angle. \<close>

lemma PSE_angular_motion:
  "\<^bold>{avLW = AV*axisLength/(2*RADIUS) \<and> avRW = -AV*axisLength/(2*RADIUS) \<and> yw = yw\<^sub>0 - timer*AV \<and> mx = mx\<^sub>i \<and> my = my\<^sub>i\<^bold>}
    PSEvolution
   \<^bold>{avLW = AV*axisLength/(2*RADIUS) \<and> avRW = -AV*axisLength/(2*RADIUS) \<and> yw = yw\<^sub>0 - timer*AV \<and> mx = mx\<^sub>i \<and> my = my\<^sub>i\<^bold>}"
  apply (dInduct_mega)
  using non_zeros apply force+
  by (dInduct_mega)

end

context wmr_no_obstacle
begin

text \<open> What we really want to prove: overall, system moves linearly. \<close>

lemma
  "\<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + timer*LV * cos(yw) \<and> my = my\<^sub>i + timer*LV * sin(yw)\<^bold>}
    System0
   \<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + timer*LV * cos(yw) \<and> my = my\<^sub>i + timer*LV * sin(yw)\<^bold>}"
  oops



(* What I really need to show *)

(* Take the following two *)


thm hoare_kcomp_inv_rhs
thm hoare_kcomp


(* Q: Is there a better way to define a constant that has IRVoltage, IRDistance, etc? *)

(*
lemma SendToSoftware_nmods_IRVoltage [nmods]:
  "SendToSoftware nmods {IRVoltage,avLW,avRW,mx,yx,yw,t}"
  unfolding SendToSoftware_def
  by nmods_auto

lemma SimSMovement_nmods_IRVoltage [nmods]: 
  "SimSMovement nmods {IRVoltage,mx,yx,yw,t}"
  unfolding SimSMovement_def 
  by nmods_auto

lemma Ctrl_nmods [nmods]: 
  "Ctrl nmods {IRVoltage,mx,yx,yw,t}"
  unfolding Ctrl_def by nmods_auto

lemma IF_Ctrl_Skip:
  "(IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip) nmods {IRVoltage,mx,yx,yw,t}"
  by nmods_auto
*)

lemma PSEvolution_nmods:
  "PSEvolution nmods {state}"
  by (auto intro!:closure, subst_eval)

lemma PSE_linear_motion':
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
    PSEvolution
   \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (dInduct_mega)
   apply (rule nmods_invariant) 
   defer
   apply (dInduct_mega)
   apply (rule nmods_invariant) 
    defer
   apply (dInduct_mega)
  using non_zeros apply blast
   apply (dInduct_mega)
  using non_zeros apply blast
  by (auto intro!:closure, subst_eval, subst_eval)

lemma Ctrl_IF_PSEvolution:
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   (IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip) ; PSEvolution
   \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  using Ctrl_IF' PSE_linear_motion' hoare_kcomp
  by blast

lemma Ctrl_IF_PSEvolution_iter:
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   ((IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip) ; PSEvolution)\<^sup>*
   \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  using Ctrl_IF_PSEvolution hoare_kstar_inv by blast

lemma Ctrl_IF_PSEvolution_iter':
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   ((IF timer \<ge> TimeScale*Cycle THEN Ctrl ELSE skip) ; PSEvolution)\<^sup>*
   \<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule hoare_weaken_post[where Q="(IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing)\<^sup>e"])
  using Ctrl_IF_PSEvolution_iter 
  by simp

lemma Init_yw_mx_my_Ctrl:
  "\<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   Init ; Ctrl
   \<^bold>{(state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing) 
    \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule hoare_weaken_pre_conj[where P="(True)\<^sup>e"], expr_simp)
  apply (rule nmods_frame_law[where I="(yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw))\<^sup>e"])
   apply (nmods_auto)
  using Init_Ctrl by blast

lemma Init_yw_mx_my_Ctrl_Voltage:
  "\<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
   Init ; Ctrl
   \<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing
    \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule hoare_strengthen_pos_universal)
  using IRDistance_no_detect_iff eq_IRVoltage_IRDistance no_obstacle apply simp
  using Init_yw_mx_my_Ctrl
  by presburger

text \<open> Main property \<close>

theorem System0_behaviour:
  "\<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
    System0
   \<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule hoare_kcomp[
        where R="(IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing
    \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw))\<^sup>e"])
  using Init_yw_mx_my_Ctrl_Voltage apply blast
  using Ctrl_IF_PSEvolution_iter' by blast    

(* Note below can only cope if have the additional conjunct in the 
   postcondition. Not ideal. *)

theorem System0_behaviour_tpd:
  "\<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
    System0
   \<^bold>{state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  unfolding Init_def
  apply (hoare_cycle)
    apply (metis IRDistance_no_detect_iff eq_IRVoltage_IRDistance linorder_not_less no_obstacle zero_less_numeral)
  using non_zeros by blast+

theorem System0_behaviour_full_tpd:
  "\<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}
    System0
   \<^bold>{yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw)\<^bold>}"
  apply (rule hoare_stengthen_post[
        where Q="(state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing
    \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw))\<^sup>e"], simp)
  unfolding Init_def
  apply (hoare_cycle)
    apply (metis IRDistance_no_detect_iff eq_IRVoltage_IRDistance linorder_not_less no_obstacle zero_less_numeral)
  using non_zeros by blast+

lemma "\<^bold>{P\<^bold>} SendToSoftware \<^bold>{P \<and> \<not>obstacle\<^bold>}"
  apply (hoare_wp_auto)
  using no_obstacle IRDistance_no_detect_iff eq_IRVoltage_IRDistance
  by (metis linorder_not_less zero_less_numeral)

lemma SimSMovement_maintain_linear_motion: 
  "\<^bold>{\<not> obstacle \<and> state \<noteq> STurning \<and> avLW = avRW\<^bold>}
   SimSMovement
   \<^bold>{\<not> obstacle \<and> avLW = avRW\<^bold>}"
  by (hoare_wp_simp)

(*
lemma unfold_while:
  assumes "`P \<longrightarrow> X`" "\<^bold>{P\<^bold>} (\<questiondown>X? ; Y)\<^sup>* ; Z \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} Y ; (\<questiondown>X? ; Y)\<^sup>* ; Z \<^bold>{Q\<^bold>}"
  using assms 
  by (metis (mono_tags, lifting) SEXP_def fbox_def fbox_kcomp predicate1D predicate1I)
*)

subsection \<open> Version with torque, no instantaneous change in velocity. \<close>

end

text \<open> If you do have obstacles, then what should the property
       we're after look like? \<close>

text \<open> If it's a path we're talking about, then it is fairly simple,
       where (yw0,mx0,my0) is the initial configuration and 
       (ywF,mxF,myF) is the final configuration. 

       The key would be to be take a list of 'obstacles', which could
       be navigation waypoints anyway, and  \<close>

theorem 
  "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   System
   \<^bold>{ yw = yw\<^sub>f \<and> mx = mx\<^sub>f \<and> my = my\<^sub>f \<^bold>}"
  oops

end