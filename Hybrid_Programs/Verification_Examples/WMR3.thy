theory WMR3

imports 
  "Hybrid-Verification.Hybrid_Verification"
  "Hoare_Help"
  "RoboSim"
  "HOL-Library.FSet"
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
    \<comment> \<open> s-model fixed quantities \<close>
    obstacles :: "(real vec[4]) fset" (* or just one obstacle? [x,y,yaw,length] *)
  assumes
    non_zeros: "RADIUS > 0" "WIDTH > 0" "LENGTH > 0" "\<epsilon>\<^sub>s > 0" "\<epsilon>\<^sub>s < 1"
  variables
    \<comment> \<open> State machine variables and inputs/outputs \<close>
    state     :: STATE
    obstacle  :: bool
    MBC       :: nat
    \<comment> \<open> P-model: sensor input/output \<close>
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

definition boxBoundary :: "real \<Rightarrow> (real \<times> real) set" where 
"boxBoundary L = 
    {(x,y).   (x = L/2 \<and> (-L/2 \<le> y \<or> y \<le> L/2))
            \<or> (x = -L/2 \<and> (-L/2 \<le> y \<or> y \<le> L/2))
            \<or> (y = L/2 \<and> (-L/2 \<le> x \<or> x \<le> L/2))
            \<or> (y = -L/2 \<and> (-L/2 \<le> x \<or> x \<le> L/2))
    }" 

term "a::(real mat[1,1])"

lemma transpose_vec:"\<^bold>[[x,y]\<^bold>]\<^sup>T = \<^bold>[[x],[y]\<^bold>]"
  apply (simp add:matrix_eq_iff)
  apply (auto simp add:transpose_def)
  apply (case_tac i)
  by (metis One_nat_def Suc_1 Suc_leI Suc_less_eq atLeastLessThan_iff bot_nat_0.extremum_unique card_bit0 card_num1 mult_numeral_1_right nat_of_range not0_implies_Suc nth_Cons_0 nth_Cons_Suc numeral_One)

text \<open> Rotation matrix in 2D plane. \<close>

definition Rotation :: "real \<Rightarrow> (real mat[2,2])" where
"Rotation \<theta> = \<^bold>[[cos \<theta>, - sin \<theta>],[sin \<theta>, cos \<theta>]\<^bold>]" (* Is this perhaps already defined elsewhere? *)

lemma Rotation_pi_over_2:"Rotation (pi/2) = \<^bold>[[0, -1],[1, 0]\<^bold>]"
  unfolding Rotation_def
  by fastforce

lemma "(Rotation (pi/2) ** \<^bold>[[1,0]\<^bold>]\<^sup>T) = \<^bold>[[0,1]\<^bold>]\<^sup>T"
  apply (auto simp add:Rotation_pi_over_2 transpose_vec)
  apply (vector)
  apply (auto simp add:matrix_matrix_mult_def)
  apply (case_tac i, auto)
   by (smt (verit, del_insts) One_nat_def card_bit0 card_num1 exhaust_2 less_2_cases_iff mult_cancel_left1 mult_cancel_right2 mult_numeral_1_right nat_of_0 nat_of_1 nth_Cons_0 nth_Cons_Suc num1_eq1 numerals(1) sum_2)
 (* Is there a better way to calculate such simple results? *)

text \<open> Function that given a finite set of obstacle descriptions 
       (vectors with 4 components (x,y,yaw,length))
       returns the obstacle boundaries in the absolute reference frame. \<close>

definition obsBoundaries :: "(real vec[4]) fset \<Rightarrow> (real \<times> real) set" where 
"obsBoundaries obs = 
  {(x,y). \<exists>mx my yw L. \<^bold>[[mx, my, yw, L]\<^bold>] |\<in>| obs 
          \<and> \<^bold>[[x, y]\<^bold>]\<^sup>T \<in> (\<lambda>(x,y). \<^bold>[[mx, my]\<^bold>]\<^sup>T + (Rotation yw ** \<^bold>[[x,y]\<^bold>]\<^sup>T)) ` (boxBoundary L) }"

text \<open> Function that given an angle \<theta> returns the set of points in its range, where
       range is over the angle -\<theta>/2 and +\<theta>/2. \<close>

definition visRange :: "real \<Rightarrow> (real \<times> real) set" where
"visRange \<theta> = {(x,y). \<exists>k \<beta>. 0 \<le> k \<and> (- \<theta>/2) \<le> \<beta> \<and> \<beta> \<le> (\<theta>/2) \<and> \<^bold>[[x,y]\<^bold>]\<^sup>T = Rotation \<beta> ** \<^bold>[[k,0]\<^bold>]\<^sup>T}"

text \<open> Given a vector pose for the sensor, and its horizontal field of view, yields 
       the set of points in its range.  \<close>

definition senRange :: "real vec[3] \<Rightarrow> real \<Rightarrow> (real \<times> real) set" where
"senRange v \<theta> = {(x,y). \<^bold>[[x, y]\<^bold>]\<^sup>T \<in> (\<lambda>(x,y). \<^bold>[[v$0$0,v$0$1]\<^bold>]\<^sup>T + (Rotation (v$0$2) ** \<^bold>[[x,y]\<^bold>]\<^sup>T)) ` (visRange \<theta>)}"

definition vec2to3 :: "(real vec[2]) \<Rightarrow> (real vec[3])" where
"vec2to3 v = \<^bold>[[v$0$0,v$0$1,0]\<^bold>]"

definition sensorPose :: "(real vec[3]) \<Rightarrow> (real vec[3])" where
"sensorPose v = v + (vec2to3 ((Rotation (v$0$2) ** \<^bold>[[(LENGTH/2),0]\<^bold>]\<^sup>T)\<^sup>T))"

definition distances :: "real vec[3] \<Rightarrow> real \<Rightarrow> (real vec[4]) fset \<Rightarrow> real set" where
"distances v \<theta> obs = {d. \<exists>x y. (x,y) \<in> ((senRange (sensorPose v) \<theta>) \<inter> obsBoundaries obs) \<and> d = \<parallel>\<^bold>[[v$0$0,v$0$1]\<^bold>] - \<^bold>[[x,y]\<^bold>]\<parallel>}"

definition minDistance :: "real vec[3] \<Rightarrow> real \<Rightarrow> (real vec[4]) fset \<Rightarrow> real" where
"minDistance v \<theta> obs = Min(distances v \<theta> obs)"

section \<open> Platform mapping \<close>

abbreviation "axisLength \<equiv> WIDTH+2*(RADIUS/4+0.5)"

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

lemma avLW_avRW_dsl_dsr:
  assumes "RADIUS > 0" "WIDTH > 0" "lv = RADIUS*(dsl+dsr)/2" "av = RADIUS*(dsl-dsr)/axisLength"
  shows "dsl = (2*lv+av*axisLength)/(2*RADIUS)" 
        "dsr = (2*lv-av*axisLength)/(2*RADIUS)"
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

section \<open> Software \<close>

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

subsection \<open> SimSMovement behaviour  \<close>

text \<open> Checks that SimSMovement behaves as expected. \<close>

lemma simS1: "\<^bold>{state = Initial \<and> executing\<^bold>} SimSMovement \<^bold>{state = SMoving \<and> executing\<^bold>}"
  by (hoare_wp_simp)

lemma simS1': "\<^bold>{state = Initial \<and> executing\<^bold>} SimSMovement ; SimSMovement \<^bold>{state = DMoving \<and> executing\<^bold>}"
  by (hoare_wp_simp)

lemma simS1'': "\<^bold>{state = DMoving \<and> executing\<^bold>} SimSMovement \<^bold>{state = DMoving \<and> \<not>executing\<^bold>}"
  by (hoare_wp_auto)

lemma simS1''': "\<^bold>{state = Initial \<and> executing\<^bold>} SimSMovement ; SimSMovement ; SimSMovement \<^bold>{state = DMoving \<and> \<not> executing\<^bold>}"
  by (hoare_wp_auto)

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

subsection \<open> Software mapping \<close>

text \<open> Below we define how the d and p-model are mapped. \<close>

text \<open> Discrete initialisation of the system. \<close>

definition[simp]: "DInit \<equiv> wait ::= False ; executing ::= True ; state ::= Initial"
definition[simp]: "SendToSoftware \<equiv> IF IRVoltage \<ge> 3.0 THEN obstacle ::= True ELSE obstacle ::= False"
definition "Ctrl \<equiv> SendToSoftware ; DO SimSMovement WHILE executing"

lemma SendToSoftware_spec:
  "\<^bold>{IRVoltage < 3\<^bold>} SendToSoftware \<^bold>{ \<not> obstacle \<^bold>}"
  by (hoare_wp_auto)

lemma Ctrl_DMoving_inv:
  "\<^bold>{IRVoltage < 3 \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}
   Ctrl
   \<^bold>{\<not> obstacle \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing\<^bold>}"
  unfolding Ctrl_def
   apply (rule hoare_kcomp[where R="(\<not> obstacle \<and> state = DMoving \<and> avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing )\<^sup>e"])
   apply (hoare_wp_simp)
  using SimSMovement_obs_executing_need by metis 

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

lemma SimSMovement_DMoving_to_Waiting:
  "\<^bold>{executing \<and> state = Initial \<and> obstacle \<and> \<not>executing\<^bold>} 
   DO SimSMovement WHILE executing
   \<^bold>{\<not> executing \<and> state = Waiting \<and> avLW = 0 \<and> avRW = 0 \<^bold>}"
  by hoare_wp_auto

lemma SimSMovement_Waiting_to_DTurning:
  "\<^bold>{executing \<and> state = Waiting \<and> \<not>executing\<^bold>} 
   DO SimSMovement WHILE executing
   \<^bold>{\<not> executing \<and> state = DTurning \<and> avLW = LV/RADIUS \<and> avRW = -LV/RADIUS \<^bold>}"
  by hoare_wp_auto

section \<open> Scenario modelling \<close>

subsection \<open> Version 0: no torque, assumes instantaneous change in velocity. \<close>

abbreviation "PSEqs \<equiv> 
  [yw \<leadsto> (RADIUS/axisLength * avRW)-(RADIUS/axisLength * avLW),
   mx \<leadsto> (RADIUS/2 * cos(yw) * avLW)+(RADIUS/2 * cos(yw) * avRW),
   my \<leadsto> (RADIUS/2 * sin(yw) * avLW)+(RADIUS/2 * sin(yw) * avRW)]"

(* IRDistance = d(mx,my)*)

(* Evolution on variables timer and t is specified in RoboSim.thy *)

text \<open> Variables used in ODEs. \<close>

abbreviation (input) "PSEqsVars \<equiv> yw +\<^sub>L mx +\<^sub>L my"

text \<open> Initialisation of continuous variables. \<close>

abbreviation "CInit \<equiv> avLW ::= 0; avRW ::=0"

text \<open> Initialisation of both. \<close>

definition[simp]: "Init \<equiv> DInit ; CInit"
abbreviation "Step \<delta> \<equiv> EvolveUntil \<delta> PSEqsVars PSEqs"
abbreviation "System \<equiv> Init ; Step \<epsilon>\<^sub>s ; (T(Ctrl) ; Step (TimeScale*Cycle))\<^sup>+"

 (*startup \<epsilon>\<^sub>s (yw +\<^sub>L t +\<^sub>L mx +\<^sub>L my +\<^sub>L timer) PSEqs (True)\<^sup>e"*)

lemma "(timer ::= 0 ; g_dl_ode_frame timer [timer \<leadsto> 1] (timer \<le> \<epsilon>\<^sub>s)\<^sub>e) = (timer ::= 0 ; (\<Sqinter> i \<in> {v. 0 \<le> v \<and> v \<le> \<epsilon>\<^sub>s}. {timer` = 1 | timer \<le> i}))"
  apply (simp add:Nondet_choice_def fbox_def fun_eq_iff assigns_def kcomp_def expr_defs, auto)
  apply (meson non_zeros(4) order.order_iff_strict)
  by (smt (verit, ccfv_threshold) g_orbital_on_eq mem_Collect_eq subsetD subsetI)

lemma "\<^bold>{P\<^bold>} \<questiondown>\<not>P? \<^bold>{False\<^bold>}"
  by hoare_wp_auto

lemma "timer ::= 0 ; {timer` = 1 | timer \<le> \<delta>} = timer ::= 0 ; (\<Sqinter> i \<in> {v. 0 \<le> v \<and> v \<le> \<delta>}. {timer` = 1 | timer \<le> i})"
  apply (simp add:Nondet_choice_def fbox_def fun_eq_iff assigns_def kcomp_def expr_defs, auto)
  oops

lemma "\<questiondown>P? = IF P THEN skip ELSE abort"
  by (metis if_then_else_eq kcomp_skip(1) nondet_choice_abort_unit test_nondet_unit)

lemma "TimerEvo \<delta> (yw +\<^sub>L mx +\<^sub>L my) PSEqs (True)\<^sub>e nmods avLW = 0 \<and> avRW = 0 \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0"
  unfolding TimerEvo_def apply expr_auto oops

lemma 
  assumes "\<^bold>{I\<^bold>} P \<^bold>{I\<^bold>}"
  shows "P nmods I"
  by (simp add: not_modifies_def)

lemma
  assumes "P nmods I"
  shows "\<^bold>{I\<^bold>} P \<^bold>{I\<^bold>}"
  using assms nmods_invariant by blast

lemma "\<^bold>{avLW = 0 \<and> avRW = 0 \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0\<^bold>}
        TimerEvo \<delta> (yw +\<^sub>L mx +\<^sub>L my) PSEqs (True)\<^sub>e 
       \<^bold>{avLW = 0 \<and> avRW = 0 \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0\<^bold>}"
  unfolding TimerEvo_def by (dInduct_mega)

(* Actual system model *)



term "Step d"

lemma Step_not_wait:
  "\<^bold>{ \<not> wait \<^bold>} Step \<delta> \<^bold>{ \<not> wait \<longrightarrow> timer = \<delta> \<^bold>}"
  unfolding T_def EvolveUntil_def
  apply (rule hoare_if_then_else)
   apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp)
   apply ((simp only:kcomp_assoc)?, rule hoare_floyd_kcomp, simp, subst_eval)
   apply (rule hoare_kcomp[where R="($wait \<and> $timer \<le> \<delta>)\<^sup>e"])
  apply (rule hoare_weaken_pre_conj[where P="($wait)\<^sup>e"], simp)
    apply (rule TimerEvo_delta_nmods)
  unfolding TimerEvo_def apply (auto intro!:closure; subst_eval)
  by wlp_full+  

lemma "\<^bold>{ wait \<and> P \<^bold>} T(X) \<^bold>{ wait \<and> P \<^bold>}"
  unfolding T_def by (wlp_full)

lemma 
  "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw) \<and> t = t\<^sub>0 \<^bold>} 
    System
   \<^bold>{ yw = yw\<^sub>0 \<and> (\<exists>\<epsilon>\<^sub>0. 0 \<le> \<epsilon>\<^sub>0 \<and> \<epsilon>\<^sub>0 \<le> \<epsilon>\<^sub>s 
                \<and> mx = mx\<^sub>i + (t+\<epsilon>\<^sub>0)*LV * cos(yw) 
                \<and> my = my\<^sub>i + (t+\<epsilon>\<^sub>0)*LV * sin(yw)) \<^bold>}"
  oops

lemma Ctrl_t_increasing:
  "\<^bold>{t\<^sub>1 \<le> $t\<^bold>} Ctrl \<^bold>{t\<^sub>1 \<le> $t\<^bold>}"
  apply (rule nmods_invariant)
  unfolding Ctrl_def ifthenelse_def
  by (nmods_auto)

lemma "$wait \<sharp> ($avLW = 0 \<and> $avRW = 0 \<and> $yw = yw\<^sub>0 \<and> $mx = mx\<^sub>0 \<and> $my = my\<^sub>0 \<and> $executing \<and> $state = Initial)\<^sub>e"
  by unrest
  
(* In general, we are only interested in showing the second conjunct. Even then, it's unclear
   how that can it become an invariant over the ODE directly. Could it become... ?
   which we know how to prove *)

lemma Evo_at_rest:
  "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV * cos(yw) \<and> my = my\<^sub>i + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV * sin(yw) \<^bold>} 
     (T(Ctrl) ; Step (TimeScale*Cycle))\<^sup>*
   \<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV * cos(yw) \<and> my = my\<^sub>i + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV * sin(yw) \<^bold>}"
  unfolding Ctrl_def (* apply (rule cycle_loop) *)
  thm cycle_loop

(* Q: What shape of properties do we need to handle?

      1. Invariants over the overall system.
      2. Invariants that only hold after some condition is satisfied.
      3. Other properties?
*)

(* ; Ctrl ; (PSEvolution ; (IF timer \<ge> TimeScale*Cycle THEN (Ctrl ; Reset) ELSE skip))\<^sup>*" *)

(* Also need a notion that corresponds better to the interrupt? Otherwise, (Ctrl ; PSEvolution)\<^sup>+ 
   allows for Ctrl to be executed after any of the trajectories in PSEvolution.

   The original operator is Evo \<triangle> g, where g is a condition. *)

(* Q1: Should we have (Ctrl ; PSEvolution)\<^sup>* or a version with one or more finite iterations? 
       What is the consequence of this?

       Or should we simply have Ctrl ; (PSEvolution ; Ctrl)\<^sup>* ?

   Q2: Relative time in evolution: do we always need to reset a timer or is there a better
       modelling alternative?
*)

lemma "\<^bold>{ avRW = 0 \<and> avLW = 0 \<^bold>} CInit \<^bold>{ timer < \<epsilon>\<^sub>s \<and> (timer = \<epsilon>\<^sub>s \<longrightarrow> t = t\<^sub>0 + \<epsilon>\<^sub>s) \<^bold>}"
  oops

(* In general, for properties that cannot be expressed as invariants we have a problem in that we
   can't use differential induction. However, for specific cases, as in this example,
   I think we can identify modes of operation whether an invariant holds, which can be used
   to establish the overall property below. *)

lemma 
  "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i \<and> my = my\<^sub>i \<and> t = t\<^sub>0 \<^bold>} 
    System
   \<^bold>{ yw = yw\<^sub>0 \<and> (\<exists>\<epsilon>\<^sub>0. 0 \<le> \<epsilon>\<^sub>0 \<and> \<epsilon>\<^sub>0 \<le> \<epsilon>\<^sub>s 
                \<and> mx = mx\<^sub>i + (if (t-(t\<^sub>0+\<epsilon>\<^sub>0)) \<le> 0 then 0 else (t-(t\<^sub>0+\<epsilon>\<^sub>0))*LV * cos(yw)) 
                \<and> my = my\<^sub>i + (if (t-(t\<^sub>0+\<epsilon>\<^sub>0)) \<le> 0 then 0 else (t-(t\<^sub>0+\<epsilon>\<^sub>0))*LV * sin(yw))) \<^bold>}"
  oops

(* This is equivalent to the following *)

lemma "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i \<and> my = my\<^sub>i \<and> t = t\<^sub>0 \<^bold>} 
        System
       \<^bold>{ yw = yw\<^sub>0 \<and> (\<exists>\<epsilon>\<^sub>0. 0 \<le> \<epsilon>\<^sub>0 \<and> \<epsilon>\<^sub>0 \<le> \<epsilon>\<^sub>s
                    \<and> (t \<le> t\<^sub>0+\<epsilon>\<^sub>0 \<longrightarrow> mx = mx\<^sub>i) \<and> (t > t\<^sub>0+\<epsilon>\<^sub>0 \<longrightarrow> mx = mx\<^sub>i + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV*cos(yw)) 
                    \<and> (t \<le> t\<^sub>0+\<epsilon>\<^sub>0 \<longrightarrow> my = my\<^sub>i) \<and> (t > t\<^sub>0+\<epsilon>\<^sub>0 \<longrightarrow> mx = mx\<^sub>i + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV*cos(yw))) \<^bold>}"
  oops

(* More generally, if we had stated it as originally, then, if the controller
   didn't reset wheel speeds within the \<epsilon>\<^sub>s time at the beginning, we would
   expect the following to be the case.*)

lemma 
  "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i + t*LV * cos(yw) \<and> my = my\<^sub>i + t*LV * sin(yw) \<and> t = t\<^sub>0 \<^bold>} 
    System
   \<^bold>{ yw = yw\<^sub>0 \<and> (\<exists>\<epsilon>\<^sub>0. 0 \<le> \<epsilon>\<^sub>0 \<and> \<epsilon>\<^sub>0 \<le> \<epsilon>\<^sub>s 
                \<and> mx = mx\<^sub>i + (t+\<epsilon>\<^sub>0)*LV * cos(yw) 
                \<and> my = my\<^sub>i + (t+\<epsilon>\<^sub>0)*LV * sin(yw)) \<^bold>}"
  oops

(* But I think we are not strictly guaranteed the above either.. because the initial evolution
   is over [0,\<epsilon>\<^sub>s]. Is this a problem for the semantics? *)

(* Are we creating a problem, assuming it is initially static? *)

(* Idea: consider the actual property only after \<epsilon>\<^sub>s? *)

lemma "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i \<and> my = my\<^sub>i \<^bold>} 
       DInit
       \<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>i \<and> my = my\<^sub>i \<^bold>}"
  unfolding DInit_def
  by (hoare_wp_auto)
(*
lemma "\<^bold>{ \<^bold>} CInit \<^bold>{ \<^bold>}"

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
  by (dInduct_mega) *)

end

context wmr_no_obstacle
begin

text \<open> In a context where there are no obstacles. \<close>

lemma IRVoltage_below_3:"\<not> 3 \<le> $IRVoltage"
  using eq_IRVoltage_IRDistance no_obstacle 
  by (metis linorder_not_le wmr.IRDistance_no_detect_iff wmr_axioms zero_less_numeral)

text \<open> What we really want to prove: overall, system moves linearly. \<close>

lemma Evo_at_rest:
  "\<^bold>{ avLW = 0 \<and> avRW = 0 \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<and> t = t\<^sub>0 \<^bold>} 
     System
   \<^bold>{(t < t\<^sub>0 + \<epsilon>\<^sub>s \<longrightarrow> (avLW = 0 \<and> avRW = 0 \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0)) \<and>
    (t\<^sub>0 + \<epsilon>\<^sub>s \<le> t \<longrightarrow> (yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV * cos(yw) \<and> my = my\<^sub>0 + (t-(t\<^sub>0+\<epsilon>\<^sub>s))*LV * sin(yw))) \<^bold>}"
  unfolding Init_def DInit_def 
  apply (hoare_help)
  apply (rule hoare_weaken_pre_conj[where
         P="(($avLW = 0 \<and> $avRW = 0 \<and> $yw = yw\<^sub>0 \<and> $mx = mx\<^sub>0 \<and> $my = my\<^sub>0 \<and> $executing \<and> $state = Initial) \<and> $t = t\<^sub>0 \<and> \<not> $wait)\<^sup>e"], wlp_full)  
  (* Need to strengthen postcondition because of parentheses.. Is there a better way? *)
  apply (rule hoare_stengthen_post[
        where Q="
      (($t < t\<^sub>0 + \<epsilon>\<^sub>s \<longrightarrow> avLW = 0 \<and> avRW = 0 \<and> yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<and> executing \<and> state = Initial) \<and>
       (t\<^sub>0 + \<epsilon>\<^sub>s \<le> $t \<longrightarrow>
        (avLW = LV/RADIUS \<and> avRW = LV/RADIUS \<and> \<not> executing \<and> state = DMoving)
        \<and>
        (yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 + ($t - (t\<^sub>0 + \<epsilon>\<^sub>s)) * LV * cos (yw) \<and> my = my\<^sub>0 + ($t - (t\<^sub>0 + \<epsilon>\<^sub>s)) * LV * sin (yw)
        )))\<^sup>e"], simp)
  apply (insert non_zeros IRVoltage_below_3)
  apply ((rule EvolveUntil_two_post_plus, simp_all add:Ctrl_t_increasing))
  apply (hoare_help add:Ctrl_def TimerEvo_def)
  apply (rule EvolveUntil_TimerEvo, simp_all add:TimerEvo_def)
  apply (hoare_help)
  done

lemma "\<^bold>{P\<^bold>} SendToSoftware \<^bold>{P \<and> \<not>obstacle\<^bold>}"
  apply (hoare_wp_auto)
  using no_obstacle IRDistance_no_detect_iff eq_IRVoltage_IRDistance
  by (metis linorder_not_less zero_less_numeral)

lemma SimSMovement_maintain_linear_motion: 
  "\<^bold>{\<not> obstacle \<and> state \<noteq> STurning \<and> avLW = avRW\<^bold>}
   SimSMovement
   \<^bold>{\<not> obstacle \<and> avLW = avRW\<^bold>}"
  by (hoare_wp_simp)

end

context wmr
begin

text \<open> If you do have obstacles, then what should the property
       we're after look like? \<close>

text \<open> If it's a path we're talking about, then it is fairly simple,
       where (yw0,mx0,my0) is the initial configuration and 
       (ywF,mxF,myF) is the final configuration. 

       The key would be to be take a list of 'obstacles', which could
       be navigation waypoints anyway, and  \<close>

(* Turning property: if the detected voltage is higher for a certain period of time between 
                     t\<^sub>0 and t\<^sub>1, where t\<^sub>1 - t\<^sub>0 > \<epsilon>\<^sub>d, where \<epsilon>\<^sub>d needs to be at least one simulation 
                     cycle? *)

text \<open> The following property states that if by the time (\<epsilon>+c*TimeScale*Cycle) that the software
       is executing, then, if IRVoltage > 3, for at least the next cycle, that is when t is 
       between (\<epsilon>+c*TimeScale*Cycle) and (\<epsilon>+2*c*TimeScale*Cycle), the movement is angular with
       speed given by AV. \<close>


lemma Evo_turning:
  fixes c :: nat and t\<^sub>0 :: real and t\<^sub>1 :: real
    (* The choice of 'c' is contingent on satisfying the following
       assumptions. *)
  assumes 
    (* At cycle c the obstacle is detected *)
    "`t = (\<epsilon>\<^sub>s+c*TimeScale*Cycle) \<longrightarrow> (IRVoltage > 3)`" 
    (* At cycle c-1 the motion was linear (but non-zero, so that
       the system is not in state Waiting at cycle (c-1)!) *)
    "`t = (\<epsilon>\<^sub>s+(c-1)*TimeScale*Cycle) \<longrightarrow> (avLW = avRW \<and> avLW > 0)`"
    (* We cannot impose a condition, at this level, for example
       so that state = DMoving. At any 't' that the control software
       executes there will necessarily be a change of states. Similarly,
       the outputs avLW and avRW may change too.

       Also c must be non-zero, ie. not the very first cycle. *)
    "c > 1"

          (* We need to know that state = DMoving. 
             Without this assumption, When is the system in that state?

             Ans: it depends on the times at which the obstacle is detected,
                  and how long it takes to come back to that state. *)
  shows "\<^bold>{ True \<^bold>} 
          System
         \<^bold>{ (t = (\<epsilon>\<^sub>s+c*TimeScale*Cycle) \<longrightarrow> (yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0))
            \<and>
           (((\<epsilon>\<^sub>s+(c+1)*TimeScale*Cycle) \<le> t \<and> t < (\<epsilon>\<^sub>s+(c+1+PI/AV)*TimeScale*Cycle))
            \<longrightarrow> (yw = yw\<^sub>0 + (t-(\<epsilon>\<^sub>s+(c+1)*TimeScale*Cycle))*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0)) \<^bold>}"
  apply (rule hoare_stengthen_post[
        where Q="(
           (t = (\<epsilon>\<^sub>s+c*TimeScale*Cycle) \<longrightarrow> (yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<and> MBC = 0))
            \<and>
           (((\<epsilon>\<^sub>s+(c+1)*TimeScale*Cycle) \<le> t \<and> t < (\<epsilon>\<^sub>s+(c+1+PI/AV)*TimeScale*Cycle))
            \<longrightarrow> (state = DTurning \<and> MBC \<le> (PI/AV) \<and> yw = yw\<^sub>0 + (t-(\<epsilon>\<^sub>s+(c+1)*TimeScale*Cycle))*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0)))\<^sup>e"])
   apply (wlp_full)
  apply (hoare_help)
  apply (rule hoare_kcomp[where R="($executing \<and> $state = Initial \<and> $avLW = 0 \<and> $avRW = 0)\<^sup>e"])
  unfolding EvolveUntil_def T_def TimerEvo_def
   apply (hoare_help)
  apply (simp only:kcomp_assoc[symmetric] T_def[symmetric] TimerEvo_def[symmetric] EvolveUntil_def[symmetric])
  thm EvolveUntil_def
  apply (simp only:EvolveUntil_def[symmetric])
  (* Need to transfer result from P\<^sup>+ over any cycle 'c' into one about
     a particular cycle, or, range of time... where the property is 
     invariant over that time.
      
     That in turn should be possible to prove using fixed_star_def for a
     particular constant? Need a lifting from this to P\<^sup>+ *)
  term real
  term of_real
  oops

lemma kpower_T_when_not_wait:
  assumes "\<forall>t\<^sub>0. \<^bold>{ \<not>wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} T(X) \<^bold>{ \<not>wait \<longrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright> \<^bold>}"
  shows "\<^bold>{ \<not>wait \<and> t = \<guillemotleft>t\<^sub>1\<guillemotright> \<^bold>} kpower (T(X)) k \<^bold>{ \<not>wait \<longrightarrow> t = \<guillemotleft>t\<^sub>1\<guillemotright>+\<guillemotleft>c\<guillemotright>*\<guillemotleft>k\<guillemotright> \<^bold>}"
proof (induct k arbitrary:t\<^sub>1)
  case 0
  then show ?case
    by (smt (verit, best) SEXP_def fbox_kpower_0 mult_eq_0_iff of_nat_0 predicate1I)
next
  case (Suc k)
  have p:"kpower (T X) (Suc k) = (T X) ; kpower (T X) k"
    using kpower_Suc by blast
  show ?case
    apply (simp only:p)
    apply (rule hoare_kcomp[where R="(\<not> $wait \<longrightarrow> $t = t\<^sub>1 + c)\<^sup>e"])
    using assms apply blast
    apply (rule hoare_disj_preI[where a="(\<not> $wait \<longrightarrow> $t = t\<^sub>1 + c)\<^sup>e" and b="(\<not>wait)\<^sup>e" and c="(wait)\<^sup>e"])
      defer
      defer
      apply expr_auto
     defer
    using kpower_from_wait apply simp
    apply (rule hoare_pre_eq[where Q="(\<not>wait \<and> t = \<guillemotleft>t\<^sub>1\<guillemotright>+c)\<^sup>e"])
    defer
     apply expr_auto
    apply (rule hoare_post_eq[where R="(\<not>wait \<longrightarrow> t = \<guillemotleft>t\<^sub>1\<guillemotright> + c + c * real k)\<^sup>e"])
    using Suc apply blast
    apply expr_auto
    by (simp_all add: distrib_left)
  (*
  have a:"kpower (T X) (Suc k) = kpower (T X) k ; (T X)"
    using kpower_Suc' by blast
  show ?case
    apply (simp only:a)
    apply (rule hoare_kcomp[where R="(\<not> $wait \<longrightarrow> $t = t\<^sub>1 + c)\<^sup>e"])
*)
  (*
    apply (rule hoare_kcomp[where R="(\<not> $wait \<longrightarrow> $t = t\<^sub>1 + c * real k)\<^sup>e"])
    using Suc apply blast
    thm hoare_disj_preI
    apply (rule hoare_disj_preI[where a="(True)\<^sup>e" and b="(\<not> $wait \<and> $t = t\<^sub>1 + c * real k)\<^sup>e" and c="($wait)\<^sup>e"], simp)
      defer
      apply (smt (verit) SEXP_def hoare_T_wait predicate1I tautI)
    apply expr_auto
    using Suc sledgehammer*)
qed



lemma
  assumes (* I is invariant over 'k' iterations, 
             starting from a state satisfying 'P'. *)
          "\<^bold>{P \<and> I\<^bold>} (T(X))\<^bsup>k\<^esup> \<^bold>{I\<^bold>}" 
          (* When started, it terminates after 'c' time.
             FIXME: introduce a definition for this? *)
          "\<^bold>{ \<not>$wait \<and> t = \<guillemotleft>t\<^sub>0\<guillemotright> \<^bold>} T(X) \<^bold>{ \<not>wait \<longrightarrow> t = \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>c\<guillemotright> \<^bold>}"
    shows "\<^bold>{P\<^bold>} (T(X))\<^sup>+ \<^bold>{ (\<guillemotleft>t\<^sub>0\<guillemotright> \<le> t \<and> t < \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>k\<guillemotright>*\<guillemotleft>c\<guillemotright>) \<longrightarrow> I \<^bold>}"
  using assms 
proof(induct k)
  case 0
  then show ?case sorry
next
  case (Suc k)
  then have "\<^bold>{P \<and> I\<^bold>} (T X)\<^bsup>k\<^esup> \<^bold>{I\<^bold>}"
    by (metis SEXP_def fbox_def predicate1I)
  then have "\<^bold>{P\<^bold>} (T X)\<^sup>+ \<^bold>{t\<^sub>0 \<le> $t \<and> $t < t\<^sub>0 + real k * c \<longrightarrow> I\<^bold>}"
    using Suc.hyps assms(2) by blast
  then show ?case
    using Suc (* Need proof that kpower T(X) k yields t = t\<^sub>0 + c*k,
      then knowing that kpower T(X) k is in (T X)\<^bsup>k\<^esup>, and that I
      holds everywhere, then it also holds when t < t\<^sub>0 + k*c.

      By a similar argument, so does kpower T(X) (k+1) ?

      Perhaps no need for proof by induction. *)
    sorry
qed
  have "(T(X))\<^sup>+ = (T(X))\<^bsup>k\<^esup> ; (T(X))\<^sup>+"
    by (simp add: kstar_fixed_comp_eq_kstar_one)
  (* Sketch: find the decomposition of k + ... iterations, prove that
             I holds within 'k', and show that after 'k',
             then t \<ge> \<guillemotleft>t\<^sub>0\<guillemotright>+\<guillemotleft>k\<guillemotright>*\<guillemotleft>c\<guillemotright>, so 'I' no longer needs to apply.

             This is not the case for \<^bsup>k\<^esup> *)
  oops

lemma
  "\<^bold>{ avLW = AV*axisLength/(2*RADIUS) \<and> avRW = -AV*axisLength/(2*RADIUS) \<and> yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   TimerEvo \<delta> PSEqsVars PSEqs (True)\<^sup>e
   \<^bold>{ avLW = AV*axisLength/(2*RADIUS) \<and> avRW = -AV*axisLength/(2*RADIUS) \<and> yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}"
  unfolding EvolveUntil_def T_def TimerEvo_def
  apply (hoare_help)
  using non_zeros(1) non_zeros(2) apply force+
  by (hoare_help)

lemma
  "\<^bold>{ executing \<and> state = DTurning \<^bold>}
    Ctrl
   \<^bold>{ \<not>executing \<and> state = DTurning \<^bold>}"
  unfolding Ctrl_def SendToSoftware_def SimSMovement_def
  by (hoare_help)

lemma
  "\<^bold>{ executing \<and> state = DTurningJunction \<and> MBC < pi/AV \<^bold>}
    Ctrl
   \<^bold>{ \<not>executing \<and> state = DTurning \<^bold>}"
  unfolding Ctrl_def SendToSoftware_def SimSMovement_def
  by hoare_help

lemma
  "\<^bold>{ \<not>executing \<and> state = DTurning \<and> MBC < pi/AV \<^bold>}
    Ctrl
   \<^bold>{ \<not>executing \<and> state = DTurning \<^bold>}"
  unfolding Ctrl_def SendToSoftware_def SimSMovement_def
  by hoare_help

lemma
  "\<^bold>{ \<not>executing \<and> state = DTurning \<and> MBC \<ge> pi/AV \<^bold>}
    Ctrl
   \<^bold>{ \<not>executing \<and> state = DMoving \<^bold>}"
  unfolding Ctrl_def SendToSoftware_def SimSMovement_def
  by hoare_help   

lemma
  fixes c :: nat
  assumes "P nmods executing" "P nmods MBC" "P nmods state"
        "c \<le> pi/av/Cycle"
  shows "\<^bold>{ \<not>executing \<and> state = DTurning \<and> MBC < pi/av \<^bold>}
          T(Ctrl) ; P ; (T(Ctrl) ; P)\<^bsup>c\<^esup>
         \<^bold>{ \<not>executing \<and> state = DTurning \<and> MBC < pi/av \<^bold>}" (* Counter? *)
  unfolding kstar_one_def
  apply (rule hoare_kcomp[where R="(\<not>executing \<and> state = DTurning \<and> (MBC < (pi/AV) \<or> MBC \<ge> (pi/AV)))\<^sup>e"])
  thm hoare_kstarI
  thm hoare_kstar_inv
  oops

lemma
  assumes "P nmods executing" "P nmods MBC" "P nmods state"
  shows "\<^bold>{ \<not>executing \<and> state = DTurning \<and> MBC = k \<^bold>}
         (T(Ctrl) ; P)\<^sup>+
         \<^bold>{ \<not>executing \<and> (MBC-Cycle < pi/av \<longrightarrow> state = DTurning) \<^bold>}" (* Counter? *)
  unfolding kstar_one_def
  thm hoare_kstarI
  thm hoare_kstar_inv
  oops

lemma
  assumes  "AV > 0"
  shows
  "\<^bold>{ MBC = 0 \<and> \<not>executing \<and> state = DTurning \<and>
       avLW = AV*axisLength/(2*RADIUS) \<and>
       avRW = -AV*axisLength/(2*RADIUS) \<and>
       yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   (T(Ctrl) ; Step (TimeScale*Cycle))
   \<^bold>{ \<not>executing \<and> state = DTurning \<and>
      avLW = AV*axisLength/(2*RADIUS) \<and>
      avRW = -AV*axisLength/(2*RADIUS) \<and>
      yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}"
  unfolding kstar_one_def T_def Ctrl_def (*EvolveUntil_def TimerEvo_def T_def*)
  apply (hoare_help_rs)
  thm SimSMovement_def
     defer
     apply (hoare_help_rs)
  using assms divide_pos_pos pi_gt_zero apply fastforce
          defer
       apply (simp_all)
       apply fastforce
      apply (hoare_help_rs)
       defer
       apply (simp_all)
          apply (hoare_help_rs)
        using assms divide_pos_pos pi_gt_zero apply fastforce
         defer
         apply force
            apply (hoare_help_rs)
        (*apply (tactic distinct_subgoals_tac)*)
        unfolding EvolveUntil_def T_def TimerEvo_def
        thm hoare_if_then_else
        apply (hoare_help_rs ; hoare_help_rs?)+
        using non_zeros(1) non_zeros(2) apply linarith+
        by (hoare_help_rs)        

      thm hoare_weaken_pre_conj

lemma
  assumes  "AV > 0"
  shows
  "\<^bold>{ MBC = 0 \<and> \<not>executing \<and> state = DTurning \<and>
       avLW = AV*axisLength/(2*RADIUS) \<and>
       avRW = -AV*axisLength/(2*RADIUS) \<and>
       yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   (T(Ctrl) ; Step (TimeScale*Cycle))
   \<^bold>{ MBC = Cycle \<and> \<not>executing \<and> state = DTurning \<and>
      avLW = AV*axisLength/(2*RADIUS) \<and>
      avRW = -AV*axisLength/(2*RADIUS) \<and>
      yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}"
  unfolding kstar_one_def T_def Ctrl_def (*EvolveUntil_def TimerEvo_def T_def*)
  apply (hoare_help_rs)
  thm SimSMovement_def
     defer
     apply (hoare_help_rs)
  using assms divide_pos_pos pi_gt_zero apply fastforce
          defer
       apply (simp_all)
       apply fastforce
      apply (hoare_help_rs)
       defer
       apply (simp_all)
          apply (hoare_help_rs)
        using assms divide_pos_pos pi_gt_zero apply fastforce
         defer
         apply force
            apply (hoare_help_rs)
        (*apply (tactic distinct_subgoals_tac)*)
        unfolding EvolveUntil_def T_def TimerEvo_def
        thm hoare_if_then_else
        apply (hoare_help_rs ; hoare_help_rs?)+
        using non_zeros(1) non_zeros(2) apply linarith+
        by (hoare_help_rs)        


lemma
  assumes "AV > 0" "(Cycle*k) < (pi/AV)"
  shows
  "\<^bold>{  \<not>executing \<and> MBC = 0 \<and> state = DTurning \<and>
       avLW = AV*axisLength/(2*RADIUS) \<and>
       avRW = -AV*axisLength/(2*RADIUS) \<and>
       yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   (T(Ctrl) ; Step (TimeScale*Cycle))\<^bsup>k\<^esup>
   \<^bold>{ \<not>executing \<and> state = DTurning \<and>
      avLW = AV*axisLength/(2*RADIUS) \<and>
      avRW = -AV*axisLength/(2*RADIUS) \<and>
      yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}"
  unfolding kstar_one_def T_def Ctrl_def (*EvolveUntil_def TimerEvo_def T_def*)
  apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_ifte_kcomp))
  apply (simp add:unrest usubst expr_simps)
   apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_ifte_kcomp))
  
    apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_floyd_kcomp, simp, simp add: usubst_eval usubst unrest))
    apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_ifte_kcomp))
  thm hoare_floyd_kcomp
     apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_floyd_kcomp, simp, simp), (unrest))
                                                                                                   
    apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_floyd_kcomp, simp, simp add: usubst_eval usubst unrest))
  apply ((simp only:kcomp_assoc kcomp_skip)?, (rule hoare_ifte_kcomp))
  apply (hoare_help_rs)
  defer
        apply (simp_all)
        apply (hoare_help_rs)
  defer
        apply (simp_all)
        apply (hoare_help_rs)
  apply (simp_all)
lemma
  "\<^bold>{ \<not>executing \<and> state = DTurning \<and>
       MBC = k \<and>
       avLW = AV*axisLength/(2*RADIUS) \<and>
       avRW = -AV*axisLength/(2*RADIUS) \<and>
       yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   (T(Ctrl) ; Step (TimeScale*Cycle))\<^sup>+
   \<^bold>{ MBC < (pi/AV) \<longrightarrow> (\<not>executing \<and> state = DTurning \<and>
      avLW = AV*axisLength/(2*RADIUS) \<and>
      avRW = -AV*axisLength/(2*RADIUS) \<and>
      yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0) \<^bold>}"
  unfolding kstar_one_def T_def Ctrl_def EvolveUntil_def
  apply (hoare_help)
  apply (rule hoare_kcomp[where R="(\<not>executing \<and> state = DTurning \<and> MBC \<le> (pi/AV) \<and> avLW = AV*axisLength/(2*RADIUS) \<and> avRW = -AV*axisLength/(2*RADIUS) \<and>
      yw = yw\<^sub>0 - t*AV \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0)\<^sup>e"])
  unfolding T_def Ctrl_def EvolveUntil_def
  apply (hoare_help)
  thm hoare_kcomp
(* Question: can we use this to prove a more general property about continuous angular movement?
             ie. one that states that the system keeps rotating between cycles so long as the
                 voltage at each such cycles is maintained. *)


theorem 
  "\<^bold>{ yw = yw\<^sub>0 \<and> mx = mx\<^sub>0 \<and> my = my\<^sub>0 \<^bold>}
   System
   \<^bold>{ yw = yw\<^sub>f \<and> mx = mx\<^sub>f \<and> my = my\<^sub>f \<^bold>}"
  oops

end