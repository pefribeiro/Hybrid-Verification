theory SpringMassDamper

imports
  "Hybrid-Verification.Hybrid_Verification"
begin

lit_vars

dataspace smd =
  constants
    \<zeta> :: real
    \<omega> :: real
    C\<^sub>1 :: real
    C\<^sub>2 :: real
  assumes
        non_zero: "0 < \<zeta>"
    and real_diff: "\<zeta>\<^sup>2 \<ge> 4 * \<omega>\<^sup>2"
  variables
    x :: real
    v :: real

context smd
begin

abbreviation "L1 \<equiv> (-\<zeta> + sqrt(\<zeta>^2-4*\<omega>^2))/2"
abbreviation "L2 \<equiv> (-\<zeta> - sqrt(\<zeta>^2-4*\<omega>^2))/2"

lemma 
  fixes a :: real
  shows "(a/b)^2 = (a^2/b^2)"
  by (simp add: power_divide)

lemma 
  assumes "0 \<le> a"
  shows "sqrt(a)^2 = a"
  by (simp add: assms)

lemma L1_squared:"L1^2 = (\<zeta>\<^sup>2 + (sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2))\<^sup>2 - (2*\<zeta> * sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2)))/4"
proof -
  have A:"L1 = (-\<zeta>/2) + (sqrt(\<zeta>^2-4*\<omega>^2)/2)"
    by auto
  
  then have B:"((-\<zeta>/2) + (sqrt(\<zeta>^2-4*\<omega>^2)/2))^2 = (-\<zeta>/2)^2 + (sqrt(\<zeta>^2-4*\<omega>^2)/2)^2 + 2*((-\<zeta>/2)*(sqrt(\<zeta>^2-4*\<omega>^2)/2))"
    by (simp add: power2_diff)
  also have "... = (\<zeta>^2/4) + sqrt(\<zeta>^2-4*\<omega>^2)^2/4 - (2*\<zeta> * sqrt(\<zeta>^2-4*\<omega>^2))/4"
  proof -
    have "(-\<zeta>/2)^2 = (\<zeta>^2/4)"
         "(sqrt(\<zeta>^2-4*\<omega>^2)/2)^2 = (sqrt(\<zeta>^2-4*\<omega>^2)^2/4)"
        apply (simp add: four_x_squared mult.commute)
      by (auto simp add: power_divide)
    then show ?thesis
      by auto
  qed
  also have "... = (\<zeta>\<^sup>2 + (sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2))\<^sup>2 - (2*\<zeta> * sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2)))/4"
    by auto
  then show ?thesis
    using A calculation by presburger
qed

lemma L2_squared:"L2^2 = (\<zeta>\<^sup>2 + (sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2))\<^sup>2 + (2*\<zeta> * sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2)))/4"
proof -
  have A:"L2 = (-\<zeta>/2) - (sqrt(\<zeta>^2-4*\<omega>^2)/2)"
    by auto
  
  then have B:"((-\<zeta>/2) - (sqrt(\<zeta>^2-4*\<omega>^2)/2))^2 = (-\<zeta>/2)^2 + (sqrt(\<zeta>^2-4*\<omega>^2)/2)^2 - 2*((-\<zeta>/2)*(sqrt(\<zeta>^2-4*\<omega>^2)/2))"
    by (simp add: power2_diff)
  also have "... = (\<zeta>^2/4) + sqrt(\<zeta>^2-4*\<omega>^2)^2/4 + (2*\<zeta> * sqrt(\<zeta>^2-4*\<omega>^2))/4"
  proof -
    have "(-\<zeta>/2)^2 = (\<zeta>^2/4)"
         "(sqrt(\<zeta>^2-4*\<omega>^2)/2)^2 = (sqrt(\<zeta>^2-4*\<omega>^2)^2/4)"
        apply (simp add: four_x_squared mult.commute)
      by (auto simp add: power_divide)
    then show ?thesis
      by auto
  qed
  also have "... = (\<zeta>\<^sup>2 + (sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2))\<^sup>2 + (2*\<zeta> * sqrt(\<zeta>\<^sup>2 - 4 * \<omega>\<^sup>2)))/4"
    by auto
  then show ?thesis
    using A calculation by presburger
qed

lemma L2_squared_real:
  assumes "\<zeta>\<^sup>2 \<ge> 4 * \<omega>\<^sup>2"
  shows "L2^2 = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 + (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)))/2"
  using assms L2_squared
  by simp

lemma L1_squared_real:
  assumes "\<zeta>\<^sup>2 \<ge> 4 * \<omega>\<^sup>2"
  shows "L1^2 = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 - (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)))/2"
  using assms L1_squared
  by simp

abbreviation "x0(t) \<equiv> C\<^sub>1*exp(L1*t) + C\<^sub>2*exp(L2*t)"
abbreviation "v0(t) \<equiv> C\<^sub>1*L1*exp(L1*t) + C\<^sub>2*L2*exp(L2*t)"
abbreviation "a0(t) \<equiv> C\<^sub>1*L1\<^sup>2*exp(L1*t) + C\<^sub>2*L2\<^sup>2*exp(L2*t)"

lemma L1_square_sums_eq_zero:
  assumes "\<zeta>\<^sup>2 \<ge> 4 * \<omega>\<^sup>2"
  shows "L1\<^sup>2 + \<zeta>*L1 + \<omega>\<^sup>2 = 0"
proof -
  have "L1\<^sup>2 + \<zeta>*L1 + \<omega>\<^sup>2 = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 - (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)))/2 + \<zeta>*((-\<zeta>/2) + (sqrt(\<zeta>^2-4*\<omega>^2)/2)) + \<omega>\<^sup>2"
    using assms L1_squared 
    by (metis (no_types, lifting) L1_squared_real add_divide_distrib)
  also have "... = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 - (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)))/2 + (-\<zeta>\<^sup>2/2) + (\<zeta> * sqrt(\<zeta>^2-4*\<omega>^2)/2) + \<omega>\<^sup>2"
    by (simp add: power2_eq_square right_diff_distrib')
  also have "... = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 - (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)) + -\<zeta>\<^sup>2 + \<zeta> * sqrt(\<zeta>^2-4*\<omega>^2) + 2*\<omega>\<^sup>2)/2"
    by (smt (z3) field_sum_of_halves)
  also have "... = 0"
    by auto
  finally show ?thesis .
qed

lemma L2_square_sums_eq_zero:
  assumes "\<zeta>\<^sup>2 \<ge> 4 * \<omega>\<^sup>2"
  shows "L2\<^sup>2 + \<zeta>*L2 + \<omega>\<^sup>2 = 0"
proof -
  have "L2\<^sup>2 + \<zeta>*L2 + \<omega>\<^sup>2 = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 + (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)))/2 + \<zeta>*((-\<zeta>/2) - (sqrt(\<zeta>^2-4*\<omega>^2)/2)) + \<omega>\<^sup>2"
    using assms L2_squared
    by (simp add: diff_divide_distrib)
  also have "... = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 + (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)))/2 + (-\<zeta>\<^sup>2/2) - (\<zeta> * sqrt(\<zeta>^2-4*\<omega>^2)/2) + \<omega>\<^sup>2"
    by (simp add: power2_eq_square right_diff_distrib')
  also have "... = (\<zeta>\<^sup>2 - 2*\<omega>\<^sup>2 + (\<zeta> * sqrt(\<zeta>\<^sup>2 - 4*\<omega>\<^sup>2)) + -\<zeta>\<^sup>2 - \<zeta> * sqrt(\<zeta>^2-4*\<omega>^2) + 2*\<omega>\<^sup>2)/2"
    by (smt (z3) field_sum_of_halves)
  also have "... = 0"
    by auto
  finally show ?thesis .
qed

lemma diff_eq_zero:
  assumes "\<zeta>\<^sup>2 \<ge> 4 * \<omega>\<^sup>2"
  shows "a0(t) + \<zeta> * v0(t) + \<omega>\<^sup>2*x0(t) = 0"
proof -
  have "a0(t) + \<zeta> * v0(t) + \<omega>\<^sup>2*x0(t) = C\<^sub>1*exp(L1*t)*L1\<^sup>2 + C\<^sub>2*exp(L2*t)*L2\<^sup>2 + \<zeta>*C\<^sub>1*L1*exp(L1*t) + \<zeta>*C\<^sub>2*L2*exp(L2*t) + \<omega>\<^sup>2*C\<^sub>1*exp(L1*t) + \<omega>\<^sup>2*C\<^sub>2*exp(L2*t)"
    by (simp add: distrib_left)
  also have "... = C\<^sub>1*exp(L1*t)*L1\<^sup>2 + C\<^sub>2*exp(L2*t)*L2\<^sup>2 + C\<^sub>1*exp(L1*t)*\<zeta>*L1 + C\<^sub>2*exp(L2*t)*\<zeta>*L2 + C\<^sub>1*exp(L1*t)*\<omega>\<^sup>2 + C\<^sub>2*exp(L2*t)*\<omega>\<^sup>2"
    by (simp add: mult.commute mult.left_commute)
  also have "... = C\<^sub>1*exp(L1*t)*L1\<^sup>2 + C\<^sub>1*exp(L1*t)*\<zeta>*L1 + C\<^sub>1*exp(L1*t)*\<omega>\<^sup>2 + C\<^sub>2*exp(L2*t)*L2\<^sup>2 + C\<^sub>2*exp(L2*t)*\<zeta>*L2 + C\<^sub>2*exp(L2*t)*\<omega>\<^sup>2"
    by auto
  also have "... = C\<^sub>1*exp(L1*t)*(L1\<^sup>2 + \<zeta>*L1 + \<omega>\<^sup>2) + C\<^sub>2*exp(L2*t)*L2\<^sup>2 + C\<^sub>2*exp(L2*t)*\<zeta>*L2 + C\<^sub>2*exp(L2*t)*\<omega>\<^sup>2"
    by (simp add: distrib_left)
  also have "... = C\<^sub>1*exp(L1*t)*(L1\<^sup>2 + \<zeta>*L1 + \<omega>\<^sup>2) + C\<^sub>2*exp(L2*t)*(L2\<^sup>2 + \<zeta>*L2 + \<omega>\<^sup>2)"
    by (simp add: distrib_left)
  also have "... = 0"
    using assms L1_square_sums_eq_zero L2_square_sums_eq_zero
    by fastforce
  finally show ?thesis . 
qed

abbreviation "evolve \<equiv> {x` = v, v` = - (\<omega>^2) - (\<zeta> * v)}"

abbreviation "evolve_flow \<equiv> [x \<leadsto> v, v \<leadsto> - (\<omega>^2) - (\<zeta> * v)]"

abbreviation "flow \<tau> \<equiv> [x \<leadsto> C\<^sub>1*exp (L1*\<tau>) + C\<^sub>2*exp (L2*\<tau>), v \<leadsto> C\<^sub>1*L1*exp (L1*\<tau>) + C\<^sub>2*L2*exp (L2*\<tau>)]"

(*lemma flow_exp:
  "local_flow_on evolve_flow (x+\<^sub>Lv) UNIV UNIV flow"
  apply (auto simp add: local_flow_on_def)
  apply (unfold_locales, auto)
    apply (lipschitz "\<zeta>")
  using non_zero real_diff
  apply (expr_auto)
  defer
  apply (expr_simp) 
    (* apply (force intro!: vderiv_intros)
    apply (simp: vec_eq_iff field_simps) *)
  oops
*)

end

end