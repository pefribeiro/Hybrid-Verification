theory Hoare_Help

imports
  "Hybrid-Verification.Diff_Dyn_Logic"
begin

lemma hoare_kcomp_inv_rhs:
  assumes "\<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>}" and "\<^bold>{Q\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} G ; F \<^bold>{Q\<^bold>}"
  using assms hoare_kcomp by blast

lemma hoare_stengthen_post:
  assumes "\<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>}" and "`Q \<longrightarrow> R`"
  shows "\<^bold>{P\<^bold>} G \<^bold>{R\<^bold>}"
  using assms Diff_Dyn_Logic.strengthen by blast

lemma strenghten_pre_post:
  assumes "\<^bold>{P\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> \<guillemotleft>I\<guillemotright>\<^bold>} F \<^bold>{Q \<and> \<guillemotleft>I\<guillemotright>\<^bold>}"
  using assms fbox_def by auto

lemma hoare_do_while:
  assumes "\<^bold>{I\<^bold>} A \<^bold>{I \<and> T\<^bold>}" and "\<^bold>{I \<and> T\<^bold>} X \<^bold>{I\<^bold>}"
  shows "\<^bold>{I\<^bold>} (A ; WHILE T DO X) \<^bold>{\<not> T \<and> I\<^bold>}"
  using assms
  by (metis (mono_tags) hoare_conj_pos hoare_kcomp hoare_while)

lemma nondet_choice_commute: "P \<sqinter> Q = Q \<sqinter> P"
  unfolding nondet_choice_def by auto

lemma kcomp_right_dist_nondetchoice:
  "(P \<sqinter> Q) ; R = (P ; R) \<sqinter> (Q ; R)"
  unfolding nondet_choice_def kcomp_def
  by (auto, metis UN_Un comp_apply)

lemma kcomp_left_dist_nondetchoice:
  "P ; (Q \<sqinter> R) = (P ; Q) \<sqinter> (P ; R)"
  unfolding nondet_choice_def kcomp_def 
  by (auto, metis UN_Un_distrib comp_apply)

lemma kcomp_left_dist_Nondet_choice: "(\<Sqinter>i\<in>UNIV. P ; F P i) = P ; (\<Sqinter>i\<in>UNIV. F P i)"
  unfolding Nondet_choice_def kcomp_def apply auto
  by fastforce

lemma test_False:
  "\<questiondown>False? = abort"
  unfolding test_def abort_def by auto

lemma While_False_eq_skip:
  "WHILE False DO X = skip"
  unfolding kcomp_def while_def test_def skip_def
  by (auto, metis UN_singleton comp_apply kstar_empty)

lemma abort_skip_eq_skip: "abort \<sqinter> skip = skip"
  unfolding abort_def nondet_choice_def skip_def by auto

lemma kstar_one_or_zero_or_more: "P\<^sup>* = P \<sqinter> P\<^sup>*"
  unfolding nondet_choice_def kstar_def apply auto
  apply (simp add:fun_eq_iff, auto)
  by (metis kpower_Suc_0)

lemma 
  assumes "i > 0"
  shows "kpower P i = P ; (kpower P (i-1))"
  using assms unfolding kpower_def skip_def oops

lemma "(\<Sqinter>i\<in>UNIV-{0}. kpower P i) = (P ; P\<^sup>*)"
  unfolding Nondet_choice_def nondet_choice_def kstar_def kcomp_def apply auto
  oops

lemma
  assumes "xa \<in> kpower P i x" "\<forall>n. \<forall>z\<in>(P x). xa \<notin> kpower P n z"
  shows "xa = x"
  apply (insert assms) unfolding kpower_def
  oops

lemma UNIV_kpower_skip_nondet_choice:"(\<Sqinter>i\<in>UNIV. kpower P i) = skip \<sqinter> (\<Sqinter>i\<in>UNIV. (kpower P i ; P))"
  unfolding Nondet_choice_def nondet_choice_def skip_def kcomp_def
  apply (simp add:fun_eq_iff)
  apply (safe, auto)
  defer
    apply (metis insertI1 kpower_0)
   apply (metis (mono_tags, opaque_lifting) UN_I comp_apply kcomp_def kpower_Suc')
  by (metis (no_types, opaque_lifting) UN_E comp_apply kcomp_def kpower_0 kpower_Suc' not0_implies_Suc singletonD)

lemma UNIV_kpower_skip_nondet_choice':"(\<Sqinter>i\<in>UNIV. kpower P i) = skip \<sqinter> (\<Sqinter>i\<in>UNIV. P ; kpower P i)"
proof -
  have "(\<Sqinter>i\<in>UNIV. kpower P i) = skip \<sqinter> (\<Sqinter>i\<in>UNIV. (kpower P i ; P))"
    using UNIV_kpower_skip_nondet_choice
    by blast
  also have "... = skip \<sqinter> (\<Sqinter>i\<in>UNIV. (P ; kpower P i))"
    using kcomp_kpower
    by metis
  then show ?thesis using calculation by auto
qed

lemma UNIV_kpower_skip_one_more: "(\<Sqinter>i\<in>UNIV. kpower P i) = skip \<sqinter> P ; (\<Sqinter>i\<in>UNIV. kpower P i)"
  using kcomp_left_dist_Nondet_choice UNIV_kpower_skip_nondet_choice' by metis

lemma kstar_zero_or_one_or_more: "P\<^sup>* = skip \<sqinter> (P ; P\<^sup>*)"
  by (metis UNIV_kpower_skip_one_more kstar_alt)

lemma "(\<questiondown>\<not> T? ; X)\<^sup>* = skip \<sqinter> \<questiondown>\<not> T? ; X ; (\<questiondown>\<not> T? ; X)\<^sup>*"
  using kstar_zero_or_one_or_more by blast 

lemma test_not_kcomp_test_abort: "(\<questiondown>\<not> T? ; \<questiondown>T?) = abort"
  unfolding test_def kcomp_def abort_def by auto

lemma kcomp_left_zero: "abort ; X = abort"
  unfolding abort_def kcomp_def by auto

lemma nondet_choice_abort_unit: "P \<sqinter> abort = P"
  by (simp add: abort_def nondet_choice_def)

lemma negative_test_WHILE_DO_absorb:"(\<questiondown>\<not> T? ; WHILE T DO X) = \<questiondown>\<not> T?"
proof -
  have "\<questiondown>\<not> T? ; WHILE T DO X = \<questiondown>\<not> T? ; (\<questiondown>T? ; X)\<^sup>* ; \<questiondown>\<not> T?"
    unfolding while_def
    by (simp add: kcomp_assoc)
  also have "... = \<questiondown>\<not> T? ; ((skip \<sqinter> (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>*) ; \<questiondown>\<not> T?)"
    using kstar_zero_or_one_or_more
    by (metis kcomp_assoc)
  also have "... = (\<questiondown>\<not> T? ; (skip \<sqinter> (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>*)) ; \<questiondown>\<not> T?"
    by (metis kcomp_assoc)
  also have "... = ((\<questiondown>\<not> T? ; skip) \<sqinter> (\<questiondown>\<not> T? ; (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>*)) ; \<questiondown>\<not> T?"
    by (simp add: kcomp_assoc kcomp_left_dist_nondetchoice)
  also have "... = (\<questiondown>\<not> T? \<sqinter> (\<questiondown>\<not> T? ; (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>*)) ; \<questiondown>\<not> T?"
    by (simp add: kcomp_skip(1))
  also have "... = (\<questiondown>\<not> T? \<sqinter> ((\<questiondown>\<not> T? ; \<questiondown>T?) ; X) ; (\<questiondown>T? ; X)\<^sup>*) ; \<questiondown>\<not> T?"
    by (metis kcomp_assoc)
  also have "... = (\<questiondown>\<not> T? \<sqinter> (abort ; X) ; (\<questiondown>T? ; X)\<^sup>*) ; \<questiondown>\<not> T?"
    using test_not_kcomp_test_abort by metis
  also have "... = (\<questiondown>\<not> T? \<sqinter> abort) ; \<questiondown>\<not> T?"
    using kcomp_left_zero by metis
  also have "... = \<questiondown>\<not> T? ; \<questiondown>\<not> T?"
    using nondet_choice_abort_unit by metis
  also have "... = \<questiondown>\<not> T?"
    unfolding test_def kcomp_def by auto
  finally show ?thesis .
qed

lemma WHILE_unroll:
  "WHILE T DO X = \<questiondown>\<not> T? \<sqinter> (\<questiondown>T? ; X) ; WHILE T DO X"
proof -
  have while_T_do_X:"WHILE T DO X = (\<questiondown>T? ; X)\<^sup>* ; \<questiondown>\<not> T?"
    unfolding while_def by auto
  also have "... = (skip \<sqinter> (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>*) ; \<questiondown>\<not> T?"
    using kstar_zero_or_one_or_more by metis
  also have "... = (skip ; \<questiondown>\<not> T?) \<sqinter> (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>* ; \<questiondown>\<not> T?"
    using kcomp_right_dist_nondetchoice by blast
  also have "... = \<questiondown>\<not> T? \<sqinter> (\<questiondown>T? ; X) ; (\<questiondown>T? ; X)\<^sup>* ; \<questiondown>\<not> T?"
    by (simp add: kcomp_skip(2))
  also have "... = \<questiondown>\<not> T? \<sqinter> (\<questiondown>T? ; X) ; WHILE T DO X"
    by (simp add: kcomp_assoc while_T_do_X)
  finally show ?thesis .
qed
  
lemma WHILE_unroll_IF: "IF T THEN X ELSE skip ; WHILE T DO X = WHILE T DO X"
proof -
  have "IF T THEN X ELSE skip ; WHILE T DO X = (\<questiondown>T? ; X \<sqinter> \<questiondown>\<not> T? ; skip) ; WHILE T DO X"
    by (simp add:if_then_else_eq)
  also have "... = (\<questiondown>T? ; X ; WHILE T DO X) \<sqinter> (\<questiondown>\<not> T? ; skip ; WHILE T DO X)"
    using kcomp_right_dist_nondetchoice by blast
  also have "... = (\<questiondown>T? ; X ; WHILE T DO X) \<sqinter> (\<questiondown>\<not> T? ; WHILE T DO X)"
    by (simp add: kcomp_skip(1))
  also have "... = (\<questiondown>T? ; X ; WHILE T DO X) \<sqinter> \<questiondown>\<not> T?"
    using negative_test_WHILE_DO_absorb by metis
  also have "... = \<questiondown>\<not> T? \<sqinter> (\<questiondown>T? ; X ; WHILE T DO X)"
    using nondet_choice_commute by auto
  also have "... = WHILE T DO X"
    using WHILE_unroll by metis
  finally show ?thesis .
qed

lemma hoare_if_then_else:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}" "\<^bold>{P\<^bold>} Y \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} IF T THEN X ELSE Y \<^bold>{Q\<^bold>}"
  using assms 
  by fastforce

lemma hoare_if_then_cond:
  assumes "`P \<longrightarrow> T`" "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} IF T THEN X ELSE Y \<^bold>{Q\<^bold>}"
  using assms unfolding fbox_def ifthenelse_def 
  by (auto simp add: taut_def)

lemma hoare_weaken_pre_conj:
  assumes "`Q \<longrightarrow> P`" "\<^bold>{P \<and> Q\<^bold>} X \<^bold>{R\<^bold>}" 
  shows "\<^bold>{Q\<^bold>} X \<^bold>{R\<^bold>}"
  using assms
  by (simp add: refine_iff_implies taut_def)

lemma hoare_strengthen_post:
  assumes "`T \<longrightarrow> R`" "\<^bold>{P\<^bold>} X \<^bold>{R \<and> T\<^bold>}" 
  shows "\<^bold>{P\<^bold>} X \<^bold>{R\<^bold>}"
  using assms
  by (simp add: hoare_conj_pos)
  
lemma hoare_strengthen_pos_universal:
  assumes "`U`" "\<^bold>{P\<^bold>} X \<^bold>{R\<^bold>}" 
  shows "\<^bold>{P\<^bold>} X \<^bold>{U \<and> R\<^bold>}"
  using assms 
  by (simp add: refine_iff_implies taut_def)


lemma
  shows "\<^bold>{P\<^bold>} skip \<^bold>{Q\<^bold>}"
  nitpick
  oops

lemma nmods_while:
  assumes "X nmods e"
  shows "WHILE T DO X nmods e"
  using assms unfolding while_def
  apply auto
  apply (rule nmods_seq) 
   apply (rule nmods_star)
   apply (rule nmods_seq)
  by (rule nmods_test, simp, rule nmods_test)

lemma nmods_subset:
  assumes "P nmods I" "\<forall>s. Q s \<subseteq> P s"
  shows "Q nmods I"
  by (meson assms(1) assms(2) not_modifies_def subsetD)

lemma nmods_frame_law':
  assumes "S nmods I" "\<^bold>{P \<and> I\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> I\<^bold>} S \<^bold>{Q \<and> I\<^bold>}"
  using assms
  by (auto simp add: prog_defs fbox_def expr_defs not_modifies_def)

lemma hoare_while_unroll_kcomp:
  assumes "\<^bold>{P\<^bold>} IF T THEN X ELSE skip \<^bold>{Q\<^bold>}" "\<^bold>{Q\<^bold>} WHILE T DO X \<^bold>{R\<^bold>}" 
  shows "\<^bold>{P\<^bold>} WHILE T DO X \<^bold>{R\<^bold>}"
  using assms WHILE_unroll_IF
  by (metis hoare_kcomp) 

(*
  by (metis (mono_tags) SEXP_def hoare_kcomp nmods_invariant not_modifies_def)
  by (metis (mono_tags) hoare_conj_pos hoare_kcomp hoare_while)*)


(*
lemma unfold_while:
  assumes "`P \<longrightarrow> X`" "\<^bold>{P\<^bold>} (\<questiondown>X? ; Y)\<^sup>* ; Z \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} Y ; (\<questiondown>X? ; Y)\<^sup>* ; Z \<^bold>{Q\<^bold>}"
  using assms
  by (metis (mono_tags, lifting) SEXP_def fbox_def fbox_kcomp predicate1D predicate1I)
*)

end