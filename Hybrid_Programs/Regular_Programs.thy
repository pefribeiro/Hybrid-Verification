(*  Title: HS verification with lenses *)

section \<open> HS verification with lenses \<close>

text \<open> We use shallow expressions to rephrase hybrid systems properties. Each operator below 
includes lemmas for verification condition generation. \<close>

theory Regular_Programs
  imports "Framed_ODEs.HS_Preliminaries" Correctness_Specs
begin

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)
no_notation Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999)

subsection \<open> Skip \<close>

definition [prog_defs]: "skip = (\<lambda>s. {s})"

lemma fbox_skip [wlp]: "|skip] P = P"
  unfolding fbox_def skip_def by simp

lemma fdia_skip: "|skip\<rangle> P = P"
  unfolding fdia_def skip_def by simp

lemma hoare_skip: "\<^bold>{P\<^bold>} skip \<^bold>{P\<^bold>}"
  by (auto simp: fbox_skip)


subsection \<open> Abort \<close>

definition [prog_defs]: "abort = (\<lambda>s. {})"

lemma fbox_abort [wlp]: "|abort] P = (True)\<^sub>e"
  unfolding fbox_def abort_def by auto

lemma fdia_abort: "|abort\<rangle> P = (False)\<^sub>e"
  unfolding fdia_def abort_def by expr_simp

lemma hoare_abort: "\<^bold>{P\<^bold>} abort \<^bold>{Q\<^bold>}"
  by (auto simp: fbox_abort)


subsection \<open> Tests \<close>

definition test :: "'a pred \<Rightarrow> 'a \<Rightarrow> 'a set"
  where [prog_defs]: "test P = (\<lambda>s. {x. x = s \<and> P x})"

syntax 
  "_test" :: "logic \<Rightarrow> logic" ("(1\<questiondown>_?)")

translations
  "_test P" == "CONST test (P)\<^sub>e"

lemma fbox_test [wlp]: "|\<questiondown>P?] Q = (P \<longrightarrow> Q)\<^sub>e"
  unfolding fbox_def test_def by (simp add: expr_defs)

lemma fdia_test: "|\<questiondown>P?\<rangle> Q = (P \<and> Q)\<^sub>e"
  unfolding fdia_def test_def by expr_simp

lemma hoare_test: "\<^bold>{P\<^bold>} \<questiondown>T? \<^bold>{P \<and> T\<^bold>}"
  by (auto simp: fbox_test)

lemma test_False:
  "\<questiondown>False? = abort"
  unfolding test_def abort_def by auto

subsection \<open> Assignments \<close>

thm subst_nil_def subst_bop
thm subst_basic_ops
thm subst_lookup_def subst_app_def lens_update_def

definition assigns :: "'s subst \<Rightarrow> 's \<Rightarrow> 's set" ("\<langle>_\<rangle>") 
  where [prog_defs]: "\<langle>\<sigma>\<rangle> = (\<lambda> s. {\<sigma> s})"

syntax
  "_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("(2_ ::= _)" [65, 64] 64)

translations
  "_assign x e" == "\<langle>CONST subst_upd [\<leadsto>] x (e)\<^sub>e\<rangle>" (* "\<langle>[x \<leadsto>\<^sub>s e]\<rangle>" *)


lemma fbox_assign: "|x ::= e] Q = (Q\<lbrakk>e/x\<rbrakk>)\<^sub>e"
  by (simp add: assigns_def subst_app_def fbox_def fun_eq_iff)

lemma hoare_assign: "\<^bold>{Q\<lbrakk>e/x\<rbrakk>\<^bold>} (x ::= e) \<^bold>{Q\<^bold>}"
  by (auto simp: fbox_assign)

lemma fbox_assigns [wlp]: "|\<langle>\<sigma>\<rangle>] Q = \<sigma> \<dagger> (Q)\<^sub>e"
  by (simp add: assigns_def expr_defs fbox_def)

lemma H_assign_floyd_hoare:
  assumes "vwb_lens x"
  shows "\<^bold>{p\<^bold>} x ::= e \<^bold>{\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<^bold>}"
  using assms apply (simp add: wlp, expr_auto)
  by (metis vwb_lens_def wb_lens.source_stability)

lemma fdia_assign: "|x ::= e\<rangle> P = (P\<lbrakk>e/x\<rbrakk>)\<^sub>e"
  by (simp add: assigns_def expr_defs fdia_def)


subsection \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's prog" ("(2_ ::= ?)" [64] 65)
  where [prog_defs]: "(x ::= ?) = (\<lambda>s. {(put\<^bsub>x\<^esub> s k)|k. True})"

lemma fbox_nondet_assign [wlp]: "|x ::= ?] P = (\<forall>k. P\<lbrakk>k/x\<rbrakk>)\<^sub>e"
  unfolding fbox_def nondet_assign_def 
  by (auto simp add: fun_eq_iff expr_defs)

lemma hoare_nondet_assign: "\<^bold>{\<forall>k. Q\<lbrakk>k/x\<rbrakk>\<^bold>} (x ::= ?) \<^bold>{Q\<^bold>}"
  by (simp add: fbox_nondet_assign)

lemma fdia_nondet_assign: "|x ::= ?\<rangle> P = (\<exists>k. P\<lbrakk>k/x\<rbrakk>)\<^sub>e"
  unfolding fdia_def nondet_assign_def 
  by (auto simp add: fun_eq_iff expr_defs)


subsection \<open> Nondeterministic choice \<close>

definition nondet_choice :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" (infixr "\<sqinter>" 60) 
  where [prog_defs]: "nondet_choice F G = (\<lambda> s. F s \<union> G s)"

lemma fbox_choice [wlp]: "|F \<sqinter> G] P = ( |F] P \<and> |G] P)\<^sub>e"
  unfolding fbox_def nondet_choice_def by auto

lemma le_fbox_choice_iff: "P \<le> |F \<sqinter> G] Q \<longleftrightarrow> P \<le> |F] Q \<and> P \<le> |G] Q"
  unfolding fbox_def nondet_choice_def by auto

lemma le_fbox_choice_iff': "P \<le> ( |F \<sqinter> G] Q)\<^sub>e \<longleftrightarrow> P \<le> |F] Q \<and> P \<le> |G] Q"
  unfolding fbox_def nondet_choice_def by expr_auto

lemma hoare_choice: 
  "\<^bold>{P\<^bold>} F \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} (F \<sqinter> G) \<^bold>{Q\<^bold>}"
  by (subst le_fbox_choice_iff, simp)

lemma fdia_choice: "|F \<sqinter> G\<rangle> P = ( |F\<rangle> P \<or> |G\<rangle> P)\<^sub>e"
  unfolding fdia_def nondet_choice_def by expr_auto

definition Nondet_choice :: "('i \<Rightarrow> 's prog) \<Rightarrow> 'i set \<Rightarrow> 's prog"
  where "Nondet_choice F I = (\<lambda>s. \<Union> i\<in>I. F i s)"

syntax
  "_Nondet_choice" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<Sqinter> _ \<in> _./ _" [0, 0, 10] 10)

translations "_Nondet_choice i I P" == "CONST Nondet_choice (\<lambda> i. P) I"

lemma fbox_Choice [wlp]: "|\<Sqinter> i\<in>I. F(i)] P = (\<forall> i\<in>\<guillemotleft>I\<guillemotright>. |F(i)] P)\<^sub>e"
  by (auto simp add: fbox_def Nondet_choice_def fun_eq_iff)

lemma nondet_choice_commute: "P \<sqinter> Q = Q \<sqinter> P"
  unfolding nondet_choice_def by auto

lemma abort_skip_eq_skip: "abort \<sqinter> skip = skip"
  unfolding abort_def nondet_choice_def skip_def by auto

lemma nondet_choice_abort_unit: "P \<sqinter> abort = P"
  by (simp add: abort_def nondet_choice_def)

subsection \<open> Sequential composition \<close>

definition kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl ";" 62) 
  where [prog_defs]: "F ; G = \<mu> \<circ> (`) G \<circ> F"

lemma kcomp_eq: "(f ; g) x = \<Union> {g y |y. y \<in> f x}"
  unfolding kcomp_def image_def by auto

lemma kcomp_id: 
  shows "f ; (\<lambda>s. {s}) = f"
    and "(\<lambda>s. {s}) ; f = f"
  unfolding kcomp_eq 
  by auto

lemmas kcomp_skip = kcomp_id[unfolded skip_def[symmetric]]

lemma kcomp_assoc: "f ; g ; h = f ; (g ; h)"
  unfolding kcomp_eq 
  by (auto simp: fun_eq_iff)

lemma fbox_kcomp[wlp]: "|G ; F] P = |G] |F] P"
  unfolding fbox_def kcomp_def by auto

lemma hoare_kcomp:
  assumes "\<^bold>{P\<^bold>} G \<^bold>{R\<^bold>}" and "\<^bold>{R\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} G ; F \<^bold>{Q\<^bold>}"
  apply(subst fbox_kcomp)
  using assms fbox_iso
  by (metis (mono_tags, lifting) SEXP_def predicate1D predicate1I) 

lemma hoare_kcomp_inv:
  assumes "\<^bold>{I\<^bold>} G \<^bold>{I\<^bold>}" and "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>}"
  shows "\<^bold>{I\<^bold>} G ; F \<^bold>{I\<^bold>}"
  using assms hoare_kcomp by fastforce

lemma hoare_kcomp_inv_rhs:
  assumes "\<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>}" and "\<^bold>{Q\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} G ; F \<^bold>{Q\<^bold>}"
  using assms hoare_kcomp by blast

lemma fdia_kcomp: "|G ; F\<rangle> P = |G\<rangle> |F\<rangle> P"
  unfolding fdia_def kcomp_def by auto

lemma hoare_fwd_assign:
  assumes "vwb_lens x" "\<And> x\<^sub>0. \<^bold>{$x = e\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> P\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>} S \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} x ::= e ; S \<^bold>{Q\<^bold>}"
  using assms
  unfolding kcomp_def assigns_def fbox_def le_fun_def
  by (expr_simp) (metis vwb_lens.put_eq vwb_lens_wb wb_lens_def weak_lens.put_get)

lemma fbox_invI_break: 
  "P \<le> |Y] I \<Longrightarrow> I \<le> |X] I \<Longrightarrow> I \<le> Q \<Longrightarrow> P \<le> |Y ; X INV I] Q"
  apply(subst fbox_to_hoare, rule hoare_kcomp, force)
  by (rule fbox_invI) auto

lemma hoare_invI_break: 
  "\<^bold>{P\<^bold>} Y \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> I \<le> Q \<Longrightarrow> \<^bold>{P\<^bold>} Y ; X INV I\<^bold>{Q\<^bold>}"
  by (rule fbox_invI_break; expr_auto)

lemma fdia_invI_break: 
  "P \<le> |Y\<rangle> I \<Longrightarrow> I \<le> |X\<rangle> I \<Longrightarrow> I \<le> Q \<Longrightarrow> P \<le> |Y ; X INV I\<rangle> Q"
  apply(subst fdia_kcomp)
  apply (rule_tac Q\<^sub>2=I in fdia_conseq, force, expr_auto)
  by (unfold impl_eq_leq invar_def, rule_tac P\<^sub>2=I in fdia_conseq, force)
    (auto simp: taut_def)

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

lemma test_not_kcomp_test_abort: "(\<questiondown>\<not> T? ; \<questiondown>T?) = abort"
  unfolding test_def kcomp_def abort_def by auto

lemma kcomp_left_zero: "abort ; X = abort"
  unfolding abort_def kcomp_def by auto

lemma hoare_insert_post_test:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}"
  shows "\<questiondown>P? ; X = \<questiondown>P? ; X ; \<questiondown>Q?"
proof -
  have "P \<le> |X] Q"
    using assms by force
  then have "P \<le> (\<lambda>s. (\<forall>s'. s' \<in> X s \<longrightarrow> Q s'))"
    by (simp add: fbox_def)
  then have "\<forall>s. P s \<longrightarrow> (\<forall>s'. s' \<in> X s \<longrightarrow> Q s')"
    by auto
  then have "\<forall>s. P s \<longrightarrow> (X ; \<questiondown>Q?) s = X s"
    unfolding kcomp_def test_def
    by auto
  then have "\<questiondown>P? ; X = \<questiondown>P? ; X ; \<questiondown>Q?"
    unfolding test_def kcomp_def by auto
  then show ?thesis .
qed

lemma test_to_choice:
  "X = \<questiondown>P? ; X \<sqinter> \<questiondown>\<not> P? ; X"
  unfolding nondet_choice_def test_def kcomp_def by auto

lemma test_nondet_unit:
  "X = \<questiondown>P? ; X \<sqinter> X"
  unfolding nondet_choice_def test_def kcomp_def by auto

lemma hoare_insert_test:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}"
  shows "X = \<questiondown>P? ; X ; \<questiondown>Q? \<sqinter> X"
  using assms hoare_insert_post_test
  by (metis test_nondet_unit)

lemma "P ; abort = abort"
  by (auto simp add:kcomp_def abort_def)

lemma "abort ; P = abort"
  by (auto simp add:kcomp_def abort_def)

lemma hoare_floyd_kcomp:
  assumes "vwb_lens x" "\<^bold>{\<exists> v . P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} x ::= e ; F \<^bold>{Q\<^bold>}"
  apply (rule hoare_kcomp[where R="(\<exists> v . P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<^sup>e"])
   apply (rule H_assign_floyd_hoare)
  using assms(1) apply simp
  using assms(2) by blast

lemma hoare_kcomp_bracket:
  assumes "\<^bold>{P\<^bold>} F ; (G ; H) \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} (F ; G) ; H \<^bold>{Q\<^bold>}"
  using assms
  by (simp add: kcomp_assoc)

subsection \<open> Conditional statement \<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)" where
  [prog_defs]: "ifthenelse P X Y \<equiv> (\<lambda>s. if P s then X s else Y s)"

syntax "_ifthenelse" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("IF _ THEN _ ELSE _" [0,0,63] 64)
translations "IF P THEN X ELSE Y" == "CONST ifthenelse (P)\<^sub>e X Y"

lemma if_then_else_eq: "IF T THEN X ELSE Y = \<questiondown>T? ; X \<sqinter> \<questiondown>\<not> T? ; Y"
  by (auto simp: fun_eq_iff test_def kcomp_def ifthenelse_def nondet_choice_def)

lemma fbox_if_then_else [simp]:
  "|IF T THEN X ELSE Y] Q = ((T \<longrightarrow> |X] Q) \<and> (\<not> T \<longrightarrow> |Y] Q))\<^sub>e"
  unfolding fbox_def ifthenelse_def by auto

lemma hoare_if_then_else:
  assumes "\<^bold>{P \<and> T\<^bold>} X \<^bold>{Q\<^bold>}"
    and "\<^bold>{P \<and> \<not> T\<^bold>} Y \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} (IF T THEN X ELSE Y) \<^bold>{Q\<^bold>}"
  using assms unfolding fbox_def ifthenelse_def by auto

lemma hoare_if_then_else_inv:
  assumes "\<^bold>{b \<and> I\<^bold>}P\<^bold>{b \<and> I\<^bold>}" "\<^bold>{\<not>b \<and> I\<^bold>}Q\<^bold>{\<not>b \<and> I\<^bold>}" 
  shows "\<^bold>{I\<^bold>}IF b THEN P ELSE Q\<^bold>{I\<^bold>}"
  using assms
  by (auto simp add: fbox_def expr_defs ifthenelse_def)

lemma fdia_if_then_else:
  "|IF T THEN X ELSE Y\<rangle> Q = ((T \<and> |X\<rangle> Q) \<or> (\<not> T \<and> |Y\<rangle> Q))\<^sub>e"
  unfolding fdia_def ifthenelse_def by expr_auto

lemma hoare_if_then_else':
  assumes "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}" "\<^bold>{P\<^bold>} Y \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} IF T THEN X ELSE Y \<^bold>{Q\<^bold>}"
  using assms 
  by fastforce

lemma hoare_if_then_cond:
  assumes "`P \<longrightarrow> T`" "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} IF T THEN X ELSE Y \<^bold>{Q\<^bold>}"
  using assms unfolding fbox_def ifthenelse_def 
  by (auto simp add: taut_def)

lemma hoare_insert_ifthenelse:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>}"
  shows "X = IF P THEN X ; \<questiondown>Q? ELSE X"
proof -
  have "P \<le> |X] Q"
    using assms by force
  then have "P \<le> (\<lambda>s. (\<forall>s'. s' \<in> X s \<longrightarrow> Q s'))"
    by (simp add: fbox_def)
  then have "\<forall>s. P s \<longrightarrow> (\<forall>s'. s' \<in> X s \<longrightarrow> Q s')"
    by auto
  then have "\<forall>s. P s \<longrightarrow> (X ; \<questiondown>Q?) s = X s"
    unfolding kcomp_def test_def
    by auto
  
  then have "(\<lambda>s. if P s then (X ; \<questiondown>Q?) s else X s) = (\<lambda>s. if P s then X s else X s)"
    by meson
  then have "(IF P THEN X ; \<questiondown>Q? ELSE X) = IF P THEN X ELSE X"
    unfolding ifthenelse_def
    by auto
  then show ?thesis
    unfolding ifthenelse_def
    by auto
qed

lemma hoare_ifte_kcomp:
  assumes "\<^bold>{P \<and> T\<^bold>} X ; Z \<^bold>{Q\<^bold>}" "\<^bold>{P \<and> \<not> T\<^bold>} Y ; Z \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} (IF T THEN X ELSE Y) ; Z \<^bold>{Q\<^bold>}"
  using assms 
  by (smt (verit, ccfv_SIG) SEXP_def fbox_if_then_else fbox_kcomp le_fun_def)

lemma hoare_if_kcomp:
  assumes "`P \<longrightarrow> T`" "\<^bold>{P\<^bold>} X ; Z \<^bold>{Q\<^bold>}" 
  shows "\<^bold>{P\<^bold>} (IF T THEN X ELSE Y) ; Z \<^bold>{Q\<^bold>}"
  using assms 
  by (metis (no_types, lifting) SEXP_def fbox_kcomp hoare_if_then_cond taut_def)

lemma hoare_else_kcomp:
  assumes "`P \<longrightarrow> \<not> T`" "\<^bold>{P\<^bold>} Y ; Z \<^bold>{Q\<^bold>}" 
  shows "\<^bold>{P\<^bold>} (IF T THEN X ELSE Y) ; Z \<^bold>{Q\<^bold>}"
  using assms 
  by (smt (verit, del_insts) SEXP_def fbox_if_then_else fbox_kcomp predicate1D predicate1I taut_def)

subsection \<open> N iterations \<close>

definition kpower :: "('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "kpower f n = (\<lambda>s. (((;) f ^^ n) skip) s)"

lemma kpower_base:
  shows kpower_0: "kpower f 0 = (\<lambda>s. {s})" 
    and kpower_Suc_0: "kpower f (Suc 0) = (\<lambda>s. f s)"
  unfolding kpower_def 
  by (auto simp: kcomp_eq skip_def fun_eq_iff)

lemmas kpower_0' = kpower_0[unfolded skip_def[symmetric]]

lemma kpower_Suc: "kpower f (Suc n) = (f ; kpower f n)"
  apply (induct n)
  unfolding kcomp_eq kpower_base
   apply(force simp: subset_antisym)
  unfolding kpower_def kcomp_eq by simp

lemma kpower_Suc': "kpower f (Suc n) = (kpower f n; f)"
  apply (induct n)
  by (simp add: kpower_base kcomp_def)
    (simp add: kpower_Suc kcomp_assoc[symmetric])

lemma "kpower f 2 s = (\<Union> {f s' |s'. s' \<in> f s})"
  by (subgoal_tac "2 = Suc (Suc 0)", erule ssubst)
    (auto simp: kpower_Suc kpower_base kcomp_id kcomp_eq)

lemma kpower_empty: "kpower (\<lambda>s. {}) (Suc n) = (\<lambda>s. {})"
  by (induct n) 
    (simp_all add: kpower_base kpower_Suc kcomp_eq)

lemmas kpower_abort = kpower_empty[unfolded abort_def[symmetric]]

lemma kpower_id: "kpower (\<lambda>s. {s}) n = (\<lambda>s. {s})"
  by (induct n) 
    (simp_all add: kpower_base kpower_Suc kcomp_eq)

lemmas kpower_skip = kpower_id[unfolded skip_def[symmetric]]

lemma kcomp_kpower: "(f ; kpower f n) = (kpower f n; f)"
  by (induct n, simp_all add: kpower_base kcomp_id 
      kpower_Suc kpower_Suc' kcomp_assoc[symmetric])

lemma kpower_inv: 
  fixes F :: "'a \<Rightarrow> 'a set"
  assumes "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> F s \<longrightarrow> I s')" 
  shows "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> (kpower F n s) \<longrightarrow> I s')"
  apply(clarsimp, induct n)
  unfolding kpower_base kpower_Suc
   apply(simp_all add: kcomp_eq, clarsimp) 
  apply(subgoal_tac "I y", simp)
  using assms by blast

lemma fbox_kpower_0: "|kpower F 0] Q = Q"
  by (simp only: kpower_0 skip_def[symmetric] fbox_skip)

lemma fbox_kpower_Suc: "|kpower F (Suc n)] Q = ( |F] |kpower F n] Q)"
  by (simp only: kpower_Suc fbox_kcomp)

lemma fdia_kpower_0: "|kpower F 0\<rangle> Q = Q"
  by (simp only: kpower_0 skip_def[symmetric] fdia_skip)

lemma fdia_kpower_Suc: "|kpower F (Suc n)\<rangle> Q = ( |F\<rangle> |kpower F n\<rangle> Q)"
  by (simp only: kpower_Suc fdia_kcomp)


subsection \<open> Finite iteration \<close>

definition kstar :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^sup>*)" [1000] 999)
  where [prog_defs]: "(f\<^sup>*) s = \<Union> {kpower f n s |n. n \<in> UNIV}"

lemma kstar_alt: "f\<^sup>* = (\<Sqinter>i\<in>UNIV. kpower f i)"
  by (auto simp add: fun_eq_iff kstar_def Nondet_choice_def)

lemma in_kstar_self: "s \<in> (f\<^sup>*) s"
  unfolding kstar_def apply clarsimp
  by (rule_tac x="{s}" in exI, clarsimp)
    (rule_tac x=0 in exI, clarsimp simp: kpower_base)

lemma kstar_empty: "(\<lambda>s. {})\<^sup>* = (\<lambda>s. {s})"
  unfolding kstar_def apply (intro ext set_eqI iffI; clarsimp)
  subgoal for s' s n by (induct n, simp_all add: kpower_id kpower_empty kpower_base)
  by (rule_tac x="{s}" in exI, clarsimp)
    (rule_tac x=0 in exI, clarsimp simp: kpower_base)

lemmas kstar_abort = kstar_empty[unfolded abort_def[symmetric] skip_def[symmetric]]

lemma kstar_id: "(\<lambda>s. {s})\<^sup>* = (\<lambda>s. {s})"
  unfolding kstar_def 
  by (auto simp: fun_eq_iff kpower_base kpower_id)

lemmas kstar_skip = kstar_id[unfolded skip_def[symmetric]]

lemma kcomp_kstar: "f ; f\<^sup>* = f\<^sup>* ; f"
proof(intro ext set_eqI iffI conjI impI, goal_cases "\<subseteq>" "\<supseteq>")
  case ("\<subseteq>" s s')
  then obtain n where "s' \<in> (f ; kpower f n) s"
    unfolding kcomp_eq kstar_def 
    by auto
  hence "s' \<in> (kpower f n; f) s"
    unfolding kcomp_kpower by simp
  then show "s' \<in> (f\<^sup>*; f) s" 
    unfolding kcomp_eq kstar_def 
    by auto
next
  case ("\<supseteq>" s s')
  then obtain n where "s' \<in> (kpower f n; f) s"
    unfolding kcomp_eq kstar_def 
    by auto
  hence "s' \<in> (f; kpower f n) s"
    unfolding kcomp_kpower by simp
  then show "s' \<in> (f; f\<^sup>*) s" 
    unfolding kcomp_eq kstar_def 
    by auto
qed

lemma fbox_kstar: "|F\<^sup>*] Q = (\<lambda>s. \<forall>n. ( |kpower F n] Q) s)"
  unfolding kstar_def fbox_def
  by expr_auto

lemma fdia_kstar: "|F\<^sup>*\<rangle> Q = (\<lambda>s. \<exists>n. ( |kpower F n\<rangle> Q) s)"
  unfolding kstar_def fdia_def
  by expr_auto

lemma fdia_kstarI: "( |kpower F n\<rangle> Q) s \<Longrightarrow> ( |F\<^sup>*\<rangle> Q) s"
  unfolding fdia_kstar 
  by auto

lemma fbox_kstar_inv: "I \<le> |F] I \<Longrightarrow> I \<le> |F\<^sup>*] I"
  unfolding kstar_def fbox_def 
  apply clarsimp
  apply(unfold le_fun_def, subgoal_tac "\<forall>x. I x \<longrightarrow> (\<forall>s'. s' \<in> F x \<longrightarrow> I s')")
  using kpower_inv[of I F] by blast simp

lemma hoare_kstar_inv: "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} F\<^sup>* \<^bold>{I\<^bold>}"
  by (metis SEXP_def fbox_kstar_inv)

lemma fdia_kstar_inv: "I \<le> |F\<rangle> I \<Longrightarrow> I \<le> |F\<^sup>*\<rangle> I"
  unfolding kstar_def fdia_def apply(clarsimp simp: le_fun_def)
  apply(erule_tac x=x in allE, clarsimp, rule_tac x=s' in exI, simp)
  apply(rule_tac x="kpower F 1 x" in exI, simp add: kpower_base)
  by (rule_tac x=1 in exI, simp add: kpower_base)

lemma le_fbox_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> |F] I" 
  shows "P \<le> |F\<^sup>*] Q"
proof-
  have "I \<le> |F\<^sup>*] I"
    using assms(3) fbox_kstar_inv by blast
  hence "P \<le> |F\<^sup>*] I"
    using assms(1) by auto
  also have "|F\<^sup>*] I \<le> |F\<^sup>*] Q"
    by (rule fbox_iso[OF assms(2)])
  finally show ?thesis .
qed

lemma hoare_kstarI: "`P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} F\<^sup>* \<^bold>{Q\<^bold>}"
  by (rule le_fbox_kstarI) (auto simp: SEXP_def taut_def)

lemma le_fdia_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> |F\<rangle> I" 
  shows "P \<le> |F\<^sup>*\<rangle> Q"
proof-
  have "I \<le> |F\<^sup>*\<rangle> I"
    using assms(3) fdia_kstar_inv by blast
  hence "P \<le> |F\<^sup>*\<rangle> I"
    using assms(1) by auto
  also have "|F\<^sup>*\<rangle> I \<le> |F\<^sup>*\<rangle> Q"
    by (rule fdia_iso[OF assms(2)])
  finally show ?thesis .
qed

lemma fdia_kstar_fixpoint: 
  "`|F\<^sup>*\<rangle> Q \<longleftrightarrow> ( |F\<rangle> |F\<^sup>*\<rangle> Q \<or> Q)`"
  apply (intro pred_iffI)
  subgoal
    unfolding fdia_kstar
    unfolding fdia_def
    unfolding taut_def SEXP_def
    apply (intro allI impI conjI)
    unfolding fdia_def apply clarsimp
    apply (rename_tac s n s')
     apply (subgoal_tac "n \<noteq> 0")
    prefer 2 using kpower_0[of F, simplified fun_eq_iff]
      apply (metis singletonD)
     apply (subgoal_tac "\<exists>m. n = Suc m"; clarsimp)
      prefer 2 using not0_implies_Suc apply blast
    unfolding kpower_Suc kcomp_def apply clarsimp
    apply (rule_tac x=x in exI, simp)
    by (rule_tac x=m in exI, force) (* first conjunct done *)
  subgoal
    unfolding fdia_kstar
    unfolding fdia_def
    unfolding taut_def SEXP_def
    apply (intro allI impI conjI)
    apply (erule disjE; clarsimp?)
    apply (rename_tac s s' n s'')
    apply (rule_tac x="Suc n" in exI, clarsimp simp: kpower_Suc kcomp_def, force)
    by (rule_tac x=0 in exI, clarsimp simp: kpower_0)
  done

lemma fdia_kstar_fixpoint': 
  "( |F\<^sup>*\<rangle> Q) = (\<lambda>s. ( |F\<rangle> |F\<^sup>*\<rangle> Q) s \<or> Q s)"
  "( |F\<^sup>*\<rangle> Q) s = (( |F\<rangle> |F\<^sup>*\<rangle> Q) s \<or> Q s)"
  using fdia_kstar_fixpoint[of F Q]
  unfolding taut_def SEXP_def by blast+

lemma fdia_kstar_strongest: 
  "`@P \<longleftrightarrow> ( |F\<rangle> P) \<or> Q` \<Longrightarrow> `|F\<^sup>*\<rangle> Q \<longrightarrow> @P`"
  unfolding fdia_kstar
  unfolding taut_def SEXP_def
  apply (intro conjI impI allI)
  apply (clarsimp simp: )
  subgoal for s n
    apply (induct n arbitrary: s)
    apply (thin_tac "\<forall>\<s>. P \<s> = (fdia F P \<s> \<or> Q \<s>)")
     apply (clarsimp simp: kpower_0 fdia_def)
    apply (subst fdia_def, clarsimp simp: kpower_Suc)
    apply (subst (asm) fdia_kcomp[unfolded SEXP_def])
    apply (subst (asm) fdia_def[of F "fdia _ _"], clarsimp)
    by blast
  done

(* TODO: revise proofs, names and usage of these |F\<^sup>*\<rangle> Q *)

lemma fdia_unfoldI: "( |F\<rangle> Q) s \<or> ( |F\<rangle> |F\<^sup>*\<rangle> Q) s \<Longrightarrow> ( |F\<^sup>*\<rangle> Q) s"
proof-
  assume "( |F\<rangle> Q) s \<or> ( |F\<rangle> |F\<^sup>*\<rangle> Q) s"
  moreover
  {assume "( |F\<rangle> Q) s"
    hence "( |kpower F (Suc 0)\<rangle> Q) s"
      unfolding fdia_def kpower_base .
    hence "( |F\<^sup>*\<rangle> Q) s"
      using fdia_kstarI[of F "Suc 0"] 
      by blast}
  moreover
  {assume hyp: "( |F\<rangle> |F\<^sup>*\<rangle> Q) s"
    then obtain n s' \<sigma> where fst_step: "\<sigma> \<in> F s" 
      and end_step: "Q s'" and nth_step: "s' \<in> kpower F n \<sigma>"
      by (clarsimp simp: kstar_def fdia_def)
    hence "( |F\<^sup>*\<rangle> Q) s"
    proof (clarsimp simp: kstar_def fdia_def, cases "n=0")
      case True
      then show "\<exists>s'. (\<exists>x. (\<exists>m. x = kpower F m s) \<and> s' \<in> x) \<and> Q s'"
        using nth_step fst_step end_step
        apply (rule_tac x=s' in exI, clarsimp)
        by (rule_tac x="kpower F 1 s" in exI, simp add: kpower_base)
          (rule_tac x=1 in exI, simp add: kpower_base)
    next
      case False
      hence "\<exists>m. \<mu> {kpower F n y |y. y \<in> F s} = kpower F m s"
        apply (rule_tac x="Suc n" in exI, subst kcomp_eq[of F "kpower F n", symmetric])
        by (auto simp: kpower_Suc)
      then show "\<exists>s'. (\<exists>x. (\<exists>m. x = kpower F m s) \<and> s' \<in> x) \<and> Q s'" 
        using nth_step fst_step end_step
        apply (rule_tac x=s' in exI, clarsimp)
        by (rule_tac x="kpower F (Suc n) s" in exI)
          (auto simp add: kpower_Suc kcomp_eq)
    qed
  }
  ultimately show ?thesis
    by blast
qed

lemma nat_strong_induct[case_names zero induct]:
  assumes "P 0"
    and "(\<And>n. (\<And>m. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n))"
  shows "P n"
  using assms
  apply (induct n rule: full_nat_induct)
  by simp (metis Suc_le_mono not0_implies_Suc)

lemma fdia_kstar_variant':
  assumes init: "I (n::nat) s"
    and iter: "`\<forall>m>0. \<exists>n. @(I m) \<le> |F\<rangle> @(I n) \<and> n < m`"
  shows "( |F\<^sup>*\<rangle> @(I 0)) s"
proof(simp add: fdia_kstar)
  have "n = 0 \<Longrightarrow> ( |F\<^sup>*\<rangle> @(I 0)) s"
    using init 
    by (simp add: fdia_kstar)
      (metis fdia_kpower_0)
  have "\<forall>ms. fst ms > 0 \<and> I (fst ms) (snd ms) 
    \<longrightarrow> (\<exists>ns. snd ns \<in> F (snd ms) \<and> I (fst ns) (snd ns) \<and> fst ns < fst ms)"
    using iter apply (clarsimp simp: taut_def fdia_def)
    by (erule_tac x=b in allE, erule_tac x=a in allE, force)
  then obtain f where f_hyp: "\<forall>ms. fst ms > 0 \<and> I (fst ms) (snd ms)
    \<longrightarrow> (snd (f ms) \<in> F (snd ms) \<and> I (fst (f ms)) (snd (f ms)) \<and> fst (f ms) < fst ms)"
    using iter
    apply (atomize_elim)
    by (rule choice_iff'[of "\<lambda>x. fst x > 0 \<and> I (fst x) (snd x)"
          "\<lambda>ms ns. (snd ns) \<in> F (snd ms) \<and> I (fst ns) (snd ns) \<and> fst ns < fst ms", THEN iffD1])
      (auto simp: taut_def SEXP_def)
(* I n s \<Longrightarrow> f (n, s) = (n\<^sub>1, s\<^sub>1) \<and> I n\<^sub>1 s\<^sub>1 \<and> n\<^sub>1 < n \<and> s\<^sub>1 \<in> F s
         \<Longrightarrow> f (n\<^sub>1, s\<^sub>1) = (n\<^sub>2, s\<^sub>2) \<and> I n\<^sub>2 s\<^sub>2 \<and> n\<^sub>2 < n\<^sub>1 \<and> s\<^sub>2 \<in> F s\<^sub>1
         \<Longrightarrow> ...
         \<Longrightarrow> f (n\<^sub>m\<^sub>-\<^sub>1, s\<^sub>m\<^sub>-\<^sub>1) = (n\<^sub>m, s\<^sub>m) \<and> I n\<^sub>m s\<^sub>m \<and> 0 = n\<^sub>m < n\<^sub>m\<^sub>-\<^sub>1 \<and> s\<^sub>m \<in> F s\<^sub>m\<^sub>-\<^sub>1 *)
  have "\<exists>m\<le>n. fst ((f^^m) (n, s)) = 0 \<and> (\<forall>l\<le>m. \<forall>ms. (f ^^ l) (n, s) = ms 
    \<longrightarrow> (snd ms) \<in> kpower F l s \<and> I (fst ms) (snd ms))"
    using init
  proof (induct n arbitrary: s rule: nat_strong_induct)
    case zero
    then show ?case
      by (rule_tac x=0 in exI, simp add: kpower_0)
  next
    case (induct n)
    then obtain m and s' where "s' \<in> F s" "I m s'" "m \<le> n"
      and f_Suc: "(m, s') = f (Suc n, s)"
      using f_hyp[rule_format, of "(Suc n, s)"] 
      by auto
    then obtain k and s'' where "((f ^^ k) (m, s')) = (0, s'')" and "k \<le> m"
      and "\<forall>l\<le>k. snd ((f ^^ l) (m, s')) \<in> kpower F l s' 
        \<and> I (fst ((f ^^ l) (m, s'))) (snd ((f ^^ l) (m, s')))"
      using induct.hyps[OF \<open>m \<le> n\<close> \<open>I m s'\<close>, simplified]
      by auto (metis prod.collapse)
    thus ?case 
      using \<open>m \<le> n\<close>
      apply (rule_tac x="Suc k" in exI)
      apply (clarsimp simp add: funpow_Suc_right f_Suc simp del: funpow.simps(2))
      subgoal for l
        apply (cases l; simp add: kpower_0 kpower_Suc kcomp_def 
            funpow_Suc_right del: funpow.simps(2))
        using induct.prems apply blast
        using \<open>s' \<in> F s\<close> by blast
      done
  qed
  then obtain m where "fst ((f^^m) (n, s)) = 0" 
    and "\<forall>l\<le>m. \<forall>ms. (f ^^ l) (n, s) = ms \<longrightarrow> (snd ms) \<in> kpower F l s \<and> I (fst ms) (snd ms)"
    and "m \<le> n"
    by blast
  then show "\<exists>n. ( |kpower F n\<rangle> @(I 0)) s"
    by (rule_tac x=m in exI)
      (metis SEXP_def dual_order.refl fdia_def)
qed

lemma fdia_kstar_convergence:
  fixes P::"real \<Rightarrow> 'a \<Rightarrow> bool"
  defines "Q \<equiv> (\<lambda>s. \<exists>r::real\<le>0. P r s)"
  assumes init: "P r s"
    and iter: "`\<forall>r>0. @(P r) \<longrightarrow> ( |F\<rangle> @(P (r - 1)))`"
  shows "( |F\<^sup>*\<rangle> Q) s"
proof-
  have iter': "\<And>s. \<forall>r>0. P r s \<longrightarrow> ( |F\<rangle> @(P (r - 1))) s"
    using iter by (auto simp: taut_def)
  have init': "P r s"
    using init by expr_simp
  then obtain r where "P r s"
    by blast
  hence "r \<le> 0 \<Longrightarrow> Q s"
    using assms by blast
  hence case1: "r \<le> 0 \<Longrightarrow> ( |F\<^sup>*\<rangle> Q) s"
    by (clarsimp simp: fdia_def)
      (rule_tac x=s in exI, simp add: in_kstar_self)
  have obs_induct: 
    "`\<forall>t::real. t - \<guillemotleft>n\<guillemotright> > 0 \<longrightarrow> @(P t) \<longrightarrow> ( |kpower F n\<rangle> @(P (t - n)))`" for n::nat
  proof (induct n )
    case 0
    then show ?case 
      using iter'[rule_format]
      by (simp add: kpower_base fdia_def taut_def)
  next
    case (Suc n)
    show ?case
    proof(clarsimp simp only: taut_def, clarsimp)
      fix s t
      assume hyps: "1 + real n < t" "P t s"
      hence "t > 0" "0 < t - real n"
        by auto
      hence induct': "\<And>m s t. 0 < t - real n \<Longrightarrow> P t s 
        \<Longrightarrow> ( |kpower F n\<rangle> @(P (t - real n))) s"
        using Suc
        by expr_simp
      hence case_eq0: "n = 0 \<Longrightarrow> ( |kpower F (Suc n)\<rangle> @(P (t - (1 + real n)))) s"
        using iter'[rule_format, OF \<open>t > 0\<close> \<open>P t s\<close>]
        by (subst kpower_Suc, subst fdia_kcomp)
          (simp add: kpower_base skip_def[symmetric] fdia_skip)
      have "( |kpower F n\<rangle> @(P (t - real n))) s"
        using hyps induct'[OF \<open>0 < t - real n\<close>]
        by force
      moreover note iter'[rule_format, OF \<open>0 < t - real n\<close>]
      ultimately have "n \<noteq> 0 \<Longrightarrow> ( |kpower F (Suc n)\<rangle> @(P (t - (1 + real n)))) s"
        apply -
        apply (frule not0_implies_Suc, clarsimp)
        apply (subst kpower_Suc, subst fdia_kcomp)
        apply (subst (asm) kpower_Suc, subst (asm) fdia_kcomp)
        apply (rule fdia_mono, force)
        apply (subst kpower_Suc, subst kcomp_kpower, subst fdia_kcomp)
        by (rule fdia_mono) (auto simp: taut_def diff_add_eq_diff_diff_swap)
      thus "( |kpower F (Suc n)\<rangle> @(P (t - (1 + real n)))) s"
        using case_eq0 by blast
    qed
  qed
  moreover
  {assume "r > 0"
    then obtain n::nat where r_hyps: "Suc n \<ge> r" "r - n > 0"
      using pos_real_within_Suc 
      by auto
    hence "( |kpower F n\<rangle> @(P (r - n))) s"
      using obs_induct[unfolded taut_def, rule_format, 
          simplified, rule_format, OF _ \<open>P r s\<close>]
      by simp
    hence "( |F\<^sup>*\<rangle> @(P (r - n))) s"
      using fdia_kstarI[of F "n"] 
      by force
    hence "( |F\<^sup>*\<rangle> @(P (r - (Suc n)))) s"
      apply (intro fdia_unfoldI disjI2)
      apply (subst fdia_kcomp[symmetric])
      apply (subst kcomp_kstar, subst fdia_kcomp)
      apply (rule fdia_mono, force)
      using iter'[rule_format, OF \<open>r - n > 0\<close>]
      by (auto simp: taut_def diff_add_eq_diff_diff_swap)
    hence "( |F\<^sup>*\<rangle> @Q) s"
      unfolding assms 
      apply (rule fdia_mono)
      using r_hyps
      by (clarsimp simp: taut_def)
        (rule_tac x="r - Suc n" in exI, force)}
  ultimately show "( |F\<^sup>*\<rangle> @Q) s"
    using case1 by linarith
qed

lemma fdia_kstar_real_variantI:
  fixes P::"real \<Rightarrow> 'a \<Rightarrow> bool"
  assumes init: "P r s"
    and iter: "`\<forall>r>0. @(P r) \<longrightarrow> ( |F\<rangle> @(P (r - 1)))`"
    and "`(\<exists>r\<le>0. @(P r)) \<longrightarrow> Q`"
  shows "( |F\<^sup>*\<rangle> Q) s"
  by (rule fdia_mono(1)[OF fdia_kstar_convergence[OF assms(1,2)] assms(3)])

lemma fdia_kstar_variantI: "`P \<longrightarrow> @(V k)` \<Longrightarrow> `\<forall>k. @(V k) \<le> |F\<rangle> (@(V (k-1)))` 
  \<Longrightarrow> `(\<exists>k\<le>0. @(V k)) \<longrightarrow> Q` \<Longrightarrow> P \<le> |F\<^sup>*\<rangle> Q" for k::int
  apply (subst impl_eq_leq[symmetric])
  apply (subst taut_def, subst SEXP_def)
  apply (clarify)
  apply (rule_tac P="\<lambda>r s. V \<lfloor>r\<rfloor> s" and r="real_of_int k" in fdia_kstar_real_variantI)
    apply (clarsimp simp: taut_def)
   apply (clarsimp simp: taut_def)
  apply (thin_tac "`P \<longrightarrow> @(V k)`", thin_tac "`\<forall>k. @(V k) \<le> |F\<rangle> (@(V (k-1)))`")
  apply (clarsimp simp: taut_def)
  apply (erule_tac x=s in allE)
  by (erule impE, rule_tac x="\<lfloor>r\<rfloor>" in exI, simp_all)

lemma kstar_one_or_zero_or_more: "P\<^sup>* = P \<sqinter> P\<^sup>*"
  unfolding nondet_choice_def kstar_def apply auto
  apply (simp add:fun_eq_iff, auto)
  by (metis kpower_Suc_0)

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

lemma kstar_abort_eq: "(abort)\<^sup>* = skip \<sqinter> abort"
  by (simp add: kstar_abort nondet_choice_abort_unit)

subsection \<open> Finite iteration of at least one \<close>

definition kstar_one :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^sup>+)" [1000] 999)
  where [prog_defs]: "(f\<^sup>+) s = (f ; (f\<^sup>*)) s"

term "skip\<^sup>+"

lemma "P\<^sup>+ = P ; P\<^sup>*"
  unfolding kstar_one_def by auto

subsection \<open> Loops with annotated invariants \<close>

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "loopi F I \<equiv> (F\<^sup>*)"

syntax "_loopi" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("LOOP _ INV _" [0, 63] 64)
translations "_loopi F I" == "CONST loopi F (I)\<^sub>e"

lemma change_loopI: "LOOP X INV G = LOOP X INV I"
  unfolding loopi_def by simp

lemma fbox_loopI: "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |F] I \<Longrightarrow> P \<le> |LOOP F INV I] Q"
  unfolding loopi_def using le_fbox_kstarI[of "P"] by (auto simp: SEXP_def)

lemma in_fbox_loopI: "I s \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> ( |R] @(I)) \<Longrightarrow> ( |LOOP R INV @I] (@Q)) s"
  using fbox_loopI[of I I Q R]
  by (clarsimp simp: le_fun_def)

lemma fbox_loopI': "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> fbox F I \<Longrightarrow> P \<le> fbox (loopi F I) Q"
  by (metis clarify_fbox le_fbox_kstarI loopi_def)

lemma hoare_loopI: "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{P\<^bold>} LOOP F INV I \<^bold>{Q\<^bold>}"
  by (rule fbox_loopI) (auto simp: SEXP_def taut_def)

lemma fdia_loopI: "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |F\<rangle> I \<Longrightarrow> P \<le> |LOOP F INV I\<rangle> Q"
  unfolding loopi_def using le_fdia_kstarI[of "P"] by (auto simp: SEXP_def)

lemma hoare_loop_seqI: "\<^bold>{I\<^bold>} F \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} G \<^bold>{I\<^bold>} \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<longrightarrow> Q` 
  \<Longrightarrow> \<^bold>{P\<^bold>} LOOP (F ; G) INV I \<^bold>{Q\<^bold>}"
  by (rule fbox_loopI, simp_all add: wlp refine_iff_implies)
     (metis (full_types) fbox_iso order.trans refine_iff_implies)

lemma fbox_loopI_break: 
  "P \<le> |Y] I \<Longrightarrow> I \<le> |X] I \<Longrightarrow> I \<le> Q \<Longrightarrow> P \<le> |Y ; (LOOP X INV I)] Q"
  apply(subst fbox_to_hoare, rule hoare_kcomp, force)
  by (rule hoare_loopI, auto simp: SEXP_def taut_def)

lemma hoare_loopI_break: 
  "\<^bold>{I\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} Y \<^bold>{I\<^bold>} \<Longrightarrow> `I \<longrightarrow> Q` \<Longrightarrow> \<^bold>{P\<^bold>} (Y ; (LOOP X INV I)) \<^bold>{Q\<^bold>}"
  by (rule hoare_kcomp, force) (rule hoare_loopI, simp_all)


subsection \<open> While loop \<close>

definition while :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where [prog_defs]: "while T X \<equiv> (\<questiondown>T? ; X)\<^sup>* ; \<questiondown>\<not>T?"

syntax "_while" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("WHILE _ DO _" [0,64] 64)
translations "WHILE T DO X" == "CONST while (T)\<^sub>e X"

lemma hoare_while:
  "\<^bold>{I \<and> T\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I\<^bold>} (WHILE T DO X) \<^bold>{\<not> T \<and> I\<^bold>}"
  unfolding while_def 
  apply (simp add: fbox_test fbox_kcomp)
  apply (rule_tac p\<^sub>2=I and q\<^sub>2=I in hoare_conseq)
    prefer 3 apply expr_simp
  prefer 2 apply expr_simp
  apply (rule_tac I="I" in hoare_kstarI)
      apply expr_simp
   apply expr_simp
  apply (rule_tac R="(I \<and> T)\<^sup>e" in hoare_kcomp)
  by (auto simp: fbox_test fbox_kcomp)

lemma hoare_whileI: "\<^bold>{I \<and> T\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> `P \<longrightarrow> I` \<Longrightarrow> `I \<and> \<not> T \<longrightarrow> Q`
  \<Longrightarrow> \<^bold>{P\<^bold>} WHILE T DO X INV I \<^bold>{Q\<^bold>}"
  by (rule hoare_conseq, subst invar_def)
    (rule hoare_while, assumption, auto simp: taut_def)

lemma fbox_whileI: "P \<le> I \<Longrightarrow> (I \<and> T)\<^sub>e \<le> |X] I \<Longrightarrow> (I \<and> \<not> T)\<^sub>e \<le> Q 
  \<Longrightarrow> P \<le> |WHILE T DO X INV I] Q"
  using hoare_whileI[unfolded fbox_to_hoare[symmetric], of I T X P Q] 
  by expr_auto

lemma hoare_whileI_break: 
  "\<^bold>{I \<and> T\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} Y \<^bold>{I\<^bold>} \<Longrightarrow> `I \<and> \<not> T \<longrightarrow> Q` \<Longrightarrow> \<^bold>{P\<^bold>} Y ; WHILE T DO X INV I \<^bold>{Q\<^bold>}"
  by (rule hoare_kcomp, force)
    (rule hoare_whileI; expr_auto)

lemma fdia_while_variantI:
  fixes V :: "int \<Rightarrow> 's \<Rightarrow> bool" and T :: "'s \<Rightarrow> bool"
  shows "`P \<longrightarrow> @(V k)` 
  \<Longrightarrow> `\<forall>k>0. @(V k) \<longrightarrow> T`
  \<Longrightarrow> `\<forall>k::int. @(V k) \<le> |X\<rangle> @(V (k-1))` 
  \<Longrightarrow> `(\<exists>k\<le>0. @(V k)) \<longrightarrow> \<not> T \<and> Q` \<Longrightarrow> P \<le> |WHILE T DO X\<rangle> Q"
  apply (simp add: while_def fdia_kcomp fdia_test)
  apply (cases "k \<le> 0", clarsimp simp: taut_def fdia_kstar)
  apply (erule_tac P="\<lambda>s. (\<exists>k\<le>0. V k s) \<longrightarrow> \<not> T s \<and> Q s" and x=x in allE)
  apply (erule impE, force, rule_tac x=0 in exI, simp add: fdia_kpower_0)
  apply (rule_tac P\<^sub>2="V k" and Q\<^sub>2="V 0" in fdia_conseq)
    prefer 3 apply (fastforce simp: taut_def)
   prefer 2 apply simp
  apply (clarsimp simp: impl_eq_leq[symmetric] taut_def)
  apply (rule fdia_kstar_variant'[of V _ _ "\<questiondown>T? ; X", simplified, of "nat k"])
   apply simp
  apply (clarsimp simp add: taut_def)
  apply (rule_tac x="m - 1" in exI, clarsimp)
  apply (rename_tac s s' m)
  apply (erule_tac P="\<lambda>s. \<forall>k. V k s \<longrightarrow> ( |X\<rangle> @(V (k - 1))) s" and x=s' in allE)
  apply (erule_tac x="int m" in allE, simp add: fdia_kcomp fdia_test)
  apply (rule conjI)
  by force 
    (metis One_nat_def Suc_leI of_nat_1 of_nat_diff)

lemma While_False_eq_skip:
  "WHILE False DO X = skip"
  unfolding kcomp_def while_def test_def skip_def
  by (auto, metis UN_singleton comp_apply kstar_empty)

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

lemma hoare_while_unroll_kcomp:
  assumes "\<^bold>{P\<^bold>} IF T THEN X ELSE skip \<^bold>{Q\<^bold>}" "\<^bold>{Q\<^bold>} WHILE T DO X \<^bold>{R\<^bold>}" 
  shows "\<^bold>{P\<^bold>} WHILE T DO X \<^bold>{R\<^bold>}"
  using assms WHILE_unroll_IF
  by (metis hoare_kcomp) 

lemma hoare_ineffective_while:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{\<not> T\<^bold>}"
  shows "\<questiondown>P? ; X ; WHILE T DO Y = \<questiondown>P? ; X"
proof -
  have "\<questiondown>P? ; X ; WHILE T DO Y = \<questiondown>P? ; X ; \<questiondown>\<not>T? ; WHILE T DO Y"
    using assms hoare_insert_post_test by metis
  also have "... = \<questiondown>P? ; X ; \<questiondown>\<not>T?"
    using negative_test_WHILE_DO_absorb kcomp_assoc by metis
  also have "... = \<questiondown>P? ; X"
    using assms hoare_insert_post_test by metis
  finally show ?thesis .
qed

lemma hoare_pre_not_while:
  assumes "`P \<longrightarrow> \<not> T`" "`P \<longrightarrow> Q`"
  shows "\<^bold>{P\<^bold>} (WHILE T DO X) \<^bold>{Q\<^bold>}"
proof -
  have "\<^bold>{P\<^bold>} (WHILE T DO X) \<^bold>{Q\<^bold>} = \<^bold>{P\<^bold>} \<questiondown>\<not> T? \<sqinter> (\<questiondown>T? ; X) ; WHILE T DO X \<^bold>{Q\<^bold>}"
    by (metis WHILE_unroll)

  have "\<^bold>{P\<^bold>} \<questiondown>\<not> T? \<sqinter> (\<questiondown>T? ; X) ; WHILE T DO X \<^bold>{Q\<^bold>}"
    apply (rule hoare_choice)
     apply (metis (mono_tags, lifting) SEXP_def assms(2) fbox_test predicate1I taut_def)
    by (metis (mono_tags, lifting) SEXP_def assms(1) fbox_kcomp fbox_test predicate1I taut_def)
  then show ?thesis  
    by (metis WHILE_unroll)
qed

lemma hoare_pre_not_while_seq:
  assumes "`P \<longrightarrow> \<not> T`" "`P \<longrightarrow> Q`" "\<^bold>{Q\<^bold>} Z \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} (WHILE T DO X) ; Z \<^bold>{Q\<^bold>}"
  by (meson assms(1) assms(2) assms(3) hoare_kcomp hoare_pre_not_while)

subsection \<open> Do while loop \<close>

syntax "_do_while" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("DO _ WHILE _" [0,64] 64)
translations "DO X WHILE T" => "X ; CONST while (T)\<^sub>e X"

term "DO skip WHILE True"

lemma hoare_do_while:
  assumes "\<^bold>{I\<^bold>} A \<^bold>{I \<and> T\<^bold>}" and "\<^bold>{I \<and> T\<^bold>} X \<^bold>{I\<^bold>}"
  shows "\<^bold>{I\<^bold>} (A ; WHILE T DO X) \<^bold>{\<not> T \<and> I\<^bold>}"
  using assms
  by (metis (mono_tags) hoare_conj_pos hoare_kcomp hoare_while)

subsection \<open> Framing \<close>

named_theorems closure

definition frame :: "'s scene \<Rightarrow> 's prog \<Rightarrow> 's prog"
  where [prog_defs]: "frame a P = (\<lambda> s. {s'. s = cp\<^bsub>a\<^esub> s s' \<and> s' \<in> P s})"

syntax "_frame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [65] 65)
translations "_frame a P" == "CONST frame a P"

lemma frame_UNIV: "\<Sigma>:[P] = P"
  by (simp add: frame_def lens_defs)

lemma frame_skip: "idem_scene a \<Longrightarrow> a:[skip] = skip"
  by (auto simp add: skip_def frame_def fun_eq_iff)
  
lemma frame_assign_in:
  assumes "vwb_lens x" "idem_scene a" "\<lbrakk>x\<rbrakk>\<^sub>\<sim> \<le> a"
  shows "a:[x ::= v] = x ::= v"
  using assms
  by (auto simp add: prog_defs expr_defs fun_eq_iff put_scene_override_le)
  
definition not_modifies :: "'s prog \<Rightarrow> ('a, 's) expr \<Rightarrow> bool" where
  "not_modifies P e = (\<forall> s s'. s' \<in> P s \<longrightarrow> e s' = e s)" 

syntax "_not_modifies" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "nmods" 30)
translations "_not_modifies P e" == "CONST not_modifies P (e)\<^sub>e"

(* FIXME: The following rule is an inefficient way to calculate modification; 
  replace with scene membership laws. *)

lemma nmods_union [closure]:
  assumes "P nmods e" "P nmods f"
  shows "P nmods (e, f)"
  using assms
  by (auto simp add: not_modifies_def prog_defs)

lemma nmods_skip [closure]: "skip nmods e"
  by (simp add: not_modifies_def prog_defs scene_equiv_def)

lemma nmods_seq [closure]:
  assumes "P nmods e" "Q nmods e"
  shows "(P ; Q) nmods e"
  using assms 
  by (auto simp add: not_modifies_def prog_defs scene_equiv_def)

lemma nmods_if [closure]:
  assumes "P nmods e" "Q nmods e"
  shows "IF b THEN P ELSE Q nmods e"
  using assms by (auto simp add: not_modifies_def prog_defs)

lemma nmods_choice [closure]:
  assumes "P nmods e" "Q nmods e"
  shows "P \<sqinter> Q nmods e"  
  using assms by (auto simp add: not_modifies_def prog_defs)

lemma nmods_Choice [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P(i) nmods e"
  shows "(\<Sqinter> i\<in>I. P(i)) nmods e"
  using assms
  by (auto simp add: Nondet_choice_def not_modifies_def)

lemma nmods_kpower [closure]:
  assumes "P nmods e"
  shows "(kpower P n) nmods e"
proof (induct n)
  case 0
  then show ?case
    by (metis kpower_0' nmods_skip) 
next
  case (Suc n)
  then show ?case
    by (metis assms kpower_Suc' nmods_seq)
qed

lemma nmods_star [closure]:
  assumes "P nmods e"
  shows "P\<^sup>* nmods e"
  by (simp add: assms kstar_alt nmods_Choice nmods_kpower)

lemma nmods_loop [closure]:
  assumes "P nmods e"
  shows "LOOP P INV B nmods e"
  by (simp add: assms loopi_def nmods_star)

lemma nmods_test [closure]:
  "\<questiondown>b? nmods e"
  by (auto simp add: not_modifies_def prog_defs scene_equiv_def)

lemma nmods_assigns [closure]:
  assumes "\<sigma> \<dagger> (e)\<^sub>e = (e)\<^sub>e" 
  shows "\<langle>\<sigma>\<rangle> nmods e"
  using assms
  by (expr_simp add: not_modifies_def assigns_def put_scene_override_indep)

lemma nmods_assign:
  assumes "(a)\<^sub>e\<lbrakk>e/x\<rbrakk> = (a)\<^sub>e"
  shows "x ::= e nmods a"
  by (metis SEXP_def assms nmods_assigns)

lemma nmods_via_fbox:
  "\<lbrakk> vwb_lens x; \<And> v. |P] (e = \<guillemotleft>v\<guillemotright>) = (e = \<guillemotleft>v\<guillemotright>)\<^sub>e \<rbrakk> \<Longrightarrow> P nmods e"
  by (expr_simp add: fbox_def not_modifies_def)

text \<open> Important principle: If @{term P} does not modify @{term a}, and predicate @{term b} does
  not refers only variables outside of @{term a} then @{term b} is an invariant of @{term P}. \<close>

lemma nmods_frame_law:
  assumes "S nmods I" "\<^bold>{P\<^bold>}S\<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> I\<^bold>}S\<^bold>{Q \<and> I\<^bold>}"
  using assms
  by (auto simp add: prog_defs fbox_def expr_defs not_modifies_def)

lemma nmods_frame_law'':
  assumes "S nmods I" "\<^bold>{P\<^bold>}S\<^bold>{Q\<^bold>}"
  shows "\<^bold>{I \<and> P\<^bold>}S\<^bold>{I \<and> Q\<^bold>}"
  using assms 
  by (auto simp add: prog_defs fbox_def expr_defs not_modifies_def)

lemma nmods_invariant:
  assumes "P nmods b"
  shows "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  using assms
  by (auto simp add: prog_defs fbox_def expr_defs not_modifies_def)

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

lemma nmods_set:
  assumes "v \<in> s" "P nmods \<guillemotleft>s\<guillemotright>"
  shows "P nmods \<guillemotleft>v\<guillemotright>"
  using assms unfolding not_modifies_def by auto

lemma nmods_subset':
  assumes "v \<subseteq> s" "P nmods \<guillemotleft>s\<guillemotright>"
  shows "P nmods \<guillemotleft>v\<guillemotright>"
  using assms unfolding not_modifies_def by auto

method nmods_auto = 
  (auto intro: nmods_set nmods_subset)?;
  ( 
      (
        (rule nmods_assign ; expr_simp)
      | (rule nmods_if) 
      | (rule nmods_while)
      | (rule nmods_seq) 
      | (rule nmods_assign) 
      | (rule nmods_skip)
      | (rule nmods_choice)
      | (rule nmods_test)
      | (rule nmods_star)
      | (rule nmods_invariant ; (auto intro!: nmods_set nmods_subset nmods_subset')?)
    )
  )+

end