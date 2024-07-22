theory Hoare_Help

imports
  "Hybrid-Verification.Diff_Dyn_Logic"
begin

lemma hoare_stengthen_post:
  assumes "`Q \<longrightarrow> R`" and "\<^bold>{P\<^bold>} G \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P\<^bold>} G \<^bold>{R\<^bold>}"
  using assms Diff_Dyn_Logic.strengthen by blast

lemma strenghten_pre_post:
  assumes "\<^bold>{P\<^bold>} F \<^bold>{Q\<^bold>}"
  shows "\<^bold>{P \<and> \<guillemotleft>I\<guillemotright>\<^bold>} F \<^bold>{Q \<and> \<guillemotleft>I\<guillemotright>\<^bold>}"
  using assms fbox_def by auto

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


(*lemma hoare_strengthen_post:
  assumes "\<^bold>{P\<^bold>} X \<^bold>{Q \<and> T \<and> R\<^bold>}"
  shows "\<^bold>{P\<^bold>} X \<^bold>{Q \<and> R\<^bold>}"
  using assms
  by (simp add: hoare_conj_pos)*)
  
lemma hoare_strengthen_pos_universal:
  assumes "`U`" "\<^bold>{P\<^bold>} X \<^bold>{R\<^bold>}" 
  shows "\<^bold>{P\<^bold>} X \<^bold>{U \<and> R\<^bold>}"
  using assms 
  by (simp add: refine_iff_implies taut_def)

lemma hoare_weaken_post:
  assumes "\<^bold>{P\<^bold>} S \<^bold>{Q \<and> R\<^bold>}"
  shows "\<^bold>{P\<^bold>} S \<^bold>{R\<^bold>}"
  using assms
  by (simp add: hoare_conj_pos)

lemma hoare_assoc_post:
  assumes "\<^bold>{P\<^bold>} S \<^bold>{(Q \<and> R) \<and> T\<^bold>}"
  shows "\<^bold>{P\<^bold>} S \<^bold>{Q \<and> (R \<and> T)\<^bold>}"
  using assms
  by (simp add: hoare_conj_pos)

lemma hoare_assoc_pre:
  assumes "\<^bold>{(P \<and> Q) \<and> R\<^bold>} S \<^bold>{T\<^bold>}"
  shows "\<^bold>{P \<and> (Q \<and> R)\<^bold>} S \<^bold>{T\<^bold>}"
  using assms
  by (simp add: hoare_conj_pos)


lemma 
  assumes "\<^bold>{P\<^bold>} X \<^bold>{\<not>T\<^bold>}" "X \<noteq> abort"
  shows "X ; ((IF T THEN X ELSE skip) ; E)\<^sup>* = (X ; WHILE \<not> T DO E)\<^sup>*"
  oops (* TODO: This does not hold, even if X \<noteq> abort. Let X = x::=e,
          then the lhs always establishes this, whereas the rhs also has
          the possibility for skip!

          NB X cannot be abort as kstar satisfies the following law. *)







end