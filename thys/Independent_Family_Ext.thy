theory Independent_Family_Ext
  imports Main "HOL-Probability.Independent_Family"
begin

lemma set_comp_subsetI: "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> {f x|x. P x} \<subseteq> B"
  by blast

lemma set_comp_cong: 
  assumes "\<And>x. P x \<Longrightarrow> f x = h (g x)"
  shows "{f x| x. P x} = h ` {g x| x. P x}"
  using assms by (simp add: setcompr_eq_image, auto)

lemma indep_sets_distr:
  assumes "f \<in> measurable M N"
  assumes "prob_space M"
  assumes "prob_space.indep_sets M (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` A i) I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets N"
  shows "prob_space.indep_sets (distr M N f) A I"
proof -
  define F where "F = (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` A i)"
  have indep_F: "prob_space.indep_sets M F I"
    using F_def assms(3) by simp

  have sets_A: "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets N"
    using assms(4) by blast

  have indep_A: "\<And>A' J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> 
  \<forall>j\<in>J. A' j \<in> A j \<Longrightarrow> measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
  proof -
    fix A' J
    assume a1:"J \<subseteq> I"
    assume a2:"finite J"
    assume a3:"J \<noteq> {}"
    assume a4:"\<forall>j \<in> J. A' j \<in> A j"

    define F' where "F' = (\<lambda>i. f -` A' i \<inter> space M)"

    have "\<Inter> (F' ` J) = f -` (\<Inter> (A' ` J)) \<inter> space M" 
      apply (rule order_antisym)
      apply (rule subsetI, simp add:F'_def a3)
      by (rule subsetI, simp add:F'_def a3)
    moreover have "\<Inter> (A' ` J) \<in> sets N" 
      using a4 a1 sets_A 
      by (metis a2 a3 sets.finite_INT subset_iff)
    ultimately have r1: "measure (distr M N f) (\<Inter> (A' ` J)) = measure M (\<Inter> (F' ` J))" 
      using assms(1) measure_distr by metis

    have "\<And>j. j \<in> J \<Longrightarrow> F' j \<in> F j"
      using a4 F'_def F_def by blast
    hence r2:"measure M (\<Inter> (F' ` J)) = (\<Prod>j\<in> J. measure M (F' j))"
      using indep_F prob_space.indep_setsD assms(2) a1 a2 a3 by metis

    have "\<And>j. j \<in> J \<Longrightarrow> F' j =  f -` A' j  \<inter> space M" 
      by (simp add:F'_def)
    moreover have "\<And>j. j \<in> J \<Longrightarrow> A' j \<in> sets N" 
      using a4 a1 sets_A by blast
    ultimately have r3:"\<And>j. j \<in> J \<Longrightarrow> measure M (F' j) = measure (distr M N f) (A' j)"
      using assms(1) measure_distr by metis

    show "measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
      using r1 r2 r3 by auto
  qed

  show ?thesis 
    apply (rule prob_space.indep_setsI)
    using assms apply (simp add:prob_space.prob_space_distr)
    apply (simp add:sets_A)
    using indep_A by blast
qed

lemma indep_vars_distr:
  assumes "f \<in> measurable M N"
  assumes "\<And>i. i \<in> I \<Longrightarrow> X' i \<in> measurable N (M' i)"
  assumes "prob_space.indep_vars M M' (\<lambda>i. (X' i) \<circ> f) I"
  assumes "prob_space M"
  shows "prob_space.indep_vars (distr M N f) M' X' I"
proof -
  have b1: "f \<in> space M \<rightarrow> space N" using assms(1) by (simp add:measurable_def)
  have a:"\<And>i. i \<in> I \<Longrightarrow> {(X' i \<circ> f) -` A \<inter> space M |A. A \<in> sets (M' i)} = (\<lambda>a. f -` a \<inter> space M) ` {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}"
    apply (rule set_comp_cong)
    apply (rule order_antisym, rule subsetI, simp) using b1 apply fast
    by (rule subsetI, simp) 
  show ?thesis 
  using assms apply (simp add:prob_space.indep_vars_def2 prob_space.prob_space_distr)
   apply (rule indep_sets_distr)
  apply (simp add:a cong:prob_space.indep_sets_cong)
  apply (simp add:a cong:prob_space.indep_sets_cong)
   apply (simp add:a cong:prob_space.indep_sets_cong)
  using assms(2)  measurable_sets by blast
qed

lemma enn2real_prod:
  assumes "finite J"
  shows "(\<Prod>j \<in> J. enn2real (f j)) = enn2real( \<Prod>j \<in> J. f j)"
  using assms apply (induction J rule:finite_induct)
  by (simp add:enn2real_mult)+


lemma lift_rv:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space.random_variable (\<Omega> i) (M' i) (X' i)"
  shows "\<And>i. i \<in> I \<Longrightarrow> prob_space.random_variable (\<Pi>\<^sub>M i \<in> I. \<Omega> i) (M' i) (\<lambda>\<omega>. X' i (\<omega> i))"
  using assms by measurable

lemma pow_unit_cases:
  assumes "P {x}"
  assumes "P {}"
  shows "\<forall>y \<in> Pow {x}. P y"
  by (metis PowD assms(1) assms(2) subset_singleton_iff)

lemma indep_vars_product_space:
  assumes "J \<noteq> {}"
  assumes "f ` J \<subseteq> I"
  assumes "inj_on f J"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  shows "prob_space.indep_vars (PiM I \<Omega>) (\<Omega> \<circ> f) (\<lambda>i \<omega>. (\<omega> (f i))) J"
proof -
  define \<Omega>' where "\<Omega>' = (\<lambda>i. (if i \<in> I then \<Omega> i else count_space {undefined}))"
  have "prob_space (count_space {undefined})"
    by (rule prob_spaceI, simp)
  hence prob_space_i: "\<And>i. prob_space (\<Omega>' i)" 
    using assms  apply (simp add:\<Omega>'_def) by blast

  have t:"\<And>i. f i \<notin> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> (f i)) -` {undefined} \<inter> space (Pi\<^sub>M I \<Omega>') = space (Pi\<^sub>M I \<Omega>')" 
    apply (simp add:space_PiM PiE_def Pi_def)
    apply (rule order_antisym)
    by (rule subsetI, simp add:extensional_def)+
  have "\<And>i. f i \<notin> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> (f i)) \<in> measurable (PiM I \<Omega>') (count_space {undefined})" 
    apply (simp add: measurable_def, rule conjI)
     apply (simp add:space_PiM PiE_def Pi_def extensional_def)
    apply (rule pow_unit_cases)
    by (simp add:t)+

  hence "\<And>i. f i \<notin> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> (f i)) \<in> measurable (PiM I \<Omega>') (\<Omega>' (f i))"
    by (simp add:\<Omega>'_def)
  moreover have "\<And>i. f i \<in> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> (f i)) \<in> measurable (PiM I \<Omega>') (\<Omega>' (f i))"
    by measurable

  ultimately have meas: "\<And>i. (\<lambda>\<omega>. \<omega> (f i)) \<in> measurable (PiM I \<Omega>') (\<Omega>' (f i))"
    by blast
  
  interpret product_prob_space "\<Omega>'"
    apply (simp add:product_prob_space_def product_sigma_finite_def product_prob_space_axioms_def)
    using prob_space_i prob_space_imp_sigma_finite by blast

  have a:"prob_space (Pi\<^sub>M I \<Omega>')" using prob_space_i by (simp add:prob_space_PiM)


  have "prob_space.indep_vars (PiM I \<Omega>') (\<Omega>' \<circ> f) (\<lambda>i \<omega>. (\<omega> (f i))) J" 
    apply (subst prob_space.indep_vars_iff_distr_eq_PiM)
       apply (simp add:a)
      apply (simp add:assms)
    apply (simp add:meas)
    apply (simp add:comp_def)
    apply (subst distr_PiM_reindex)
       apply (simp add:prob_space_i)
      using assms apply blast
     using assms apply blast
    apply (rule PiM_cong, simp)
    apply (subst product_prob_space.PiM_component)
      using product_prob_space_axioms apply blast
     using assms apply blast
    by simp
  moreover have "\<And>i. i \<in> J \<Longrightarrow> (\<Omega>' \<circ> f) i = (\<Omega> \<circ> f) i" 
    using assms(2) by (simp add:\<Omega>'_def image_subset_iff)
  ultimately have "prob_space.indep_vars (PiM I \<Omega>') (\<Omega> \<circ> f) (\<lambda>i \<omega>. (\<omega> (f i))) J"
    by (simp  cong:indep_vars_cong)
  moreover have "Pi\<^sub>M I \<Omega> = Pi\<^sub>M I \<Omega>'" 
    by (rule PiM_cong, simp, simp add:\<Omega>'_def)
  ultimately
  show ?thesis by simp
qed


lemma indep_pointwise:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i. i \<in> J \<Longrightarrow> X' i \<in> measurable (PiM I M) (M' i)"
  assumes "\<And>\<omega>1 \<omega>2 i. i \<in> J \<Longrightarrow> \<omega>1 (f i) = \<omega>2 (f i) \<Longrightarrow>  X' i \<omega>1 = X' i \<omega>2"
  assumes "f ` J \<subseteq> I"
  assumes "inj_on f J"
  assumes "J \<noteq> {}"
  shows "prob_space.indep_vars (PiM I M) M' X' J"
proof -
  have c:"prob_space (PiM I M)" using assms(1) by (simp add:prob_space_PiM)
  hence "space (PiM I M) \<noteq> {}" using prob_space.not_empty by blast
  then obtain z where z_def: "z \<in> space (PiM I M)" by blast
  define Y where "Y = (\<lambda>i u. X' i (\<lambda>k. if k = f i then u else z k))"
  have b:"\<And>i. i \<in> J \<Longrightarrow> Y i \<circ> (\<lambda>\<omega>. \<omega> (f i)) = X' i"
    apply (simp add:Y_def comp_def)
    apply (rule ext)
    by (rule assms(3), simp, simp) 
  have a:"\<And>i. i \<in> J \<Longrightarrow> f  i \<in> I" using assms(4) by blast
  have "\<And>i. i \<in> J \<Longrightarrow> (\<lambda>x k. if k = f i then x else z k) \<in> M (f i) \<rightarrow>\<^sub>M Pi\<^sub>M I M"
    apply (rule measurable_PiM_Collect)
    using z_def a apply (simp add:space_PiM PiE_def Pi_def)
    apply (simp add:extensional_def)
    by simp
  hence e:"\<And>i. i \<in> J \<Longrightarrow> Y i \<in> measurable (M (f i)) (M' i)"
    apply (simp add:Y_def)
    using z_def assms(2) apply measurable
    by simp
  have d:"prob_space.indep_vars (PiM I M) (M \<circ> f) (\<lambda>i \<omega>. \<omega> (f i)) J" 
    apply (rule indep_vars_product_space)     
    using assms by blast+
  have "prob_space.indep_vars (PiM I M) M' (\<lambda>i. Y i \<circ> (\<lambda>\<omega>. \<omega> (f i))) J" 
    apply (rule prob_space.indep_vars_compose[where M'="M \<circ> f"])
    by (simp add:c, simp add:d, simp add:e)

  thus ?thesis
    using c by (simp add:b cong:prob_space.indep_vars_cong)
qed 

end