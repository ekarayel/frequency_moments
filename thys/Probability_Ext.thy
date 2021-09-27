section \<open>Probabilities and Independent Families\<close>

text \<open>Some additional results about probabilities and independent families.\<close>

theory Probability_Ext
  imports Main "HOL-Probability.Independent_Family" Multiset_Ext "HOL-Probability.Stream_Space"
begin

lemma measure_inters: "measure M (E \<inter> space M) = \<P>(x in M. x \<in> E)"
  by (simp add: Collect_conj_eq inf_commute)

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
  using assms(2) measurable_sets by blast
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
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  shows "prob_space.indep_vars (PiM I \<Omega>) \<Omega> (\<lambda>i \<omega>. (\<omega> i)) I"
proof -
  define \<Omega>' where "\<Omega>' = (\<lambda>i. (if i \<in> I then \<Omega> i else count_space {undefined}))"
  have "prob_space (count_space {undefined})"
    by (rule prob_spaceI, simp)
  hence prob_space_i: "\<And>i. prob_space (\<Omega>' i)" 
    using assms  apply (simp add:\<Omega>'_def) by blast

  have t:"\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> i) -` {undefined} \<inter> space (Pi\<^sub>M I \<Omega>') = space (Pi\<^sub>M I \<Omega>')" 
    apply (simp add:space_PiM PiE_def Pi_def)
    apply (rule order_antisym)
    by (rule subsetI, simp add:extensional_def)+
  have "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> i) \<in> measurable (PiM I \<Omega>') (count_space {undefined})" 
    apply (simp add: measurable_def, rule conjI)
     apply (simp add:space_PiM PiE_def Pi_def extensional_def)
    apply (rule pow_unit_cases)
    by (simp add:t)+

  hence "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> i) \<in> measurable (PiM I \<Omega>') (\<Omega>' i)"
    by (simp add:\<Omega>'_def)
  moreover have "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>\<omega>. \<omega> i) \<in> measurable (PiM I \<Omega>') (\<Omega>' i)"
    by measurable

  ultimately have meas: "\<And>i. (\<lambda>\<omega>. \<omega> i) \<in> measurable (PiM I \<Omega>') (\<Omega>' i)"
    by blast
  
  interpret product_prob_space "\<Omega>'"
    apply (simp add:product_prob_space_def product_sigma_finite_def product_prob_space_axioms_def)
    using prob_space_i prob_space_imp_sigma_finite by blast

  have a:"prob_space (Pi\<^sub>M I \<Omega>')" using prob_space_i by (simp add:prob_space_PiM)

  have "prob_space.indep_vars (PiM I \<Omega>') \<Omega>' (\<lambda>i \<omega>. (\<omega> i)) I" 
    apply (subst prob_space.indep_vars_iff_distr_eq_PiM)
       apply (simp add:a)
      apply (simp add:assms)
    apply (simp add:meas)
    apply (subst distr_PiM_reindex)
       apply (simp add:prob_space_i)
    apply simp apply simp
    apply (rule PiM_cong, simp)
    apply (subst product_prob_space.PiM_component)
      using product_prob_space_axioms apply blast
      apply blast
    by simp
  moreover have "\<And>i. i \<in> I \<Longrightarrow> \<Omega>' i = \<Omega> i" 
    using assms(2) by (simp add:\<Omega>'_def image_subset_iff)
  ultimately have "prob_space.indep_vars (PiM I \<Omega>') \<Omega> (\<lambda>i \<omega>. (\<omega>  i)) I"
    by (simp  cong:indep_vars_cong)
  moreover have "Pi\<^sub>M I \<Omega> = Pi\<^sub>M I \<Omega>'" 
    by (rule PiM_cong, simp, simp add:\<Omega>'_def)
  ultimately
  show ?thesis by simp
qed

text \<open>Random variables that depend on disjoint sets of the components of a product space are
independent.\<close>

lemma indep_pim:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i. i \<in> J \<Longrightarrow> X' i \<in> measurable (PiM (f i) M) (M' i)"
  assumes "\<And>\<omega> i. i \<in> J \<Longrightarrow>  X' i \<omega> = X' i (restrict \<omega> (f i))"
  assumes "disjoint_family_on f J"
  assumes "J \<noteq> {}"
  assumes "\<And>i. i \<in> J \<Longrightarrow> f i \<subseteq> I"
  assumes "I \<noteq> {}"
  shows "prob_space.indep_vars (PiM I M) M' X' J"
proof -
  interpret prob_space "(PiM I M)" using assms(1) by (simp add:prob_space_PiM)

  have "I \<noteq> {}" by (simp add:assms)
  hence "indep_vars M (\<lambda>i \<omega>. (\<omega> i)) I"
    using assms(1) indep_vars_product_space[where I="I" and \<Omega>="M"]
    by simp

  hence b:"indep_vars (\<lambda>j. PiM (f j) M) (\<lambda>j \<omega>. restrict \<omega> (f j)) J" 
    using assms indep_vars_restrict[where X="(\<lambda>i \<omega>. \<omega> i)"] by blast

  define Y' where "Y' = X'"
  have d:"\<And>i. i \<in> J \<Longrightarrow> X' i = (\<lambda>\<omega>. Y' i (restrict \<omega> (f i)))"
    apply (rule ext) using assms(3) Y'_def by blast
  show ?thesis 
    apply (simp add: d cong:indep_vars_cong)
    apply (rule indep_vars_compose2[where X="(\<lambda>i \<omega>. restrict \<omega> (f i))" and M'="(\<lambda>j. PiM (f j) M)"])
     apply(simp add:b)
    by (simp add:Y'_def assms(2))
qed

lemma make_ext: 
  assumes "\<And>x. P x = P (restrict x I)" 
  shows "(\<forall>x \<in> Pi I A. P x) = (\<forall>x \<in> PiE I A. P x)"
  apply (simp add:PiE_def Pi_def)
  apply (rule order_antisym)
   apply (simp add:Pi_def)
  using assms by fastforce

lemma PiE_reindex:
  assumes "inj_on f I"
  shows "PiE I (A \<circ> f) = (\<lambda>a. restrict (a \<circ> f) I) ` PiE (f ` I) A" (is "?lhs = ?f ` ?rhs")
proof -
  have "?lhs \<subseteq> ?f` ?rhs"
  proof (rule subsetI)
    fix x
    assume a:"x \<in> Pi\<^sub>E I (A \<circ> f)"
    define y where y_def: "y = (\<lambda>k. if k \<in> f ` I then x (the_inv_into I f k) else undefined)"
    have b:"y \<in> PiE (f ` I) A" 
      apply (rule PiE_I)
      using a apply (simp add:y_def PiE_iff)
       apply (metis imageE assms the_inv_into_f_eq)
      using a by (simp add:y_def PiE_iff extensional_def)
    have c: "x = (\<lambda>a. restrict (a \<circ> f) I) y" 
      apply (rule ext)
      using a apply (simp add:y_def PiE_iff)
      apply (rule conjI)
      using assms the_inv_into_f_eq 
      apply (simp add: the_inv_into_f_eq)
      by (meson extensional_arb)
    show "x \<in> ?f ` ?rhs" using b c by blast
  qed
  moreover have "?f ` ?rhs \<subseteq> ?lhs"
    apply (rule image_subsetI)
    by (simp add:Pi_def PiE_def)
  ultimately show ?thesis by blast
qed

lemma (in prob_space) indep_sets_reindex:
  assumes "inj_on f I"
  shows "indep_sets A (f ` I) = indep_sets (\<lambda>i. A (f i)) I"
proof -
  have a:"\<And>J g. J \<subseteq> I \<Longrightarrow> (\<Prod>j \<in> f ` J. g j) = (\<Prod>j \<in> J. g (f j))"
    by (metis assms prod.reindex_cong subset_inj_on)

  have "\<And>J. J \<subseteq> I \<Longrightarrow> (\<Pi>\<^sub>E i \<in> J. A (f i)) = (\<lambda>a. restrict (a \<circ> f) J) ` PiE (f ` J) A"
    apply (subst PiE_reindex[symmetric])
    using assms inj_on_subset apply blast
    by (simp add: comp_def)

  hence b:"\<And>P J. J \<subseteq> I \<Longrightarrow>  (\<And>x. P x = P (restrict x J)) \<Longrightarrow> (\<forall>A'\<in>PiE (f ` J) A. P (A' \<circ> f)) = (\<forall>A' \<in> \<Pi>\<^sub>E i \<in> J. A (f i). P A')"
    by (simp)

  have c:"\<And>J. J \<subseteq> I \<Longrightarrow> finite (f ` J) = finite J" 
    by (meson assms finite_image_iff inj_on_subset)

  show ?thesis
    apply (simp add:indep_sets_def all_subset_image a c)
    apply (subst make_ext) apply (simp cong:restrict_cong)
    apply (subst make_ext) apply (simp cong:restrict_cong)
    by (simp add:b[symmetric])
qed

lemma (in prob_space) indep_vars_reindex:
  assumes "inj_on f I"
  assumes "indep_vars M' X' (f ` I)"
  shows "indep_vars (M' \<circ> f) (\<lambda>k \<omega>. X' (f k) \<omega>) I"
  using assms by (simp add:indep_vars_def2 indep_sets_reindex)

lemma lift_nn_integral_PiM:
  assumes "i \<in> I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "\<And>x. x \<in> space (M i) \<Longrightarrow> f x \<ge> 0"
  assumes "(f :: 'a \<Rightarrow> real) \<in> borel_measurable (M i)"
  assumes "finite I"
  shows  "integral\<^sup>N (PiM I M) (\<lambda>\<omega>. f (\<omega> i)) = integral\<^sup>N (M i) f"
proof -
  define M' where "M' = (\<lambda>i. if i \<in> I then M i else count_space {undefined})"
  have "\<And>i. sigma_finite_measure (M' i)"
    using M'_def assms(2) 
    by (simp add: prob_space_imp_sigma_finite sigma_finite_measure_count_space_finite)
  hence a: "product_sigma_finite M'"    
    by (simp add: product_sigma_finite_def)
  have b:"PiM I M = PiM I M'"
    by (simp add:M'_def cong:PiM_cong)

  define g where "g = (\<lambda>k \<omega>. ennreal (if k = i then f \<omega> else 1))"
  have c:"\<And>\<omega>. \<omega> \<in> space (PiM I M') \<Longrightarrow> f (\<omega> i) =  (\<Prod>k \<in> I. g k (\<omega> k))"
    apply (simp add:g_def)
    apply (subst prod_ennreal)
    using assms(3) apply (simp add:M'_def space_PiM, force)
    apply (rule arg_cong[where f="ennreal"])
    using assms(5) assms(1) by (induction I rule:finite_induct, simp, simp)

  have d:"\<And>j. j \<in> I \<Longrightarrow> j \<noteq> i \<Longrightarrow> g j \<in> borel_measurable (M' j)"
    by (simp add:g_def M'_def)
  moreover have "g i \<in> borel_measurable (M' i)"
    using assms(1) apply (simp add:g_def M'_def)
    apply measurable
    using assms(4) by auto
  ultimately have d:"\<And>i. i \<in> I \<Longrightarrow> g i \<in> borel_measurable (M' i)"
    by blast

  have e:"\<And>j. j \<in> I \<Longrightarrow> integral\<^sup>N (M' j) (g j) = (if j = i then  integral\<^sup>N (M i) f else 1)"
    apply (simp add:M'_def g_def)
    using assms(2) prob_space.emeasure_space_1 by blast
  show ?thesis 
    apply (simp add:b)
    apply (simp add:c cong:nn_integral_cong)
    apply (subst product_sigma_finite.product_nn_integral_prod)
    apply (simp add:a)
      apply (simp add:assms(5))
     apply (simp add:d)
    apply (simp add:e)
    using assms(5) assms(1) by (induction I, simp, simp)
qed

lemma lift_pos_bochner_integral_PiM:
  assumes "i \<in> I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "integrable (M i) (f :: 'a \<Rightarrow> real)"
  assumes "\<And>x. x \<in> space (M i) \<Longrightarrow> f x \<ge> 0"
  assumes "finite I"
  shows "integral\<^sup>L (PiM I M) (\<lambda>\<omega>. f (\<omega> i)) = integral\<^sup>L (M i) f" (is ?A)
  and "integrable (PiM I M) (\<lambda>\<omega>. f (\<omega> i))" (is ?B)
proof -
  have f_meas:"f \<in> borel_measurable (M i)" using borel_measurable_integrable assms(3) by auto

  define f_int where "f_int = integral\<^sup>L (M i) f"

  have f_pos_ae: "AE x in M i. f x \<ge> 0" apply (rule AE_I2) using assms(4) by simp
  hence f_pos :"f_int \<ge> 0" apply (simp add:f_int_def) using integral_nonneg_AE by blast
 
  have "integrable (M i) f" using assms(3) nn_integral_eq_integrable by simp 
  hence "(\<integral>\<^sup>+x. f (x i) \<partial>(PiM I M)) = ennreal (f_int)"
    using assms f_meas apply (simp add:lift_nn_integral_PiM)
    using f_meas f_pos f_pos_ae f_int_def nn_integral_eq_integrable by metis
  moreover have "(\<lambda>\<omega>. f (\<omega> i)) \<in> borel_measurable (PiM I M)" using f_meas assms by measurable
  moreover have "AE x in PiM I M. f (x i) \<ge> 0"
    apply (rule AE_I2, simp add:space_PiM PiE_def Pi_def)
    using assms(4) assms(1) by blast
  ultimately have r1: "integral\<^sup>L (PiM I M) (\<lambda>\<omega>. f (\<omega> i)) = f_int" and r2: "integrable (PiM I M) (\<lambda>\<omega>. f (\<omega> i))"
    using nn_integral_eq_integrable f_pos by blast+

  show ?A using r1 by (simp add:f_int_def)
  show ?B using r2 by auto
qed

lemma lift_bochner_integral_PiM:
  assumes "i \<in> I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "integrable (M i) (f :: 'a \<Rightarrow> real)"
  assumes "finite I"
  shows integral_prod_space: 
    "integral\<^sup>L (PiM I M) (\<lambda>\<omega>. f (\<omega> i)) = integral\<^sup>L (M i) f" (is ?A)
  and integral_prod_space_int:
    "integrable (PiM I M) (\<lambda>\<omega>. f (\<omega> i))" (is ?B)
proof -
  define f_p where "f_p = (\<lambda>\<omega>. max (f \<omega>) 0)"
  define f_n where "f_n = (\<lambda>\<omega>. max (-(f \<omega>)) 0)"
  have f_int: "integrable (M i) f_p" "integrable (M i) f_n"
        using assms(3) by (simp add:f_p_def f_n_def)+
  have f_pos_ptw: 
    "\<And> x. x \<in> space (M i) \<Longrightarrow> f_p x \<ge> 0" 
    "\<And> x. x \<in> space (M i) \<Longrightarrow> f_n x \<ge> 0" by (simp add:f_p_def f_n_def)+
  have f_split: "f = (\<lambda>\<omega>. f_p \<omega> - f_n \<omega>)"
    by (rule ext, simp add:f_p_def f_n_def max_def) 

  show ?A
    using assms f_int f_pos_ptw 
    by (simp add:lift_pos_bochner_integral_PiM f_split)
  show ?B
    using assms f_int f_pos_ptw 
    by (simp add:lift_pos_bochner_integral_PiM f_split)
qed

lemma lift_has_bochner_integral:
  assumes "i \<in> I"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "has_bochner_integral (M i) f (r::real)"
  shows "has_bochner_integral (PiM I M) (\<lambda>\<omega>. f (\<omega> i)) r"
  using assms lift_bochner_integral_PiM[where i="i" and I="I" and M="M" and f="f"]
  by (simp add:has_bochner_integral_iff)

definition has_variance where
  "has_variance M f r = (integrable M (\<lambda>\<omega>. f \<omega>^2) \<and> integrable M f \<and> prob_space M \<and> r ((prob_space.variance M f) ::real))"

lemma has_variance_scale:
  assumes "has_variance M f (\<lambda>x. r (x * a^2))"
  shows "has_variance M (\<lambda>\<omega>. f \<omega> * a) r"
  using assms by(simp add:has_variance_def power_mult_distrib  left_diff_distrib[symmetric]) 

lemma has_variance_imp:
  assumes "\<And>x. r x \<Longrightarrow> s x"
  assumes "has_variance M f r"
  shows "has_variance M f s"
  using assms by (simp add:has_variance_def)

lemma has_variance_divide:
  assumes "has_variance M f (\<lambda>x. r (x / a^2))"
  shows "has_variance M (\<lambda>\<omega>. f \<omega> / a) r"
  apply (rule has_variance_scale[where a="1/a", simplified])
  using assms by (simp add:power_divide)

lemma lift_has_variance:
  assumes "i \<in> I"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes "has_variance (M i) f r"
  shows "has_variance (PiM I M) (\<lambda>\<omega>. f (\<omega> i)) r"
  using assms apply (simp add:has_variance_def)
  apply (rule conjI, rule lift_bochner_integral_PiM(2), simp, simp, simp, simp)
  apply (rule conjI, rule lift_bochner_integral_PiM(2), simp, simp, simp, simp)
  apply (rule conjI, simp add:prob_space_PiM)
  apply (subst lift_bochner_integral_PiM(1), simp, simp, simp, simp)
  apply (subst lift_bochner_integral_PiM(1), simp, simp)
    apply (simp add:power2_diff)
  apply (rule Bochner_Integration.integrable_diff)
     apply (rule Bochner_Integration.integrable_add, simp) 
  apply (rule finite_measure.integrable_const) 
  using prob_space.finite_measure apply blast
  by simp+


lemma (in prob_space)
  assumes "finite I"
  assumes "indep_vars (\<lambda>_. borel ::real measure) X' I" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. X' i \<omega>)" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. X' i \<omega>^2)" 
  shows var_sum:"variance (\<lambda>\<omega>. \<Sum>i\<in> I. X' i \<omega>) = (\<Sum> i \<in> I. variance (\<lambda>\<omega>. X' i \<omega>))"  (is ?A) and
    var_sum_int:"integrable M (\<lambda>\<omega>. (\<Sum>i \<in> I. X' i \<omega>)\<^sup>2)" (is ?B)
proof -
  have a:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> expectation (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>)) = 
     expectation (X' i) * expectation (X' j) \<and> integrable M (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>))"
    (is "\<And>i j. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?ths1 i j \<and> ?ths2 i j")
  proof -
    fix i j
    assume a1:"i \<in> I"
    assume a2:"j \<in> I"
    assume a3:"i \<noteq> j"
    have "{i,j} \<subseteq> I" using a1 a2 by simp
    hence "indep_vars (\<lambda>_. borel) X' {i, j}" 
      using indep_vars_subset assms(2) by blast
    moreover have "\<And>i'. i' \<in> {i,j} \<Longrightarrow> integrable M (X' i')" 
      using a1 a2 assms(3) by blast
    ultimately show "?ths1 i j \<and> ?ths2 i j"
      using a3 indep_vars_lebesgue_integral[where I="{i,j}" and X="X'"] indep_vars_integrable[where I="{i,j}" and X="X'"]
      by simp
  qed

  have b:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> expectation (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>)) =
    (if i \<noteq> j then 0 else expectation (\<lambda>\<omega>. (X' i \<omega>)^2) - expectation (X' i) * expectation (X' j)) +  expectation (X' i) * expectation (X' j)"
    (is "\<And>i j. _ \<Longrightarrow> _ \<Longrightarrow> ?lhs i j = ?rhs i j")
  proof -
    fix i j
    assume "i \<in> I"
    moreover assume "j \<in> I"
    ultimately show "?lhs i j = ?rhs i j"
      apply (cases "i = j")
       apply (simp add:power2_eq_square)
      by (simp add:a)
  qed
  have c:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>))" (is "\<And>i j. _ \<Longrightarrow> _ \<Longrightarrow> ?ths i j")
  proof -
    fix i j
    assume "i \<in> I"
    moreover assume "j \<in> I"
    ultimately show "?ths i j"
      apply (cases "i = j")
       using assms(4) apply (simp add: power2_eq_square)
      by (simp add:a)
  qed
  have d:"integrable M (\<lambda>\<omega>. (\<Sum>i \<in> I. X' i \<omega>)\<^sup>2)" 
    by (simp add:c sum_distrib_left sum_distrib_right power2_eq_square)
  thus ?B by auto
  show ?A
    apply (subst variance_eq)
    apply (simp add: assms)
    apply (simp add: d)
    apply (simp add: variance_eq assms)
    apply (subst (1 2) power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right)
    apply (simp add: c Bochner_Integration.integral_sum)
    apply (simp add: sum_subtractf[symmetric])
    apply (simp add: b assms(1) sum_collapse)
    by (simp add:power2_eq_square)
qed

lemma (in prob_space) has_variance_sum:
  assumes "finite I"
  assumes "prob_space.indep_vars M (\<lambda>_. borel ::real measure) X' I" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> has_variance M (X' i) (r i)"
  assumes "\<And>f. (\<And>i. i \<in> I \<Longrightarrow> (r i) (f i)) \<Longrightarrow> s (sum f I)"
  shows "has_variance M (\<lambda>\<omega>. \<Sum> i \<in> I. X' i \<omega>) s"
  using assms
  apply (simp only:has_variance_def)
  apply (rule conjI, rule prob_space.var_sum_int) 
  using prob_space_axioms apply blast 
      apply (simp, simp, simp, simp)
  apply (rule conjI)
  using prob_space_axioms apply blast 
  apply (subst var_sum, simp, simp, simp, simp, simp)
  using prob_space_axioms by blast 

text \<open>On a finite set $M$ the $\sigma$-Algebra generated by singletons and the empty set
is already the power set of $M$.\<close>
lemma sigma_sets_singletons_and_empty:
  assumes "countable M"
  shows "sigma_sets M (insert {} ((\<lambda>k. {k}) ` M)) = Pow M"
proof -
  have "sigma_sets M ((\<lambda>k. {k}) ` M) = Pow M"
    using assms sigma_sets_singletons by auto
  hence "Pow M \<subseteq> sigma_sets M (insert {} ((\<lambda>k. {k}) ` M))"
    by (metis sigma_sets_subseteq subset_insertI)
  moreover have "(insert {} ((\<lambda>k. {k}) ` M)) \<subseteq> Pow M" by blast
  hence "sigma_sets M (insert {} ((\<lambda>k. {k}) ` M)) \<subseteq> Pow M"
    by (meson sigma_algebra.sigma_sets_subset sigma_algebra_Pow)
  ultimately show ?thesis by force
qed

end