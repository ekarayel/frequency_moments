section \<open>Probability Spaces\<close>

text \<open>Some additional results about probability spaces in addition to "HOL-Probability".\<close>

theory Probability_Ext
  imports Main "HOL-Probability.Independent_Family" Multiset_Ext "HOL-Probability.Stream_Space"
 "HOL-Probability.Probability_Mass_Function"
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


text \<open>Random variables that depend on disjoint sets of the components of a product space are
independent.\<close>

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

lemma (in prob_space) variance_divide:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  shows "variance (\<lambda>\<omega>. f \<omega> / r) = variance f / r^2"
  apply (subst Bochner_Integration.integral_divide[OF assms(1)])
  apply (subst diff_divide_distrib[symmetric])
  using assms by (simp add:power2_eq_square algebra_simps)

lemma pmf_eq:
  assumes "\<And>x. x \<in> set_pmf \<Omega> \<Longrightarrow> (x \<in> P) = (x \<in> Q)"
  shows "measure (measure_pmf \<Omega>) P = measure (measure_pmf \<Omega>) Q"
    apply (rule measure_eq_AE)
      apply (subst AE_measure_pmf_iff)
    using assms by auto

lemma pmf_mono_1:
  assumes "\<And>x. x \<in> P \<Longrightarrow> x \<in> set_pmf \<Omega> \<Longrightarrow> x \<in> Q"
  shows "measure (measure_pmf \<Omega>) P \<le> measure (measure_pmf \<Omega>) Q"
proof -
  have "measure (measure_pmf \<Omega>) P = measure (measure_pmf \<Omega>) (P \<inter> set_pmf \<Omega>)" 
    by (rule pmf_eq, simp)
  also have "... \<le>  measure (measure_pmf \<Omega>) Q"
  apply (rule finite_measure.finite_measure_mono, simp)
     apply (rule subsetI) using assms apply blast
    by simp
  finally show ?thesis by simp
qed

definition (in prob_space) covariance where 
  "covariance f g = expectation (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g))"

lemma (in prob_space) real_prod_integrable:
  fixes f g :: "'a \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes sq_int: "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. f \<omega> * g \<omega>)"
  unfolding integrable_iff_bounded
proof
  have "(\<integral>\<^sup>+ \<omega>. ennreal (norm (f \<omega> * g \<omega>)) \<partial>M)\<^sup>2 = (\<integral>\<^sup>+ \<omega>. ennreal \<bar>f \<omega>\<bar> * ennreal \<bar>g \<omega>\<bar> \<partial>M)\<^sup>2" 
    by (simp add: abs_mult ennreal_mult)
  also have "... \<le>  (\<integral>\<^sup>+ \<omega>. ennreal \<bar>f \<omega>\<bar>^2 \<partial>M) * (\<integral>\<^sup>+ \<omega>. ennreal \<bar>g \<omega>\<bar>^2 \<partial>M)"
    apply (rule Cauchy_Schwarz_nn_integral) by auto
  also have "... < \<infinity>" 
    using sq_int by (auto simp: integrable_iff_bounded ennreal_power ennreal_mult_less_top)
  finally have "(\<integral>\<^sup>+ x. ennreal (norm (f x * g x)) \<partial>M)\<^sup>2 < \<infinity>" 
    by simp
  thus "(\<integral>\<^sup>+ x. ennreal (norm (f x * g x)) \<partial>M) < \<infinity>" 
    by (simp add: power_less_top_ennreal)
qed auto

lemma (in prob_space) covariance_eq:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "covariance f g = expectation (\<lambda>\<omega>. f \<omega> * g \<omega>) - expectation f * expectation g"
proof -
  have "integrable M f" using square_integrable_imp_integrable assms by auto
  moreover have "integrable M g" using square_integrable_imp_integrable assms by auto
  ultimately show ?thesis
    using assms real_prod_integrable
    by (simp add:covariance_def algebra_simps prob_space)
qed

lemma (in prob_space) covar_integrable:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)" "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g))"
proof -
  have "integrable M f" using square_integrable_imp_integrable assms by auto
  moreover have "integrable M g" using square_integrable_imp_integrable assms by auto
  ultimately show ?thesis using assms real_prod_integrable by (simp add: algebra_simps)
qed

lemma (in prob_space) sum_square_int:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)\<^sup>2)"
  apply (simp add:power2_eq_square sum_distrib_left sum_distrib_right)
  apply (rule Bochner_Integration.integrable_sum)
  apply (rule Bochner_Integration.integrable_sum)
  apply (rule real_prod_integrable)
  using assms by auto 

lemma (in prob_space) var_sum_1:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows 
    "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. (\<Sum>j \<in> I. covariance (f i) (f j)))" (is "?lhs = ?rhs")
proof -
  have a:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. (f i \<omega> - expectation (f i)) * (f j \<omega> - expectation (f j)))" 
    using assms covar_integrable by simp
  have "?lhs = expectation (\<lambda>\<omega>. (\<Sum>i\<in>I. f i \<omega> - expectation (f i))\<^sup>2)"
    apply (subst Bochner_Integration.integral_sum)
    apply (simp add: square_integrable_imp_integrable[OF assms(2) assms(3)])
    by (subst sum_subtractf[symmetric], simp)
  also have "... = expectation (\<lambda>\<omega>. (\<Sum>i \<in> I. (\<Sum>j \<in> I. (f i \<omega> - expectation (f i)) *  (f j \<omega> - expectation (f j)))))"
    apply (simp add: power2_eq_square sum_distrib_right sum_distrib_left)
    apply (rule Bochner_Integration.integral_cong, simp)
    apply (rule sum.cong, simp)+
    by (simp add:mult.commute)
  also have "... = (\<Sum>i \<in> I. (\<Sum>j \<in> I. covariance (f i) (f j)))"
    using a by (simp add: Bochner_Integration.integral_sum covariance_def) 
  finally show ?thesis by simp
qed

lemma (in prob_space) covar_self_eq:
  fixes f :: "'a \<Rightarrow> real"
  shows "covariance f f = variance f"
  by (simp add:covariance_def power2_eq_square)

lemma (in prob_space) covar_indep_eq_zero:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  assumes "integrable M g"
  assumes "indep_var borel f borel g"
  shows "covariance f g = 0"
proof -
  have a:"indep_var borel ((\<lambda>t. t - expectation f) \<circ> f) borel  ((\<lambda>t. t - expectation g) \<circ> g)"
    by (rule indep_var_compose[OF assms(3)], simp, simp)

  show ?thesis
    apply (simp add:covariance_def)
    apply (subst indep_var_lebesgue_integral)
    using a assms by (simp add:comp_def prob_space)+
qed

lemma (in prob_space) var_sum_2:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = 
      (\<Sum>i \<in> I. variance (f i)) + (\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j))"
  apply (subst var_sum_1[OF assms(1) assms(2) assms(3)], simp)
  apply (subst covar_self_eq[symmetric])
  apply (subst sum.distrib[symmetric])
  apply (rule sum.cong, simp)
  apply (subst sum.insert[symmetric], simp add:assms, simp)
  by (rule sum.cong, simp add:insert_absorb, simp)

lemma (in prob_space) var_sum_pairwise_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_var borel (f i) borel (f j)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
proof -
  have "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I - {i} \<Longrightarrow> covariance (f i) (f j) = 0" 
    apply (rule covar_indep_eq_zero)
    using assms square_integrable_imp_integrable[OF assms(2) assms(3)] by auto

  hence a:"(\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j)) = 0"
    by simp

  show ?thesis
    by (subst var_sum_2[OF assms(1) assms(2) assms(3)], simp, simp add:a)
qed

lemma (in prob_space) indep_var_from_indep_vars:
  assumes "i \<noteq> j"
  assumes "indep_vars (\<lambda>_. M') f {i, j}" 
  shows "indep_var M' (f i) M' (f j)"
proof -
  have a:"inj (case_bool i j)" using assms(1) 
    by (simp add: bool.case_eq_if inj_def)
  have b:"range (case_bool i j) = {i,j}" 
    by (simp add: UNIV_bool insert_commute)
  have c:"indep_vars (\<lambda>_. M') f (range (case_bool i j))" using assms(2) b by simp

  have "True = indep_vars (\<lambda>x. M') (\<lambda>x. f (case_bool i j x)) UNIV" 
    using indep_vars_reindex[OF a c]
    by (simp add:comp_def)
  also have "... = indep_vars (\<lambda>x. case_bool M' M' x) (\<lambda>x. case_bool (f i) (f j) x) UNIV"
    apply (rule indep_vars_cong, simp)
    apply (metis bool.case_distrib)
    by (simp add: bool.case_eq_if)
  also have "... = ?thesis"
    apply (subst indep_var_def) by simp
  finally show ?thesis by simp
qed

lemma (in prob_space) var_sum_pairwise_indep_2:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>J. J \<subseteq> I \<Longrightarrow> card J = 2 \<Longrightarrow> indep_vars (\<lambda> _. borel) f J"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  apply (rule var_sum_pairwise_indep[OF assms(1) assms(2) assms(3)], simp, simp)
  apply (rule indep_var_from_indep_vars, simp)
  by (rule assms(4), simp, simp)

lemma (in prob_space) var_sum_all_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "indep_vars (\<lambda> _. borel) f I"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  apply (rule var_sum_pairwise_indep_2[OF assms(1) assms(2) assms(3)], simp, simp)
  using indep_vars_subset[OF assms(4)] by simp

end
