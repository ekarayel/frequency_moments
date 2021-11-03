section \<open>Probabilities and Independent Families\<close>

text \<open>Some additional results about probabilities and independent families.\<close>

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

(*TODO Remove *)
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
  fixes f :: "'a \<Rightarrow> real"
  fixes g :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  assumes "integrable M g"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)"
  assumes "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. f \<omega> * g \<omega>)"
proof -
  have b1:"(\<lambda>\<omega>. ennreal (abs (f \<omega>))) \<in> borel_measurable M" 
    using assms(1) assms(2) by measurable
  have b2:"(\<lambda>\<omega>. ennreal (abs (g \<omega>))) \<in> borel_measurable M" 
    using assms(1) assms(2) by measurable
  have b:"(\<lambda>\<omega>. f \<omega> * g \<omega>) \<in> borel_measurable M" 
    using assms(1) assms(2) by measurable

  have a1: "integral\<^sup>N M (\<lambda>\<omega>. (ennreal \<bar>f \<omega>\<bar>)\<^sup>2) < \<infinity>" using assms(3) 
    apply (subst (asm) integrable_iff_bounded) by (simp add:ennreal_power)
  have a2: "integral\<^sup>N M (\<lambda>\<omega>. (ennreal \<bar>g \<omega>\<bar>)\<^sup>2) < \<infinity>" using assms(4)
    apply (subst (asm) integrable_iff_bounded) by (simp add:ennreal_power)
  show "integrable M (\<lambda>\<omega>. f \<omega> * g \<omega>)" 
    apply (subst integrable_iff_bounded)
    apply (rule conjI, metis b)
    apply (simp add:abs_mult)
    apply (subst ennreal_mult, simp, simp)
    using Cauchy_Schwarz_nn_integral[OF b1 b2] a1 a2 
    by (metis (no_types, lifting) ennreal_0 ennreal_mult_less_top infinity_ennreal_def 
          linorder_not_le neq_top_trans power2_eq_square top_neq_ennreal)
qed

lemma (in prob_space) covariance_eq:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  assumes "integrable M g"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)"
  assumes "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "covariance f g = expectation (\<lambda>\<omega>. f \<omega> * g \<omega>) - expectation f * expectation g"
  using real_prod_integrable assms
  by (simp add:covariance_def algebra_simps prob_space)


lemma (in prob_space) covar_integrable:
  fixes f :: "'a \<Rightarrow> real"
  fixes g :: "'a \<Rightarrow> real"
  assumes "integrable M f"
  assumes "integrable M (\<lambda>\<omega>. f \<omega>^2)"
  assumes "integrable M g"
  assumes "integrable M (\<lambda>\<omega>. g \<omega>^2)"
  shows "integrable M (\<lambda>\<omega>. (f \<omega> - expectation f) * (g \<omega> - expectation g))"
  apply (rule real_prod_integrable)
  using assms by (simp add:power2_eq_square right_diff_distrib left_diff_distrib)+

lemma (in prob_space) sum_square_int:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)"
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
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows 
    "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. (\<Sum>j \<in> I. covariance (f i) (f j)))" (is "?lhs = ?rhs")
proof -
  have a:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. (f i \<omega> - expectation (f i)) * (f j \<omega> - expectation (f j)))" 
    using assms covar_integrable by simp
  have "?lhs = expectation (\<lambda>\<omega>. (\<Sum>i\<in>I. f i \<omega> - expectation (f i))\<^sup>2)"
    apply (subst Bochner_Integration.integral_sum, simp add:assms)
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
  using indep_var_def
  by (simp add:covariance_def power2_eq_square)

lemma (in prob_space) covar_indep_eq_zero:
  fixes f :: "'a \<Rightarrow> real"
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
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = 
      (\<Sum>i \<in> I. variance (f i)) + (\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j))"
  apply (subst var_sum_1[OF assms(1) assms(2) assms(3)], simp)
  apply (subst covar_self_eq[symmetric])
  apply (subst sum.distrib[symmetric])
  apply (rule sum.cong, simp)
  apply (subst sum.insert[symmetric], simp add:assms, simp)
  by (rule sum.cong, simp add:insert_absorb, simp)

lemma sum_zero_all: 
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i = (0 :: 'a :: ab_group_add)"
  shows "sum f I = 0"
  using assms by simp

lemma (in prob_space) var_sum_pairwise_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> indep_var borel (f i) borel (f j)"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
proof -
  have a:" (\<Sum>i \<in> I. \<Sum>j \<in> I - {i}. covariance (f i) (f j)) = 0"
    apply (rule sum_zero_all)
    apply (rule sum_zero_all)
    using covar_indep_eq_zero assms by auto

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
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "\<And>J. J \<subseteq> I \<Longrightarrow> card J = 2 \<Longrightarrow> indep_vars (\<lambda> _. borel) f J"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  apply (rule var_sum_pairwise_indep[OF assms(1) assms(2) assms(3)], simp, simp)
  apply (rule indep_var_from_indep_vars, simp)
  by (rule assms(4), simp, simp)

lemma (in prob_space) var_sum_all_indep:
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. f i \<omega>^2)"
  assumes "indep_vars (\<lambda> _. borel) f I"
  shows "variance (\<lambda>\<omega>. (\<Sum>i \<in> I. f i \<omega>)) = (\<Sum>i \<in> I. variance (f i))"
  apply (rule var_sum_pairwise_indep_2[OF assms(1) assms(2) assms(3)], simp, simp)
  using indep_vars_subset[OF assms(4)] by simp

lemma (in prob_space) has_variance_sum:
  assumes "finite I"
  assumes "prob_space.indep_vars M (\<lambda>_. borel ::real measure) X' I" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> has_variance M (X' i) (r i)"
  assumes "\<And>f. (\<And>i. i \<in> I \<Longrightarrow> (r i) (f i)) \<Longrightarrow> s (sum f I)"
  shows "has_variance M (\<lambda>\<omega>. \<Sum> i \<in> I. X' i \<omega>) s"
  using assms
  apply (simp only:has_variance_def)
  apply (rule conjI, rule prob_space.sum_square_int) 
  using prob_space_axioms apply blast 
      apply (simp, simp, simp)
  apply (rule conjI)
  using prob_space_axioms apply blast 
  apply (subst var_sum_all_indep, simp, simp, simp, simp)
  apply (rule conjI)
  using prob_space_axioms apply blast 
  by simp

end
