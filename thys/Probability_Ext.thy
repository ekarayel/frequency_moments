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