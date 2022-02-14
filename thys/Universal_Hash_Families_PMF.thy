theory Universal_Hash_Families_PMF
  imports 
    "HOL-Probability.Stream_Space"
    "HOL-Probability.Product_PMF"
begin

lemma inters_eq_set_filter: "A \<inter> {x. P x} = {x \<in> A. P x}"
  by blast

lemma set_comp_cong: 
  assumes "\<And>x. P x \<Longrightarrow> f x = h (g x)"
  shows "{f x| x. P x} = h ` {g x| x. P x}"
  using assms by (auto simp: setcompr_eq_image)

text \<open>The following two lemmas are of independent interest, they help infer independence of events
and random variables on distributions. (Candidates for 
@{theory "HOL-Probability.Independent_Family"}.\<close>

lemma (in prob_space) indep_sets_distr:
  fixes A
  assumes "random_variable N f"
  defines "F \<equiv> (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` A i)"
  assumes indep_F: "indep_sets F I"
  assumes sets_A: "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets N"
  shows "prob_space.indep_sets (distr M N f) A I"
proof (rule prob_space.indep_setsI)
  show "prob_space (distr M N f)" by (rule prob_space_distr[OF assms(1)])
  show "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets (distr M N f)" using sets_A sets_distr by blast

  show "\<And>A' J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> \<forall>j\<in>J. A' j \<in> A j \<Longrightarrow> 
      measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
  proof -
    fix A' J
    assume a:"J \<subseteq> I" "finite J" "J \<noteq> {}" "\<forall>j \<in> J. A' j \<in> A j"

    define F' where "F' = (\<lambda>i. f -` A' i \<inter> space M)"

    have "\<Inter> (F' ` J) = f -` (\<Inter> (A' ` J)) \<inter> space M" 
      unfolding  set_eq_iff by (simp add:a(3) F'_def)
    moreover have "\<Inter> (A' ` J) \<in> sets N" 
      by (metis a sets_A sets.finite_INT subset_iff)
    ultimately have b: "measure (distr M N f) (\<Inter> (A' ` J)) = measure M (\<Inter> (F' ` J))" 
      by (metis assms(1) measure_distr)

    have "\<And>j. j \<in> J \<Longrightarrow> F' j \<in> F j"
      using a(4) F'_def F_def by blast
    hence c:"measure M (\<Inter> (F' ` J)) = (\<Prod>j\<in> J. measure M (F' j))"
      by (metis indep_F indep_setsD a(1,2,3))

    have "\<And>j. j \<in> J \<Longrightarrow> F' j =  f -` A' j  \<inter> space M" 
      by (simp add:F'_def)
    moreover have "\<And>j. j \<in> J \<Longrightarrow> A' j \<in> sets N" 
      using a(1,4) sets_A by blast
    ultimately have d:"\<And>j. j \<in> J \<Longrightarrow> measure M (F' j) = measure (distr M N f) (A' j)"
      using assms(1) measure_distr by metis

    show "measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
      using b c d by auto
  qed
qed

lemma (in prob_space) indep_vars_distr:
  assumes "f \<in> measurable M N"
  assumes "\<And>i. i \<in> I \<Longrightarrow> X' i \<in> measurable N (M' i)"
  assumes "indep_vars M' (\<lambda>i. (X' i) \<circ> f) I"
  shows "prob_space.indep_vars (distr M N f) M' X' I"
proof -
  interpret D: prob_space "(distr M N f)"
    using prob_space_distr[OF assms(1)] by simp

  have a: "f \<in> space M \<rightarrow> space N" using assms(1) by (simp add:measurable_def)

  have "D.indep_sets (\<lambda>i. {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}) I"
  proof (rule indep_sets_distr[OF assms(1)])
    have "\<And>i. i \<in> I \<Longrightarrow> {(X' i \<circ> f) -` A \<inter> space M |A. A \<in> sets (M' i)} = 
      (\<lambda>a. f -` a \<inter> space M) ` {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}"
      by (rule set_comp_cong, simp add:set_eq_iff, use a in blast)
    thus "indep_sets (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}) I"
      using assms(3) by (simp add:indep_vars_def2 cong:indep_sets_cong)
  next
    fix i
    assume "i \<in> I"
    thus "{X' i -` A \<inter> space N |A. A \<in> sets (M' i)} \<subseteq> sets N"
      using assms(2) measurable_sets by blast
  qed
  thus ?thesis 
    using assms by (simp add:D.indep_vars_def2)
qed

lemma range_inter: "range ((\<inter>) F) = Pow F"
  unfolding set_eq_iff image_def by auto

text \<open>The singletons and the empty set form an intersection stable generator of a countable
discrete \<sigma>-algebra:\<close>

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

lemma prob_space_restrict_space:"prob_space (restrict_space (measure_pmf M) (set_pmf M))"
  by (rule prob_spaceI, auto simp:emeasure_restrict_space emeasure_pmf)

lemma indep_vars_restrict_space:
  assumes "prob_space.indep_vars (restrict_space (measure_pmf M) (set_pmf M))  (\<lambda>i. measure_pmf (N i)) X I"
  shows "prob_space.indep_vars (measure_pmf M) (\<lambda>i. measure_pmf (N i)) X I"
proof -
  have a: "id \<in> restrict_space (measure_pmf M) (set_pmf M) \<rightarrow>\<^sub>M measure_pmf M"
    by (simp add:measurable_def range_inter sets_restrict_space)

  have "prob_space.indep_vars
    (distr (restrict_space (measure_pmf M) (set_pmf M)) (measure_pmf M) id) (\<lambda>i. measure_pmf (N i)) X I"
    by (rule prob_space.indep_vars_distr[OF prob_space_restrict_space a], auto simp:assms)
  moreover have "distr (restrict_space (measure_pmf M) (set_pmf M)) (measure_pmf M) id = measure_pmf M"
    by (rule measure_eqI, auto simp: emeasure_distr[OF a] emeasure_restrict_space emeasure_Int_set_pmf)
  ultimately show ?thesis by simp
qed

text \<open>With the following definitions it is possible to state theorems that hold for pmfs more
concisele, for example, instead of  @{term "measure_pmf.prob X A \<le> measure_pmf.prob X B"} we can 
just write @{term "is_pmf \<Longrightarrow> prob A \<le> prob B"} in the locale @{locale "prob_space"}.\<close>

definition (in prob_space) is_pmf where "is_pmf \<equiv> sets M = UNIV \<and> (AE x in M. measure M {x} \<noteq> 0)"

lemma (in prob_space) is_pmf_iff: 
  assumes "is_pmf"
  shows "M = measure_pmf (Abs_pmf M)"
  using assms prob_space_axioms Abs_pmf_inverse measure_pmf unfolding is_pmf_def by force

lemma is_pmfI: "prob_space.is_pmf (measure_pmf X)"
  unfolding measure_pmf.is_pmf_def using measure_pmf by (auto simp: AE_iff_null)

lemma (in prob_space) measure_pmf_eq:
  assumes "is_pmf"
  assumes "\<And>x. x \<in> set_pmf (Abs_pmf M) \<Longrightarrow> (x \<in> P) = (x \<in> Q)"
  shows "prob P = prob Q"
proof -
  have "measure_pmf.prob (Abs_pmf M) P = measure_pmf.prob (Abs_pmf M) Q"
    using assms by (auto intro!: measure_eq_AE AE_pmfI)
  thus ?thesis
    using is_pmf_iff[OF assms(1)] by metis
qed

text \<open>The following lemma is an intro rule for the independence of random variables defined on pmfs.
In that case it is possible, to check the independence of random variables point-wise.

The proof relies on the fact that the support of a pmf is countable and the \<sigma>-algebra of such a set
can be generated by singletons.\<close>

lemma (in prob_space) indep_vars_pmf':
  assumes "is_pmf"
  assumes "\<And>a J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> 
    prob {\<omega>. \<forall>i \<in> J. X i \<omega> = a i} = (\<Prod>i \<in> J. prob {\<omega>. X i \<omega> = a i})"
  shows "indep_vars (\<lambda>i. measure_pmf (N i)) X I"
proof -
  define M' where "M' = Abs_pmf M"
  hence M_def: "M = measure_pmf M'" using is_pmf_iff[OF assms(1)] by simp
  interpret R:prob_space "(restrict_space M (set_pmf M'))"
    using prob_space_restrict_space M_def by blast

  have events_eq_pow: "R.events = Pow (set_pmf M')"
    by (simp add:sets_restrict_space range_inter M_def)

  define G where "G = (\<lambda>i. {{}} \<union> (\<lambda>x. {x}) ` (X i ` set_pmf M'))"
  define F where "F = (\<lambda>i. {X i -` a \<inter> set_pmf M'|a. a \<in> G i})"

  have sigma_sets_pow: "\<And>i. i \<in> I \<Longrightarrow> sigma_sets (X i ` set_pmf M') (G i) = Pow (X i ` set_pmf M')"
    by (simp add:G_def, metis countable_image countable_set_pmf sigma_sets_singletons_and_empty)

  have F_in_events: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> Pow (set_pmf M')"
    by (simp add:F_def, rule subsetI, simp, blast)

  have as_sigma_sets:"\<And>i. i \<in> I \<Longrightarrow> {u. \<exists>A. u = X i -` A \<inter> set_pmf M'} = sigma_sets (set_pmf M') (F i)"
  proof -
    fix i
    assume a:"i \<in> I"
    have "\<And>A. X i -` A \<inter> set_pmf M' = X i -` (A \<inter> X i ` set_pmf M') \<inter> set_pmf M'"
      by (auto simp: set_eq_iff)
    hence "{u. \<exists>A. u = X i -` A \<inter> set_pmf M'} = {X i -` A \<inter> set_pmf M' |A. A \<subseteq> X i ` set_pmf M'}" 
      by (metis (no_types, opaque_lifting) inf_le2)
    also have "... = {X i -` A \<inter> set_pmf M' |A. A \<in> sigma_sets (X i ` set_pmf M') (G i)}" 
      using a by (simp add:sigma_sets_pow)
    also have "... = sigma_sets (set_pmf M') {X i -` a \<inter> set_pmf M' |a. a \<in> G i}" 
      by (subst sigma_sets_vimage_commute[symmetric, where \<Omega>' = "X i ` set_pmf M'"], blast, simp)
    also have "... = sigma_sets (set_pmf M') (F i)"
      by (simp add:F_def)
    finally show "{u. \<exists>A. u = X i -` A \<inter> set_pmf M'} = sigma_sets (set_pmf M') (F i)" by simp
  qed

  have F_Int_stable: "\<And>i. i \<in> I \<Longrightarrow> Int_stable (F i)"
  proof (rule Int_stableI)
    fix i a b
    assume "i \<in> I"
    assume "a \<in> F i"
    moreover assume "b \<in> F i"
    ultimately show "a \<inter> b \<in> (F i)"
      by (cases "a \<inter> b = {}", simp_all add:F_def G_def, blast+)
  qed

  have F_indep_sets:"R.indep_sets F I"
  proof (rule R.indep_setsI)
    fix i
    assume "i \<in> I"
    show "F i \<subseteq> R.events"
      unfolding F_def events_eq_pow by blast
  next
    fix A
    fix J
    assume a:"J \<subseteq> I" "J \<noteq> {}" "finite J" "\<forall>j\<in>J. A j \<in> F j"
    have b: "\<And>j. j \<in> J \<Longrightarrow> A j \<subseteq> set_pmf M'"
      by (metis PowD a(1,4) subsetD F_in_events)
    obtain a where a_def:"\<And>j. j \<in> J  \<Longrightarrow> A j = X j -` a j \<inter> set_pmf M' \<and> a j \<in> G j"
      using a(4) by (simp add:Pi_def F_def, metis)

    show "R.prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. R.prob (A j))"
    proof (cases "\<exists>j \<in> J. A j = {}")
      case True
      hence "\<Inter> (A ` J) = {}" by blast
      then show ?thesis
        using a(3) True by (simp, metis measure_empty)
    next
      case False
      then have "\<And>j. j \<in> J \<Longrightarrow> a j \<noteq> {}" using a_def by auto
      hence "\<And>j. j \<in> J \<Longrightarrow> a j \<in> (\<lambda>x. {x}) ` X j ` set_pmf M'"
        using a_def by (simp add:G_def) 
      then obtain b where b_def: "\<And>j. j \<in> J \<Longrightarrow> a j = {b j}"
        by (simp add:image_def, metis) 

      have "\<Inter> (A ` J) \<subseteq> set_pmf M'" using b a(2) by blast
      hence "R.prob (\<Inter> (A ` J)) = prob (\<Inter> j \<in> J. A j)"
        by (simp add: measure_restrict_space M_def)
      also have "... = prob ({\<omega>. \<forall>j \<in> J. X j \<omega> = b j})"
        using a(2) a_def b_def M_def apply (simp add:vimage_def measure_Int_set_pmf)
        by (rule arg_cong2 [where f="measure"], simp, blast)
      also have "... = (\<Prod> j\<in> J. prob (A j))"
        using M_def a_def b_def a(2) assms(2)[OF a(1,3)]
        by (simp add:vimage_def measure_Int_set_pmf)
      also have "... = (\<Prod>j\<in>J. R.prob (A j))"
        using b M_def by (simp add: measure_restrict_space cong:prod.cong)
      finally show ?thesis by blast
    qed
  qed

  have "R.indep_sets (\<lambda>i. sigma_sets (set_pmf M') (F i)) I"
    using R.indep_sets_sigma[simplified] F_Int_stable F_indep_sets
    by (auto simp:space_restrict_space M_def)

  hence "R.indep_sets (\<lambda>i. {u. \<exists>A. u = X i -` A \<inter> set_pmf M'}) I"
    by (simp add: as_sigma_sets cong:R.indep_sets_cong)

  hence "R.indep_vars (\<lambda>i. measure_pmf (N i)) X I"
    by (subst R.indep_vars_def2, simp add:measurable_def sets_restrict_space range_inter M_def)

  thus ?thesis unfolding M_def by (rule indep_vars_restrict_space)
qed

lemma (in prob_space) split_indep_events:
  assumes "is_pmf"
  assumes "indep_vars (\<lambda>i. measure_pmf (M' i)) X' I"
  assumes "K \<subseteq> I" "finite K"
  shows "prob {\<omega>. \<forall>x \<in> K. P x (X' x \<omega>)} = (\<Prod>x \<in> K. prob {\<omega>. P x (X' x \<omega>)})"
proof -
  have [simp]: "space M = UNIV"  "events = UNIV"  "prob UNIV = 1"
    by (subst is_pmf_iff[OF assms(1)], simp)+

  have "indep_vars (\<lambda>i. measure_pmf (M' i)) X' K"
    using assms(2,3) indep_vars_subset by blast
  hence "indep_events (\<lambda>x. {\<omega> \<in> space M. P x (X' x \<omega>)}) K"
    using indep_eventsI_indep_vars by force
  hence a:"indep_events (\<lambda>x. {\<omega>. P x (X' x \<omega>)}) K"
    by (simp) 

  have "prob  {\<omega>. \<forall>x \<in> K. P x (X' x \<omega>)} = prob (\<Inter>x \<in> K. {\<omega>. P x (X' x \<omega>)})"
    by (simp add: measure_pmf_eq[OF assms(1)])
  also have "... =  (\<Prod> x \<in> K. prob {\<omega>. P x (X' x \<omega>)})"
    using a assms(4) by (cases "K = {}", auto simp: indep_events_def)
  finally show ?thesis by simp
qed

definition (in prob_space) "uniform_on X A = ((map_pmf X (Abs_pmf M) = pmf_of_set A) \<and> A \<noteq> {} \<and> finite A)"
definition (in prob_space) "uniform_on' X A = 
  ((distr M (count_space UNIV) X = uniform_measure (count_space UNIV) A) \<and> 
    A \<noteq> {} \<and> finite A \<and> random_variable (count_space UNIV) X)"

lemma (in prob_space) uniform_on'D:
  assumes "uniform_on' X A"
  shows "prob {\<omega> \<in> space M. X \<omega> \<in> B} = card (A \<inter> B) / card A"
proof -
  have "prob {\<omega> \<in> space M. X \<omega> \<in> B} = prob (X -` B \<inter> space M)"
    by (subst Int_commute, simp add:vimage_def inters_eq_set_filter)
  also have "... = measure (distr M (count_space UNIV) X) B"
    using assms by (subst measure_distr, auto simp:uniform_on'_def)
  also have "... = measure (uniform_measure (count_space UNIV) A) B"
    using assms by (simp add:uniform_on'_def)
  also have "... = card (A \<inter> B) / card A"
    using assms by (subst measure_uniform_measure, auto simp:uniform_on'_def)+
  finally show ?thesis by simp
qed

lemma (in prob_space) uniform_onD:
  assumes "is_pmf"
  assumes "uniform_on X A"
  shows "prob {\<omega>. X \<omega> \<in> B} = card (A \<inter> B) / card A"
proof -             
  have "prob {\<omega>. X \<omega> \<in> B} = prob (X -` B)" unfolding vimage_def by simp
  also have "... = measure_pmf.prob (map_pmf X (Abs_pmf M)) B"
    using is_pmf_iff[OF assms(1)] by simp
  also have "... = measure_pmf.prob (pmf_of_set A) B"
    using assms(2) unfolding uniform_on_def by simp
  also have "... = card (A \<inter> B) / card A"
    using assms(2) unfolding uniform_on_def by (simp add: measure_pmf_of_set)
  finally show ?thesis
    by simp
qed

lemma (in prob_space) uniform_onI:
  assumes "is_pmf"
  assumes "finite A" "A \<noteq> {}"
  assumes "\<And>a. prob {\<omega>. X \<omega> = a} = indicator A a / card A"
  shows "uniform_on X A"
proof -
  have a:"\<And>a. measure_pmf.prob (Abs_pmf M) {x. X x = a} = indicator A a / card A"
    using assms(4) is_pmf_iff[OF assms(1)] by simp

  have "map_pmf X (Abs_pmf M) = pmf_of_set A"
    by (rule pmf_eqI, simp add:assms pmf_map vimage_def a)

  thus ?thesis
    using assms uniform_on_def by blast
qed


end