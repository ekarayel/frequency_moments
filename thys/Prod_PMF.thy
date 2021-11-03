section \<open>Product Combinator for Probability Mass Functions\<close>

theory Prod_PMF
  imports Main "HOL-Probability.Probability_Mass_Function" "HOL-Probability.Stream_Space"
      "HOL-Probability.Independent_Family" Probability_Ext 
begin

text \<open>Alternative version of @{thm [source] product_sigma_finite.emeasure_PiM} 
where @{term "M i"} has to be a sigma finite measure \emph{only} for @{term "i \<in> I"}.\<close>
lemma emeasure_prod:
  assumes "\<And>i. i \<in> I \<Longrightarrow> sigma_finite_measure (M i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  assumes "finite I"
  shows "emeasure (PiM I M) (PiE I A) = (\<Prod> i \<in> I. emeasure (M i) (A i))"
proof -
  define M' where "M' = (\<lambda>i. if i \<in> I then M i else count_space {undefined})" 

  interpret product_sigma_finite M'
    apply (simp add:product_sigma_finite_def M'_def)
    by (metis assms(1) finite.emptyI finite_insert sigma_finite_measure_count_space_finite)

  have a:"\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M' i)"
    using assms(2) M'_def by simp
  have b:"PiM I M = PiM I M'"
    by (rule PiM_cong, simp, simp add:M'_def)
  have c:"\<And>i. i \<in> I \<Longrightarrow> emeasure (M i) = emeasure (M' i)"
    by (simp add:M'_def)  
  show ?thesis by (simp add:b c emeasure_PiM[OF assms(3) a]) 
qed

lemma count_space_prod:
  assumes "\<And>i. i \<in> I \<Longrightarrow> countable (M i)"
  assumes "finite I"
  shows "count_space (PiE I M) = PiM I (count_space \<circ> M)"
proof -
  have a:"countable (PiE I M)" using countable_PiE assms by blast

  have b:"\<And>s. s \<in>  Pi\<^sub>E I M \<Longrightarrow> (PiE I (\<lambda>i. {s i})) \<in> prod_algebra I (count_space \<circ> M)"
    by (rule prod_algebraI_finite, metis assms(2), simp add:PiE_iff)
  have c: "\<And>s. s \<in> PiE I M \<Longrightarrow> (PiE I (\<lambda>i. {s i})) = {s}" 
    by (metis (mono_tags, lifting) PiE_eq_singleton PiE_restrict)
  have d:" (\<lambda>s. {s}) ` Pi\<^sub>E I M \<subseteq> prod_algebra I (count_space \<circ> M)"
    apply (rule subsetI) using b c by auto

  show ?thesis
    apply (rule measure_eqI_countable, simp)
      apply (simp add:sets_PiM)
      apply (rule order_antisym)
       apply (rule sigma_algebra.sigma_sets_subset, rule sigma_algebra_Pow)
       using prod_algebra_sets_into_space[where M="\<lambda>i. count_space (M i)", simplified] 
       apply (simp add: comp_def)
      apply (subst sigma_sets_singletons[OF a, symmetric])
      apply (rule sigma_sets_subseteq)
      apply (metis d)
     apply (metis a)
    apply (simp)
    apply (subst c[symmetric], simp)
    apply (subst emeasure_prod)
       apply (simp add: sigma_finite_measure_count_space_countable assms(1))
      apply (simp add: PiE_iff)
     apply (metis assms(2))
    by (simp add:comp_def emeasure_count_space PiE_iff)
qed

context 
  fixes I :: "'a set"
  assumes finite_I: "finite I"
  fixes M :: "'a \<Rightarrow> 'b pmf"
begin
lift_definition prod_pmf :: "('a \<Rightarrow> 'b) pmf" is "(\<lambda>x. (if x \<in> extensional I then \<Prod>i \<in> I. (pmf (M i)) (x i) else 0))"
proof -
  have a: "count_space (PiE I (set_pmf \<circ> M)) = PiM I (\<lambda>i. count_space (set_pmf ( M i)))"
    using count_space_prod countable_set_pmf 
    by (metis (mono_tags, lifting) PiM_cong comp_def finite_I) 

  have b: "\<And>i. i \<in> I \<Longrightarrow> integral\<^sup>N (count_space (set_pmf (M i))) (pmf (M i)) = 1"
    by (simp add: emeasure_pmf nn_integral_pmf)
  have "integral\<^sup>N (count_space UNIV) (\<lambda>x. ennreal (if x \<in> extensional I then \<Prod>i\<in>I. pmf (M i) (x i) else 0)) = 
    integral\<^sup>N (count_space UNIV) (\<lambda>x. ((\<Prod>i\<in>I. ennreal (pmf (M i) (x i)))) * indicator (PiE I (set_pmf \<circ> M)) x)"
  proof (rule nn_integral_cong)
    fix x :: "'a \<Rightarrow> 'b"
    assume "x \<in> space (count_space UNIV)"
    show "ennreal (if x \<in> extensional I then \<Prod>i\<in>I. pmf (M i) (x i) else 0) =
          (\<Prod>i\<in>I. ennreal(pmf (M i) (x i))) * indicator (Pi\<^sub>E I (set_pmf \<circ> M)) x"
      apply (cases "x \<in> PiE I (set_pmf \<circ> M)", simp add:PiE_def prod_ennreal)
      apply (simp add:PiE_def Pi_def)
      apply (rule impI, simp add:ennreal_eq_0_iff)
      apply (rule order_eq_refl)
      using finite_I apply (simp)
      by (metis set_pmf_iff)
  qed
  also have "... = integral\<^sup>N (count_space (PiE I (set_pmf \<circ> M))) (\<lambda>x. (\<Prod>i\<in>I. ennreal (pmf (M i) (x i))))"
    by (subst nn_integral_restrict_space[symmetric], simp, simp add:restrict_count_space)
  also have "... = integral\<^sup>N (\<Pi>\<^sub>M i \<in> I. count_space (set_pmf (M i))) (\<lambda>x. (\<Prod>i\<in>I. ennreal (pmf (M i) (x i))))"
    by (subst a, simp)
  also have "... = 1"
    apply (subst product_sigma_finite.product_nn_integral_prod)
       apply (simp add:product_sigma_finite_def)
       using countable_set_pmf 
       apply (simp add: sigma_finite_measure_count_space_countable)
      apply (metis finite_I)
     apply simp
    by (simp add:b)
  finally have "integral\<^sup>N (count_space UNIV) (\<lambda>x. ennreal (if x \<in> extensional I then \<Prod>i\<in>I. pmf (M i) (x i) else 0)) = 1" 
    by simp
  moreover have "\<And>x. 0 \<le> (if x \<in> extensional I then \<Prod>i\<in>I. pmf (M i) (x i) else 0)" (is "\<And>x. ?ths x")
  proof -
    fix x
    show "?ths x"
      apply (cases "x \<in> extensional I")
       apply (simp, rule prod_nonneg, fastforce)
      by simp
  qed
  ultimately show ?thesis by blast
qed
end

lemma pmf_prod_pmf: 
  assumes "finite I"
  shows "pmf (prod_pmf I M) x = (if x \<in> extensional I then \<Prod>i \<in> I. (pmf (M i)) (x i) else 0)"
  by (simp add: prod_pmf.rep_eq[OF assms])

lemma set_prod_pmf:
  assumes "finite I"
  shows "set_pmf (prod_pmf I M) = PiE I (set_pmf \<circ> M)"
  apply (simp add:set_pmf_eq pmf_prod_pmf[OF assms(1)] prod_zero_iff[OF assms(1)])
  apply (simp add:set_pmf_iff[symmetric] PiE_def Pi_def)
  by blast

lemma set_pmf_iff': "x \<notin> set_pmf M \<longleftrightarrow> pmf M x = 0"
  using set_pmf_iff by metis

lemma prob_prod_pmf: 
  assumes "finite I"
  shows "measure (measure_pmf (prod_pmf I M)) (Pi I A) = (\<Prod> i \<in> I. measure (M i) (A i))"
proof -
  have "integral\<^sup>L (count_space (Pi I A)) (pmf (prod_pmf I M)) = 
    integral\<^sup>L (count_space (Pi I A)) (\<lambda>x. indicat_real (PiE I (set_pmf \<circ> M)) x *\<^sub>R pmf (prod_pmf I M) x)"
    by (rule Bochner_Integration.integral_cong, simp, simp add:indicator_def set_pmf_iff'[symmetric] set_prod_pmf[OF assms(1)])
  also have "... = integral\<^sup>L (count_space (PiE I (\<lambda>i. if i \<in> I then (A i \<inter> set_pmf (M i)) else {undefined})))  (\<lambda>\<omega>. \<Prod> i \<in> I. pmf (M i) (\<omega> i))"
    apply (subst integral_restrict_space[symmetric], simp, simp add:restrict_count_space)
    apply (rule Bochner_Integration.integral_cong)
     apply (rule arg_cong[where f="count_space"])
     apply (rule order_antisym, rule subsetI, simp add:Pi_def PiE_def, rule subsetI, simp add:Pi_def PiE_def, simp)
    by (simp add:pmf_prod_pmf[OF assms(1)] PiE_def)
  also have "... = (\<Prod>i\<in>I. integral\<^sup>L ((count_space \<circ> (\<lambda>i. if i \<in> I then A i \<inter> set_pmf (M i) else {undefined})) i) (pmf (M i)))"
    apply (subst count_space_prod, simp, metis assms)
    apply (subst product_sigma_finite.product_integral_prod)
       apply (simp add:product_sigma_finite_def)
       apply (metis countable_Int2 countable_empty countable_insert  sigma_finite_measure_count_space_countable countable_set_pmf)
      apply (metis assms)
     apply (simp add:comp_def integrable_pmf)
    by simp
  also have "... = (\<Prod> i \<in> I. integral\<^sup>L (count_space (A i)) (\<lambda>x. indicat_real (set_pmf (M i)) x *\<^sub>R pmf (M i) x))"
    apply (rule prod.cong, simp)
    by (subst integral_restrict_space[symmetric], simp, simp add:restrict_count_space inf_commute)
  also have "... = (\<Prod> i \<in> I. integral\<^sup>L (count_space (A i)) (pmf (M i)))"
    apply (rule prod.cong, simp)
    by (rule Bochner_Integration.integral_cong, simp, simp add:indicator_def set_pmf_iff'[symmetric])
  finally have r:"integral\<^sup>L (count_space (Pi I A)) (pmf (prod_pmf I M)) = (\<Prod> i \<in> I. integral\<^sup>L (count_space (A i)) (pmf (M i)))"
    by blast

  show ?thesis
    apply (subst (1 2) integral_pmf[symmetric])
    by (metis r)
qed

lemma prob_prod_pmf': 
  assumes "finite I"
  assumes "J \<subseteq> I"
  shows "measure (measure_pmf (prod_pmf I M)) (Pi J A) = (\<Prod> i \<in> J. measure (M i) (A i))"
proof -
  have a:"Pi J A = Pi I (\<lambda>i. if i \<in> J then A i else UNIV)"
    apply (simp add:Pi_def)
    apply (rule Collect_cong)
    using assms(2) by blast
  show ?thesis
    apply (simp add:if_distrib  a prob_prod_pmf[OF assms(1)] prod.If_cases[OF assms(1)])
    apply (rule arg_cong2[where f="prod"], simp)
    using assms(2) by blast
qed

lemma prob_prod_pmf_slice:
  assumes "finite I"
  assumes "i \<in> I"
  shows "measure (measure_pmf (prod_pmf I M)) {\<omega>. P (\<omega> i)} = measure (M i) {\<omega>. P \<omega>}"
  using prob_prod_pmf'[OF assms(1), where J="{i}" and M="M" and A="\<lambda>_. Collect P"]
  by (simp add:assms Pi_def)

lemma range_inter: "range ((\<inter>) F) = Pow F"
  apply (rule order_antisym, rule subsetI, simp add:image_def, blast)
  by (rule subsetI, simp add:image_def, blast)


lemma indep_vars_pmf:
  assumes "\<And>a J. J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> 
    \<P>(\<omega> in measure_pmf M. \<forall>i \<in> J. X i \<omega> = a i) = (\<Prod>i \<in> J. \<P>(\<omega> in measure_pmf M. X i \<omega> = a i))"
  shows "prob_space.indep_vars (measure_pmf M) (\<lambda>i. measure_pmf ( M' i)) X I"
proof -
  define G where "G = (\<lambda>i. {{}} \<union> (\<lambda>x. {x}) ` (X i ` set_pmf M))"
  define F where "F = (\<lambda>i. {X i -` a \<inter> set_pmf M|a. a \<in> G i})"

  have g: "\<And>i. i \<in> I \<Longrightarrow> sigma_sets (X i ` set_pmf M) (G i) = Pow (X i ` set_pmf M)"
    by (simp add:G_def, metis countable_image countable_set_pmf sigma_sets_singletons_and_empty)

  have e: "\<And>i. i \<in> I \<Longrightarrow> F i \<subseteq> Pow (set_pmf M)"
    by (simp add:F_def, rule subsetI, simp, blast)

  have a:"distr (restrict_space (measure_pmf M) (set_pmf M)) (measure_pmf M) id = measure_pmf M"
    apply (rule measure_eqI, simp, simp)
    apply (subst emeasure_distr)
    apply (simp add:measurable_def sets_restrict_space) 
      apply blast
     apply simp
    apply (simp add:emeasure_restrict_space)
    by (metis emeasure_Int_set_pmf)

  have b: "prob_space (restrict_space (measure_pmf M) (set_pmf M))"
    apply (rule prob_spaceI)
    apply simp
    apply (subst emeasure_restrict_space, simp, simp)
    using emeasure_pmf by blast

  have d:"\<And>i. i \<in> I \<Longrightarrow> {u. \<exists>A. u = X i -` A \<inter> set_pmf M} = sigma_sets (set_pmf M) (F i)"
  proof -
    fix i
    assume d1:"i \<in> I"
    have d2: "\<And>A. X i -` A \<inter> set_pmf M = X i -` (A \<inter> X i ` set_pmf M) \<inter> set_pmf M"
      apply (rule order_antisym)
      by (rule subsetI, simp)+
    show " {u. \<exists>A. u = X i -` A \<inter> set_pmf M} = sigma_sets (set_pmf M) (F i)"
      apply (simp add:F_def)
      apply (subst sigma_sets_vimage_commute[symmetric, where \<Omega>' = "X i ` set_pmf M"], blast)
      using d1 apply (simp add:g)
      apply (rule order_antisym)
       apply (rule subsetI, simp, meson inf_le2 d2)
      by (rule subsetI, simp, blast)
  qed

  have h:"\<And>J A. J \<subseteq> I \<Longrightarrow> J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> A\<in>Pi J F \<Longrightarrow>
               Sigma_Algebra.measure (restrict_space (measure_pmf M) (set_pmf M)) (\<Inter> (A ` J)) =
               (\<Prod>j\<in>J. Sigma_Algebra.measure (restrict_space (measure_pmf M) (set_pmf M)) (A j))"
  proof -
    fix J A
    assume h1: "J \<subseteq> I"
    assume h2: "J \<noteq> {}"
    assume h3:"finite J"
    assume h4: "A \<in> Pi J F"

    have h5: "\<And>j. j \<in> J \<Longrightarrow> A j \<subseteq> set_pmf M"
      by (metis PiE PowD h1 subsetD e h4)
    obtain a where h6:"\<And>j. j \<in> J  \<Longrightarrow> A j = X j -` a j \<inter> set_pmf M \<and> a j \<in> G j"
      using h4 by (simp add:Pi_def F_def, metis)

    show "Sigma_Algebra.measure (restrict_space (measure_pmf M) (set_pmf M)) (\<Inter> (A ` J)) =
               (\<Prod>j\<in>J. Sigma_Algebra.measure (restrict_space (measure_pmf M) (set_pmf M)) (A j))"
    proof (cases "\<exists>j \<in> J. A j = {}")
      case True
      hence "\<Inter> (A ` J) = {}" by blast
      then show ?thesis
        using h3 True apply simp 
        by (metis measure_empty)
    next
      case False
      then have "\<And>j. j \<in> J \<Longrightarrow> a j \<noteq> {}" using h6 by auto
      hence "\<And>j. j \<in> J \<Longrightarrow> a j \<in> (\<lambda>x. {x}) ` X j ` set_pmf M" using h6 by (simp add:G_def) 
      then obtain b where h7: "\<And>j. j \<in> J \<Longrightarrow> a j = {b j}" by (simp add:image_def, metis) 

      have "Sigma_Algebra.measure (restrict_space (measure_pmf M) (set_pmf M)) (\<Inter> (A ` J)) =
        Sigma_Algebra.measure (measure_pmf M) (\<Inter> j \<in> J. A j)"
        apply (subst measure_restrict_space, simp)
        using h5 h2 apply blast
        by simp
      also have "... = Sigma_Algebra.measure (measure_pmf M) ({\<omega>. \<forall>j \<in> J. X j \<omega> = b j})"
        using h2 h6 h7 apply (simp add:vimage_def measure_Int_set_pmf)
        by (rule arg_cong2 [where f="measure"], simp, blast)
      also have "... = (\<Prod> j\<in> J. Sigma_Algebra.measure (measure_pmf M) (A j))"
        using h6 h7 h2 assms(1)[OF h1 h3] by (simp add:vimage_def measure_Int_set_pmf)
      also have "... = (\<Prod>j\<in>J. Sigma_Algebra.measure (restrict_space (measure_pmf M) (set_pmf M)) (A j))"
        by (rule prod.cong, simp, subst measure_restrict_space, simp, metis h5, simp)
      finally show ?thesis by blast
    qed
  qed

  have i: "\<And>i. i \<in> I \<Longrightarrow> Int_stable (F i)"
  proof (rule Int_stableI)
    fix i a b
    assume "i \<in> I"
    assume "a \<in> F i"
    moreover assume "b \<in> F i"
    ultimately show "a \<inter> b \<in> (F i)"
      apply (cases "a \<inter> b = {}", simp add:F_def G_def, blast)
      by (simp add:F_def G_def, blast)
  qed

  have c: "prob_space.indep_sets (restrict_space (measure_pmf M) (set_pmf M)) (\<lambda>i. {u. \<exists>A. u = X i -` A \<inter> set_pmf M}) I"
    apply (simp add: d cong:prob_space.indep_sets_cong[OF b])
    apply (rule prob_space.indep_sets_sigma[where M="restrict_space (measure_pmf M) (set_pmf M)", simplified])
      apply (metis b)
     apply (subst prob_space.indep_sets_def, metis b, simp add:sets_restrict_space range_inter e)
     apply (metis h)
    by (metis i)
  
  show ?thesis
    apply (subst a [symmetric])
    apply (rule indep_vars_distr)
    apply (simp add:measurable_def sets_restrict_space) 
       apply blast
      apply simp
    apply simp
    apply (subst prob_space.indep_vars_def2)
      apply (metis b)
     apply (simp add:measurable_def sets_restrict_space range_inter)
    by (metis c, metis b)
qed

lemma indep_vars_restrict:
  fixes M :: "'a \<Rightarrow> 'b pmf"
  fixes J :: "'c set"
  assumes "disjoint_family_on f J"
  assumes "J \<noteq> {}"
  assumes "\<And>i. i \<in> J \<Longrightarrow> f i \<subseteq> I"
  assumes "finite I"
  shows "prob_space.indep_vars (measure_pmf (prod_pmf I M)) (\<lambda>i. measure_pmf (prod_pmf (f i) M)) (\<lambda>i \<omega>. restrict \<omega> (f i)) J"
proof (rule indep_vars_pmf[simplified])
  fix a :: "'c \<Rightarrow> 'a \<Rightarrow> 'b"
  fix J'
  assume e:"J' \<subseteq> J"
  assume c:"finite J'"
  show "measure_pmf.prob (prod_pmf I M) {\<omega>. \<forall>i\<in>J'. restrict \<omega> (f i) = a i} =
       (\<Prod>i\<in>J'. measure_pmf.prob (prod_pmf I M) {\<omega>. restrict \<omega> (f i) = a i})"
  proof (cases "\<forall>j \<in> J'. a j \<in> extensional (f j)")
    case True
    define b where "b = (\<lambda>i. if i \<in> (\<Union> (f ` J')) then a (THE j. i \<in> f j \<and> j \<in> J') i else undefined)" 
    have b_def:"\<And>i. i \<in> J' \<Longrightarrow> a i = restrict b (f i)"
    proof -
      fix i 
      assume b_def_1:"i \<in> J'"
      have b_def_2: "\<And>x. x \<in> f i \<Longrightarrow> i = (THE j. x \<in> f j \<and> j \<in> J')"
        using disjoint_family_on_mono[OF e assms(1)] b_def_1 
        apply (simp add:disjoint_family_on_def) 
        by (metis (mono_tags, lifting) IntI empty_iff the_equality)
      show "a i = restrict b (f i)"
        apply (rule extensionalityI[where A ="f i"]) using b_def_1 True apply blast
         apply (rule restrict_extensional)
        apply (simp add:restrict_apply' b_def b_def_2[symmetric])
        using b_def_1 by force
    qed    
    have a:"{\<omega>. \<forall>i\<in>J'. restrict \<omega> (f i) = a i} = Pi (\<Union> (f ` J')) (\<lambda>i. {b i})"
      apply (simp add:b_def)
      apply (rule order_antisym)
       apply (rule subsetI, simp add:Pi_def, metis restrict_apply')
      by (rule subsetI, simp add:Pi_def, meson assms(3) e restrict_ext singletonD subsetD)
    have b:"\<And>i. i \<in> J' \<Longrightarrow> {\<omega>. restrict \<omega> (f i) = a i} = Pi (f i) (\<lambda>i. {b i})"
      apply (simp add:b_def)
      apply (rule order_antisym)
       apply (rule subsetI, simp add:Pi_def, metis restrict_apply')
      by (rule subsetI, simp add:Pi_def, meson assms(3) e restrict_ext singletonD subsetD)
    show ?thesis
      apply (simp add: a b)
      apply (subst prob_prod_pmf'[OF assms(4)], meson UN_least e in_mono assms(3))
      apply (subst prod.UNION_disjoint, metis c)
        apply (metis in_mono  e assms(3) assms(4) finite_subset)
       apply (metis e  disjoint_family_on_def assms(1) subset_eq)
      apply (rule prod.cong, simp)
      apply (subst prob_prod_pmf'[OF assms(4)]) using e assms(3) apply blast
      by simp
  next
    case False
    then obtain j where j_def: "j \<in> J'" and "a j \<notin> extensional (f j)" by blast
    hence "\<And>\<omega>. restrict \<omega> (f j) \<noteq> a j" by (metis restrict_extensional)
    then show ?thesis 
      by (metis (mono_tags, lifting) Collect_empty_eq j_def c measure_empty prod_zero_iff)
  qed
qed  

lemma indep_vars_restrict_intro:
  fixes M :: "'a \<Rightarrow> 'b pmf"
  fixes J :: "'c set"
  assumes "\<And>\<omega> i. i \<in> J \<Longrightarrow>  X i \<omega> = X i (restrict \<omega> (f i))"
  assumes "disjoint_family_on f J"
  assumes "J \<noteq> {}"
  assumes "\<And>i. i \<in> J \<Longrightarrow> f i \<subseteq> I"
  assumes "finite I"
  assumes "\<And>\<omega> i. i \<in> J \<Longrightarrow>  X i \<omega> \<in> space (M' i)"
  shows "prob_space.indep_vars (measure_pmf (prod_pmf I M)) M' (\<lambda>i \<omega>. X i \<omega>) J"
proof -
  have "prob_space.indep_vars (measure_pmf (prod_pmf I M)) M' (\<lambda>i \<omega>. X i (restrict \<omega> (f i))) J" (is ?A)
    apply (rule prob_space.indep_vars_compose2[where X="\<lambda>i \<omega>. restrict \<omega> (f i)"])
      apply (metis prob_space_measure_pmf)
     apply (rule indep_vars_restrict, metis assms(2), metis assms(3), metis assms(4), metis assms(5))
    apply simp using assms(6) by blast
  moreover have "?A = ?thesis"
    apply (rule prob_space.indep_vars_cong, metis prob_space_measure_pmf, simp)
    by (rule ext, metis assms(1), simp)
  ultimately show ?thesis by blast
qed

lemma has_bochner_integral_prod_pmfI:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> has_bochner_integral (measure_pmf (M i)) (f i) (r i)"
  shows "has_bochner_integral (prod_pmf I M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) (\<Prod>i \<in> I. r i)"
proof -
  define M' where "M' = (\<lambda>i. if i \<in> I then restrict_space (measure_pmf (M i)) (set_pmf (M i)) else count_space {undefined})"

  have a:"\<And>i. i \<in> I \<Longrightarrow> finite_measure (restrict_space (measure_pmf (M i)) (set_pmf (M i)))"
    apply (rule finite_measureI)
    by (simp add:emeasure_restrict_space)

  interpret product_sigma_finite M'
    apply (simp add:product_sigma_finite_def M'_def)
    by (metis a finite_measure.axioms(1) finite.emptyI finite_insert sigma_finite_measure_count_space_finite)

  have "\<And>i. i \<in> I \<Longrightarrow> has_bochner_integral (M' i) (f i) (r i)"
    apply (simp add:M'_def has_bochner_integral_restrict_space)
    apply (rule has_bochner_integralI_AE[OF assms(2)], simp, simp)
    by (subst AE_measure_pmf_iff, simp)

  hence b:"has_bochner_integral (PiM I M') (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) (\<Prod>i \<in> I. r i)"
    apply (subst has_bochner_integral_iff)
    apply (rule conjI)
     apply (rule product_integrable_prod[OF assms(1)])
     apply (simp add: has_bochner_integral_iff)
    apply (subst  product_integral_prod[OF assms(1)])
    apply (simp add: has_bochner_integral_iff)
    apply (rule prod.cong, simp)
    by (simp add: has_bochner_integral_iff)

  have d:"sets (Pi\<^sub>M I M') = Pow (Pi\<^sub>E I (set_pmf \<circ> M))"
    apply (simp add:sets_PiM M'_def comp_def cong:PiM_cong)
    apply (rule order_antisym)
     apply (rule subsetI)
     apply (simp)
     apply (rule sigma_sets_into_sp [where A="prod_algebra I (\<lambda>x. restrict_space (measure_pmf (M x)) (set_pmf (M x)))"])
      apply (metis (mono_tags, lifting)  prod_algebra_sets_into_space space_restrict_space PiE_cong UNIV_I sets_measure_pmf space_restrict_space2)
     apply simp
    apply (subst sigma_sets_singletons[symmetric])
     apply (rule countable_PiE, metis assms(1), metis countable_set_pmf)
    apply (rule sigma_sets_subseteq)
    apply (rule image_subsetI)
    apply (subst PiE_singleton[symmetric, where A="I"], simp add:PiE_def)
    apply (rule prod_algebraI_finite, metis assms(1))
    apply (simp add:sets_restrict_space PiE_iff image_def)
    by blast

  have c:"PiM I M' = restrict_space (measure_pmf (prod_pmf I M)) (PiE I (set_pmf \<circ> M))"
    apply (rule measure_eqI_countable[where A="PiE I (set_pmf \<circ> M)"])
       apply (metis d)
      apply (simp add:sets_restrict_space image_def, fastforce)
     apply (rule countable_PiE, metis assms(1), simp add:comp_def)
    apply (subst PiE_singleton[symmetric, where A="I"], simp add:PiE_def)
    apply (subst emeasure_PiM, metis assms(1), simp add:M'_def sets_restrict_space, fastforce)
    apply (subst emeasure_restrict_space, simp, simp)
    apply (simp add:emeasure_pmf_single pmf_prod_pmf[OF assms(1)] PiE_def prod_ennreal[symmetric] M'_def)
    apply (rule prod.cong, simp)
    apply (subst emeasure_restrict_space, simp, simp add:Pi_iff)
    by (simp add:emeasure_pmf_single)

  have a:"has_bochner_integral (prod_pmf I M) (\<lambda>x. indicator (PiE I (set_pmf \<circ> M)) x *\<^sub>R (\<Prod>i \<in> I. f i (x i))) (\<Prod>i \<in> I. r i)"
    apply (subst Lebesgue_Measure.has_bochner_integral_restrict_space[symmetric], simp)
    by (subst c[symmetric], metis b)

  have "(\<lambda>x. \<Prod>i \<in> I. f i (x i)) \<in> borel_measurable (prod_pmf I M)"
    by simp
  show "has_bochner_integral (prod_pmf I M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) (\<Prod>i \<in> I. r i)"
    apply (rule has_bochner_integralI_AE[OF a], simp)
    apply (subst AE_measure_pmf_iff)
    using assms by (simp add:set_prod_pmf)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable (measure_pmf (M i)) (f i)"
  shows prod_pmf_integrable: "integrable (prod_pmf I M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i)))" (is ?A) and
   prod_pmf_integral: "integral\<^sup>L (prod_pmf I M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) = 
    (\<Prod> i \<in> I. integral\<^sup>L (M i) (f i))" (is ?B)
proof -
  have a:"has_bochner_integral (prod_pmf I M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i)))  (\<Prod> i \<in> I. integral\<^sup>L (M i) (f i))"
    apply (rule has_bochner_integral_prod_pmfI[OF assms(1)])
    by (rule has_bochner_integral_integrable[OF assms(2)], simp)
  show ?A using a has_bochner_integral_iff by blast
  show ?B using a has_bochner_integral_iff by blast
qed

lemma has_bochner_integral_prod_pmf_sliceI:
  fixes f :: "'a \<Rightarrow> ('b :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "has_bochner_integral (measure_pmf (M i)) (f) r"
  shows "has_bochner_integral (prod_pmf I M) (\<lambda>x. (f (x i))) r"
proof -
  define g where "g = (\<lambda>j \<omega>. if j = i then f \<omega> else 1)"

  have b: "\<And>M. has_bochner_integral (measure_pmf M) (\<lambda>\<omega>. 1::'b) 1"
    apply (subst has_bochner_integral_iff, rule conjI, simp)
    by (subst lebesgue_integral_const, simp)
  
  have a:"\<And>j. j \<in> I \<Longrightarrow> has_bochner_integral (measure_pmf (M j)) (g j) (if j = i then r else 1)"
    using assms(3) by (simp add:g_def b)
  have "has_bochner_integral (prod_pmf I M) (\<lambda>x. (\<Prod>j \<in> I. g j (x j))) (\<Prod>j \<in> I. if j = i then r else 1)"
    by (rule has_bochner_integral_prod_pmfI[OF assms(1)], metis a)
  thus ?thesis
    using assms(2) by (simp add:g_def prod.If_cases[OF assms(1)])
qed

lemma
  fixes f :: "'a \<Rightarrow> ('b :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "integrable (measure_pmf (M i)) f"
  shows integrable_prod_pmf_slice: "integrable (prod_pmf I M) (\<lambda>x. (f (x i)))" (is ?A) and
   integral_prod_pmf_slice: "integral\<^sup>L (prod_pmf I M) (\<lambda>x. (f (x i))) = integral\<^sup>L (M i) f" (is ?B)
proof -
  have a:"has_bochner_integral (prod_pmf I M) (\<lambda>x. (f (x i))) (integral\<^sup>L (M i) f)"
    apply (rule has_bochner_integral_prod_pmf_sliceI[OF assms(1) assms(2)])
    using assms(3) by (simp add: has_bochner_integral_iff)
  show ?A using a has_bochner_integral_iff by blast
  show ?B using a has_bochner_integral_iff by blast
qed

lemma has_variance_prod_pmf_sliceI:
  assumes "i \<in> I"
  assumes "finite I"
  assumes "has_variance (measure_pmf (M i)) f r"
  shows "has_variance (prod_pmf I M) (\<lambda>\<omega>. f (\<omega> i)) r"
proof -
  have a:"integrable (measure_pmf (M i)) f" 
    using assms(3) by (simp add:has_variance_def) 
  have b:"integrable (measure_pmf (M i)) (\<lambda>\<omega>. (f \<omega>)\<^sup>2)" 
    using assms(3) by (simp add:has_variance_def) 
  have c:"integrable (measure_pmf (prod_pmf I M)) (\<lambda>\<omega>. f (\<omega> i))"
    by (rule integrable_prod_pmf_slice[OF assms(2) assms(1)], metis a)
  have d:"integrable (measure_pmf (prod_pmf I M)) (\<lambda>\<omega>. (f (\<omega> i))\<^sup>2)" 
    by (rule integrable_prod_pmf_slice[OF assms(2) assms(1)], metis b)

  have e:"r (prob_space.variance (measure_pmf (prod_pmf I M)) (\<lambda>\<omega>. f(\<omega> i)))"
    apply (subst prob_space.variance_eq, metis prob_space_measure_pmf, metis c, metis d)
    apply (subst integral_prod_pmf_slice[OF assms(2) assms(1)], metis b)
    apply (subst integral_prod_pmf_slice[OF assms(2) assms(1)], metis a)
    apply (subst prob_space.variance_eq[symmetric], metis prob_space_measure_pmf, metis a, metis b)
    using assms(3) by (simp add:has_variance_def)
  show ?thesis
    by (simp add:has_variance_def, metis c d e prob_space_measure_pmf)
qed

lemma pmf_of_set_prod:
  assumes "finite I"
  assumes "\<And>x. x \<in> I \<Longrightarrow> finite (M x)"
  assumes "\<And>x. x \<in> I \<Longrightarrow> M x \<noteq> {}"
  shows "pmf_of_set (PiE I M) = prod_pmf I (\<lambda>i. pmf_of_set (M i))"
proof -
  have a:"\<And>f. indicat_real (Pi\<^sub>E I M) f / real (card (Pi\<^sub>E I M)) =
    (if f \<in> extensional I then (\<Prod>i\<in>I. indicat_real (M i) (f i) / real (card (M i)))  else 0)" (is "\<And>f. ?a f")
  proof -
    fix f
    show "?a f"
      apply (cases "f \<in> extensional I")
       apply (cases "f \<in> PiE I M") 
        apply (simp add: card_PiE[OF assms(1)])
        apply (simp add:PiE_iff indicator_def Pi_def)
       apply (simp add: prod_dividef[where f= "\<lambda>_. 1" , simplified])
       apply (simp, simp add:PiE_iff prod_dividef indicator_def assms)
      by (simp add:PiE_def)
  qed

  show ?thesis
  apply (rule pmf_eqI)
  apply (subst pmf_of_set, metis PiE_eq_empty_iff assms(3), metis finite_PiE assms(1) assms(2))
  apply (subst pmf_prod_pmf, metis assms(1))
  using a assms by simp
qed


lemma extensionality_iff:
  assumes "f \<in> extensional I"
  shows "((\<lambda>i \<in> I. g i) = f) = (\<forall>i \<in> I. g i = f i)"
  using assms apply (simp add:extensional_def restrict_def) by auto

lemma of_bool_prod:
  assumes "finite I"
  shows "of_bool (\<forall>i \<in> I. P i) = (\<Prod>i \<in> I. (of_bool (P i) :: 'a :: field))"
  using assms by (induction I rule:finite_induct, simp, simp)

lemma map_ptw:
  fixes I :: "'a set"
  fixes M :: "'a \<Rightarrow> 'b pmf" 
  fixes f :: "'b \<Rightarrow> 'c"
  assumes "finite I"
  shows "prod_pmf I M \<bind> (\<lambda>x. return_pmf (\<lambda>i \<in> I. f (x i))) = prod_pmf I (\<lambda>i. (M i \<bind> (\<lambda>x. return_pmf (f x))))"
proof (rule pmf_eqI)
  fix i :: "'a \<Rightarrow> 'c"

  have a:"\<And>x. i \<in> extensional I \<Longrightarrow> (of_bool ((\<lambda>j\<in>I. f (x j)) = i) :: real) = (\<Prod>j \<in> I. of_bool (f (x j) = i j))"
    apply (subst extensionality_iff, simp)
    by (rule of_bool_prod[OF assms(1)])

  have b:"\<And>x. i \<notin> extensional I \<Longrightarrow> of_bool ((\<lambda>j\<in>I. f (x j)) = i) = 0"
    by auto

  show "pmf (prod_pmf I M \<bind> (\<lambda>x. return_pmf (\<lambda>i\<in>I. f (x i)))) i = pmf (prod_pmf I (\<lambda>i. M i \<bind> (\<lambda>x. return_pmf (f x)))) i"
  apply (subst pmf_bind)
  apply (subst pmf_prod_pmf) defer
  apply (subst pmf_bind)
   apply (simp add:indicator_def)
   apply (rule conjI, rule impI)
      apply (subst a, simp)
      apply (subst prod_pmf_integral[OF assms(1)])
       apply (rule finite_measure.integrable_const_bound[where B="1"], simp, simp, simp, simp)
    by (simp add:b, metis assms(1))
qed

lemma pair_pmfI:
  "A \<bind> (\<lambda>a. B \<bind> (\<lambda>b. return_pmf (f a b))) = pair_pmf A B \<bind> (\<lambda>(a,b). return_pmf (f a b))"
  apply (simp add:pair_pmf_def)
  apply (subst bind_assoc_pmf)
  apply (subst bind_assoc_pmf)
  by (simp add:bind_return_pmf)

lemma pmf_pair':
  "pmf (pair_pmf M N) x = pmf M (fst x) * pmf N (snd x)"
  by (cases x,simp add:pmf_pair)

lemma pair_pmf_ptw:
  assumes "finite I"
  shows "pair_pmf (prod_pmf I A :: (('i \<Rightarrow> 'a) pmf)) (prod_pmf I B :: (('i \<Rightarrow> 'b) pmf)) = 
    prod_pmf I (\<lambda>i. pair_pmf (A i) (B i)) \<bind> 
      (\<lambda>f. return_pmf (restrict (fst \<circ> f) I, restrict (snd \<circ> f) I))"
    (is "?lhs = ?rhs")
proof -
  define h where "h = (\<lambda>f x. 
    if x \<in> I then 
      f x 
    else (
      if (f x) = undefined then 
        (undefined :: 'a,undefined :: 'b)
      else (
        if (f x) = (undefined,undefined) then 
          undefined 
        else
          f x)))"

  have h_h_id: "\<And>f. h (h f) = f"
    apply (rule ext)
    by (simp add:h_def)
  
  have b:"\<And>i g. i \<in> I \<Longrightarrow> h g i = g i" 
    by (simp add:h_def)

  have a:"inj (\<lambda>f. (fst \<circ> h f, snd \<circ> h f))"
  proof (rule injI)
    fix x y
    assume "(fst \<circ> h x, snd \<circ> h x) = (fst \<circ> h y, snd \<circ> h y)"
    hence a1:"h x = h y"
      by (simp, metis convol_expand_snd)
    show "x = y"
      apply (rule ext)
      using a1 apply (simp add:h_def) 
      by (metis (no_types, opaque_lifting))
  qed

  have c:"\<And>g. (fst \<circ> h g \<in> extensional I \<and> snd \<circ> h g \<in> extensional I) = (g \<in> extensional I)" 
    apply (rule order_antisym)
    apply (simp add:h_def extensional_def) 
     apply (metis prod.collapse)
    by (simp add:h_def extensional_def) 

  have "pair_pmf (prod_pmf I A :: (('i \<Rightarrow> 'a) pmf)) (prod_pmf I B :: (('i \<Rightarrow> 'b) pmf)) = prod_pmf I (\<lambda>i. pair_pmf (A i) (B i)) \<bind>
      (\<lambda>f. return_pmf (fst \<circ> h f, snd \<circ> h f))"
  proof (rule pmf_eqI)
    fix f
    define g where "g = h (\<lambda>i. (fst f i, snd f i))"
    hence  g_rev: "f = (\<lambda>f. (fst \<circ> h f, snd \<circ> h f)) g" 
      by (simp add:comp_def h_h_id) 
    show " pmf (pair_pmf (prod_pmf I A) (prod_pmf I B)) f =
         pmf (prod_pmf I (\<lambda>i. pair_pmf (A i) (B i)) \<bind> (\<lambda>f. return_pmf (fst \<circ> h f, snd \<circ> h f))) f"
      apply (subst map_pmf_def[symmetric], simp add: g_rev, subst pmf_map_inj', metis a)
      apply (simp add:pmf_pair' pmf_prod_pmf[OF assms(1)] b prod.distrib)
      using c by blast
  qed
  also have "... = ?rhs"
    apply (rule bind_pmf_cong ,simp)
    apply (simp add: h_def comp_def set_prod_pmf[OF assms(1)] PiE_iff extensional_def restrict_def)
    apply (rule conjI)
    by(rule ext, simp)+
  finally show ?thesis 
    by blast
qed

end
