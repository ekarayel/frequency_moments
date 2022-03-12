section \<open>Indexed Products of Probability Mass Functions\<close>

theory Product_PMF_Ext
  imports Main Probability_Ext "HOL-Probability.Product_PMF" Universal_Hash_Families.Preliminary_Results
begin

text \<open>This section introduces a restricted version of @{term "Pi_pmf"} where the default value is @{term "undefined"}
and contains some additional results about that case in addition to @{theory "HOL-Probability.Product_PMF"}\<close>

abbreviation prod_pmf where "prod_pmf I M \<equiv> Pi_pmf I undefined M"

lemma pmf_prod_pmf: 
  assumes "finite I"
  shows "pmf (prod_pmf I M) x = (if x \<in> extensional I then \<Prod>i \<in> I. (pmf (M i)) (x i) else 0)"
  by (simp add:  pmf_Pi[OF assms(1)] extensional_def)

lemma PiE_defaut_undefined_eq: "PiE_dflt I undefined M = PiE I M" 
  by (simp add:PiE_dflt_def PiE_def extensional_def Pi_def set_eq_iff) blast

lemma set_prod_pmf:
  assumes "finite I"
  shows "set_pmf (prod_pmf I M) = PiE I (set_pmf \<circ> M)"
  by (simp add:set_Pi_pmf[OF assms] PiE_defaut_undefined_eq)

text \<open>A more general version of @{thm [source] "measure_Pi_pmf_Pi"}.\<close>
lemma prob_prod_pmf': 
  assumes "finite I"
  assumes "J \<subseteq> I"
  shows "measure (measure_pmf (Pi_pmf I d M)) (Pi J A) = (\<Prod> i \<in> J. measure (M i) (A i))"
proof -
  have a:"Pi J A = Pi I (\<lambda>i. if i \<in> J then A i else UNIV)"
    using assms by (simp add:Pi_def set_eq_iff, blast)
  show ?thesis
    using assms
    by (simp add:if_distrib  a measure_Pi_pmf_Pi[OF assms(1)] prod.If_cases[OF assms(1)] Int_absorb1)
qed

lemma prob_prod_pmf_slice:
  assumes "finite I"
  assumes "i \<in> I"
  shows "measure (measure_pmf (prod_pmf I M)) {\<omega>. P (\<omega> i)} = measure (M i) {\<omega>. P \<omega>}"
  using prob_prod_pmf'[OF assms(1), where J="{i}" and M="M" and A="\<lambda>_. Collect P"]
  by (simp add:assms Pi_def)


definition restrict_dfl where "restrict_dfl f A d = (\<lambda>x. if x \<in> A then f x else d)"

lemma pi_pmf_decompose:
  assumes "finite I"
  shows "Pi_pmf I d M = map_pmf (\<lambda>\<omega>. restrict_dfl (\<lambda>i. \<omega> (f i) i) I d) (Pi_pmf (f ` I) (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> I) d M))"
proof -
  have fin_F_I:"finite (f ` I)" using assms by blast

  have "finite I \<Longrightarrow> ?thesis"
    using fin_F_I
  proof (induction "f ` I" arbitrary: I rule:finite_induct)
    case empty
    then show ?case by (simp add:restrict_dfl_def)
  next
    case (insert x F)
    have a: "(f -` {x} \<inter> I) \<union> (f -` F \<inter> I) = I"
      using insert(4) by blast
    have b: "F = f `  (f -` F \<inter> I) " using insert(2,4) 
      by (auto simp add:set_eq_iff image_def vimage_def) 
    have c: "finite (f -` F \<inter> I)" using insert by blast
    have d: "\<And>j. j \<in> F \<Longrightarrow> (f -` {j} \<inter> (f -` F \<inter> I)) = (f -` {j} \<inter> I)"
      using insert(4) by blast 

    have " Pi_pmf I d M = Pi_pmf ((f -` {x} \<inter> I) \<union> (f -` F \<inter> I)) d M"
      by (simp add:a)
    also have "... = map_pmf (\<lambda>(g, h) i. if i \<in> f -` {x} \<inter> I then g i else h i) 
      (pair_pmf (Pi_pmf (f -` {x} \<inter> I) d M) (Pi_pmf (f -` F \<inter> I) d M))"
      using insert by (subst Pi_pmf_union) auto
    also have "... = map_pmf (\<lambda>(g,h) i. if f i = x \<and> i \<in> I then g i else if f i \<in> F \<and> i \<in> I then h (f i) i else d)
      (pair_pmf (Pi_pmf (f -` {x} \<inter> I) d M) (Pi_pmf F (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> (f -` F \<inter> I)) d M)))"
      by (simp add:insert(3)[OF b c] map_pmf_comp case_prod_beta' apsnd_def map_prod_def 
          pair_map_pmf2 b[symmetric] restrict_dfl_def) (metis fst_conv snd_conv)
    also have "... = map_pmf (\<lambda>(g,h) i. if i \<in> I then (h(x := g)) (f i) i else d) 
      (pair_pmf (Pi_pmf (f -` {x} \<inter> I) d M) (Pi_pmf F (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> I) d M)))" 
      using insert(4) d
      by (intro arg_cong2[where f="map_pmf"] ext) (auto simp add:case_prod_beta' cong:Pi_pmf_cong) 
    also have "... = map_pmf (\<lambda>\<omega> i. if i \<in> I then \<omega> (f i) i else d) (Pi_pmf (insert x F) (\<lambda>_. d) (\<lambda>j. Pi_pmf (f -` {j} \<inter> I) d M))"
      by (simp add:Pi_pmf_insert[OF insert(1,2)] map_pmf_comp case_prod_beta')
    finally show ?case by (simp add:insert(4) restrict_dfl_def)
  qed
  thus ?thesis using assms by blast
qed

lemma restrict_dfl_iter: "restrict_dfl (restrict_dfl f I d) J d = restrict_dfl f (I \<inter> J) d"
  by (rule ext, simp add:restrict_dfl_def)

lemma indep_vars_restrict':
  assumes "finite I"
  shows "prob_space.indep_vars (Pi_pmf I d M) (\<lambda>_. discrete) (\<lambda>i \<omega>. restrict_dfl \<omega> (f -` {i} \<inter> I) d) (f ` I)"
proof -
  let ?Q = "(Pi_pmf (f ` I) (\<lambda>_. d) (\<lambda>i. Pi_pmf (I \<inter> f -` {i}) d M))"
  have a:"prob_space.indep_vars ?Q (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) (f ` I)"
    using assms by (intro indep_vars_Pi_pmf, blast)
  have b: "AE x in measure_pmf ?Q. \<forall>i\<in>f ` I. x i = restrict_dfl (\<lambda>i. x (f i) i) (I \<inter> f -` {i}) d"
    using assms
    by (auto simp add:PiE_dflt_def restrict_dfl_def AE_measure_pmf_iff set_Pi_pmf comp_def Int_commute)
  have "prob_space.indep_vars ?Q (\<lambda>_. discrete) (\<lambda>i x. restrict_dfl (\<lambda>i. x (f i) i) (I \<inter> f -` {i}) d) (f ` I)"
    by (rule prob_space.indep_vars_cong_AE[OF prob_space_measure_pmf b a],  simp)
  thus ?thesis
    using prob_space_measure_pmf 
    by (auto intro!:prob_space.indep_vars_distr simp:pi_pmf_decompose[OF assms, where f="f"]  
        map_pmf_rep_eq comp_def restrict_dfl_iter Int_commute) 
qed

lemma indep_vars_restrict_intro':
  assumes "M = measure_pmf (Pi_pmf I d p)"
  assumes "finite I"
  assumes "\<And>i \<omega>. i \<in> J \<Longrightarrow> X i \<omega> = X i (restrict_dfl \<omega> (f -` {i} \<inter> I) d)"
  assumes "J = f ` I"
  assumes "\<And>\<omega> i. i \<in> J \<Longrightarrow>  X i \<omega> \<in> space (M' i)"
  shows "prob_space.indep_vars M M' (\<lambda>i \<omega>. X i \<omega>) J"
proof -
  interpret prob_space "M"
    using assms(1) prob_space_measure_pmf by blast
  have "indep_vars (\<lambda>_. discrete) (\<lambda>i x. restrict_dfl x (f -` {i} \<inter> I) d) (f ` I)" 
    unfolding assms(1)  by (rule indep_vars_restrict'[OF assms(2)])
  hence "indep_vars M' (\<lambda>i \<omega>. X i (restrict_dfl \<omega> ( f -` {i} \<inter> I) d)) (f ` I)"
    using assms(5)
    by (intro indep_vars_compose2[where Y="X" and N="M'" and M'="\<lambda>_. discrete"])  (auto simp:assms(4))
  hence "indep_vars M' (\<lambda>i \<omega>. X i \<omega>) (f ` I)"
    using assms(3)[symmetric]
    by (simp add:assms(4) cong:indep_vars_cong)
  thus ?thesis
    using assms(4) by simp 
qed

lemma  
  fixes f :: "'b \<Rightarrow> ('c :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "integrable (measure_pmf (M i)) f"
  shows  integrable_Pi_pmf_slice: "integrable (Pi_pmf I d M) (\<lambda>x. f (x i))"
  and expectation_Pi_pmf_slice: "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f (x i)) = integral\<^sup>L (M i) f"
proof -
  have a:"distr (Pi_pmf I d M) (M i) (\<lambda>\<omega>. \<omega> i) = distr (Pi_pmf I d M) discrete (\<lambda>\<omega>. \<omega> i)"
    by (rule distr_cong, auto)

  have b: "measure_pmf.random_variable (M i) borel f"
    using assms(3) by simp

  have c:"integrable (distr (Pi_pmf I d M) (M i) (\<lambda>\<omega>. \<omega> i)) f" 
    using assms(1,2,3)
    by (subst a, subst map_pmf_rep_eq[symmetric], subst Pi_pmf_component, auto)

  show "integrable (Pi_pmf I d M) (\<lambda>x. f (x i))"
    by (rule integrable_distr[where f="f" and M'="M i"])  (auto intro: c)

  have "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f (x i)) = integral\<^sup>L (distr (Pi_pmf I d M) (M i) (\<lambda>\<omega>. \<omega> i)) f"
    using b by (intro integral_distr[symmetric], auto)
  also have "... =  integral\<^sup>L (map_pmf (\<lambda>\<omega>. \<omega> i) (Pi_pmf I d M)) f"
    by (subst a, subst map_pmf_rep_eq[symmetric], simp)
  also have "... =  integral\<^sup>L (M i) f"
    using assms(1,2) by (simp add: Pi_pmf_component)
  finally show "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f (x i)) = integral\<^sup>L (M i) f" by simp
qed

text \<open>This is an improved version of @{thm [source] "expectation_prod_Pi_pmf"}.
It works for general normed fields instead of non-negative real functions .\<close>

lemma expectation_prod_Pi_pmf: 
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> ('c :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable (measure_pmf (M i)) (f i)"
  shows   "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) = (\<Prod> i \<in> I. integral\<^sup>L (M i) (f i))"
proof -
  have a: "prob_space.indep_vars (measure_pmf (Pi_pmf I d M)) (\<lambda>_. borel) (\<lambda>i \<omega>. f i (\<omega> i)) I"
    by (intro prob_space.indep_vars_compose2[where Y="f" and M'="\<lambda>_. discrete"] 
        prob_space_measure_pmf indep_vars_Pi_pmf assms(1)) auto
  have "integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. (\<Prod>i \<in> I. f i (x i))) = (\<Prod> i \<in> I. integral\<^sup>L (Pi_pmf I d M) (\<lambda>x. f i (x i)))"
    by (intro prob_space.indep_vars_lebesgue_integral prob_space_measure_pmf assms(1,2) 
        a integrable_Pi_pmf_slice) auto
  also have "... = (\<Prod> i \<in> I. integral\<^sup>L (M i) (f i))"
    by (intro prod.cong expectation_Pi_pmf_slice assms(1,2)) auto
  finally show ?thesis by simp
qed

lemma has_bochner_integral_prod_pmf_sliceI: (* TODO Remove *)
  fixes f :: "'a \<Rightarrow> ('b :: {second_countable_topology,banach,real_normed_field})"
  assumes "finite I"
  assumes "i \<in> I"
  assumes "has_bochner_integral (measure_pmf (M i)) f r"
  shows "has_bochner_integral (Pi_pmf I d M) (\<lambda>x. (f (x i))) r"
  using assms integrable_Pi_pmf_slice[OF assms(1,2), where M="M" and f="f"] 
    expectation_Pi_pmf_slice[OF assms(1,2), where M="M" and f="f"]
  by (simp add:has_bochner_integral_iff) 

lemma variance_prod_pmf_slice:
  fixes f :: "'a \<Rightarrow> real"
  assumes "i \<in> I" "finite I"
  assumes "integrable (measure_pmf (M i)) (\<lambda>\<omega>. f \<omega>^2)"
  shows "prob_space.variance (Pi_pmf I d M) (\<lambda>\<omega>. f (\<omega> i)) = prob_space.variance (M i) f"
proof -
  have a:"integrable (measure_pmf (M i)) f"
    using assms(3) measure_pmf.square_integrable_imp_integrable by auto
  have b:" integrable (measure_pmf (Pi_pmf I d M)) (\<lambda>x. (f (x i))\<^sup>2)"
    by (rule integrable_Pi_pmf_slice[OF assms(2) assms(1)], metis assms(3))
  have c:" integrable (measure_pmf (Pi_pmf I d M)) (\<lambda>x. (f (x i)))"
    by (rule integrable_Pi_pmf_slice[OF assms(2) assms(1)], metis a)

  have "measure_pmf.expectation (Pi_pmf I d M) (\<lambda>x. (f (x i))\<^sup>2) - (measure_pmf.expectation (Pi_pmf I d M) (\<lambda>x. f (x i)))\<^sup>2 =
      measure_pmf.expectation (M i) (\<lambda>x. (f x)\<^sup>2) - (measure_pmf.expectation (M i) f)\<^sup>2"
    using assms a b c by ((subst expectation_Pi_pmf_slice[OF assms(2,1)])?, simp)+

  thus ?thesis
    using assms a b c by (simp add: measure_pmf.variance_eq)
qed

lemma pmf_of_set_prod:
  assumes "finite I"
  assumes "\<And>x. x \<in> I \<Longrightarrow> finite (M x)"
  assumes "\<And>x. x \<in> I \<Longrightarrow> M x \<noteq> {}"
  shows "pmf_of_set (PiE I M) = prod_pmf I (\<lambda>i. pmf_of_set (M i))"
  by (simp add: PiE_defaut_undefined_eq Pi_pmf_of_set[OF assms(1,2,3)])

lemma extensionality_iff:
  assumes "f \<in> extensional I"
  shows "((\<lambda>i \<in> I. g i) = f) = (\<forall>i \<in> I. g i = f i)"
  using assms by (auto simp:extensional_def restrict_def)

lemma of_bool_prod:
  assumes "finite I"
  shows "of_bool (\<forall>i \<in> I. P i) = (\<Prod>i \<in> I. (of_bool (P i) :: 'a :: field))"
  using assms by (induction I rule:finite_induct, auto)

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
      apply (subst expectation_prod_Pi_pmf[OF assms(1)])
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
  by (cases x, simp add:pmf_pair)

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
    hence g_rev: "f = (\<lambda>f. (fst \<circ> h f, snd \<circ> h f)) g" 
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
