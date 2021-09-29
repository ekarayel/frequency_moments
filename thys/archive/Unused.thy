theory Unused
  imports UniversalHashFamily Probability_Ext
begin

lemma poly_probabilities:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> (carrier F)"
  shows "prob_space.prob (poly_hash_family F n) 
    {\<omega>. \<omega> \<in> space (poly_hash_family F n) \<and> (\<forall>k \<in> K. hash_function F k \<omega> = y k)} = 1/(real (card (carrier F))^ card K)"
    (is "prob_space.prob (poly_hash_family F n) ?T = ?B")
proof -
  interpret prob_space "(poly_hash_family F n)" using prob_space_poly_family assms by metis

  have "\<zero>\<^bsub>F\<^esub> \<in> carrier F"
    using assms(1) by (simp add: cring.cring_simprules(2) fieldE(1))
  hence non_zero_den: "carrier F \<noteq> {}" by blast
  have "card {\<omega> \<in> bounded_degree_polynomials F n. (\<forall>k \<in> {}. hash_function F k \<omega> = y k)} = card (carrier F)^(n-card {})"
    using poly_cards[where K="{}"] assms by auto
  hence "card (bounded_degree_polynomials  F n) = card (carrier F)^n" by simp
  moreover have "finite (bounded_degree_polynomials F n)"
    using finite_poly_count assms(1) assms(2) by blast
  moreover have "?T \<subseteq> bounded_degree_polynomials F n"
    by (simp add:poly_hash_family_def space_uniform_count_measure)
  ultimately show ?thesis
    apply (simp add:measure_uniform_count_measure poly_hash_family_def hash_function_def)
    using assms apply (simp add:poly_cards space_uniform_count_measure)
     using non_zero_den apply (subst frac_eq_eq, simp, simp) 
     by (metis add.commute add_diff_inverse_nat mult.left_neutral not_less power_add)
qed

text \<open>The main result of this section is that
\begin{itemize}
\item Each hash function has uniform distribution over the finite fields.
\item The hash functions are k-wise independent random variables. 
\end{itemize}
\<close>

lemma uniform_distribution:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "n > 0"
  assumes "k \<in> carrier F"
  assumes "v \<in> carrier F"
  shows "\<P>(\<omega> in poly_hash_family F n. hash_function F k \<omega> = v) = 1/(real (card (carrier F)))"
proof -
  have "{k} \<subseteq> carrier F" using assms(4) by simp
  moreover have "card {k} \<le> n" using assms(3) by simp
  moreover have "(\<lambda>_. v) ` {k} \<subseteq> carrier F" apply (rule subsetI) using assms(5) by simp 
  ultimately show ?thesis
    using assms(1) assms(2) poly_probabilities[where F="F" and K="{k}" and y="(\<lambda>_. v)"] by simp
qed


lemma indep:
  assumes "field F"
  assumes "finite (carrier F)"
  shows 
     "prob_space.k_wise_indep_vars (poly_hash_family F n) n (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) (carrier F)" (is ?B)
proof -
  interpret prob_space "(poly_hash_family F n)" using prob_space_poly_family assms by metis

  have a1:"ring F" using assms(1) by (simp add:domain_def field_def cring_def)

  have "\<And>J. J \<subseteq> carrier F  \<Longrightarrow> card J \<le> n \<Longrightarrow> finite J \<Longrightarrow> 
    indep_vars (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) J"
  proof -
    fix J
    assume d:"J \<subseteq> carrier F"
    assume d2:"card J \<le> n"
    assume d3:"finite J"
    have b:"\<And>i. i \<in> J \<Longrightarrow> random_variable (uniform_count_measure (carrier F)) (\<lambda>\<omega>. hash_function F i \<omega>)" 
      apply (simp add:hash_function_def)
      apply (simp add:poly_hash_family_def uniform_count_measure_def point_measure_def Pi_def bounded_degree_polynomials_def)
      by (meson a1 d ring.carrier_is_subring ring.eval_in_carrier ring.polynomial_in_carrier subsetD univ_poly_carrier)

    define M where "M = (\<lambda>k. {k}) ` carrier F \<union> {{}}"
    define S where "S = (\<lambda>i. {hash_function F i -` y \<inter> space (poly_hash_family F n) | y. y \<in> M})" 
      (* maybe we can use singletons and use indep-sets_sigma here *)
    have e:"\<And>i. i \<in> J \<Longrightarrow> hash_function F i \<in> space (poly_hash_family F n) \<rightarrow> space (uniform_count_measure (carrier F))"
      apply (simp add:Pi_def poly_hash_family_def space_uniform_count_measure hash_function_def)
      using a1 d 
      by (metis (no_types, lifting) bounded_degree_polynomials_def mem_Collect_eq ring.carrier_is_subring ring.eval_poly_in_carrier subsetD univ_poly_carrier)
    have f:"sigma_sets (space (uniform_count_measure (carrier F))) M = sets (uniform_count_measure (carrier F))"
      apply (simp add: space_uniform_count_measure M_def sets_uniform_count_measure)
      apply (rule sigma_sets_singletons_and_empty)
      using countable_finite assms(2) by auto
    have "\<And>A K. K \<noteq> {} \<Longrightarrow> K \<subseteq> J \<Longrightarrow> finite K \<Longrightarrow> (\<forall>k \<in> K. A k \<in> S k) \<Longrightarrow> prob (\<Inter>k \<in> K. A k) = (\<Prod>k \<in> K. prob (A k))"
    proof -
      fix A K
      assume f6:"K \<subseteq> J"
      hence f4: "card K \<le> n" using d2 d3 by (meson card_mono dual_order.trans)
      assume f2:"K \<noteq> {}"
      assume f7:"finite K"
      assume "\<forall>k \<in> K. A k \<in> S k"
      hence "\<exists>y. \<forall>k. k \<in> K \<longrightarrow> A k = hash_function F k -` y k \<inter> space (poly_hash_family F n) \<and> y k \<in> M"
        by (simp add: S_def, meson)
      then obtain y where A_def: 
        "\<And>k. k \<in> K \<Longrightarrow> A k = hash_function F k -` y k \<inter> space (poly_hash_family F n) \<and> y k \<in> M"
        by blast
      show "prob  (\<Inter>k \<in> K. A k) = (\<Prod>k \<in> K. prob (A k))"
      proof (cases "\<exists>k \<in> K. y k = {}")
        case True
        then obtain k where k_def: "y k = {} \<and> k \<in> K" by blast
        hence f1: "A k = {}" using A_def by auto
        hence "\<Inter> (A ` K) = {}" using k_def by blast
        moreover have "prob (A k) = 0"  using f1 by simp
        ultimately show ?thesis using k_def 
          by (metis \<open>finite K\<close> measure_empty prod_zero_iff) 
      next
        case False
        hence "\<forall>k \<in> K. \<exists>h \<in> carrier F. y k = {h}" using M_def A_def by fastforce
        hence "\<exists>y'. \<forall>k \<in> K. (y k = {y' k} \<and> y' k \<in> carrier F)" by meson
        then obtain y' where y'_def: "\<And>k. k \<in> K \<Longrightarrow> y k = {y' k} \<and> y' k \<in> carrier F" by blast
        hence f1: "\<And>k. k \<in> K \<Longrightarrow> A k = hash_function F k -` {y' k} \<inter> space (poly_hash_family F n)" using A_def by auto
        have "\<And>k. k \<in> K \<Longrightarrow> prob (A k) = 1/(card (carrier F))"
        proof -
          fix k
          assume a:"k \<in> K"
          have g:"A k = {\<omega>. \<omega> \<in> space (poly_hash_family F n) \<and> (\<forall>k\<in>{k}. hash_function F k \<omega> = y' k)}"
            apply (rule order_antisym)
            apply (rule subsetI, simp add:f1 f2 a)
            by (rule subsetI, simp add:f1 f2 a)
          have "card {k} \<le> n" using f4 a f7 
            by (meson bot.extremum card_mono insert_subset le_trans)
          moreover have "y' ` {k} \<subseteq> carrier F" using y'_def a by auto
          moreover have "{k} \<subseteq> carrier F" using a f6 d by blast
          ultimately have "prob (A k) = 1/(real (card (carrier F)))^card {k}"
            apply (simp (no_asm_simp) only:g)
            using assms(1) assms(2) poly_probabilities[where K="{k}" and F="F"] by presburger
          thus "prob (A k) = 1/(real (card (carrier F)))" by simp
        qed
        moreover have "prob (\<Inter>(A ` K)) =  1/(real (card (carrier F)))^(card K)"
        proof -
          have g:"\<Inter>(A ` K) = {\<omega>. \<omega> \<in> space (poly_hash_family F n) \<and> (\<forall>k \<in> K. hash_function F k \<omega> = y' k)}"
            apply (rule order_antisym)
            apply (rule subsetI, simp add:f1 f2)
            by (rule subsetI, simp add:f1 f2)
          have "card K \<le> n" using f4 by auto
          moreover have "K \<subseteq> carrier F" using f6 d by blast
          moreover have "y' ` K \<subseteq> carrier F" using y'_def by blast
          ultimately show "prob (\<Inter>(A ` K)) = 1/(real (card (carrier F)))^card K"
            apply (simp (no_asm_simp) only:g)
            using assms(1) assms(2) poly_probabilities[where K="K" and F="F"] by presburger
        qed
        ultimately show ?thesis by (simp add:power_one_over)
      qed
    qed
    moreover have "\<And>j. j \<in> J \<Longrightarrow> S j \<subseteq> events"
      apply (simp add:S_def poly_hash_family_def space_uniform_count_measure sets_uniform_count_measure Pow_def) by blast
    ultimately have "indep_sets S J"
      by (simp add: indep_setsI)
    moreover have "\<And>i. i \<in> J \<Longrightarrow> Int_stable (S i)"
    proof (rule Int_stableI)
      fix i a b
      assume "i \<in> J"
      assume a: "a \<in> S i"
      then obtain y1 where y1_def: "y1 \<in> M" and a_def: "a = hash_function F i -` y1 \<inter> space (poly_hash_family F n)"
        apply (simp add:S_def) by blast
      assume "b \<in> S i"
      then obtain y2 where y2_def: "y2 \<in> M" and b_def: "b = hash_function F i -` y2 \<inter> space (poly_hash_family F n)"
        apply (simp add:S_def) by blast
      show "a \<inter> b \<in> S i"
      proof (cases "y1 = y2")
        case True
        hence "a = b" using a_def b_def by fastforce
        hence "a \<inter> b = a" by blast
        then show ?thesis using a by auto
      next
        case False
        hence a:"y1 \<inter> y2 = {}" using y1_def y2_def M_def by blast
        have "a \<inter> b \<subseteq> {}" 
          apply (rule subsetI, simp add:a_def b_def)
          using False a by blast
        hence "a \<inter> b = {}" by force
        moreover have "{} \<in> S i" apply (simp add:S_def M_def) by blast
        ultimately show ?thesis by auto
      qed
    qed
    ultimately have "indep_sets (\<lambda>i. sigma_sets (space (poly_hash_family F n)) (S i)) J"
      using indep_sets_sigma by auto
    moreover have "\<And>i. i \<in> J \<Longrightarrow> sigma_sets (space (poly_hash_family F n)) (S i) \<supseteq>
      { hash_function F i -` A \<inter> space (poly_hash_family F n) | A. A \<in> sets (uniform_count_measure (carrier F))}"
      apply (simp add:S_def)
      by (simp add:sigma_sets_vimage_commute[where  \<Omega>'="space (uniform_count_measure (carrier F))",symmetric] e f)
    ultimately have c:"indep_sets 
      (\<lambda>i. { hash_function F i -` A \<inter> space (poly_hash_family F n) | A. A \<in> sets (uniform_count_measure (carrier F))}) J"
      using indep_sets_mono_sets by force
    show "indep_vars (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) J"
      apply (simp add:indep_vars_def2)
      using  b c by presburger
  qed
  thus ?B using k_wise_indep_vars_def by blast
qed

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




end