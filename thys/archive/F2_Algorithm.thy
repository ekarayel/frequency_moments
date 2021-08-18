section \<open>Frequency Moment 2\<close>

theory F2_Algorithm
  imports Main "HOL-Probability.Giry_Monad" UniversalHashFamily Field 
    Median Probability_Ext "HOL-Library.Multiset" Partitions Primes_Ext
begin

text \<open>This algorithm estimates the second frequency moment $F_2$, it was introduced by Alon et. al.:
Let $a_1, \cdots, a_n \subset U = \{0,\ldots,m-1\}$ be a sequence. It makes one (read-only) pass
over the sequence requiring $O(- \lambda^{-1} \log \varepsilon (\log n + \log m))$ bits of memory. At the
end it returns an estimate $F_2^{*}$ that deviates from $F_2$ by more than $\lambda F_2$ with
probability at most $\varepsilon$.\<close>

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. (real (count_list xs x) * f x \<omega>))"

definition f2_value
  where
    "f2_value xs = (\<Sum> x \<in> set xs. (real (count_list xs x)^2))"


lemma (in prob_space)
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> indep_vars (\<lambda>_. borel) h I"
  assumes "\<And>i (m :: nat). i \<in> set xs \<Longrightarrow> integrable M (\<lambda>\<omega>. (h i \<omega>)^m)"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (h i) = 0"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^2) = 1"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^4) \<le> 3"
  shows var_f2:"variance (\<lambda>\<omega>. f2_sketch h xs \<omega>^2) \<le> (2*f2_value xs^2)" (is "?A \<le> ?B")
  and exp_f2:"expectation (\<lambda>\<omega>. f2_sketch h xs \<omega>^2) = f2_value xs" (is ?D)
  and int_exp_f2:"integrable M (\<lambda>\<omega>. f2_sketch h xs \<omega>^2)" (is ?E)
  and int_var_f2:"integrable M (\<lambda>\<omega>. (f2_sketch h xs \<omega>^2)^2)" (is ?F)
proof -

  have "\<And>i. i \<in> set xs \<Longrightarrow> indep_vars (\<lambda>_. borel) h {i}" using assms(1) by simp
  hence meas:"\<And>i. i \<in> set xs \<Longrightarrow> h i \<in> measurable M borel" by (simp add:indep_vars_def2) 

  define f2_sum where "f2_sum = (\<lambda>x \<omega>. real (count_list xs x) * h x \<omega>)"
  define f2_pow where "f2_pow = (\<lambda>x n \<omega>. f2_sum x \<omega> ^ n)"
  define h_power where "h_power = (\<lambda>i m. expectation (\<lambda>\<omega>. (h i \<omega>)^m))"
  define h_power_4_diff where "h_power_4_diff = (\<lambda>i. h_power i 4 - 3)"

  have f2_sketch_elim: "\<And>\<omega>. f2_sketch h xs \<omega> = (\<Sum> x \<in> set xs. f2_sum x \<omega>)"
    by (simp add:f2_sketch_def f2_sum_def)
  have h_power_simps: 
    "\<And>x. x \<in> set xs \<Longrightarrow> h_power x (Suc 0) = 0" 
    "\<And>x. x \<in> set xs \<Longrightarrow> h_power x (Suc (Suc 0)) = 1" 
    "\<And>x. x \<in> set xs \<Longrightarrow> h_power x (Suc (Suc (Suc (Suc 0)))) = (3 + h_power_4_diff x)" 
    using assms(3) assms(4) h_power_4_diff_def h_power_def numeral_eq_Suc by simp+
  have h_power_4_estimate:
    "\<And>x. x \<in> set xs \<Longrightarrow> h_power_4_diff x \<le> 0" 
    using assms(3) assms(5) h_power_4_diff_def h_power_def by simp+

  have sketch_exp: "\<And>x m. x \<in> set xs  \<Longrightarrow>
    expectation (\<lambda>\<omega>. f2_pow x m \<omega>) = h_power x m * (count_list xs x ^ m)"
    using assms(2) by (simp add:f2_pow_def f2_sum_def algebra_simps h_power_def)

  have sketch_int: "\<And>x m. x \<in> set xs  \<Longrightarrow> integrable M (\<lambda>\<omega>. f2_pow x m \<omega>)"
    using assms(2) by (simp add:f2_pow_def f2_sum_def algebra_simps)

  define f where "f = (\<lambda>l \<omega>. prod_mset (image_mset (\<lambda>i. f2_sum i \<omega>) (mset l)))"
  
  have c1: "\<And>k \<omega>. f2_sum k \<omega> = f [k] \<omega>" by (simp add:f_def)
  
  have c2: "\<And>a b \<omega>. f a \<omega> * f b \<omega> = f (a@b) \<omega>" by (simp add:f_def)

  define g where "g = (\<lambda>l p \<omega>. (if has_eq_relation p l then f l \<omega> else 0))"

  have c3 :"\<And>x. f x = (\<lambda>\<omega>. sum_list (map (\<lambda>p. g x p \<omega>) (enum_partitions (length x))))"
    apply (simp only: g_def)
    using sum_partitions by metis

  have indep:
    "\<And>x j. x \<subseteq> set xs \<Longrightarrow> finite x \<Longrightarrow> card x \<le> 4 \<Longrightarrow>
    indep_vars (\<lambda>_. borel) (\<lambda>i. f2_pow i (j i)) x" 
  proof -
    fix x j
    assume "x \<subseteq> set xs"
    moreover assume "finite x"
    moreover assume "card x \<le> 4"
    ultimately have "indep_vars (\<lambda>_. borel) (\<lambda>i. h i) x" using assms by auto
    moreover define Y where "Y = (\<lambda>i t. (real (count_list xs i) * t)^ j i)"
    moreover have "\<And>i. i \<in> x \<Longrightarrow> Y i \<in> measurable borel borel" by (simp add:Y_def, measurable)
    ultimately have "indep_vars (\<lambda>_. borel) (\<lambda>i. Y i \<circ> h i) x" using indep_vars_compose by fast
    thus "indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. f2_pow i (j i) \<omega>) x"
      by (simp add:f2_pow_def f2_sum_def Y_def comp_def) 
  qed

  have indep_2_aux:
    "\<And>x. set x \<subseteq> set xs  \<Longrightarrow> length x \<le> 4 \<Longrightarrow> integrable M (f x)"
  proof -
    fix x
    assume "set x \<subseteq> set xs"
    moreover assume "length x \<le> 4"
    hence "card (set x) \<le> 4" by (meson card_length le_trans)
    ultimately have "integrable M (\<lambda>\<omega>. \<Prod>i\<in>set x. f2_pow i (count (mset x) i) \<omega>)"
      apply (subst indep_vars_integrable)
         apply (simp add:assms(1))+
      using indep apply blast
      using sketch_int apply blast
      by simp
    thus "integrable M (\<lambda>\<omega>. f x \<omega>)"
      by (simp add:f_def prod_mset_conv f2_pow_def)
  qed

  hence indep2:
    "\<And>x p. set x \<subseteq> set xs  \<Longrightarrow> length x \<le> 4  \<Longrightarrow> integrable M (g x p)"
  proof -
    fix x p
    assume "set x \<subseteq> set xs"
    moreover assume "length x \<le> 4"
    ultimately show "integrable M (g x p)"
      apply (cases "has_eq_relation p x")
      by (simp add:g_def indep_2_aux)+ 
  qed
    
  have
    "\<And> x p. set x \<subseteq> set xs \<Longrightarrow> length x \<le> 4  \<Longrightarrow> has_eq_relation p x \<Longrightarrow>
      integral\<^sup>L M (f x) = 
      prod_list (map (\<lambda>i. h_power (x ! i) (count_list_p p i) * real (count_list xs (x ! i) ^ (count_list_p p i))) (remdups_indices p))"
    proof -
    fix x p
    assume a1:"set x \<subseteq> set xs"
    assume a2:"length x \<le> 4"             
    assume a3:"has_eq_relation p x"

    have a2_1: "card (set x) \<le> 4" by (meson card_length le_trans a2)

    have t_2:"\<And>i. i \<in> set x \<Longrightarrow> i \<in> set xs" using a1 by auto
    have "(LINT \<omega>|M. (\<Prod>i\<in>set x. f2_pow i (count (mset x) i) \<omega>)) =
      prod_list (map (\<lambda>i. h_power (x ! i) (count_list_p p i) * real (count_list xs (x ! i) ^ (count_list_p p i))) (remdups_indices p))"
      apply (simp add:f_def prod_mset_conv)
      apply (subst indep_vars_lebesgue_integral)
         apply (simp add:assms(1))+
      using indep a2_1 a1 apply blast
      using sketch_int a1 apply blast
      using a3 apply (simp add: sketch_exp t_2 set_xs)
      apply (subst prod.distinct_set_conv_list, simp add:a3 distinct_set_xs)
      by (simp add:remdups_p_def comp_def count_xs cong:map_cong)

    thus "integral\<^sup>L M (f x) = 
      prod_list (map (\<lambda>i. h_power (x ! i) (count_list_p p i) * real (count_list xs (x ! i) ^ (count_list_p p i))) (remdups_indices p))"
      by (simp add:f_def prod_mset_conv  f2_pow_def)
  qed

  hence indep1:
    "\<And> x p. set x \<subseteq> set xs \<Longrightarrow> length x \<le> 4  \<Longrightarrow>  
      integral\<^sup>L M (g x p) = (if has_eq_relation p x then 1 else 0) * 
      prod_list (map (\<lambda>i. h_power (x ! i) (count_list_p p i) * real (count_list xs (x ! i) ^ (count_list_p p i))) (remdups_indices p))"
    by (simp add:g_def)

  have rev_ineq: "\<And>x y. (if (x \<noteq> y) then 1 else 0) = ((1::real) - (if (x = y) then 1 else 0))"
  by auto

  have  fold_sym: "\<And>x y. (x \<noteq> y \<and> y \<noteq> x) = (x \<noteq> y)" by auto

  show int_exp_f2: "?E"
    apply (simp add: f2_sketch_elim power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    by (simp add: c3 indep1 indep2 exp_def sum.distrib)

  show int_var_f2: "?F"
    apply (simp add: f2_sketch_elim power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    by (simp add: c3 indep1 indep2 exp_def sum.distrib)

  have exp_2: "?D"
    apply (simp add: f2_sketch_elim power2_eq_square f2_value_def)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    apply (simp add: c3 indep1 indep2 h_power_simps sum.distrib)
    apply (simp add: has_eq_relation_elim)
    by (simp add: sum_collapse rev_ineq)
  thus ?D by auto

  show "?A \<le> ?B"
    apply (subst variance_eq, metis int_exp_f2, metis int_var_f2)
    apply (simp add: exp_2 f2_value_def)
    apply (simp add: f2_sketch_elim power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    apply (simp add: c3 indep1 indep2 h_power_simps sum.distrib)
    apply (simp add: has_eq_relation_elim)
    apply (simp add: sum_collapse rev_ineq sum_subtractf algebra_simps fold_sym)
    apply (simp add: algebra_simps sum_distrib_left)
    apply (rule sum_mono)
    by (simp add: h_power_4_estimate mult_nonneg_nonpos2 algebra_simps)
qed

definition \<alpha> :: "nat \<Rightarrow> real" where "\<alpha> p = sqrt((p-1)/(p+1))"
definition \<beta> :: "nat \<Rightarrow> real" where "\<beta> p = -sqrt((p+1)/(p-1))"

fun eval_hash_function where
  "eval_hash_function p h k = (
    if (hash_function (ZFact (int p)) (zfact_embed p k) h) \<in> zfact_embed p ` {k. 2*k < p} then
      (int p - 1)
    else
      (-int p-1)
  )"

fun eval_hash_function_scaled where
  "eval_hash_function_scaled p h k = real_of_int (eval_hash_function p h k) / (real p^2-1)"

lemma eval_exp:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2" 
  shows eval_hash_exp: 
    "prob_space.expectation (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. (eval_hash_function p \<omega> k / (real p^2-1)) ^m) = 
    (real (p+1)/ real(2*p) * (real p-1) ^m) + 
    (real (p-1)/ real(2*p) * (-real p-1) ^m)" (is "?A = ?C")
    and eval_hash_int:
    "integrable (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^m)" (is ?B)
proof -
  define A where "A = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k < p}}"
  define B where "B = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k \<ge> p \<and> k < p}}"
  define f where "f = (\<lambda>\<omega>. indicator A \<omega> * (real p-1)^m)"
  define g where "g = (\<lambda>\<omega>. indicator B \<omega> * (-real p-1)^m)"

  have g:"p > 1" using assms(1) prime_gt_1_nat by auto

  have a1:"finite (carrier (ZFact p))"  using zfact_finite g by auto
  have a2:"ring (ZFact p)"  using ZFact_is_cring cring_def by blast
  have "zfact_embed p k \<in> carrier (ZFact p)" using zfact_embed_ran assms g 
    by (metis image_eqI mem_Collect_eq)
  hence g4:"\<And>\<omega>. \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<Longrightarrow> ring.eval (ZFact (int p)) \<omega> (zfact_embed p k) \<in> carrier (ZFact p)"
    using a2   ring.polynomial_in_carrier[where K="carrier (ZFact p)" and R="ZFact p"] 
    by (simp add: bounded_degree_polynomials_def ring.carrier_is_subring ring.eval_in_carrier univ_poly_carrier)
  have "odd p" using assms prime_odd_nat by blast
  then obtain t where t_def: "p=2*t+1" 
    using oddE by blast

  have a:"finite (bounded_degree_polynomials (ZFact p) 4)"
    apply (rule fin_degree_bounded)
    using a2 apply blast
    using g zfact_finite by blast
  have r3_aux: "\<And>x. x \<in> carrier (ZFact p) \<Longrightarrow> 
    (x \<in> zfact_embed p ` {k. 2*k < p}) = (x \<notin> zfact_embed p ` {k. 2*k \<ge> p \<and> k < p})" 
    (is "\<And>x. _ \<Longrightarrow> (x \<in> ?lhs) = (x \<notin> ?rhs)")
  proof -
    fix x
    assume "x \<in> carrier (ZFact p)"
    hence a:"x \<in> zfact_embed p ` {k. k < p}" 
      using zfact_embed_ran g by presburger
    moreover have "?lhs \<inter> ?rhs = {}"
    proof (rule Int_emptyI)
      fix x
      assume "x \<in> zfact_embed p ` {k. 2*k < p}"
      then obtain k1 where x_def_1: "x = zfact_embed p k1" and k1_bound: "2*k1 < p"
        by blast
      assume "x \<in> zfact_embed p ` {k. p \<le> 2*k \<and> k < p}"
      then obtain k2 where x_def_2: "x = zfact_embed p k2" and k2_bound: "p \<le> 2*k2 \<and> k2 < p"
        by blast
      have "k1 \<in> {k. k < p}" using k1_bound by auto
      moreover have "k2 \<in> {k. k < p}" using k2_bound by auto
      ultimately have "k1 = k2" using g zfact_embed_inj x_def_1 x_def_2 inj_onD
        by metis
      thus "False" using k1_bound k2_bound 
        using not_less by blast
    qed
    moreover have "?lhs \<union> ?rhs = zfact_embed p ` {k. k < p}"
      apply (simp add: image_Un[symmetric])
      apply (rule arg_cong2 [where f="(\<lambda>x y. x ` y)"], simp)
      by (rule order_antisym, rule subsetI, simp, linarith, rule subsetI, simp, meson not_le)
    ultimately show "(x \<in> ?lhs) = (x \<notin> ?rhs)"
      by (metis (no_types, lifting) UnE disjoint_iff)
  qed
  have r3: "\<And>\<omega>. \<omega> \<in> space (poly_hash_family (ZFact (int p)) 4) \<Longrightarrow> real_of_int (eval_hash_function p \<omega> k)^m =  f \<omega> + g \<omega>"
    apply (simp add:poly_hash_family_def space_uniform_count_measure)
    apply (simp add:f_def g_def A_def B_def hash_function_def)
    apply (rule conjI, rule impI) using g4 r3_aux by simp+

  have "card {k. Suc(2 * t) \<le> 2 *k \<and> k < Suc (2*t)} = card {Suc t..<Suc (2*t)}" 
    by (rule arg_cong[where f="card"], auto)
  hence card_A: "card {k. p \<le> 2 * k \<and> k < p} = (p-1)/2"
    by (simp add:t_def)
  have "card {k. 2 * k < Suc(2 * t)} = card {k. k < t+1}" 
    by (rule arg_cong[where f="card"], auto)
  hence card_B: "card {k. 2 * k < p} = (p+1)/2"
    by (simp add:t_def)
  have "A \<in> sets (poly_hash_family (ZFact p) 4)"
    by (simp add:poly_hash_family_def sets_uniform_count_measure A_def) 
  moreover have "emeasure (poly_hash_family (ZFact p) 4) A < \<infinity>" 
    by (simp add:poly_hash_family_def emeasure_uniform_count_measure a A_def) 
  ultimately have "has_bochner_integral (poly_hash_family (ZFact p) 4) (indicator A) (measure (poly_hash_family (ZFact p) 4) A)"
    using has_bochner_integral_real_indicator by blast
  moreover have "measure (poly_hash_family (ZFact p) 4) A = (p+1)/(2*p)" 
    apply (simp add:poly_hash_family_def measure_uniform_count_measure a A_def bounded_degree_polynomials_count a1 a2) 
    apply (simp add: hash_function_def)
    apply (subst poly_card_set)
    using zfact_prime_is_field assms apply force
    using zfact_finite g apply simp
    using g assms zfact_embed_ran apply blast
      apply simp
    apply (rule image_subsetI, simp) using zfact_embed_ran g 
     apply (simp add: ZFact_defs(1) ZFact_defs(2) int.a_rcosetsI zfact_embed_def)
    apply (subst card_image) using g zfact_embed_inj inj_on_subset[where B="{k. 2 * k < p}"] apply force
    using g apply (simp add: card_B zfact_card nonzero_divide_eq_eq nonzero_eq_divide_eq)
    by (simp add: power3_eq_cube power4_eq_xxxx)
  ultimately have r1:"has_bochner_integral (poly_hash_family (ZFact p) 4) f (real (p+1)/ real(2*p) * (real p-1)^m)"
    apply (subst f_def) using has_bochner_integral_mult_left by metis

  have "B \<in> sets (poly_hash_family (ZFact p) 4)"
    by (simp add:poly_hash_family_def sets_uniform_count_measure B_def) 
  moreover have "emeasure (poly_hash_family (ZFact p) 4) B < \<infinity>" 
    by (simp add:poly_hash_family_def emeasure_uniform_count_measure a B_def) 
  ultimately have "has_bochner_integral (poly_hash_family (ZFact p) 4) (indicator B) (measure (poly_hash_family (ZFact p) 4) B)"
    using has_bochner_integral_real_indicator by blast
  moreover have "measure (poly_hash_family (ZFact p) 4) B = (p-1)/(2*p)" 
    apply (simp add:poly_hash_family_def measure_uniform_count_measure a B_def bounded_degree_polynomials_count a1 a2) 
    apply (simp add: hash_function_def)
    apply (subst poly_card_set)
    using zfact_prime_is_field assms apply force
    using zfact_finite g apply simp
    using g assms zfact_embed_ran apply blast
      apply simp
    apply (rule image_subsetI, simp) using zfact_embed_ran g 
     apply (simp add: ZFact_defs(1) ZFact_defs(2) int.a_rcosetsI zfact_embed_def)
    apply (subst card_image) using g zfact_embed_inj inj_on_subset[where B="{k. p \<le> 2 * k \<and> k < p}"] apply force
    using g apply (simp add:card_A zfact_card nonzero_divide_eq_eq nonzero_eq_divide_eq)
    by (simp add: algebra_simps power3_eq_cube power4_eq_xxxx)
  ultimately have r2:"has_bochner_integral (poly_hash_family (ZFact p) 4) g (real (p-1)/ real(2*p) * (-real p-1)^m)"
    apply (subst g_def) using has_bochner_integral_mult_left by metis

  have r4: "has_bochner_integral (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^m) ?C"
    apply (subst has_bochner_integral_cong [where f="(\<lambda>\<omega>. eval_hash_function p \<omega> k^m)" and
      g ="(\<lambda>\<omega>. f \<omega> + g \<omega>)" and M =" (poly_hash_family (ZFact p) 4)" and N=" (poly_hash_family (ZFact p) 4)"
      and y="?C"])
    apply simp
      apply (simp add:r3 del:eval_hash_function.simps)
     apply simp
    apply (rule has_bochner_integral_add)
    using r1 r2 by simp+

  show "?A = ?C" using r4 has_bochner_integral_integral_eq by blast
  show "?B " using r4 has_bochner_integral_iff by blast
qed

lemma eval_exp_1_aux: "a > 0 \<Longrightarrow> a * sqrt(x) = sqrt(a^2*x)" 
  by (simp add: real_sqrt_mult)

lemma eval_4_indep:
  assumes "prime p"
  assumes "p > 2"
  shows "prob_space.k_wise_indep_vars 
    (poly_hash_family (ZFact p) 4) 4 (\<lambda>_. borel)
    (\<lambda>k \<omega>. eval_hash_function p \<omega> k) {0..<p}"
proof -
  have a1:"p > 1" using assms(2) by auto
  have a:"prob_space (poly_hash_family (ZFact p) 4)" 
    apply (rule prob_space_poly_family)
    using assms zfact_prime_is_field apply simp
    using a1 zfact_finite by auto
  have a2:"\<And>J. J\<subseteq>carrier (ZFact (int p)) \<Longrightarrow> finite J \<Longrightarrow> card J \<le> 4 \<Longrightarrow>
    prob_space.indep_vars (poly_hash_family (ZFact (int p)) 4) 
    (\<lambda>_. uniform_count_measure (carrier (ZFact (int p)))) (hash_function (ZFact (int p))) 
    J"
    using a1 indep[where F="ZFact (int p)" and n="4"] zfact_prime_is_field assms(1) a zfact_finite 
    by (simp add:prob_space.k_wise_indep_vars_def)

  have c1:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> zfact_embed p ` J \<subseteq> carrier (ZFact (int p))"
    using zfact_embed_ran a1 by fastforce
  have c2:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> card J \<le> 4 \<Longrightarrow> finite J \<Longrightarrow> card (zfact_embed p ` J) \<le> 4"
    by (meson card_image_le le_trans)
  have c3:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> finite J \<Longrightarrow> finite (zfact_embed p ` J)"
    by simp
  have b_aux:"\<And>J. J\<subseteq>{0..<p} \<Longrightarrow> finite J \<Longrightarrow> card J \<le> 4 \<Longrightarrow>
    prob_space.indep_vars (poly_hash_family (ZFact (int p)) 4) 
    ((\<lambda>_. uniform_count_measure (carrier (ZFact (int p)))) \<circ> zfact_embed p) (\<lambda>k \<omega>. hash_function (ZFact (int p)) (zfact_embed p k) \<omega>) 
    J"
    apply (subst prob_space.indep_vars_reindex [where f="zfact_embed p" and X'="hash_function (ZFact (int p))"])
       apply (simp add:a)
      apply (metis zfact_embed_inj a1 inj_on_subset atLeastLessThan_iff mem_Collect_eq subset_eq)
     using a2 c1 c2 c3 apply presburger
    by simp
  have b:"\<And>J. J\<subseteq>{0..<p} \<Longrightarrow> card J \<le> 4 \<Longrightarrow> finite J \<Longrightarrow>
    prob_space.indep_vars (poly_hash_family (ZFact (int p)) 4) (\<lambda>_. borel) (\<lambda>k \<omega>. eval_hash_function p \<omega> k) J"
    apply simp
    apply (rule prob_space.indep_vars_compose2 [where X="(\<lambda>k \<omega>. hash_function (ZFact (int p)) (zfact_embed p k) \<omega>)"
            and M'=" (\<lambda>_. uniform_count_measure (carrier (ZFact (int p))))"])
      apply (simp add:a)
     using b_aux apply (simp)
    by measurable
  
  show ?thesis
    by (simp add: a b prob_space.k_wise_indep_vars_def del:eval_hash_function.simps)
qed

lemma eval_exp_1:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "prob_space.expectation (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k) = 0"
proof -
  have b:"1 + real p > 0" 
    using assms(3) by linarith
  have c:"real (p - Suc 0) > 0"  
    using assms(3) by linarith
  have d:"real (p - Suc 0) = real p - 1" 
    using assms(3) by linarith
  have a: "(1 + real p) * sqrt ((real p - 1) / (real p + 1)) = real (p - Suc 0) * sqrt ((real p + 1) / (real p - 1))" 
    using b c apply (simp add:eval_exp_1_aux)
    apply (subst frac_eq_eq)
    using assms(3) apply linarith
    using assms(3) apply linarith
    by (simp add:power2_eq_square d add.commute) 
  show ?thesis 
    using assms eval_hash_exp[where m="1"] apply (simp del:eval_hash_function.simps)
    by (simp add:\<alpha>_def \<beta>_def a)
qed

lemma eval_exp_2:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "prob_space.expectation (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^2) = 1"
proof-
  have a:"(1 + real p) * (real p - 1) / ((real p + 1) * (2 * real p)) = (real p - 1) / (2*real p)"
    apply (subst frac_eq_eq)
    using assms(3) apply force
    using assms(3) apply force
    by simp
  have b:"real (p - Suc 0) * (real p + 1) / ((real p - 1) * (2 * real p)) = (real p + 1) / (2*real p)"
    apply (subst frac_eq_eq)
    using assms(3) apply force
    using assms(3) apply force
      apply simp
    using assms(3) by linarith
  show ?thesis
    using assms eval_hash_exp[where m="2"] apply (simp del:eval_hash_function.simps)
    by (simp add:\<alpha>_def \<beta>_def a b add_divide_distrib[symmetric])
qed

lemma sq_power_4_elim: "sqrt x^4 = x^2 " 
  by (simp add: mult.assoc power2_eq_square power4_eq_xxxx)

lemma eval_exp_4:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "prob_space.expectation (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^4) \<le> 3"
proof -
  have a:" (2 * real p) > 0" 
    using assms by force
  have b:"(1 + real p) * ((real p - 1) / (real p + 1))\<^sup>2 = (real p - 1)^2 / (real p + 1)" 
    apply (simp add:power_divide)
    apply (subst frac_eq_eq)
    using assms apply force
    using assms apply force
    using assms by (simp add:power2_eq_square)
  have c:"real (p - Suc 0) * ((real p + 1) / (real p - 1))\<^sup>2 = (real p + 1)^2 / (real p - 1)"
    apply (simp add:power_divide)
    apply (subst frac_eq_eq)
    using assms apply force
    using assms apply force
    using assms by (simp add:power2_eq_square)

  have e:"2^2 < (real p)^2"
    apply (subst power_strict_mono)
    using assms by simp+

  have d:"(real p - 1)\<^sup>2 / (real p + 1) + (real p + 1)\<^sup>2 / (real p - 1) \<le> 6 * real p"
    apply (subst add_frac_eq)
    using assms apply force
    using assms apply force
    apply (subst pos_divide_le_eq)
    using assms apply force
    apply (simp add:power2_eq_square power3_eq_cube algebra_simps)
    apply (subst mult_le_cancel_left_pos)
    using assms apply force
    using e by (simp add:power2_eq_square)
  show ?thesis
    using assms eval_hash_exp[where m="4"] apply (simp del:eval_hash_function.simps)
    apply (simp add:\<alpha>_def \<beta>_def a add_divide_distrib[symmetric] pos_divide_le_eq sq_power_4_elim)
    by (simp add:b c d)
qed

lemma
  assumes "p > 2"
  assumes "prime p"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> i < p" 
  shows var_f2':
    "prob_space.variance
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. sum_list (map (eval_hash_function p \<omega>) xs)^2 / (real p^2-1)) \<le> 2*(f2_value xs)^2" (is "?A")
  and exp_f2':
    "prob_space.expectation
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. sum_list (map (eval_hash_function p \<omega>) xs)^2 / (real p^2-1)) = f2_value xs" (is "?B")

  and int_exp_f2':
    "integrable
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. sum_list (map (eval_hash_function p \<omega>) xs)^2 / (real p^2-1))" (is "?C")
  and int_var_f2':
    "integrable
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. (sum_list (map (eval_hash_function p \<omega>) xs)^2)^2)" (is "?D")
proof -
  have f2_sketch_elim: "\<And>\<omega>. f2_sketch (\<lambda>k \<omega>. eval_hash_function p \<omega> k) xs \<omega> = sum_list (map (eval_hash_function p \<omega>) xs)"
    by (simp add:sum_list_eval f2_sketch_def del:eval_hash_function.simps)

  have set_xs: "\<And>I. I \<subseteq> set xs \<Longrightarrow> I \<subseteq> {0..<p}"
    using assms(3)  atLeastLessThan_iff by blast
  have a1:"p > 1" using assms(1) by auto
  have a:"prob_space (poly_hash_family (ZFact p) 4)" 
    apply (rule prob_space_poly_family)
    using assms zfact_prime_is_field apply simp
    using a1 zfact_finite by auto

  show ?A
    using prob_space.var_f2[where M="poly_hash_family (ZFact p) 4" and h="\<lambda>k \<omega>. eval_hash_function p \<omega> k" and xs="xs"]
    apply (simp only:f2_sketch_elim)
    using set_xs eval_4_indep[where p="p"] assms a1 a
    eval_hash_int eval_exp_1 eval_exp_2 eval_exp_4 by (simp only:prob_space.k_wise_indep_vars_def)
  show ?B 
    using prob_space.exp_f2[where M="poly_hash_family (ZFact p) 4" and h="\<lambda>k \<omega>. eval_hash_function p \<omega> k" and xs="xs"]
    apply (simp only:f2_sketch_elim)
    using set_xs eval_4_indep[where p="p"] assms a1 a
    eval_hash_int eval_exp_1 eval_exp_2 eval_exp_4 by (simp only:prob_space.k_wise_indep_vars_def)
  show ?C 
    using prob_space.int_exp_f2[where M="poly_hash_family (ZFact p) 4" and h="\<lambda>k \<omega>. eval_hash_function p \<omega> k" and xs="xs"]
    apply (simp only:f2_sketch_elim)
    using set_xs eval_4_indep[where p="p"] assms a1 a
    eval_hash_int eval_exp_1 eval_exp_2 eval_exp_4 by (simp only:prob_space.k_wise_indep_vars_def)
  show ?D 
    using prob_space.int_var_f2[where M="poly_hash_family (ZFact p) 4" and h="\<lambda>k \<omega>. eval_hash_function p \<omega> k" and xs="xs"]
    apply (simp only:f2_sketch_elim)
    using set_xs eval_4_indep[where p="p"] assms a1 a
    eval_hash_int eval_exp_1 eval_exp_2 eval_exp_4 by (simp only:prob_space.k_wise_indep_vars_def)
qed

fun f2_alg where
  "f2_alg \<delta> \<epsilon> n xs =
    do {
      let s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-32/9 * ln \<epsilon>\<rceil>;
      let p = find_odd_prime_above n;
      h \<leftarrow> \<Pi>\<^sub>M _ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. poly_hash_family (ZFact (int p)) 4;
      sketch \<leftarrow> 
          return (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. count_space UNIV)
            (\<lambda>(i\<^sub>1,i\<^sub>2) \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
              sum_list (map (eval_hash_function p (h (i\<^sub>1, i\<^sub>2))) xs));
      sketch_avg \<leftarrow> 
          return (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. borel)
            (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1} . real_of_int (sketch (i\<^sub>1, i\<^sub>2))^2) / ((real p^2 - 1) * s\<^sub>1));
      return borel (median sketch_avg s\<^sub>2)
    }"

theorem f2_alg_correct:
  assumes "\<epsilon> < 1 \<and> \<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  shows "\<P>(r in (f2_alg \<delta> \<epsilon> n xs). abs (r - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32/9 * ln \<epsilon>)\<rceil>"
  define p where "p = find_odd_prime_above n"
  define \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = PiM ({0..<s\<^sub>1}\<times>{0..<s\<^sub>2}) (\<lambda>_. poly_hash_family (ZFact (int p)) 4)"
  define \<Omega>\<^sub>1 where "\<Omega>\<^sub>1 = PiM ({0..<s\<^sub>1}\<times>{0..<s\<^sub>2}) (\<lambda>_. borel :: real measure)"
  define \<Omega>\<^sub>2 where "\<Omega>\<^sub>2 = PiM {0..<s\<^sub>2} (\<lambda>_. borel :: real measure)"
  define \<Omega>\<^sub>3 where "\<Omega>\<^sub>3 = (borel :: real measure)"
  define medians where
    "medians = (\<lambda>(sketch_avg :: nat \<Rightarrow> real). return \<Omega>\<^sub>3 (median sketch_avg s\<^sub>2))"
  define averages where 
    "averages = (\<lambda>(sketch :: nat \<times> nat \<Rightarrow> real).
    return \<Omega>\<^sub>2 (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. (\<Sum> i\<^sub>1 \<in> {0..<s\<^sub>1}. sketch (i\<^sub>1, i\<^sub>2)^2) / real s\<^sub>1) \<bind> medians)"

  define sketches where 
      "sketches = (\<lambda>h. return \<Omega>\<^sub>1 (\<lambda>(i\<^sub>1,i\<^sub>2) \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
        sum_list (map (eval_hash_function p (h (i\<^sub>1, i\<^sub>2))) xs)) \<bind> averages)"

  have prob_space_poly: "prob_space (poly_hash_family (ZFact p) 4)"
    apply (rule prob_space_poly_family)
     apply (rule zfact_prime_is_field)
    apply (simp add:p_def find_prime_above_is_prime)
    apply (rule zfact_finite)
    using find_prime_above_min apply (simp add:p_def numeral_eq_Suc) 
    by (metis less_Suc_eq less_Suc_eq_le order_le_less_trans)
  have prob_space_0: "prob_space \<Omega>\<^sub>0" 
    by (simp add:\<Omega>\<^sub>0_def, rule prob_space_PiM, simp add:prob_space_poly)

  have s1_nonzero: "s\<^sub>1 > 0"
    apply(simp add: s\<^sub>1_def)
    using assms(2) by blast
  have s2_nonzero: "s\<^sub>2 > 0"
    apply(simp add: s\<^sub>2_def)
    using assms(1) by simp

  define f3 where "f3 = (\<lambda>h. (\<lambda>(i\<^sub>1,i\<^sub>2) \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. sum_list (map (eval_hash_function p (h (i\<^sub>1, i\<^sub>2))) xs)))"
  define f2 where "f2 = (\<lambda>h. (\<lambda>i\<^sub>2\<in>{0..<s\<^sub>2}. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (h (i\<^sub>1, i\<^sub>2))\<^sup>2) / real s\<^sub>1))"
  define f1 :: "(nat \<Rightarrow> real) \<Rightarrow> real" where "f1 = (\<lambda>h. median h s\<^sub>2)"

  have f2_meas: "f2 \<in> measurable \<Omega>\<^sub>1 \<Omega>\<^sub>2"
    by (simp add:f2_def \<Omega>\<^sub>1_def \<Omega>\<^sub>2_def, measurable)
  have f3_meas: "f3 \<in> measurable \<Omega>\<^sub>0 \<Omega>\<^sub>1"
    apply (simp add:f3_def \<Omega>\<^sub>0_def \<Omega>\<^sub>1_def, measurable, simp)
    apply (rule measurable_PiM_component_rev, simp)
    by (simp add:poly_hash_family_def)
  have f23_meas: "(f2 \<circ> f3) \<in> measurable \<Omega>\<^sub>0 \<Omega>\<^sub>2"
    using f2_meas f3_meas by measurable
  have f1_meas: "f1 \<in> measurable \<Omega>\<^sub>2 \<Omega>\<^sub>3"
    using s2_nonzero median_measurable by (simp add:f1_def \<Omega>\<^sub>2_def \<Omega>\<^sub>3_def del:median.simps)
  have f123_meas: "(f1 \<circ> f2 \<circ> f3) \<in> measurable \<Omega>\<^sub>0 \<Omega>\<^sub>3"
    using f1_meas f2_meas f3_meas by measurable
  have dist_23: "distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3) = distr (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) \<Omega>\<^sub>2 f2"
    using f2_meas f3_meas by (simp add:distr_distr comp_assoc)

  have dist_123: "distr \<Omega>\<^sub>0 \<Omega>\<^sub>3 (f1 \<circ> f2 \<circ> f3) = distr (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) \<Omega>\<^sub>3 f1"
    using f1_meas f23_meas by (simp add:distr_distr comp_assoc)

  have p_conditions: "p > 2" "prime p"
    using find_prime_above_min apply (simp add:p_def numeral_eq_Suc Suc_le_eq) 
    by (simp add:p_def find_prime_above_is_prime) 

  have "n \<le> p" by (simp add:p_def find_prime_above_lower_bound)
  hence p_bound: "\<And>x. x \<in> set xs \<Longrightarrow> x < p"
    using assms(3) order_less_le_trans by blast
  have exp_3: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> prob_space.expectation (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2)
    = f2_value xs"
    apply (subst integral_distr)
      apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
    apply (simp add:f3_def \<Omega>\<^sub>0_def)
    apply (subst lift_bochner_integral_PiM, simp)
       apply (simp add:prob_space_poly)
    using p_conditions p_bound  int_exp_f2' apply blas
    apply simp
    using p_conditions p_bound exp_f2' by blast

  have int_3: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2)"
    apply (subst integrable_distr_eq)
    apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
    apply (simp add:f3_def \<Omega>\<^sub>0_def)
    apply (subst lift_bochner_integral_PiM, simp)
       apply (simp add:prob_space_poly)
    using p_conditions p_bound  int_exp_f2' apply blast
    by simp+

  have int_3_2_aux: "\<And>x. ((x::real)^2)^2 = x^4" by (simp add:power2_eq_square power4_eq_xxxx)

  have int_3_2: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. ((\<omega> (i, j))^2)^2)"
    apply (subst integrable_distr_eq)
    apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
    apply (simp add:f3_def \<Omega>\<^sub>0_def)
    apply (subst lift_bochner_integral_PiM, simp, simp add:prob_space_poly)
    using p_conditions p_bound int_var_f2' by (simp add:int_3_2_aux, simp, simp) 

  have var3_h1: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2)
    \<le> 2 * f2_value xs^2" (is "\<And> i j. _ \<Longrightarrow> _ \<Longrightarrow> ?ths i j")
  proof -
    fix i j
    assume a1:"i < s\<^sub>1"
    assume a2:"j < s\<^sub>2"

    have a4:"(LINT a|poly_hash_family (ZFact (int p)) 4. (sum_list (map (eval_hash_function p a) xs) ^ 2)^2) -
    (LINT a|poly_hash_family (ZFact (int p)) 4. (sum_list (map (eval_hash_function p a) xs))\<^sup>2)\<^sup>2
    \<le> 2 * (f2_value xs)\<^sup>2 "
      apply (subst prob_space.variance_eq[symmetric]) 
      apply (simp add:prob_space_poly)
      using p_conditions p_bound int_exp_f2' apply (simp, simp, simp)
      using p_conditions p_bound int_var_f2' apply (simp add:int_3_2_aux)
      using p_conditions p_bound var_f2' by (simp add:int_3_2_aux)

    have a3:"LINT x|\<Omega>\<^sub>0. ((f3 x (i, j))\<^sup>2 - (LINT x|\<Omega>\<^sub>0. (f3 x (i, j))\<^sup>2))\<^sup>2 \<le> 2 * (f2_value xs)\<^sup>2"
      apply (subst prob_space.variance_eq)
      apply (simp add:prob_space_0)
      using a1 a2 apply (simp add:f3_def \<Omega>\<^sub>0_def)
      apply (subst lift_bochner_integral_PiM, simp, simp add:prob_space_poly)
      using p_conditions p_bound int_exp_f2' apply (simp, simp, simp)
      using a1 a2 apply (simp add:f3_def \<Omega>\<^sub>0_def)
      apply (subst lift_bochner_integral_PiM, simp, simp add:prob_space_poly)
      using p_conditions p_bound int_var_f2' apply (simp add:int_3_2_aux, simp, simp) 
      using a1 a2 apply (simp add:f3_def \<Omega>\<^sub>0_def)
      apply (subst lift_bochner_integral_PiM, simp, simp add:prob_space_poly)
      using p_conditions p_bound int_var_f2' apply (simp add:int_3_2_aux, simp, simp) 
      apply (subst lift_bochner_integral_PiM, simp, simp add:prob_space_poly)
      using p_conditions p_bound int_exp_f2' apply (simp, simp, simp)
      using a4 by (simp add:int_3_2_aux)
    show "?ths i j"
      apply (subst integral_distr)
      apply (simp add:f3_meas)
      apply (measurable)
      using a1 a2 apply (simp add:\<Omega>\<^sub>1_def, measurable)
      apply (subst integral_distr)
      apply (simp add:f3_meas)
      using a1 a2 apply (simp add:\<Omega>\<^sub>1_def, measurable)
      by (simp add:a3)
  qed
  have var3_h2:  "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2 / real s\<^sub>1)
    =  prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2) / (real s\<^sub>1^2)"
    using int_3_2 prob_space_0 f3_meas int_3 int_3_2
    by (subst prob_space.variance_eq; simp add: prob_space.prob_space_distr power_divide diff_divide_distrib)+

  have var_3: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2 / real s\<^sub>1)
    \<le> 2 * f2_value xs^2 / real s\<^sub>1^2"
    apply (subst var3_h2, simp, simp) using var3_h1 s1_nonzero by (simp add:divide_right_mono)

  have indep_3: "\<And>i. i < s\<^sub>2 \<Longrightarrow> prob_space.indep_vars (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>_. borel) (\<lambda>n x. (x (n,i))\<^sup>2 / real s\<^sub>1) {0..<s\<^sub>1}"
    (is "\<And>i. _ \<Longrightarrow> ?ths i")
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    show "?ths i"
      apply (rule indep_vars_distr)
         apply (simp add:f3_meas)
        apply measurable
         using a apply (simp add:\<Omega>\<^sub>1_def)
        apply measurable
       apply (simp add: \<Omega>\<^sub>0_def f3_def comp_def cong:restrict_cong)
       apply (rule indep_pim [where f="(\<lambda>j. {(j,i)})"])
         apply (simp add:prob_space_poly)
         using a apply (simp cong:restrict_cong, measurable)
               apply (rule measurable_PiM_component_rev, simp, simp add:poly_hash_family_def)
         apply simp apply simp apply (simp add:disjoint_family_on_def, simp add:s1_nonzero) 
             apply (rule subsetI, simp add:a)
      using s1_nonzero s2_nonzero apply simp
      by (simp add:prob_space_0)
  qed

  have int23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)"
    apply (simp add:dist_23)
    apply (subst integrable_distr_eq)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def)
    apply (rule Bochner_Integration.integrable_divide)
    apply (rule Bochner_Integration.integrable_sum)
    using int_3 s1_nonzero by simp

  have int23_2: "\<And> i. i < s\<^sub>2  \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i^2)"
    apply (simp add:dist_23)
    apply (subst integrable_distr_eq)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def sum_divide_distrib)
    apply (rule prob_space.var_sum_int)
    apply (rule prob_space.prob_space_distr)
         apply (simp add:prob_space_0, simp add:f3_meas, simp, simp add:indep_3)
     apply (rule Bochner_Integration.integrable_divide)
    apply (simp add:int_3)
    apply (simp add:power_divide)
     apply (rule Bochner_Integration.integrable_divide)
    using int_3_2 by (simp add:int_3_2_aux)
  
  have exp23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> prob_space.expectation (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)
    = f2_value xs"
    apply (simp add:dist_23)
    apply (subst integral_distr)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def)
    using int_3 s1_nonzero by (simp add: Bochner_Integration.integral_sum exp_3)

  have "\<And> i. i < s\<^sub>2  \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)
    \<le>  s\<^sub>1 * (2 * (f2_value xs)\<^sup>2 / s\<^sub>1\<^sup>2)"
    apply (simp add:dist_23)
    apply (subst (1 2) integral_distr)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def)
    apply (simp add:f2_def sum_divide_distrib)
    apply (subst prob_space.var_sum)
         apply (rule prob_space.prob_space_distr)
          apply (simp add:prob_space_0)
         apply (simp add:f3_meas, simp, simp add:indep_3)
    apply (simp add:int_3)
    using int_3_2 apply (simp add: power_divide)
    using var_3 sum_mono[where g="(\<lambda>_. 2 * (f2_value xs)\<^sup>2 / (real s\<^sub>1)\<^sup>2)" and K="{0..<s\<^sub>1}"] 
    by simp
  moreover have "s\<^sub>1 * (2 * (f2_value xs)\<^sup>2 / s\<^sub>1\<^sup>2) =   2 * (f2_value xs)\<^sup>2 / s\<^sub>1" 
    by (simp add: power2_eq_square)
  ultimately have var23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)
    \<le>  2 * (f2_value xs)\<^sup>2 / s\<^sub>1"
    by auto

  have space_0: "space \<Omega>\<^sub>0 \<noteq> {}" using prob_space.not_empty prob_space_0 by blast

  have "\<And>i. i < s\<^sub>2 \<Longrightarrow> \<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (r i - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> 1/8"
    (is "\<And>i. i < s\<^sub>2 \<Longrightarrow> ?rhs i \<le> 1/8")
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    define M where "M = distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)"
    define v where "v = prob_space.variance M (\<lambda>\<omega>. \<omega> i)"
    have b:"integral\<^sup>L M (\<lambda>\<omega>. \<omega> i) = f2_value xs" 
      using exp23 a by (simp add: M_def) 
    have "prob_space M" using prob_space_0 f23_meas by (simp add: M_def prob_space.prob_space_distr) 
    moreover have "(\<lambda>\<omega>. \<omega> i) \<in> borel_measurable M" using a by (simp add:M_def \<Omega>\<^sub>2_def, measurable)
    moreover have "integrable M (\<lambda>x. (x i)\<^sup>2)" using a int23_2 by (simp add:M_def)
    moreover 
    have c2:"(\<Sum>x \<in> set xs. (1::real)) \<le> f2_value xs"
      apply (simp only:f2_value_def)
      apply (rule sum_mono)
      using count_list_gr_1 
      by (metis one_le_power real_of_nat_ge_one_iff)
    have "set xs \<noteq> {}" using assms(4) by blast
    hence "card (set xs) \<ge> 1" 
      by (metis List.finite_set One_nat_def Suc_le_eq card_0_eq not_gr0)
    hence "(\<Sum>x \<in> set xs. (1::real)) \<ge> 1" by simp
    hence "f2_value xs > 0"
      using c2 by linarith
    hence c:"0 < \<delta> * f2_value xs" using assms(2) by simp 
    ultimately have "?rhs i \<le> v/(\<delta> * f2_value xs)\<^sup>2"
      using prob_space.Chebyshev_inequality[where a="\<delta> * f2_value xs" and M="M" and f="(\<lambda>\<omega>. \<omega> i)"]
      apply (simp add:v_def[symmetric] M_def[symmetric])
      by (simp add:b v_def[symmetric] M_def[symmetric])
    moreover have "v \<le> 2* (f2_value xs)\<^sup>2 / s\<^sub>1"  using var23 a by (simp add:v_def M_def) 
    hence "v/(\<delta> * f2_value xs)\<^sup>2 \<le> 2/ (\<delta>\<^sup>2 * s\<^sub>1)" 
      using s1_nonzero c apply (simp add:algebra_simps  divide_le_eq  pos_le_divide_eq) 
      by (metis power2_less_0 power_mult_distrib)
    moreover have "s\<^sub>1 \<ge> 16 / \<delta>\<^sup>2" using s\<^sub>1_def 
      using real_nat_ceiling_ge by blast
    hence "2/(\<delta>\<^sup>2 * s\<^sub>1) \<le> 1/8" using assms(2) 
      by (simp add: algebra_simps divide_le_eq)
    ultimately show "?rhs i \<le> 1/8" by linarith
  qed

  moreover have "prob_space.indep_vars (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>_. borel) (\<lambda>i \<omega>. \<omega> i)  {0..<s\<^sub>2}"
    apply (rule indep_vars_distr)
       apply (simp add:f23_meas)
      apply (simp add:\<Omega>\<^sub>2_def)
     apply (simp add:\<Omega>\<^sub>0_def)
     apply (rule indep_pim [where f="(\<lambda>i. {0..<s\<^sub>1} \<times> {i})"])
            apply (simp add:prob_space_poly)
           apply (simp add:comp_def f2_def f3_def, measurable)
           apply (rule measurable_PiM_component_rev, simp, simp add:poly_hash_family_def, measurable)
         apply (simp add:f2_def f3_def)
        apply (simp add:disjoint_family_on_def, fastforce)
       apply (simp add:s2_nonzero)
      apply (rule subsetI, force)
     apply (simp add:s2_nonzero s1_nonzero)
    by (simp add:prob_space_0)

  moreover have "- 32 / 9 * ln \<epsilon> \<le> real s\<^sub>2" using s\<^sub>2_def by linarith
  moreover have "prob_space (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3))" 
    using f23_meas prob_space_0 by (simp add: prob_space.prob_space_distr)
  ultimately have 
    "\<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (median r s\<^sub>2 - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> \<epsilon>"
    using assms prob_space.median_bound[where \<delta>="\<delta>*f2_value xs" and X="\<lambda>i \<omega>. \<omega> i"]
    by blast
  moreover have "\<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>3 (f1 \<circ> f2 \<circ> f3)). abs (r - f2_value xs) \<ge> \<delta> * f2_value xs) =
    \<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (median r s\<^sub>2 - f2_value xs) \<ge> \<delta> * f2_value xs)"
    apply (subst dist_123)
    apply (subst measure_distr)
      apply (simp add: f1_meas)
     apply (simp) 
    apply (simp add:\<Omega>\<^sub>3_def)
    apply (rule measure_eq_AE)
      apply (rule AE_I2)
     apply (simp add:f1_def \<Omega>\<^sub>3_def \<Omega>\<^sub>2_def del:median.simps)
    apply (simp add:\<Omega>\<^sub>3_def \<Omega>\<^sub>2_def, measurable)
    using f1_meas apply (simp add:\<Omega>\<^sub>3_def \<Omega>\<^sub>2_def)
    apply measurable
     using s2_nonzero apply (simp  add: \<Omega>\<^sub>3_def median_measurable  \<Omega>\<^sub>2_def del:median.simps)
    by measurable
  moreover 
  have "(\<Omega>\<^sub>0 \<bind> sketches) = distr \<Omega>\<^sub>0 \<Omega>\<^sub>3 (f1 \<circ> f2 \<circ> f3)" 
    apply (simp add:sketches_def)
    apply (subst bind_return [where N="\<Omega>\<^sub>3"])
      apply (simp add:averages_def \<Omega>\<^sub>1_def \<Omega>\<^sub>3_def, measurable)
     apply (simp add:\<Omega>\<^sub>2_def)
     using median_measurable s2_nonzero apply (simp add:\<Omega>\<^sub>2_def \<Omega>\<^sub>3_def medians_def del:median.simps, measurable)
     apply (simp add:\<Omega>\<^sub>1_def space_PiM)
    apply (simp add:averages_def)
    apply (subst bind_return [where N="\<Omega>\<^sub>3"])
      using median_measurable s2_nonzero apply (simp add:medians_def del:median.simps add: \<Omega>\<^sub>2_def \<Omega>\<^sub>3_def, measurable)
     apply (simp add:\<Omega>\<^sub>2_def space_PiM)
    apply (simp add:medians_def del:median.simps cong:restrict_cong)
    apply (subst bind_return_distr')
      apply (simp add:space_0)
     using f123_meas apply (simp add: f1_def f2_def f3_def comp_def del:median.simps cong:restrict_cong)
    by (simp add: f1_def f2_def f3_def comp_def del:median.simps cong:restrict_cong)
  moreover have "f2_alg \<delta> \<epsilon> n xs = \<Omega>\<^sub>0 \<bind> sketches"
    by (simp add:\<Omega>\<^sub>0_def \<Omega>\<^sub>1_def \<Omega>\<^sub>2_def \<Omega>\<^sub>3_def sketches_def averages_def medians_def Let_def s\<^sub>1_def s\<^sub>2_def p_def
            del:median.simps)
  ultimately show ?thesis by (simp del:median.simps f2_alg.simps) 
qed

end