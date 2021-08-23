section \<open>Frequency Moment 2\<close>

theory F2_Algorithm
  imports Main "HOL-Probability.Giry_Monad" "HOL-Probability.Probability_Mass_Function" UniversalHashFamily Field 
    Median Probability_Ext "HOL-Library.Multiset" Partitions Primes_Ext
    "HOL-Library.Rewrite" "HOL-Library.Finite_Map"
begin


definition f2_value where
  "f2_value xs = (\<Sum> x \<in> set xs. (rat_of_nat (count_list xs x)^2))"

fun eval_hash_function where
  "eval_hash_function p h k = (
    if hash_function (ZFact (int p)) (zfact_embed p k) (map (zfact_embed p) h) \<in> zfact_embed p ` {k. 2*k < p} then
      int p - 1
    else
      - int p - 1
  )"

type_synonym f2_space = "nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> nat list) \<times> (nat \<times> nat \<Rightarrow> int)"

definition poly_rep :: "nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "poly_rep p n = {h. h = [] \<or> (length h \<le> n \<and> set h \<subseteq> {0..<p} \<and> hd h \<noteq> 0)}"
definition poly_rep_space where "poly_rep_space p n = uniform_count_measure (poly_rep p n)"


fun f2_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f2_space pmf" where
  "f2_init \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-32/9 * ln (real_of_rat \<epsilon>)\<rceil>;
      let p = find_odd_prime_above n;
      h \<leftarrow> pmf_of_set ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E poly_rep p 4);
      return_pmf (s\<^sub>1, s\<^sub>2, p, h, (\<lambda>_ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. (0 :: int)))
    }"

fun f2_update :: "nat \<Rightarrow> f2_space \<Rightarrow> f2_space pmf" where
  "f2_update x (s\<^sub>1, s\<^sub>2, p, h, sketch) = 
    return_pmf (s\<^sub>1, s\<^sub>2, p, h, \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. eval_hash_function p (h i) x + sketch i)"

fun f2_result :: "f2_space \<Rightarrow> rat pmf" where
  "f2_result (s\<^sub>1, s\<^sub>2, p, h, sketch) = 
    return_pmf (median (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. 
      (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1} . rat_of_int (sketch (i\<^sub>1, i\<^sub>2))^2) / ((rat_of_nat p^2-1) * rat_of_nat s\<^sub>1)) s\<^sub>2
    )"

lemma (in prob_space)
  assumes "\<And>I. k_wise_indep_vars 4 (\<lambda>_. borel) h (set xs)"
  assumes "\<And>i (m :: nat). i \<in> set xs \<Longrightarrow> integrable M (\<lambda>\<omega>. (h i \<omega>)^m)"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (h i) = 0"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^2) = 1"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^4) \<le> 3"
  defines "f2_sketch \<equiv> (\<lambda>\<omega>. \<Sum> x \<in> set xs. real (count_list xs x) * h x \<omega>)"
  shows var_f2:"has_variance M (\<lambda>\<omega>. f2_sketch \<omega>^2) (\<lambda>r. r \<le> 2*(real_of_rat (f2_value xs)^2))" (is "?A")
  and exp_f2:"has_bochner_integral M (\<lambda>\<omega>. f2_sketch \<omega>^2) (real_of_rat (f2_value xs))" (is ?B)
proof -

  have "\<And>i. i \<in> set xs \<Longrightarrow> indep_vars (\<lambda>_. borel) h {i}" using assms(1) by (simp add:k_wise_indep_vars_def)
  hence meas:"\<And>i. i \<in> set xs \<Longrightarrow> h i \<in> measurable M borel" by (simp add:indep_vars_def2) 

  define f2_sum where "f2_sum = (\<lambda>x \<omega>. real (count_list xs x) * h x \<omega>)"
  define f2_pow where "f2_pow = (\<lambda>x n \<omega>. f2_sum x \<omega> ^ n)"
  define h_power where "h_power = (\<lambda>i m. expectation (\<lambda>\<omega>. (h i \<omega>)^m))"
  define h_power_4_diff where "h_power_4_diff = (\<lambda>i. h_power i 4 - 3)"

  have f2_sketch_elim: "\<And>\<omega>. f2_sketch \<omega> = (\<Sum> x \<in> set xs. f2_sum x \<omega>)"
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
    ultimately have "indep_vars (\<lambda>_. borel) (\<lambda>i. h i) x" using assms(1) by (simp add:k_wise_indep_vars_def)
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

  have fold_sym: "\<And>x y. (x \<noteq> y \<and> y \<noteq> x) = (x \<noteq> y)" by auto

  have int_exp_f2: "integrable M (\<lambda>\<omega>. f2_sketch \<omega>^2)"
    apply (simp add: f2_sketch_elim power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    by (simp add: c3 indep1 indep2 exp_def sum.distrib)

  have int_var_f2: "integrable M (\<lambda>\<omega>. f2_sketch \<omega>^4)"
    apply (simp add: f2_sketch_elim power2_eq_square power4_eq_xxxx)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    by (simp add: c3 indep1 indep2 exp_def sum.distrib)

  show exp_2: "?B"
    apply (simp add: has_bochner_integral_iff)
    apply (simp add: f2_sketch_elim power2_eq_square f2_value_def)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    apply (simp add: c3 indep1 indep2 h_power_simps sum.distrib)
    apply (simp add: has_eq_relation_elim)
    by (simp add: sum_collapse rev_ineq of_rat_sum of_rat_mult)

  have t:"\<And>x. ((x::real)^2)^2=x^4"
    by simp

  show "?A"
    apply (simp add:has_variance_def)
    apply (rule conjI) apply (metis int_var_f2)
    apply (rule conjI) apply (metis int_exp_f2)
    apply (rule conjI, simp add: prob_space_axioms)
    apply (subst variance_eq, metis int_exp_f2, simp add:t int_var_f2)
    using exp_2 apply (simp add: has_bochner_integral_iff f2_value_def)
    apply (simp add: f2_sketch_elim power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    apply (simp add: c3 indep1 indep2 h_power_simps sum.distrib)
    apply (simp add: has_eq_relation_elim)
    apply (simp add: sum_collapse rev_ineq sum_subtractf algebra_simps fold_sym)
    apply (simp add: algebra_simps sum_distrib_left of_rat_sum of_rat_mult)
    apply (rule sum_mono)
    by (simp add: h_power_4_estimate mult_nonneg_nonpos2 algebra_simps)
qed

lemma fin_poly_rep: "finite (poly_rep p n)"
proof -
  have "poly_rep p n \<subseteq> {x. set x \<subseteq> {0..<p} \<and> length x \<le> n}"
    apply (rule subsetI, simp add:poly_rep_def)
    apply (rule conjI)
     apply (metis length_pos_if_in_set less_numeral_extra(3) list.size(3) subset_iff)
    by fastforce
  moreover have "finite {x. set x \<subseteq> {0..<p} \<and> length x \<le> n}"
    by (rule finite_lists_length_le, simp)
  ultimately show ?thesis using finite_subset by blast
qed

lemma prob_space_poly_rep_space: "prob_space (poly_rep_space p n)"
  apply (simp add:poly_rep_space_def)
  apply (rule  prob_space_uniform_count_measure)
   apply (simp add:fin_poly_rep)
  apply (simp add:poly_rep_def) by blast
  
lemma image_eqI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> g x \<in> A \<and> f (g x) = x"
  shows "f ` A = B"
  by (metis order_antisym assms image_subsetI subsetI rev_image_eqI)

lemma poly_rep_into_polynomials:
  assumes "p > 1"
  shows "map (zfact_embed p) ` (poly_rep p n) \<subseteq> bounded_degree_polynomials (ZFact p) n" (is "_ ` ?A \<subseteq> ?B")
proof (rule image_subsetI)
  fix x
  assume a:"x \<in> ?A"
  show "map (zfact_embed p) x \<in> ?B" 
    apply (cases "x= []",simp add:bounded_degree_polynomials_length univ_poly_def polynomial_def)
    using a
    apply (simp add:poly_rep_def bounded_degree_polynomials_length univ_poly_def polynomial_def)
    apply (rule conjI)
    using zfact_embed_ran[OF assms] image_mono apply blast
    by (simp add: hd_map  subset_iff zfact_embed_zero_iff[OF assms(1)]) 
qed

lemma polynomials_into_poly_rep:
  assumes "p > 1"
  shows "map (the_inv_into {0..<p} (zfact_embed p)) ` bounded_degree_polynomials (ZFact p) n \<subseteq> (poly_rep p n)" (is "_ ` ?A \<subseteq> ?B")
proof (rule image_subsetI)
  fix x
  assume a:"x \<in> ?A"
  have b:"x \<noteq> [] \<Longrightarrow> lead_coeff x \<in> carrier (ZFact p)"
    using a apply (simp add:bounded_degree_polynomials_length  univ_poly_def polynomial_def)
    using hd_in_set a by blast
  show "map (the_inv_into {0..<p} (zfact_embed p)) x \<in> ?B" 
    apply (cases "x= []",simp add:poly_rep_def)
    using a
    apply (simp add:poly_rep_def bounded_degree_polynomials_length univ_poly_def polynomial_def)
    apply (rule conjI, rule image_subsetI)
     apply (rule the_inv_into_into)
       apply(metis zfact_embed_inj[OF assms])
      using zfact_embed_ran[OF assms] apply blast
       apply simp
      apply (simp add:hd_map)
      apply(rule ccontr)
      using b by (simp add: zfact_embed_inv_zero_iff[OF assms(1)])
qed

lemma poly_rep_eq_polynomials:
  assumes "p > 1"
  shows "map (zfact_embed p) ` (poly_rep p n) = (bounded_degree_polynomials (ZFact p) n)"
  apply (rule image_eqI[where g="map (the_inv_into {0..<p} (zfact_embed p))"])
  using assms poly_rep_into_polynomials apply blast
  apply (rule conjI)
  using assms polynomials_into_poly_rep apply blast
  apply (simp add:comp_def)
  apply (rule map_idI, rule f_the_inv_into_f)
   apply (metis zfact_embed_inj[OF assms])
  apply (simp add:zfact_embed_ran[OF assms] bounded_degree_polynomials_def)
  by (metis length_greater_0_conv length_pos_if_in_set polynomial_def subsetD univ_poly_carrier)

lemma polynomials_eq_poly_rep:
  assumes "p > 1"
  shows "map (the_inv_into {0..<p} (zfact_embed p)) `  (bounded_degree_polynomials (ZFact p) n) = (poly_rep p n)"
  apply (rule image_eqI[where g="map (zfact_embed p)"])
  using assms polynomials_into_poly_rep apply blast
  apply (rule conjI)
  using assms poly_rep_into_polynomials apply blast
  apply (simp add:comp_def)
  apply (rule map_idI, rule the_inv_into_f_f)
   apply (metis zfact_embed_inj[OF assms])
  apply (simp add:poly_rep_def) 
  by (metis atLeast0LessThan length_pos_if_in_set lessThan_iff less_numeral_extra(3) list.size(3) subsetD)

lemma ex_poly: 
  "bounded_degree_polynomials (ZFact (int p)) 4 \<noteq> {}" (is "?A \<noteq> _")
proof -
  have "\<zero>\<^bsub>poly_ring (ZFact (int p))\<^esub> \<in> ?A"
    apply (simp add:bounded_degree_polynomials_def)
    apply (rule conjI)
     apply (simp add: univ_poly_zero univ_poly_zero_closed)
    using univ_poly_zero by blast
  thus ?thesis by blast
qed

lemma fin_poly: 
  assumes "prime p"
  shows "finite (bounded_degree_polynomials (ZFact (int p)) n)"
  using finite_poly_count zfact_prime_is_field zfact_finite prime_gt_1_nat assms 
  by blast

lemma distr_equiv_finite_space:
  assumes "finite A"
  assumes "B = f ` A"
  assumes "inj_on f A"
  shows "distr (uniform_count_measure A) (uniform_count_measure B) f = uniform_count_measure B"
proof -
  have a:"f \<in> uniform_count_measure A \<rightarrow>\<^sub>M uniform_count_measure B"
    apply (simp add:measurable_def space_uniform_count_measure sets_uniform_count_measure)
    using assms by blast
  have b: "finite (f ` A)" 
    using assms by blast
  show ?thesis 
    apply (rule measure_eqI, simp)
    using a apply (simp add: emeasure_distr)
    using assms b card_image[OF assms(3)]
    apply (simp add:emeasure_uniform_count_measure space_uniform_count_measure sets_uniform_count_measure)
    using assms(3) card_vimage_inj_on by blast
qed

lemma inj_on_map:
  assumes "inj_on f A"
  assumes "B \<subseteq> {x. set x \<subseteq> A}"
  shows "inj_on (map f) B"
  apply (rule inj_onI)
  apply (rule list.inj_map_strong[where f="f" and fa="f"])
   apply (metis inj_on_contraD mem_Collect_eq subsetD assms)
  by simp

lemma distr_poly_rep_rev:
  assumes "prime p"
  shows "distr (uniform_count_measure (bounded_degree_polynomials (ZFact p) n)) (uniform_count_measure (poly_rep p n))
    (map (the_inv_into {0..<p} (zfact_embed p))) = poly_rep_space p n"
  apply (simp add:poly_rep_space_def)
  apply (rule distr_equiv_finite_space)
    apply (metis fin_poly[OF assms])
   apply (metis polynomials_eq_poly_rep[OF prime_gt_1_nat[OF assms], symmetric])
  apply (rule inj_on_map[where A="carrier (ZFact p)"])
  using inj_on_the_inv_into[OF zfact_embed_inj]
   zfact_embed_ran prime_gt_1_nat  assms apply simp
  apply (simp add:bounded_degree_polynomials_def)
  apply (rule subsetI, simp)
  by (meson ZFact_is_cring cring_def ring.carrier_is_subring ring.polynomial_in_carrier univ_poly_carrier)

lemma measurable_uniform_count_measure:
  assumes "f ` A \<subseteq> B"
  shows "f \<in> uniform_count_measure A \<rightarrow>\<^sub>M uniform_count_measure B"
  apply (simp add:measurable_def space_uniform_count_measure sets_uniform_count_measure)
  using assms by blast

lemma eval_exp:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2" 
  shows eval_hash_exp: 
    "has_bochner_integral (poly_rep_space p 4) (\<lambda>\<omega>. (eval_hash_function p \<omega> k / sqrt (real p^2-1)) ^m) (
    ((real p-1)^m* (real p+1) + (-real p - 1)^m *(real p - 1))/ ((2*real p) * sqrt(real p^2-1)^m))"
proof -
  define A where "A = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k < p}}"
  define B where "B = {\<omega>. 
    \<omega> \<in>  bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k \<ge> p \<and> k < p}}"
  define f where "f = (\<lambda>\<omega>. indicator A \<omega> * (real p-1)^m)"
  define g where "g = (\<lambda>\<omega>. indicator B \<omega> * (-real p-1)^m)"

  have g:"p > 1" using assms(1) prime_gt_1_nat by auto

  have a1:"finite (carrier (ZFact p))"  using zfact_finite g by auto
  have a2:"ring (ZFact p)"  using ZFact_is_cring cring_def by blast
  have a7:"zfact_embed p k \<in> carrier (ZFact p)" 
    using zfact_embed_ran[OF g] assms(2) atLeast0LessThan by auto

  hence g4:"\<And>\<omega>. \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<Longrightarrow> ring.eval (ZFact (int p)) \<omega> (zfact_embed p k) \<in> carrier (ZFact p)"
    using a2 ring.polynomial_in_carrier[where K="carrier (ZFact p)" and R="ZFact p"] 
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
      by (metis zfact_embed_ran[OF g] atLeastLessThan_iff image_mono mem_Collect_eq subset_eq)
    moreover have "?lhs \<inter> ?rhs = {}"
    proof (rule Int_emptyI)
      fix x
      assume "x \<in> zfact_embed p ` {k. 2*k < p}"
      then obtain k1 where x_def_1: "x = zfact_embed p k1" and k1_bound: "2*k1 < p"
        by blast
      assume "x \<in> zfact_embed p ` {k. p \<le> 2*k \<and> k < p}"
      then obtain k2 where x_def_2: "x = zfact_embed p k2" and k2_bound: "p \<le> 2*k2 \<and> k2 < p"
        by blast
      have "k1 \<in> {0..< p}" using k1_bound by auto
      moreover have "k2 \<in> {0..<p}" using k2_bound by auto
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
  have r3_p: "\<And>\<omega> y. \<omega> \<in> space (poly_hash_family (ZFact (int p)) 4) \<Longrightarrow> y \<in> set \<omega> \<Longrightarrow> y \<in> zfact_embed p ` {0..<p}"
    using zfact_embed_ran[OF g]
    apply (simp add:poly_hash_family_def space_uniform_count_measure bounded_degree_polynomials_length)
    by (meson a2 ring.carrier_is_subring ring.polynomial_in_carrier subsetD univ_poly_carrier)

  have r3: "\<And>\<omega>. \<omega> \<in> space (poly_hash_family (ZFact (int p)) 4) \<Longrightarrow>
    (real_of_int (eval_hash_function p (map (the_inv_into {0..<p} (zfact_embed p)) \<omega>) k))^m =  f \<omega> + g \<omega>"
    using r3_p f_the_inv_into_f[OF zfact_embed_inj[OF g]] apply (simp add:poly_hash_family_def space_uniform_count_measure comp_def cong:map_cong)
    apply (simp add:f_def g_def A_def B_def hash_function_def)
    apply (rule conjI, rule impI) using g4 r3_aux apply (simp add:power_one_over[symmetric])
    apply (rule impI)
    using g4 r3_aux by (simp add:power_one_over[symmetric])

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
    using zfact_finite g apply simp apply (simp add:a7)
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
  moreover have "measure (poly_hash_family (ZFact p) 4) B = (real p-1)/(2*p)" 
    apply (simp add:poly_hash_family_def measure_uniform_count_measure a B_def bounded_degree_polynomials_count a1 a2) 
    apply (simp add: hash_function_def)
    apply (subst poly_card_set)
    using zfact_prime_is_field assms apply force
    using zfact_finite g apply simp apply (simp add:a7)
      apply simp
    apply (rule image_subsetI, simp) using zfact_embed_ran g 
     apply (simp add: ZFact_defs(1) ZFact_defs(2) int.a_rcosetsI zfact_embed_def)
    apply (subst card_image) using g zfact_embed_inj inj_on_subset[where B="{k. p \<le> 2 * k \<and> k < p}"] apply force
    using g apply (simp add:card_A zfact_card nonzero_divide_eq_eq nonzero_eq_divide_eq)
    by (simp add: power3_eq_cube power4_eq_xxxx)
  ultimately have r2:"has_bochner_integral (poly_hash_family (ZFact p) 4) g ((real p-1)/ real(2*p) * (-real p-1)^m)"
    apply (subst g_def) using has_bochner_integral_mult_left by metis

  show ?thesis
    apply (subst power_divide)
    apply (subst divide_divide_eq_left[symmetric])
    apply (rule has_bochner_integral_divide_zero)
    apply (subst distr_poly_rep_rev[OF assms(1), symmetric])
    apply (rule has_bochner_integral_distr)
      apply simp
     apply simp
     apply (simp add:measurable_def space_uniform_count_measure sets_uniform_count_measure) 
    using polynomials_into_poly_rep[OF g] apply (simp add:Pi_def, blast) 
    using r3 apply (simp add:add_divide_distrib poly_hash_family_def[symmetric] del:eval_hash_function.simps cong:has_bochner_integral_cong)
    apply (rule has_bochner_integral_add)
    using r1 apply (simp add:algebra_simps)
    using r2 by (simp add:algebra_simps)
qed

lemma eval_exp_1:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "has_bochner_integral (poly_rep_space p 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k/ sqrt (real p^2-1)) 0"
proof -
  have a:"((real p - 1) ^ 1 * (real p + 1) + (- real p - 1) ^ 1 * (real p - 1)) = 0"
    by (simp add:algebra_simps)
  show ?thesis 
    using assms eval_hash_exp[where m="1" and p="p"] a by (simp del:eval_hash_function.simps)
qed

lemma eval_exp_2:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "has_bochner_integral (poly_rep_space p 4) (\<lambda>\<omega>. (eval_hash_function p \<omega> k/ sqrt (real p^2-1))^2) 1"
proof -
  have b:"(-real p -1)^2=(real p +1)^2"
    by (simp add: power2_commute)

  have a:"(((real p - 1)\<^sup>2 * (real p + 1) + (- real p - 1)\<^sup>2 * (real p - 1)) / (2 * real p * (sqrt ((real p)\<^sup>2 - 1))\<^sup>2)) = 1"
    using b power2_eq_square[where a="real p-1"]  power2_eq_square[where a="real p+1"] apply (simp)
    apply (subst (2) mult.assoc)
    apply (subst mult.commute[where b="real p+1" and a="real p - 1"]) 
    apply (subst (2) mult.assoc)
    apply (simp add:mult.assoc[symmetric])
    apply (subst distrib_right[symmetric])
    apply (subst distrib_right[symmetric], simp)
    apply (subst real_sqrt_pow2)
    using assms apply simp
    apply (simp add:algebra_simps power2_eq_square)
    using assms 
    by (metis bot_nat_0.not_eq_extremum less_nat_zero_code less_one mult_less_cancel2 of_nat_1_eq_iff of_nat_mult prime_gt_1_nat)
  show ?thesis 
    apply (subst (2) a[symmetric])
    apply (rule eval_hash_exp[where m="2" and p="p"])
    using assms by auto
qed

lemma eval_exp_4:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "prob_space.expectation (poly_rep_space p 4) 
      (\<lambda>\<omega>. (eval_hash_function p \<omega> k / sqrt (real p^2-1))^4) \<le> 3"
proof -
  have a:"\<And>x. (x::real)^4=(x^2)^2"
    by simp
  have b: "\<And>x y. x\<le>y \<Longrightarrow> x \<le> 12 +(y::real)"
    by simp

  have c:"2 \<le> real p" using assms 
    by linarith
  have d: "4=(2::real)^2" by auto
  have "(((real p-1)^4* (real p+1) + (-real p - 1)^4 *(real p - 1))/ ((2*real p) * sqrt(real p^2-1)^4)) \<le> 3"
    apply (subst pos_divide_le_eq)
    using assms apply (simp add:a)
    apply (rule mult_pos_pos, simp, simp)
    apply (metis One_nat_def Suc_1 less_not_refl nat.simps(3) nat_power_eq_Suc_0_iff of_nat_1_eq_iff of_nat_power prime_gt_1_nat)
    using assms apply (subst (3) a, simp)
    apply (simp add:algebra_simps power4_eq_xxxx power2_eq_square)
    apply (subst distrib_left[symmetric])
    apply (subst mult_le_cancel_iff2, simp)
    apply (rule b)
    apply (subst mult_le_cancel_iff2, simp)
    apply (subst mult_le_cancel_iff2, simp)
    apply (simp add:power2_eq_square[symmetric])
    apply (subst d)
    by (metis c of_nat_le_iff of_nat_numeral of_nat_power power_mono zero_le)

  then show ?thesis using eval_exp[where m="4" and p="p"] has_bochner_integral_integral_eq
    by (metis assms)
qed


lemma prob_space_poly:
  assumes "prime p"
  shows "prob_space (uniform_count_measure (bounded_degree_polynomials (ZFact (int p)) 4))"
  by (metis assms prob_space_uniform_count_measure fin_poly ex_poly)

lemma eval_4_indep:
  assumes "prime p"
  assumes "p > 2"
  shows "prob_space.k_wise_indep_vars 
    (poly_rep_space p 4) 4 (\<lambda>_. borel)
    (\<lambda>k \<omega>. eval_hash_function p \<omega> k/ sqrt (real p^2-1)) {0..<p}"
proof -
  have a1:"p > 1" using assms(2) by auto
  have a:"prob_space (poly_hash_family (ZFact p) 4)" 
    apply (rule prob_space_poly_family)
    using assms zfact_prime_is_field apply simp
    using a1 zfact_finite by auto

  interpret prob_space "(poly_hash_family (ZFact p) 4)"
    by (metis a)

  have a2:"\<And>J. J\<subseteq>carrier (ZFact (int p)) \<Longrightarrow> finite J \<Longrightarrow> card J \<le> 4 \<Longrightarrow>
    prob_space.indep_vars (poly_hash_family (ZFact (int p)) 4) 
    (\<lambda>_. uniform_count_measure (carrier (ZFact (int p)))) (hash_function (ZFact (int p))) 
    J"
    using a1 poly_family_indep[where F="ZFact (int p)" and n="4"] zfact_prime_is_field assms(1) a zfact_finite 
    by (simp add:prob_space.k_wise_indep_vars_def)

  have a3_aux: "\<And>x y. x \<in> space (poly_hash_family (ZFact (int p)) 4) \<Longrightarrow> y \<in> set x \<Longrightarrow> y \<in> zfact_embed p ` {0..<p}"
    apply (simp add:poly_hash_family_def bounded_degree_polynomials_def space_uniform_count_measure zfact_embed_ran[OF a1])
        by (metis length_greater_0_conv length_pos_if_in_set polynomial_def subsetD univ_poly_carrier)
  have step_2:"\<And>J. J\<subseteq>carrier (ZFact (int p)) \<Longrightarrow> finite J \<Longrightarrow> card J \<le> 4 \<Longrightarrow>
    prob_space.indep_vars (poly_rep_space p 4) 
    (\<lambda>_. uniform_count_measure (carrier (ZFact (int p)))) (\<lambda>k \<omega>. hash_function (ZFact (int p)) k (map (zfact_embed p) \<omega>)) 
    J"
    apply (subst distr_poly_rep_rev[OF assms(1), symmetric])
    apply (rule indep_vars_distr)
       apply (metis measurable_uniform_count_measure polynomials_into_poly_rep[OF a1])
    apply (rule measurable_uniform_count_measure, rule image_subsetI)
    apply (rule hash_function_image[where n="4"])
    using assms(1) zfact_prime_is_field apply presburger
       apply blast
    using  poly_rep_into_polynomials[OF a1] apply blast
       apply (subst poly_hash_family_def[symmetric])
       apply (rule indep_vars_equiv_rv[where X'="hash_function (ZFact (int p))"])
    using f_the_inv_into_f[OF zfact_embed_inj [OF a1]] a a3_aux
      apply (simp add:comp_def poly_hash_family_def[symmetric] space_uniform_count_measure cong:indep_vars_cong_with_space map_cong)
       apply (simp add:a2)
    by (simp add: prob_space_poly[OF assms(1)])

  have reindex_subst: "(\<lambda>_. uniform_count_measure (carrier (ZFact (int p)))) =
      (\<lambda>_. uniform_count_measure (carrier (ZFact (int p)))) \<circ> zfact_embed p" by simp

  have step_1:"\<And>J. J\<subseteq>{0..<p} \<Longrightarrow> card J \<le> 4 \<Longrightarrow> finite J \<Longrightarrow>
    prob_space.indep_vars (poly_rep_space p 4) (\<lambda>_. borel) (\<lambda>k \<omega>. eval_hash_function p \<omega> k/ sqrt (real p^2-1)) J"
    apply simp
    apply (rule prob_space.indep_vars_compose2 [where X="(\<lambda>k \<omega>. hash_function (ZFact (int p)) (zfact_embed p k) (map (zfact_embed p) \<omega>))"
            and M'=" (\<lambda>_. uniform_count_measure (carrier (ZFact (int p))))"])
      apply (simp add:prob_space_poly_rep_space)
     apply (subst reindex_subst)
     apply (rule prob_space.indep_vars_reindex)
       apply (simp add:prob_space_poly_rep_space)
      apply (metis zfact_embed_inj[OF a1] inj_on_subset)
     apply (rule step_2)
    using zfact_embed_ran[OF a1] apply blast
      apply blast
     apply (subst card_image)
      apply (metis zfact_embed_inj[OF a1] inj_on_subset)
     apply simp
    by simp
  
  show ?thesis
    by (simp add: step_1 prob_space_poly_rep_space prob_space.k_wise_indep_vars_def 
        del:eval_hash_function.simps)
qed


lemma 
  assumes "prime p"
  assumes "p > 2"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < p"
  defines "M \<equiv> poly_rep_space p 4"
  defines "f2_sketch \<equiv> (\<lambda>a. (real_of_int (sum_list (map (eval_hash_function p a) xs)))\<^sup>2 / ((real p)\<^sup>2 - 1))"
  shows var_f2:"has_variance M (\<lambda>\<omega>. f2_sketch \<omega>) (\<lambda>r. r \<le> 2*(real_of_rat (f2_value xs)^2))" (is "?A")
  and exp_f2:"has_bochner_integral M (\<lambda>\<omega>. f2_sketch \<omega>) (real_of_rat (f2_value xs))" (is "?B")
proof -
  have a:"prob_space M" 
    by (simp add:M_def prob_space_poly_rep_space)

  have f2_sketch_elim:
  "f2_sketch = (\<lambda>\<omega>. (\<Sum> x \<in> set xs. real (count_list xs x) * (eval_hash_function p \<omega> x/ sqrt (real p^2-1)))^2 )"
    apply (simp add:sum_list_eval f2_sketch_def  sum_divide_distrib[symmetric] power_divide del:eval_hash_function.simps)
    apply (subst real_sqrt_pow2)
    using assms by simp+
  have b:"prob_space.k_wise_indep_vars M 4 (\<lambda>_. borel) (\<lambda>x \<omega>. real_of_int (eval_hash_function p \<omega> x) / sqrt ((real p)\<^sup>2 - 1))
          (set xs)"
    apply (rule prob_space.k_wise_subset [where I="{0..<p}"])
    apply (simp add:a)
    using eval_4_indep assms apply (simp add:poly_hash_family_def del:eval_hash_function.simps)
    apply (rule subsetI)
    using assms(3) by simp

  show ?A
    apply (simp only:f2_sketch_elim)
    apply (rule prob_space.var_f2[where xs="xs" and M="M" and h="\<lambda>x \<omega>. real_of_int (eval_hash_function p \<omega> x)/sqrt (real p^2-1)"])
    apply (simp add:a)
    apply (metis b)
    using assms eval_exp [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_1 [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_2 [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_4 [where p="p"] by (simp add:has_bochner_integral_iff poly_hash_family_def)

  show ?B
    apply (simp only:f2_sketch_elim)
    apply (rule prob_space.exp_f2[where xs="xs" and M="M" and h="\<lambda>x \<omega>. real_of_int (eval_hash_function p \<omega> x)/sqrt (real p^2-1)"])
    apply (simp add:a)
    apply (metis b)
    using assms eval_exp [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_1 [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_2 [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_4 [where p="p"] by (simp add:has_bochner_integral_iff poly_hash_family_def)
qed

lemma pmf_to_borel:
  assumes "{\<omega>. g \<omega>} \<in> sets borel"
  assumes "(real_of_rat \<circ> f) \<in> measurable (measure_pmf M) borel"
  shows "measure (distr (measure_pmf M) (count_space UNIV) f) {\<omega>. g (real_of_rat \<omega>)} = 
         \<P>(\<omega> in distr (measure_pmf M) borel (real_of_rat \<circ> f). g \<omega>)"
  using assms by (simp add:measure_distr) 

lemma represent_ext:
  assumes "x \<in> PiE I M"
  shows "{x} = PiE I (\<lambda>i. {x i})"
  apply (rule order_antisym)
  apply (rule subsetI) using assms apply (simp add:PiE_def Pi_def extensional_def)
  apply (rule subsetI) using assms apply (simp add:PiE_iff) 
  using extensionalityI by auto

lemma sets_finite_pim:
  assumes "finite I"
  assumes "finite M"
  shows "sets (PiM I (\<lambda>_. uniform_count_measure M)) = Pow (I \<rightarrow>\<^sub>E M)"
proof -
  have a:"countable (I \<rightarrow>\<^sub>E M)"
    apply (rule countable_finite)
    using assms finite_PiE by force
  have b:"(\<lambda>s. {s}) ` (I \<rightarrow>\<^sub>E M) \<subseteq> prod_algebra I (\<lambda>_. uniform_count_measure M)"
  proof (rule image_subsetI)
    fix x
    assume "x \<in> I \<rightarrow>\<^sub>E M"
    then show "{x} \<in> prod_algebra I (\<lambda>_. uniform_count_measure M)"
      apply (simp add:represent_ext)
      apply (rule prod_algebraI_finite, simp add:assms(1), simp add:sets_uniform_count_measure) 
      by blast
  qed
  show ?thesis
  apply (simp add:sets_PiM space_uniform_count_measure)
  apply (rule order_antisym)
   apply (rule sigma_algebra.sigma_sets_subset)
    apply (rule algebra.is_sigma_algebra)
     apply (rule algebra_Pow)
    apply (metis assms finite_PiE finite_Pow_iff)
   using prod_algebra_sets_into_space space_uniform_count_measure apply fastforce
  apply (subst sigma_sets_singletons[symmetric], simp add:a)
  apply (rule sigma_sets_mono')
  by (simp add:b)
qed

lemma measurable_pim:
  assumes "finite I"
  assumes "finite M"
  assumes "f \<in> (I \<rightarrow>\<^sub>E M) \<rightarrow> (space N)"
  shows "f \<in> PiM I (\<lambda>_. uniform_count_measure M) \<rightarrow>\<^sub>M N"
  apply (rule measurableI)
   using assms(3) apply (simp add:space_PiM space_uniform_count_measure, blast)
  using assms by (simp add:sets_finite_pim space_PiM space_uniform_count_measure)

lemma pim_pmf_conv:
  assumes "M \<noteq> {}" 
  assumes "finite I"
  assumes "finite M"
  shows "restrict_space (measure_pmf (pmf_of_set (I \<rightarrow>\<^sub>E M))) (I \<rightarrow>\<^sub>E M) = PiM I (\<lambda>_. uniform_count_measure M)"
proof -
  interpret product_sigma_finite "(\<lambda>_. uniform_count_measure M)"
    apply (simp add:product_sigma_finite_def)
    using assms(1) assms(3) 
    by (simp add: prob_space_imp_sigma_finite prob_space_uniform_count_measure)
  have a:"finite (I \<rightarrow>\<^sub>E M)" using assms by (simp add:finite_PiE)
  have b:"I \<rightarrow>\<^sub>E M \<noteq> {}" using assms(1) by (simp add: PiE_eq_empty_iff)

  show ?thesis
  apply (rule measure_eqI_finite[where A="I \<rightarrow>\<^sub>E M"])
     apply (simp add: sets_restrict_space)
     apply (rule order_antisym, rule subsetI, simp, fastforce, rule subsetI, simp, blast)
    using assms apply (simp add:sets_finite_pim)
    using assms apply (simp add:finite_PiE)
    apply (subst (2) represent_ext[where I="I" and M="(\<lambda>_. M)"], simp)
      apply (subst emeasure_PiM, metis assms(2), simp add:sets_uniform_count_measure PiE_iff)
    apply (subst emeasure_restrict_space, simp, simp)
    apply (simp add:emeasure_pmf_of_set a b)
    using assms(3) assms(2) apply (simp add:emeasure_uniform_count_measure PiE_iff card_PiE)
    by (simp add: ennreal_power power_one_over)
qed

lemma pmf_product:
  assumes "M \<noteq> {}"
  assumes "finite I"
  assumes "finite M"
  assumes "f \<in> UNIV \<rightarrow> space N"
  shows "distr (measure_pmf (pmf_of_set (I \<rightarrow>\<^sub>E M))) N f = 
    distr (PiM I (\<lambda>_. uniform_count_measure M)) N f"
proof -

  have a:"finite (I \<rightarrow>\<^sub>E M)" using assms by (simp add:finite_PiE)
  have b:"I \<rightarrow>\<^sub>E M \<noteq> {}" using assms(1) by (simp add: PiE_eq_empty_iff)

  show ?thesis
    apply (simp add:pim_pmf_conv[symmetric] assms)
    apply (rule measure_eqI, simp, simp)
    apply (subst emeasure_distr, simp add:assms, simp)
    apply (subst emeasure_distr) 
      apply (metis assms(4) measurable_pmf_measure1 measurable_restrict_space1)
     apply simp
    using a b  apply (simp add:emeasure_restrict_space emeasure_pmf_of_set)
    by (rule arg_cong[where f="card"], blast)
qed

lemma sorted_mono_map: 
  assumes "sorted xs"
  assumes "mono f"
  shows "sorted (map f xs)"
  using assms apply (simp add:sorted_wrt_map)
  apply (rule sorted_wrt_mono_rel[where P="(\<le>)"])
  by (simp add:mono_def, simp)

lemma map_sort:
  assumes "mono f"
  shows "sort (map f xs) = map f (sort xs)"
  apply (rule properties_for_sort)
   apply simp
  by (rule sorted_mono_map, simp, simp add:assms)

lemma "map (\<lambda>i. f (g i)) xs  = map f (map g xs)"
  by simp

lemma median_rat: 
  assumes "n > 0"
  shows "real_of_rat (median f n) = median (\<lambda>i \<in> {0..<n}. real_of_rat (f i)) n"
proof -
  have a:"map (\<lambda>i\<in>{0..<n}. real_of_rat (f i)) [0..<n] = 
    map real_of_rat (map (\<lambda>i\<in>{0..<n}. f i) [0..<n])"
    by (simp)
  show ?thesis 
    apply (simp add:a median_def del:map_map)
    apply (subst map_sort[where f="real_of_rat"], simp add:mono_def of_rat_less_eq)
    apply (subst nth_map[where f="real_of_rat"]) using assms 
    apply fastforce
    apply simp
     apply (rule arg_cong2[where f="(!)"])
    by (rule arg_cong[where f="sort"], simp, simp)
qed

lemma f2_alg_correct:
  assumes "\<epsilon> < 1 \<and> \<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> foldr (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "\<P>(\<omega> in measure_pmf (sketch \<bind> f2_result). abs (\<omega> - f2_value xs) \<ge> (\<delta> * f2_value xs)) \<le> real_of_rat \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32* ln (real_of_rat \<epsilon>) /9)\<rceil>"
  define p where "p = find_odd_prime_above n"
  define \<Omega>\<^sub>0 where 
    "\<Omega>\<^sub>0 = pmf_of_set ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E  poly_rep p 4)"
  define \<Omega>\<^sub>1 where 
    "\<Omega>\<^sub>1 = Pi\<^sub>M ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. poly_rep_space p 4)"

  define s\<^sub>1_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>1_from = fst"
  define s\<^sub>2_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>2_from = fst \<circ> snd"
  define p_from :: "f2_space \<Rightarrow> nat" where "p_from = fst \<circ> snd \<circ> snd"
  define h_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> nat list)" where "h_from = fst \<circ> snd \<circ> snd \<circ> snd"
  define sketch_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int)" where "sketch_from = snd \<circ> snd \<circ> snd \<circ> snd"


  have fin_poly': "finite (bounded_degree_polynomials (ZFact (int p)) 4)"
    apply (rule fin_poly)
    by (simp add:p_def find_prime_above_is_prime)

  have p_ge_3: "p \<ge> 3"
    using find_prime_above_min by (simp add:p_def)

  have p_prime: "prime p"
    by (simp add:p_def find_prime_above_is_prime)

  have s2_nonzero: "s\<^sub>2 > 0"
    using assms by (simp add:s\<^sub>2_def)

  have s1_nonzero: "s\<^sub>1 > 0"  
    using assms by (simp add:s\<^sub>1_def)

  have "rat_of_nat 1 \<le> rat_of_nat (card (set xs))"
    apply (rule of_nat_mono)
    using assms(4) card_0_eq[where A="set xs"] 
    by (metis List.finite_set One_nat_def Suc_leI neq0_conv set_empty)
  also have "... \<le> f2_value xs"
    apply (simp add:f2_value_def)
    apply (rule sum_mono[where K="set xs" and f="\<lambda>_.(1::rat)", simplified])
    by (metis  count_list_gr_1  of_nat_1 of_nat_power_le_of_nat_cancel_iff one_le_power)
  finally have f2_value_nonzero: "f2_value xs > 0" by (simp)

  have prob_space_1: "prob_space \<Omega>\<^sub>1"
    apply (simp add:\<Omega>\<^sub>1_def, rule prob_space_PiM)
    by (metis prob_space_poly_rep_space)

  have split_f2_space: "\<And>x. x = (s\<^sub>1_from x, s\<^sub>2_from x, p_from x, h_from x, sketch_from x)"
    by (simp add:prod_eq_iff s\<^sub>1_from_def s\<^sub>2_from_def p_from_def h_from_def sketch_from_def)

  have f2_result_conv: "f2_result = (\<lambda>x. f2_result (s\<^sub>1_from x, s\<^sub>2_from x, p_from x, h_from x, sketch_from x))"
    by (simp add:split_f2_space[symmetric] del:f2_result.simps)
  have sketch_eq:
    "sketch = f2_init \<delta> \<epsilon> n \<bind> (\<lambda>state. 
       return_pmf (s\<^sub>1, s\<^sub>2, p, h_from state, \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
       sum_list (map (eval_hash_function p (h_from state i)) xs)))"
  proof (subst sketch_def, induction xs)
    case Nil
    then show ?case apply (simp add:s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
      apply (subst bind_assoc_pmf)
      apply (rule bind_pmf_cong, simp)
      apply (subst bind_return_pmf)
      by (simp add:restrict_def h_from_def)
  next
    case (Cons a xs)
    have a:"f2_update a = (\<lambda>state. 
      return_pmf (
        s\<^sub>1_from state,
        s\<^sub>2_from state, 
        p_from state, 
        h_from state, 
        \<lambda>i \<in> {0..<s\<^sub>1_from state} \<times> {0..<s\<^sub>2_from state}. 
          eval_hash_function (p_from state) (h_from state i) a + sketch_from state i
      ))"
      apply (rule ext)
      by (subst split_f2_space, simp del:eval_hash_function.simps) 
    show ?case using Cons 
      apply (simp add:s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] del:eval_hash_function.simps f2_init.simps)
      apply (subst bind_assoc_pmf)
      apply (rule bind_pmf_cong, simp, simp add:a del:eval_hash_function.simps)
      apply (subst bind_return_pmf)
      apply (simp add:restrict_def s\<^sub>1_from_def s\<^sub>2_from_def p_from_def h_from_def sketch_from_def del:eval_hash_function.simps)
      apply (rule ext)
      by ( simp add:restrict_def h_from_def del:eval_hash_function.simps)
  qed

  define f where "f = (\<lambda>x. median
           (\<lambda>i\<in>{0..<s\<^sub>2}.
               (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (rat_of_int (sum_list (map (eval_hash_function p (x (i\<^sub>1, i))) xs)))\<^sup>2) /
               (((rat_of_nat p)\<^sup>2 - 1) * rat_of_nat s\<^sub>1))
           s\<^sub>2)"

  define f3 where 
    "f3 = (\<lambda>x (i\<^sub>1::nat) (i\<^sub>2::nat). (real_of_int (sum_list (map (eval_hash_function p (x (i\<^sub>1, i\<^sub>2))) xs)))\<^sup>2)"

  have f3_var_1: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> has_variance \<Omega>\<^sub>1 (\<lambda>\<omega>. f3 \<omega> i j / ((real p)\<^sup>2 - 1)) 
    (\<lambda>r. r \<le> 2 * (real_of_rat (f2_value xs))\<^sup>2)"
    apply (simp add:\<Omega>\<^sub>1_def f3_def)
    apply (rule lift_has_variance, simp, simp)
     apply (metis prob_space_poly_rep_space)
    apply (rule var_f2)
      apply (simp add:p_def find_prime_above_is_prime)
    using p_ge_3 apply linarith
    using assms(3) find_prime_above_lower_bound apply (simp add:p_def)
    using order_less_le_trans by blast

  have f3_var_2: " 2 * (real_of_rat (f2_value xs))\<^sup>2 \<le>  (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / (8 * real s\<^sub>1) * (real s\<^sub>1)\<^sup>2"
    using s1_nonzero apply (simp add:of_rat_mult)
    apply (subst mult.commute[where b="real s\<^sub>1"])
    apply (subst divide_divide_eq_left[symmetric])
    apply (subst pos_le_divide_eq, simp)
    apply (simp add:power2_eq_square[where a="real s\<^sub>1"] power_mult_distrib)
    apply (subst mult.commute[where b="real s\<^sub>1"])
    apply (subst mult.assoc[symmetric])
    apply (subst mult_le_cancel_iff1)
    using f2_value_nonzero apply simp
    apply (subst mult.commute[where b="real s\<^sub>1"])
    apply (subst pos_divide_le_eq[symmetric])
    using assms(2) apply simp
    apply (simp add:s\<^sub>1_def)
    by (metis (mono_tags, opaque_lifting) of_nat_numeral of_rat_ceiling of_rat_divide 
        of_rat_of_nat_eq of_rat_power real_nat_ceiling_ge)

  have div_to_mult: "\<And>a b. b \<noteq> (0::real) \<Longrightarrow> a / b = a * (1/b)" by simp

  have f3_var': "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> has_variance \<Omega>\<^sub>1 (\<lambda>\<omega>. f3 \<omega> i j / (((real p)\<^sup>2 - 1) * real s\<^sub>1))
    (\<lambda>r. r \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / (8 * real s\<^sub>1))"
    apply (subst divide_divide_eq_left[symmetric])
    apply (subst div_to_mult[where b="real s\<^sub>1"], simp)
    apply (rule has_variance_scale)
    apply (rule has_variance_imp [where r="(\<lambda>r. r \<le> 2 * (real_of_rat (f2_value xs))\<^sup>2)"])
     apply (simp add:power_one_over)
     apply (subst pos_divide_le_eq)
    using s1_nonzero of_nat_zero_less_power_iff apply blast 
    using f3_var_2 order_trans apply blast
    using f3_var_1 by simp

  define f2 where "f2 = (\<lambda>x. \<lambda>i\<in>{0..<s\<^sub>2}. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. f3 x i\<^sub>1 i) / (((real p)\<^sup>2 - 1) * real s\<^sub>1))"
  
  have f2_var: "\<And>i. i < s\<^sub>2 \<Longrightarrow> has_variance \<Omega>\<^sub>1 (\<lambda>\<omega>. f2 \<omega> i) (\<lambda>r. r \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / 8)"
    (is "\<And>i. _ \<Longrightarrow> ?lhs i")
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    show "?lhs i"
    apply (simp add:f2_def a sum_divide_distrib)
    apply (rule prob_space.has_variance_sum [where r="(\<lambda>_ r. r \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / (8 * real s\<^sub>1))"])
          apply (metis prob_space_1, simp)
    apply (simp add:\<Omega>\<^sub>1_def, rule indep_pim [where f="\<lambda>j. {(j,i)}"])
              apply (metis prob_space_poly_rep_space)
      apply (simp add:poly_rep_space_def)
             apply (rule measurable_pim, simp, simp add:fin_poly_rep, simp, simp add:f3_def)
           apply (simp add:disjoint_family_on_def, simp add:s1_nonzero, simp add:a, simp add:s1_nonzero s2_nonzero)
      using f3_var' a apply simp
      using s1_nonzero sum_mono[where g="\<lambda>_. (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / (8 * real s\<^sub>1)" and K="{0..<s\<^sub>1}"]
      by simp
  qed

  have f2_exp_1: "real_of_rat (f2_value xs) = (\<Sum> i\<in>{0..<s\<^sub>1}. real_of_rat (f2_value xs)) / real s\<^sub>1"
    by (simp add:s1_nonzero)

  have f2_exp: "\<And>i. i < s\<^sub>2 \<Longrightarrow> has_bochner_integral \<Omega>\<^sub>1 (\<lambda>\<omega>. f2 \<omega> i) (real_of_rat (f2_value xs))"
    apply (simp add:f2_def)
    apply (subst divide_divide_eq_left[symmetric])
    apply (subst f2_exp_1)
    apply (rule has_bochner_integral_divide_zero)
    apply (subst sum_divide_distrib)
    apply (rule has_bochner_integral_sum)
    apply (simp add:f3_def)
    apply (simp add:\<Omega>\<^sub>1_def)
    apply (rule lift_has_bochner_integral, simp, simp, simp add:prob_space_poly_rep_space)
    apply (rule exp_f2)
      apply (simp add:p_def find_prime_above_is_prime)
    using p_ge_3 apply linarith
    using assms(3) find_prime_above_lower_bound apply (simp add:p_def)
    using order_less_le_trans by blast

  define f' where "f' = (\<lambda>x. median (f2 x) s\<^sub>2)"
  have real_f: "real_of_rat \<circ> f = f'"
    apply (rule ext)
    using s2_nonzero apply (simp add:f'_def f2_def f3_def f_def median_rat cong:restrict_cong)
    by (simp add:of_rat_divide of_rat_sum of_rat_power of_rat_mult of_rat_diff)

  have "sketch \<bind> f2_result = map_pmf f (pmf_of_set ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E poly_rep p 4))"
    apply (simp add:sketch_eq s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] del:eval_hash_function.simps)
      apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (subst f2_result_conv, simp)
      apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (simp add:s\<^sub>2_from_def s\<^sub>1_from_def p_from_def h_from_def sketch_from_def cong:restrict_cong)
    by (simp add:map_pmf_def[symmetric] f_def)
  hence distr: "measure_pmf (sketch \<bind> f2_result) = distr (measure_pmf \<Omega>\<^sub>0) (count_space UNIV) f"
    by (simp add:map_pmf_rep_eq \<Omega>\<^sub>0_def)


  define g where "g = (\<lambda>\<omega>. real_of_rat (\<delta> * f2_value xs) \<le> \<bar>\<omega> - real_of_rat (f2_value xs)\<bar>)"
  have e: "{\<omega>. \<delta> * f2_value xs \<le> \<bar>\<omega> - f2_value xs\<bar>} = {\<omega>. (g \<circ> real_of_rat) \<omega>}"
    apply (simp add:g_def)
    apply (rule order_antisym, rule subsetI, simp) 
    apply (metis abs_of_rat of_rat_diff of_rat_less_eq)
    apply (rule subsetI, simp)
    by (metis abs_of_rat of_rat_diff of_rat_less_eq)

  have median_bound_2: "prob_space.indep_vars \<Omega>\<^sub>1 (\<lambda>_. borel) (\<lambda>i \<omega>. f2 \<omega> i) {0..<s\<^sub>2}"
    apply (simp add:f2_def \<Omega>\<^sub>1_def)
    apply (rule indep_pim[where f="\<lambda>j. {0..<s\<^sub>1} \<times> {j}"] ) (* X i1 i x = x (i1,i)  *)
          apply (metis  prob_space_poly_rep_space, simp add:poly_rep_space_def)
         apply (rule measurable_pim, simp, simp add:fin_poly_rep, simp, simp add:f3_def)
       apply (simp add:disjoint_family_on_def, fastforce, simp add:s2_nonzero)
     apply (rule subsetI, force)
    by (simp add:s1_nonzero s2_nonzero)

  have median_bound_3: " - (32 * ln (real_of_rat \<epsilon>) / 9) \<le> real s\<^sub>2"
    apply (simp add:s\<^sub>2_def)
    using of_nat_ceiling by blast

  have median_bound_4: "\<And>i. i < s\<^sub>2 \<Longrightarrow>
           \<P>(\<omega> in \<Omega>\<^sub>1. real_of_rat (\<delta> * f2_value xs) \<le> \<bar>f2 \<omega> i - real_of_rat (f2_value xs)\<bar>) \<le> 1/8"
    (is "\<And>i. _ \<Longrightarrow> ?lhs i \<le> _")
  proof -
    fix i
    assume a: "i < s\<^sub>2"
    define var where  "var = prob_space.variance \<Omega>\<^sub>1 (\<lambda>\<omega>. f2 \<omega> i)"
    have "real_of_rat (f2_value xs) = prob_space.expectation \<Omega>\<^sub>1 (\<lambda>\<omega>. f2 \<omega> i)"
      using f2_exp a has_bochner_integral_iff by metis
    moreover have "0 < real_of_rat (\<delta> * f2_value xs)"
      using assms(2) f2_value_nonzero by simp
    moreover have "integrable \<Omega>\<^sub>1 (\<lambda>\<omega>. f2 \<omega> i^2)"
      using f2_var has_variance_def a by metis 
    moreover have "(\<lambda>\<omega>. f2 \<omega> i) \<in> borel_measurable \<Omega>\<^sub>1"
      by (simp add:\<Omega>\<^sub>1_def poly_rep_space_def, rule measurable_pim, simp, simp add:fin_poly_rep, simp)
    ultimately have "?lhs i \<le> var / (real_of_rat (\<delta> * f2_value xs))\<^sup>2"
      using prob_space.Chebyshev_inequality[where M="\<Omega>\<^sub>1" and a="real_of_rat (\<delta> * f2_value xs)"
          and f="\<lambda>\<omega>. f2 \<omega> i"] assms(2) prob_space_1 f2_value_nonzero
      by (simp add:var_def)
    also  have "... \<le> 1/8" (is ?ths)
      apply (subst pos_divide_le_eq )
      using f2_value_nonzero assms(2) apply simp
      apply (simp add:var_def)
      using f2_var a has_variance_def by fastforce      
    finally show "?lhs i \<le> 1/8"
      by blast
  qed
  show ?thesis
    apply (simp add:distr e)
    apply (subst pmf_to_borel)
      apply (simp add:g_def)
     apply (simp add:f_def)
    apply (simp add:real_f f'_def \<Omega>\<^sub>0_def)
    apply (subst pmf_product, simp add:poly_rep_def, blast, simp, simp add:fin_poly_rep, simp)
       apply (subst measure_distr)
         apply (rule measurable_pim, simp add:fin_poly_rep, simp add:fin_poly_rep)
    apply simp
    apply (simp add:g_def)
    using prob_space.median_bound[where M="\<Omega>\<^sub>1" and 
          \<delta>="real_of_rat (\<delta> * f2_value xs)" and \<mu>="real_of_rat (f2_value xs)" and
          \<epsilon>="real_of_rat \<epsilon>" and n ="s\<^sub>2" and X="(\<lambda>i \<omega>. f2 \<omega> i)"]
    assms(1) prob_space_1 median_bound_2 median_bound_3 median_bound_4 \<Omega>\<^sub>1_def[symmetric] poly_rep_space_def[symmetric]
    by (simp add:measure_inters g_def)
qed


lemma f2_alg_space:
  assumes "\<epsilon> < 1 \<and> \<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  defines "state \<equiv> foldr (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in state. length (encode state) \<le> 12"
  sorry

end