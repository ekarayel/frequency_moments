section \<open>Frequency Moment 2\<close>

theory F2_Algorithm
  imports Main "HOL-Probability.Giry_Monad" "HOL-Probability.Probability_Mass_Function" UniversalHashFamily Field 
    Median Probability_Ext "HOL-Library.Multiset" Partitions Primes_Ext "HOL-Library.Extended_Nat"
    "HOL-Library.Rewrite" "Encoding" List_Ext Prod_PMF
begin

definition f2_value where
  "f2_value xs = (\<Sum> x \<in> set xs. (rat_of_nat (count_list xs x)^2))"

fun eval_hash_function where
  "eval_hash_function p h k = (
    if hash_function (ZFact (int p)) (zfact_embed p k) h \<in> zfact_embed p ` {k. 2*k < p} then
      int p - 1
    else
      - int p - 1
  )"

type_synonym f2_space = "nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> int set list) \<times> (nat \<times> nat \<Rightarrow> int)"

fun zfact\<^sub>S where "zfact\<^sub>S p x = (
    if x \<in> zfact_embed p ` {0..<p} then
      N\<^sub>S (the_inv_into {0..<p} (zfact_embed p) x)
    else
     None
  )"

lemma zfact_encoding : 
  "is_encoding (zfact\<^sub>S p)"
proof -
  have "p > 0 \<Longrightarrow> is_encoding (\<lambda>x. zfact\<^sub>S p x)"
    apply simp 
    apply (rule encoding_compose[where f="N\<^sub>S"])
     apply (metis nat_encoding)
    by (metis inj_on_the_inv_into zfact_embed_inj)
  moreover have "is_encoding (zfact\<^sub>S 0)"
    by (simp add:is_encoding_def)
  ultimately show ?thesis by blast
qed


definition encode_state where
  "encode_state = 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>1. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>2. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>p. 
    encode_prod_fun s\<^sub>1 s\<^sub>2 (list\<^sub>S (zfact\<^sub>S p)) \<times>\<^sub>S
    encode_prod_fun s\<^sub>1 s\<^sub>2 I\<^sub>S)))"

lemma "is_encoding encode_state"
  apply (simp add:encode_state_def)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis encode_prod_fun list_encoding zfact_encoding)
  by (metis encode_prod_fun int_encoding)


fun f2_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f2_space pmf" where
  "f2_init \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-32/9 * ln (real_of_rat \<epsilon>)\<rceil>;
      let p = find_odd_prime_above n;
      h \<leftarrow> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4));
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

  show "?A"
    apply (simp add:has_variance_def)
    apply (rule conjI) apply (metis int_var_f2)
    apply (rule conjI) apply (metis int_exp_f2)
    apply (rule conjI, simp add: prob_space_axioms)
    apply (subst variance_eq, metis int_exp_f2, simp add: int_var_f2)
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
  shows "finite (bounded_degree_polynomials (ZFact (int p)) 4)"
  apply (rule finite_poly_count)
   apply (rule zfact_prime_is_field)
   apply (simp add:assms)
  apply (rule zfact_finite)
  using assms  prime_gt_0_nat by blast

lemma eval_exp':
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2" 
  shows
    "has_bochner_integral (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) (\<lambda>\<omega>. (real_of_int (eval_hash_function p \<omega> k) / sqrt (real p^2-1)) ^m) (
    ((real p-1)^m* (real p+1) + (-real p - 1)^m *(real p - 1))/ ((2*real p) * sqrt(real p^2-1)^m))"
proof -
  have g:"p > 0" using assms(1) prime_gt_0_nat by auto

  have g1:"zfact_embed p k \<in> carrier (ZFact p)" using zfact_embed_ran[OF g] assms
    by auto
  have "odd p" using assms prime_odd_nat by blast
  then obtain t where t_def: "p=2*t+1" 
    using oddE by blast


  have "card {k. 2 * k < Suc(2 * t)} = card {k. k < t+1}" 
    by (rule arg_cong[where f="card"], auto)
  hence card_B: "card {k. 2 * k < p} = (p+1)/2"
    by (simp add:t_def)


  have d: "\<And> A P. A \<inter> {\<omega>. P \<omega>} = {\<omega> \<in> A. P \<omega>}"
    by blast

  have e: "\<And> f A P Q. A \<inter> -{\<omega>. f \<omega> \<in> Q} = {\<omega> \<in> A. f \<omega> \<in> - Q}"
    by blast

  have f: "\<And>A B. -A \<inter> B = B - A"
    by blast

  define F where "F = ZFact (int p)"
  define G where "G = bounded_degree_polynomials F 4"

  define H where "H = {x. hash_function (ZFact (int p)) (zfact_embed p k) x \<in> zfact_embed p ` {k. 2 * k < p}}"
  have card_G: "card G = p ^ 4"
    apply (simp add:G_def F_def)
    apply (subst poly_count, metis zfact_prime_is_field assms(1), metis zfact_finite g)
    by (subst zfact_card [OF g], simp)

  have card_G_int_H: "card (G \<inter> H) = ((real p+1) / 2) * real p^3"
    apply (simp add:G_def H_def F_def hash_function_def)
    apply (subst d)
    apply (subst poly_card_set', metis zfact_prime_is_field assms(1), metis zfact_finite g)
      apply (metis g1, simp)
    apply (subst Int_absorb2)
     apply (subst zfact_embed_ran[OF g, symmetric])
     apply (rule image_mono, rule subsetI, simp)
    apply (subst card_image)
     apply (rule inj_on_subset[OF zfact_embed_inj[OF g]], rule subsetI, simp)
    apply (simp add:  zfact_card[OF g])
    by (subst card_B, simp)

  have card_G_int_not_H: "card (G \<inter> -H) = ((real p-1) / 2) * real p^3"
    apply (simp add:G_def H_def F_def hash_function_def)
    apply (subst e)
    apply (subst poly_card_set', metis zfact_prime_is_field assms(1), metis zfact_finite g)
      apply (metis g1, simp)
    apply (subst f)
    apply (subst card_Diff_subset, rule finite_imageI) 
      apply (rule finite_subset[where B="{k. k < p}"], rule subsetI, simp, simp)
     apply (subst zfact_embed_ran[OF g, symmetric])
    apply (rule image_mono, rule subsetI, simp)
    apply (subst card_image)
     apply (rule inj_on_subset[OF zfact_embed_inj[OF g]], rule subsetI, simp)
    apply (simp add:  zfact_card[OF g])
    apply (subst of_nat_diff)
    apply (rule card_mono[where B="{0..<p}", simplified], rule subsetI, simp)
    apply (subst card_B)
    by (simp add:add_divide_distrib)

  have s1: " (\<Sum>a\<in>G. real_of_int (eval_hash_function p a k) ^ m / real (card G)) =
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
    apply (subst card_G)
    apply (subst sum_divide_distrib[symmetric])
    apply (simp)
    apply (subst if_distrib[where f="\<lambda>x. real_of_int x ^ m"])
    apply (subst sum.If_cases, simp add:G_def F_def, metis fin_poly assms(1))
    apply (simp add:H_def[symmetric] card_G_int_H card_G_int_not_H)
    apply (subst frac_eq_eq, simp add:g, simp add: g)
    apply (subst distrib_right[where c="real p ^ 4"])
    apply (subst distrib_right[where c="2* real p"])
    apply (rule arg_cong2[where f="(+)"])
    by (simp add: power3_eq_cube power4_eq_xxxx)+

  show ?thesis
    apply (subst power_divide)
    apply (subst divide_divide_eq_left[symmetric])
    apply (rule has_bochner_integral_divide_zero)
    apply (subst has_bochner_integral_iff)
    apply (rule conjI)
    apply (rule integrable_measure_pmf_finite, subst set_pmf_of_set, rule ex_poly, metis fin_poly assms(1))
    apply (subst integral_measure_pmf_real[where A="bounded_degree_polynomials (ZFact (int p)) 4"], metis fin_poly assms(1))
     apply (subst (asm) set_pmf_of_set, rule ex_poly, metis fin_poly assms(1), simp)
    apply (subst pmf_of_set, rule ex_poly, metis fin_poly assms(1))
    apply (simp add:indicator_def G_def[symmetric] F_def[symmetric] del:eval_hash_function.simps)
    by (metis s1)
qed


lemma eval_exp_1':
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "has_bochner_integral (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) (\<lambda>\<omega>. real_of_int (eval_hash_function p \<omega> k)/ sqrt (real p^2-1)) 0"
proof -
  have a:"((real p - 1) ^ 1 * (real p + 1) + (- real p - 1) ^ 1 * (real p - 1)) = 0"
    by (simp add:algebra_simps)
  show ?thesis 
    using assms eval_exp'[where m="1" and p="p"] a by (simp del:eval_hash_function.simps)
qed


lemma eval_exp_2':
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows "has_bochner_integral (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) (\<lambda>\<omega>. (real_of_int (eval_hash_function p \<omega> k)/ sqrt (real p^2-1))^2) 1"
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
    apply (rule eval_exp'[where m="2" and p="p"])
    using assms by auto
qed


lemma eval_exp_4':
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2"
  shows 
    "prob_space.expectation (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4))
      (\<lambda>\<omega>. (real_of_int (eval_hash_function p \<omega> k) / sqrt (real p^2-1))^4) \<le> 3"
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

  then show ?thesis using eval_exp'[where m="4" and p="p"] has_bochner_integral_integral_eq
    by (metis assms)
qed



lemma eval_4_indep':
  assumes "prime p"
  assumes "p > 2"
  shows "prob_space.k_wise_indep_vars (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) 4 (\<lambda>_. borel)
    (\<lambda>k \<omega>. real_of_int (eval_hash_function p \<omega> k)/ sqrt (real p^2-1)) {0..<p}"
proof -
  have a1:"p > 0" using assms(2) by auto
  have a:"prob_space (poly_hash_family (ZFact p) 4)" 
    apply (rule prob_space_poly_family)
    using assms zfact_prime_is_field apply simp
    using a1 zfact_finite by auto
  have a2:"\<And>J. J\<subseteq>carrier (ZFact (int p)) \<Longrightarrow> finite J \<Longrightarrow> card J \<le> 4  \<Longrightarrow>
    prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) 
    (\<lambda>_. pmf_of_set (carrier (ZFact (int p)))) (hash_function (ZFact (int p))) 
    J"
    apply (rule bounded_poly_indep_pmf)
    apply (metis zfact_prime_is_field assms(1))
        apply (rule zfact_finite) using assms(2) apply linarith
    by simp+

  have c1:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> zfact_embed p ` J \<subseteq> carrier (ZFact (int p))"
    using zfact_embed_ran[OF a1] by fastforce
  have c2:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> card J \<le> 4 \<Longrightarrow> finite J \<Longrightarrow> card (zfact_embed p ` J) \<le> 4"
    by (meson card_image_le le_trans)
  have c3:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> finite J \<Longrightarrow> finite (zfact_embed p ` J)"
    by simp
  have b_aux:"\<And>J. J\<subseteq>{0..<p} \<Longrightarrow> finite J \<Longrightarrow> card J \<le> 4 \<Longrightarrow> 
    prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) 
    ((\<lambda>_. measure_pmf (pmf_of_set (carrier (ZFact (int p))))) \<circ> zfact_embed p) (\<lambda>k \<omega>. hash_function (ZFact (int p)) (zfact_embed p k) \<omega>) 
    J"
    apply (subst prob_space.indep_vars_reindex [where f="zfact_embed p" and X'="hash_function (ZFact (int p))"])
      apply (metis prob_space_measure_pmf)
      apply (metis zfact_embed_inj a1 inj_on_subset)
     using a2 c1 c2 c3 apply presburger
    by simp
  have b:"\<And>J. J\<subseteq>{0..<p} \<Longrightarrow> card J \<le> 4 \<Longrightarrow> finite J \<Longrightarrow> 
    prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) (\<lambda>_. borel) (\<lambda>k \<omega>. real_of_int (eval_hash_function p \<omega> k)/ sqrt (real p^2-1)) J"
    apply simp
    apply (rule prob_space.indep_vars_compose2 [where X="(\<lambda>k \<omega>. hash_function (ZFact (int p)) (zfact_embed p k) \<omega>)"
            and M'=" (\<lambda>_. pmf_of_set (carrier (ZFact (int p))))"])
      apply (metis prob_space_measure_pmf)
     using b_aux apply (simp)
    by measurable
  
  show ?thesis
    by (simp add: prob_space_measure_pmf b prob_space.k_wise_indep_vars_def del:eval_hash_function.simps)
qed


lemma 
  assumes "prime p"
  assumes "p > 2"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < p"
  defines "M \<equiv> measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4))"
  defines "f2_sketch \<equiv> (\<lambda>a. (real_of_int (sum_list (map (eval_hash_function p a) xs)))\<^sup>2 / ((real p)\<^sup>2 - 1))"
  shows var_f2':"has_variance M (\<lambda>\<omega>. f2_sketch \<omega>) (\<lambda>r. r \<le> 2*(real_of_rat (f2_value xs)^2))" (is "?A")
  and exp_f2':"has_bochner_integral M (\<lambda>\<omega>. f2_sketch \<omega>) (real_of_rat (f2_value xs))" (is "?B")
proof -
  have a:"prob_space M" 
    by (simp add:M_def, rule prob_space_measure_pmf)

  have f2_sketch_elim:
  "f2_sketch = (\<lambda>\<omega>. (\<Sum> x \<in> set xs. real (count_list xs x) * (eval_hash_function p \<omega> x/ sqrt (real p^2-1)))^2 )"
    apply (simp add:sum_list_eval f2_sketch_def  sum_divide_distrib[symmetric] power_divide del:eval_hash_function.simps)
    apply (subst real_sqrt_pow2)
    using assms by simp+
  have b:"prob_space.k_wise_indep_vars M 4 (\<lambda>_. borel) (\<lambda>x \<omega>. real_of_int (eval_hash_function p \<omega> x) / sqrt ((real p)\<^sup>2 - 1))
          (set xs)"
    apply (rule prob_space.k_wise_subset [where I="{0..<p}"])
    apply (simp add:a)
    using eval_4_indep' assms apply (simp add:poly_hash_family_def del:eval_hash_function.simps)
    apply (rule subsetI)
    using assms(3) by simp

  show ?A
    apply (simp only:f2_sketch_elim)
    apply (rule prob_space.var_f2[where xs="xs" and M="M" and h="\<lambda>x \<omega>. real_of_int (eval_hash_function p \<omega> x)/sqrt (real p^2-1)"])
    apply (simp add:a)
    apply (metis b)
    using assms eval_exp' [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_1' [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_2' [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_4' [where p="p"] by (simp add:has_bochner_integral_iff poly_hash_family_def)

  show ?B
    apply (simp only:f2_sketch_elim)
    apply (rule prob_space.exp_f2[where xs="xs" and M="M" and h="\<lambda>x \<omega>. real_of_int (eval_hash_function p \<omega> x)/sqrt (real p^2-1)"])
    apply (simp add:a)
    apply (metis b)
    using assms eval_exp' [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_1' [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_2' [where p="p"] apply (simp add:has_bochner_integral_iff poly_hash_family_def)
    using assms eval_exp_4' [where p="p"] by (simp add:has_bochner_integral_iff poly_hash_family_def)
qed


lemma f2_alg_sketch:
  fixes n :: nat
  fixes xs :: "nat list"
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  defines "s\<^sub>1 \<equiv> nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  defines "s\<^sub>2 \<equiv> nat \<lceil>-(32* ln (real_of_rat \<epsilon>) /9)\<rceil>"
  defines "p \<equiv> find_odd_prime_above n"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  defines "\<Omega> \<equiv> prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4))" 
  shows "sketch = \<Omega> \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. sum_list (map (eval_hash_function p (h i)) xs)))"
proof -
  define ys where "ys = rev xs"
  have b:"sketch = foldr (\<lambda>x state. state \<bind> f2_update x) ys (f2_init \<delta> \<epsilon> n)"
    by (simp add: foldr_conv_fold ys_def sketch_def)
  also have "... = \<Omega> \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. sum_list (map (eval_hash_function p (h i)) ys)))"
  proof (induction ys)
    case Nil
    then show ?case 
      by (simp add:s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] \<Omega>_def restrict_def) 
  next
    case (Cons a xs)
    have a:"f2_update a = (\<lambda>x. f2_update a (fst x, fst (snd x), fst (snd (snd x)), fst (snd (snd (snd x))), 
        snd (snd (snd (snd x)))))" by simp
    show ?case
      using Cons apply (simp del:eval_hash_function.simps f2_init.simps)
      apply (subst a)
      apply (subst bind_assoc_pmf)
      apply (subst bind_return_pmf)
      by (simp add:restrict_def del:eval_hash_function.simps f2_init.simps cong:restrict_cong)
  qed
  also have "... = \<Omega> \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. sum_list (map (eval_hash_function p (h i)) xs)))"
    by (simp add: ys_def rev_map[symmetric])
  finally show ?thesis by auto
qed

lemma f2_alg_correct:
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "\<P>(\<omega> in measure_pmf (sketch \<bind> f2_result). abs (\<omega> - f2_value xs) \<ge> (\<delta> * f2_value xs)) \<le> real_of_rat \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32* ln (real_of_rat \<epsilon>) /9)\<rceil>"
  define p where "p = find_odd_prime_above n"
  define \<Omega>\<^sub>0 where 
    "\<Omega>\<^sub>0 = prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set ( bounded_degree_polynomials (ZFact (int p)) 4))"
  define \<Omega>\<^sub>1 where 
    "\<Omega>\<^sub>1 = Pi\<^sub>M ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. uniform_count_measure (bounded_degree_polynomials (ZFact (int p)) 4))"

  define s\<^sub>1_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>1_from = fst"
  define s\<^sub>2_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>2_from = fst \<circ> snd"
  define p_from :: "f2_space \<Rightarrow> nat" where "p_from = fst \<circ> snd \<circ> snd"
  define h_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int set list)" where "h_from = fst \<circ> snd \<circ> snd \<circ> snd"
  define sketch_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int)" where "sketch_from = snd \<circ> snd \<circ> snd \<circ> snd"


  have fin_poly': "finite (bounded_degree_polynomials (ZFact (int p)) 4)"
    apply (rule fin_poly)
    by (simp add:p_def find_prime_above_is_prime)

  have p_ge_3: "p \<ge> 3"
    using find_prime_above_min by (simp add:p_def)

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
    by (metis count_list_gr_1 of_nat_1 of_nat_power_le_of_nat_cancel_iff one_le_power)
  finally have f2_value_nonzero: "f2_value xs > 0" by (simp)

  have split_f2_space: "\<And>x. x = (s\<^sub>1_from x, s\<^sub>2_from x, p_from x, h_from x, sketch_from x)"
    by (simp add:prod_eq_iff s\<^sub>1_from_def s\<^sub>2_from_def p_from_def h_from_def sketch_from_def)

  have f2_result_conv: "f2_result = (\<lambda>x. f2_result (s\<^sub>1_from x, s\<^sub>2_from x, p_from x, h_from x, sketch_from x))"
    by (simp add:split_f2_space[symmetric] del:f2_result.simps)

  define f where "f = (\<lambda>x. median
           (\<lambda>i\<in>{0..<s\<^sub>2}.
               (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (rat_of_int (sum_list (map (eval_hash_function p (x (i\<^sub>1, i))) xs)))\<^sup>2) /
               (((rat_of_nat p)\<^sup>2 - 1) * rat_of_nat s\<^sub>1))
           s\<^sub>2)"

  define f3 where 
    "f3 = (\<lambda>x (i\<^sub>1::nat) (i\<^sub>2::nat). (real_of_int (sum_list (map (eval_hash_function p (x (i\<^sub>1, i\<^sub>2))) xs)))\<^sup>2)"

  have f3_var_1: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> has_variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f3 \<omega> i j / ((real p)\<^sup>2 - 1)) 
    (\<lambda>r. r \<le> 2 * (real_of_rat (f2_value xs))\<^sup>2)"
    apply (simp add:\<Omega>\<^sub>0_def f3_def)
    apply (rule has_variance_prod_pmf_sliceI, simp, simp)
    apply (rule var_f2')
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

  have f3_var': "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> has_variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f3 \<omega> i j / (((real p)\<^sup>2 - 1) * real s\<^sub>1))
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
  
  have f2_var: "\<And>i. i < s\<^sub>2 \<Longrightarrow> has_variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) (\<lambda>r. r \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / 8)"
    (is "\<And>i. _ \<Longrightarrow> ?lhs i")
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    show "?lhs i"
    apply (simp add:f2_def a sum_divide_distrib)
    apply (rule prob_space.has_variance_sum [where r="(\<lambda>_ r. r \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / (8 * real s\<^sub>1))"])
          apply (metis prob_space_measure_pmf, simp)
        apply (simp add:\<Omega>\<^sub>0_def, rule indep_vars_restrict_intro [where f="\<lambda>j. {(j,i)}"])
      apply (simp add:f3_def)
            apply (simp add:disjoint_family_on_def, simp add:s1_nonzero, simp add:a, simp add:s1_nonzero s2_nonzero)
      apply (simp)
      using f3_var' a apply simp
      using s1_nonzero sum_mono[where g="\<lambda>_. (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / (8 * real s\<^sub>1)" and K="{0..<s\<^sub>1}"]
      by simp
  qed

  have f2_exp_1: "real_of_rat (f2_value xs) = (\<Sum> i\<in>{0..<s\<^sub>1}. real_of_rat (f2_value xs)) / real s\<^sub>1"
    by (simp add:s1_nonzero)

  have f2_exp': "\<And>i. i < s\<^sub>2 \<Longrightarrow> has_bochner_integral \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) (real_of_rat (f2_value xs))"
    apply (simp add:f2_def)
    apply (subst divide_divide_eq_left[symmetric])
    apply (subst f2_exp_1)
    apply (rule has_bochner_integral_divide_zero)
    apply (subst sum_divide_distrib)
    apply (rule has_bochner_integral_sum)
    apply (simp add:f3_def)
    apply (simp add:\<Omega>\<^sub>0_def)
    apply (rule has_bochner_integral_prod_pmf_sliceI, simp, simp)
    apply (rule exp_f2')
      apply (simp add:p_def find_prime_above_is_prime)
    using p_ge_3 apply linarith
    using assms(3) find_prime_above_lower_bound apply (simp add:p_def)
    using order_less_le_trans by blast

  define f' where "f' = (\<lambda>x. median (f2 x) s\<^sub>2)"
  have real_f: "\<And>x. real_of_rat (f x) = f' x"
    using s2_nonzero apply (simp add:f'_def f2_def f3_def f_def median_rat median_restrict cong:restrict_cong)
    by (simp add:of_rat_divide of_rat_sum of_rat_power of_rat_mult of_rat_diff)

  have distr': "sketch \<bind> f2_result = map_pmf f (prod_pmf  ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)))"
      using f2_alg_sketch[OF assms(1) assms(2), where xs="xs" and n="n"]
    apply (simp add:sketch_def Let_def s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
      apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (subst f2_result_conv, simp)
    apply (simp add:s\<^sub>2_from_def s\<^sub>1_from_def p_from_def h_from_def sketch_from_def cong:restrict_cong)
    by (simp add:map_pmf_def[symmetric] f_def)

  define g where "g = (\<lambda>\<omega>. real_of_rat (\<delta> * f2_value xs) \<le> \<bar>\<omega> - real_of_rat (f2_value xs)\<bar>)"
  have e: "{\<omega>. \<delta> * f2_value xs \<le> \<bar>\<omega> - f2_value xs\<bar>} = {\<omega>. (g \<circ> real_of_rat) \<omega>}"
    apply (simp add:g_def)
    apply (rule order_antisym, rule subsetI, simp) 
    apply (metis abs_of_rat of_rat_diff of_rat_less_eq)
    apply (rule subsetI, simp)
    by (metis abs_of_rat of_rat_diff of_rat_less_eq)

  have median_bound_2': "prob_space.indep_vars \<Omega>\<^sub>0 (\<lambda>_. borel) (\<lambda>i \<omega>. f2 \<omega> i) {0..<s\<^sub>2}"
    apply (subst \<Omega>\<^sub>0_def)
    apply (rule indep_vars_restrict_intro [where f="\<lambda>j. {0..<s\<^sub>1} \<times> {j}"])
         apply (simp add:f2_def f3_def)
        apply (simp add:disjoint_family_on_def, fastforce)
    apply (simp add:s2_nonzero)
      apply (rule subsetI, simp add:mem_Times_iff)
     apply (simp)
    by (simp)
  have median_bound_3: " - (32 * ln (real_of_rat \<epsilon>) / 9) \<le> real s\<^sub>2"
    apply (simp add:s\<^sub>2_def)
    using of_nat_ceiling by blast

  have median_bound_4: "\<And>i. i < s\<^sub>2 \<Longrightarrow>
           \<P>(\<omega> in \<Omega>\<^sub>0. real_of_rat (\<delta> * f2_value xs) \<le> \<bar>f2 \<omega> i - real_of_rat (f2_value xs)\<bar>) \<le> 1/8"
    (is "\<And>i. _ \<Longrightarrow> ?lhs i \<le> _")
  proof -
    fix i
    assume a: "i < s\<^sub>2"
    define var where  "var = prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i)"
    have "real_of_rat (f2_value xs) = prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i)"
      using f2_exp' a has_bochner_integral_iff by metis
    moreover have "0 < real_of_rat (\<delta> * f2_value xs)"
      using assms(2) f2_value_nonzero by simp
    moreover have "integrable \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i^2)"
      using f2_var has_variance_def a by metis 
    moreover have "(\<lambda>\<omega>. f2 \<omega> i) \<in> borel_measurable \<Omega>\<^sub>0"
      by (simp add:\<Omega>\<^sub>0_def)
    ultimately have "?lhs i \<le> var / (real_of_rat (\<delta> * f2_value xs))\<^sup>2"
      using prob_space.Chebyshev_inequality[where M="\<Omega>\<^sub>0" and a="real_of_rat (\<delta> * f2_value xs)"
          and f="\<lambda>\<omega>. f2 \<omega> i",simplified] assms(2) prob_space_measure_pmf[where p="\<Omega>\<^sub>0"] f2_value_nonzero
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
    apply (simp add: distr' e real_f f'_def g_def \<Omega>\<^sub>0_def[symmetric])
    apply (rule prob_space.median_bound[where M="\<Omega>\<^sub>0" and 
          \<delta>="real_of_rat (\<delta> * f2_value xs)" and \<mu>="real_of_rat (f2_value xs)" and
          \<epsilon>="real_of_rat \<epsilon>" and n ="s\<^sub>2" and X="(\<lambda>i \<omega>. f2 \<omega> i)", simplified])
         apply (metis prob_space_measure_pmf)
    apply (metis assms(1))
       apply (metis assms(1))
    apply (metis median_bound_2')
    apply (metis median_bound_3)
    using  median_bound_4 by simp
qed


lemma f2_space:
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0 \<and> \<delta> < 1"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in sketch. bit_count (encode_state \<omega>) \<le> 3128 *
    (1 - ln (real_of_rat \<epsilon>)) / (real_of_rat \<delta>)\<^sup>2 * (ln (real n+1) + ln (real (length xs) + 1) + 1)"
    (is "AE \<omega> in sketch. _ \<le> ?rhs")
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32* ln (real_of_rat \<epsilon>) /9)\<rceil>"
  define p where "p = find_odd_prime_above n"
  define s\<^sub>1_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>1_from = fst"
  define s\<^sub>2_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>2_from = fst \<circ> snd"
  define p_from :: "f2_space \<Rightarrow> nat" where "p_from = fst \<circ> snd \<circ> snd"
  define h_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int set list)" where "h_from = fst \<circ> snd \<circ> snd \<circ> snd"
  define sketch_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int)" where "sketch_from = snd \<circ> snd \<circ> snd \<circ> snd"

  define R where "R = {(n::int). abs n \<le> length xs * (int p+1)}"
  define M where "M = {\<omega>. s\<^sub>1_from \<omega> = s\<^sub>1 \<and> s\<^sub>2_from \<omega> = s\<^sub>2 \<and> p_from \<omega> = p \<and>
    h_from \<omega> \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact p) 4 \<and>
    sketch_from \<omega> \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E R}"

  have b3: "abs (int p - 1) \<le> int p + 1"
    using p_def find_prime_above_min by linarith
  have b2:"\<And>y. y \<in> bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow>
    sum_list (map (eval_hash_function p y) xs) \<in> R"
  proof -
    fix y
    assume "y \<in> bounded_degree_polynomials (ZFact (int p)) 4"
    have "abs (sum_list (map (eval_hash_function p y) xs)) \<le> sum_list (map (abs \<circ> eval_hash_function p y) xs)"
      by (subst map_map[symmetric], rule sum_list_abs)
    also have "... \<le> sum_list (map (\<lambda>_. int p + 1) xs)"
      apply (rule sum_list_mono)
      by (simp add:comp_def b3)
    finally have "abs (sum_list (map (eval_hash_function p y) xs)) \<le> length xs * (int p +1)"
      by (simp add:sum_list_triv)
    thus "sum_list (map (eval_hash_function p y) xs) \<in> R" by (simp add:R_def)
  qed
  have b1:"\<And>y. y \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow>
         (\<lambda>i. sum_list (map (eval_hash_function p (y i)) xs)) \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow> R"
    using b2 by blast

  define log_m where "log_m = ln (length xs + 1)"
  define log_n where "log_n = ln (n + 1)"

  have s2_nonzero: "s\<^sub>2 > 0"
    using assms by (simp add:s\<^sub>2_def)

  have s1_nonzero: "s\<^sub>1 > 0"  
    using assms by (simp add:s\<^sub>1_def)

  define b1 where "b1 = ereal ((s\<^sub>1 * s\<^sub>2) * 2 + 1)"
  define b2 where "b2 = ereal ((s\<^sub>1 * s\<^sub>2) * 2 + 1)"
  define b3 where "b3 = ereal ((s\<^sub>1 * s\<^sub>2) * (3*log_n+5))"
  define b4 where "b4 = ereal ((s\<^sub>1 * s\<^sub>2) * (12*log_n+26) + 1)"
  define b5 where "b5 = ereal ((s\<^sub>1 * s\<^sub>2) * (3*log_m+3*log_n+7) + 1)"
  define b7 where "b7 = ereal (12*log_n+25)"
  define b8 where "b8 = ereal (3*log_m+3*log_n+6)"


  have "\<And>x. x \<ge> 0 \<Longrightarrow> real (nat x) = real_of_int x" 
    using of_nat_nat by blast
  moreover 
  have "\<lceil> 16 / \<delta>\<^sup>2 \<rceil> \<ge> 0"  apply (simp add: power2_eq_square) 
    using  assms(2) divide_pos_pos[where x="16" and y="\<delta>*\<delta>"] mult_pos_pos[where a="\<delta>" and b="\<delta>"]
    by linarith
  ultimately have "real s\<^sub>1 = \<lceil>16/ (real_of_rat \<delta>)\<^sup>2\<rceil>" apply (simp add:s\<^sub>1_def) 
    by (metis (no_types, opaque_lifting) of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power)
  hence "real s\<^sub>1 < 16/ (real_of_rat \<delta>)\<^sup>2 + 1" 
    by linarith
  also have " 16/ (real_of_rat \<delta>)\<^sup>2 + 1 \<le> 17/ (real_of_rat \<delta>)\<^sup>2"
    apply (subst pos_le_divide_eq) using assms(2) apply simp
    apply (simp add:algebra_simps) using assms(3) assms(2) 
    by (simp add: power_le_one)
  finally have s1_est: "real s\<^sub>1 \<le> 17 / (real_of_rat \<delta>)\<^sup>2"
    by auto

  have "real s\<^sub>2 = \<lceil>-32 * (ln (real_of_rat \<epsilon>))/9\<rceil>"
    apply (simp add:s\<^sub>2_def) using s2_nonzero s\<^sub>2_def by linarith
  also have  "... \<le> (-32 * (ln (real_of_rat \<epsilon>))/9)+1"
    using of_int_ceiling_le_add_one by blast
  also have "... \<le> 4 * (1-ln (real_of_rat \<epsilon>))" 
    apply (simp add:algebra_simps)
    by (metis assms(1) ln_less_zero less_eq_real_def mult_right_mono mult_zero_left of_rat_less_1_iff order_trans zero_le_numeral zero_less_of_rat_iff)
  finally have s2_est: "real s\<^sub>2 \<le> 4 * (1-ln (real_of_rat \<epsilon>))"
    by blast

  have "real (s\<^sub>1 * s\<^sub>2) \<le> (17 / (real_of_rat \<delta>)\<^sup>2) * (4 * (1-ln (real_of_rat \<epsilon>)))"
    apply (subst of_nat_mult)
    apply (subst mult_mono)
        apply (metis s1_est, metis s2_est)
    using s\<^sub>1_def s1_nonzero apply force
    using s\<^sub>2_def s2_nonzero apply force
    by simp
  also have "... =  68 * (1-ln (real_of_rat \<epsilon>)) / (real_of_rat \<delta>)\<^sup>2"
    by (simp)
  finally have s1_s2_est: "real (s\<^sub>1 * s\<^sub>2) \<le> 68 * (1-ln (real_of_rat \<epsilon>)) / (real_of_rat \<delta>)\<^sup>2"
    by blast

  have "\<And>(x::nat). ereal (2 * log 2 (real (x+ 1)) + 1) \<le> ereal (2 * real x + 1)"
    using log_est
    by (simp add: add.commute)
  hence "\<And>(x::nat). bit_count (N\<^sub>S x) \<le> 2 * real x + 1"
    using nat_bit_count order_trans by blast
  moreover have "\<And>(x::nat). x \<le> s\<^sub>1 * s\<^sub>2 \<Longrightarrow> 2 * real x + 1 \<le> ereal ((s\<^sub>1 * s\<^sub>2) * 2 + 1)"
    using of_nat_mono by fastforce
  ultimately have c1_1: "\<And>(x::nat). x \<le> s\<^sub>1 * s\<^sub>2 \<Longrightarrow> bit_count (N\<^sub>S x) \<le> ereal ((s\<^sub>1 * s\<^sub>2) * 2 + 1)"
    by (meson ereal_less_eq(3) le_ereal_le)

  have c1: "bit_count (N\<^sub>S s\<^sub>1) \<le> b1" apply (subst b1_def, rule c1_1) using s2_nonzero by simp
  have c2: "bit_count (N\<^sub>S s\<^sub>2) \<le> b2" apply (subst b2_def, rule c1_1) using s1_nonzero by simp

  have p_gr_0: "p > 0"
    apply (simp add:p_def) using find_prime_above_min 
    by (meson order_less_le_trans zero_less_numeral)

  have "2*log 2 (p+1) \<le> 2*log 2 (2*n+4)"
    apply (simp add:p_def)
    by (metis find_prime_above_upper_bound add.commute mult_2 of_nat_add of_nat_le_iff of_nat_numeral)
  also have "... \<le> 2*log 2 (real 4*(n+1))"
    by simp
  also have "... \<le> 2*log 2 (n+1) + 4"
    apply (subst log_mult, simp, simp, simp, simp, simp)
    by (metis dual_order.refl log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power2_eq_square)
  also have "... \<le> 3*ln (n+1) + 4"
    apply simp
    by (rule log_2_ln, simp)
  finally have log_n_of_p: "2*log 2 (p+1) \<le> 3*log_n + 4"
    by (simp add:log_n_def)

  have log_m: "2*log 2 (length xs +1) \<le> 3 * log_m"
    by (simp add:log_m_def, rule log_2_ln, simp)

  have "\<And>x. x \<le> p \<Longrightarrow> bit_count (N\<^sub>S x) \<le> 2*log 2 (p+1)+1"
    using nat_bit_count_est by (simp del:N\<^sub>S.simps)
  hence b3_est: "\<And>x. x \<le> p \<Longrightarrow> bit_count (N\<^sub>S x) \<le> 3*log_n+5" using log_n_of_p by fastforce

  have "bit_count (N\<^sub>S p) \<le> 3*log_n+5" using b3_est by blast
  moreover have "real (s\<^sub>1 * s\<^sub>2) * (3*log_n+5) \<ge> real 1 * (3*log_n+5)" 
    apply (subst mult_le_cancel_iff1)
    apply (simp add: log_n_def) using ln_ge_zero 
    apply (smt (z3) of_nat_less_0_iff)
    using s1_nonzero s2_nonzero 
    by (metis One_nat_def Suc_leI nat_0_less_mult_iff of_nat_1 real_of_nat_ge_one_iff)
  ultimately have c3: "bit_count (N\<^sub>S p) \<le> b3"
    apply (simp add:  b3_def del:N\<^sub>S.simps)  using le_ereal_le by blast

  have "\<And>y. y \<in> carrier (ZFact (int p)) \<Longrightarrow> bit_count (zfact\<^sub>S p y) \<le> 3*log_n+5" 
    using zfact_embed_ran[OF p_gr_0,symmetric] apply (simp del:N\<^sub>S.simps)
    apply (rule b3_est)
    using the_inv_into_into[OF zfact_embed_inj[OF p_gr_0], where B="{0..<p}"]
    by (meson atLeastLessThan_iff less_imp_le_nat subset_refl)
  hence c4_ran_1: "\<And>x y. x \<in> bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow> y \<in> set x  \<Longrightarrow> bit_count (zfact\<^sub>S p y) \<le> 3*log_n+5" 
    apply (simp add:bounded_degree_polynomials_def del:zfact\<^sub>S.simps)
    using univ_poly_carrier 
    by (metis length_greater_0_conv length_pos_if_in_set polynomial_def subsetD)
  have c4_ran_2: "\<And>x. x \<in>  bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow> ereal (real (length x)) \<le> 4"
    apply (simp add:bounded_degree_polynomials_def) 
    by (metis Suc_leI Suc_pred length_greater_0_conv less_nat_zero_code linorder_not_less 
        list.size(3) numeral_less_real_of_nat_iff)

  have c4_ran_3: "0 \<le> 6+3*log_n" by (simp add:log_n_def)
  have c4_ran: "\<And>x. x \<in>  bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow> 
    bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le> b7"
    apply (rule list_bit_count_estI[where a="3*log_n+5"], metis c4_ran_1)
    using b7_def c4_ran_2 c4_ran_3 mult_right_mono[where b="4::real" and c="6+3*log_n"] by simp

  have "\<And>x. x \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow>
    bit_count (encode_prod_fun s\<^sub>1 s\<^sub>2 (list\<^sub>S (zfact\<^sub>S p)) x) \<le> ereal (real (s\<^sub>1 * s\<^sub>2)) * (b7+1) + 1"
    apply (simp add:PiE_iff)
    apply (rule list_bit_count_estI[where a="b7"])
     apply (simp) using c4_ran apply blast
    by simp
  also have "ereal (real (s\<^sub>1 * s\<^sub>2)) * (b7+1) + 1 \<le> b4" 
    by (simp add:b7_def b4_def add.commute)  
  finally have c4: "\<And>x. x \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow>
    bit_count (encode_prod_fun s\<^sub>1 s\<^sub>2 (list\<^sub>S (zfact\<^sub>S p)) x) \<le> b4"
    by blast

  have c5_ran_1: "\<And>x. x \<in> R \<Longrightarrow> bit_count (I\<^sub>S x) \<le> 2*log 2 (length xs * (int p+1) +1) + 2"
    using int_bit_count_est[where m="int (length xs) * (int p+1)"] R_def by auto
  have "2*log 2 (length xs * (int p+1) +1) + 2 \<le> 2*log 2 (real (length xs + 1) * (p+1)) + 2" 
    apply (rule add_mono)
     apply (rule mult_left_mono)
      apply (subst log_le_cancel_iff, simp, simp) 
    apply (metis add.commute add_less_same_cancel1 linorder_neqE_linordered_idom of_nat_Suc of_nat_less_0_iff of_nat_mult zero_less_one)
       apply (simp) 
    by (simp add:algebra_simps, simp, simp) 
  also have "... \<le> 2* (log 2 (length xs +1) + log 2 (p+1)) + 2"
    by (subst log_mult, simp, simp, simp, simp, simp add:log_m_def)
  also have "... \<le> 3* log_m + 3* log_n + 6"
    using log_n_of_p log_m by simp
  finally have c5_ran_2: "2*log 2 (length xs * (int p+1) +1) + 2 \<le>  3* log_m + 3* log_n + 6"
    by blast
  have c5_ran: "\<And>x. x \<in> R \<Longrightarrow> bit_count (I\<^sub>S x) \<le> b8"
    using c5_ran_1 c5_ran_2 b8_def le_ereal_le by blast
  have "\<And>x. x \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E R \<Longrightarrow>
    bit_count (encode_prod_fun s\<^sub>1 s\<^sub>2 I\<^sub>S x) \<le> ereal (real (s\<^sub>1 * s\<^sub>2)) * (b8+1) + 1" 
    apply (simp add:PiE_iff)
    apply (rule list_bit_count_estI[where a="b8"]) 
     apply (simp del:I\<^sub>S.simps) using c5_ran apply blast
    by simp
  also have "ereal (real (s\<^sub>1 * s\<^sub>2)) * (b8+1) + 1 \<le> b5" by (simp add:b8_def b5_def algebra_simps)
  finally have c5:"\<And>x. x \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E R \<Longrightarrow> bit_count (encode_prod_fun s\<^sub>1 s\<^sub>2 I\<^sub>S x) \<le> b5"
    by blast

  define b_total where "b_total = ereal ((s\<^sub>1 * s\<^sub>2) * (18*log_n + 3*log_m + 42) + 4)"


  have c_aux:"\<And>x. x \<in> M \<Longrightarrow> bit_count (encode_state x) \<le> b1 + (b2 + (b3 + (b4 + b5)))"
    apply (simp add:M_def)
    apply (simp add: encode_state_def del:N\<^sub>S.simps encode_dependent_sum.simps)
    apply (simp add: dependent_bit_count prod_bit_count  s\<^sub>1_from_def s\<^sub>2_from_def p_from_def h_from_def
        sketch_from_def
       del:N\<^sub>S.simps encode_prod.simps encode_dependent_sum.simps encode_prod_fun.simps)
    apply (rule add_mono, metis c1)
    apply (rule add_mono, metis c2)
    apply (rule add_mono, metis c3)
    apply (rule add_mono, metis c4)
    by (metis c5)

  have "b_total \<le> ereal ((s\<^sub>1 * s\<^sub>2) * (18*log_n + 3*log_m + 46))"
    apply (simp add:algebra_simps b_total_def) using s1_nonzero s2_nonzero 
    by (metis less_nat_zero_code less_one linorder_not_le nat_0_less_mult_iff of_nat_mult real_of_nat_ge_one_iff)
  also have "... \<le> ereal ((s\<^sub>1 * s\<^sub>2) * (46 * (log_n + log_m + 1)))"
    by (simp add: log_m_def log_n_def algebra_simps)
  also have "... \<le> ereal (68 * (1-ln (real_of_rat \<epsilon>)) / (real_of_rat \<delta>)\<^sup>2 * (46*(log_n + log_m + 1)))"
    using s1_s2_est log_m_def log_n_def mult_right_mono by fastforce
  also have "... = ereal (3128 * (1-ln (real_of_rat \<epsilon>)) / (real_of_rat \<delta>)\<^sup>2 * (log_n + log_m + 1))"
    by (simp add:algebra_simps)
  finally have "b_total \<le> ?rhs"
    by (simp add: log_n_def log_m_def add.commute)
  moreover have "\<And>x. x \<in> M \<Longrightarrow> bit_count (encode_state x) \<le> b_total" using c_aux
    by (simp add:b1_def b2_def b3_def b4_def b5_def b_total_def algebra_simps)
  ultimately have c:"\<And>x. x \<in> M \<Longrightarrow> bit_count (encode_state x) \<le> ?rhs"
    using order_trans by blast

  have delta_gr_0: "\<delta> >0 " using assms by auto
  show ?thesis
    apply (subst AE_measure_pmf_iff)
     using f2_alg_sketch[OF assms(1) delta_gr_0, where n="n" and xs="xs"]
     apply (simp only:sketch_def Let_def s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
     apply (subst set_bind_pmf)
     apply (subst set_prod_pmf, simp)
     apply simp
     apply (subst set_pmf_of_set) defer defer
       apply (rule ballI)
     apply (rule c[simplified])
     apply (simp add:M_def s\<^sub>1_from_def s\<^sub>2_from_def p_from_def h_from_def sketch_from_def b1)
      apply (rule ex_poly)
     apply (rule fin_poly)
     by (simp add:p_def find_prime_above_is_prime)
qed

end