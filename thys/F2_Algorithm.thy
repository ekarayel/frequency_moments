section \<open>Frequency Moment 2\<close>

theory F2_Algorithm
  imports Main "HOL-Probability.Giry_Monad" "HOL-Probability.Probability_Mass_Function" UniversalHashFamily Field 
    Median Probability_Ext "HOL-Library.Multiset" Partitions Primes_Ext "HOL-Library.Extended_Nat"
    "HOL-Library.Rewrite" "Encoding" List_Ext Prod_PMF  "HOL-Library.Landau_Symbols"
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
      let p = find_prime_above (max n 3);
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
  defines "p \<equiv> find_prime_above (max n 3)"
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
  define p where "p = find_prime_above (max n 3)"
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
    apply (simp add:p_def)
    by (meson find_prime_above_lower_bound dual_order.trans max.cobounded2)

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
    by (metis max_def order_less_le_trans)

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
    by (metis max_def order_less_le_trans)

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

fun f2_complexity :: "(nat \<times> nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f2_complexity (n, m, \<epsilon>, \<delta>) = (
    let s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2 \<rceil> in
    let s\<^sub>2 = nat \<lceil>-(32 * ln (real_of_rat \<epsilon>)/ 9)\<rceil> in 
    5 +
    2 * log 2 (1 + s\<^sub>1) +
    2 * log 2 (1 + s\<^sub>2) +
    2 * log 2 (4 + 2 * real n) +
    s\<^sub>1 * s\<^sub>2 * (13 + 8 * log 2 (4 + 2 * real n) + 2 * log 2 (real m * (4 + 2 * real n) + 1 )))"

lemma f2_complexity:
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in sketch. bit_count (encode_state \<omega>) \<le> f2_complexity (n, length xs, \<epsilon>, \<delta>)"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32* ln (real_of_rat \<epsilon>) /9)\<rceil>"
  define p where "p = find_prime_above (max n 3)"

  have find_prime_above_3: "find_prime_above 3 = 3" 
    by (simp add:find_prime_above.simps)

  have p_ge_0: "p > 0" 
    by (metis find_prime_above_min p_def gr0I not_numeral_le_zero)
  have p_le_n: "p \<le> 2 * n + 3" 
    apply (cases "n \<le> 3")
    apply (simp add: p_def find_prime_above_3) 
    apply (simp add: p_def) 
    by (metis One_nat_def find_prime_above_upper_bound Suc_1 add_Suc_right linear not_less_eq_eq numeral_3_eq_3)

  have a: "\<And>y. y\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 4 \<Longrightarrow>
       bit_count (encode_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. 
      sum_list (map (eval_hash_function p (y i)) xs)))
       \<le> ereal (f2_complexity (n, length xs, \<epsilon>, \<delta>))"
  proof -
    fix y
    assume a_1:"y \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 4"

    have a_2: "y \<in> extensional ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})" using a_1  PiE_iff by blast

    have a_3: "\<And>x. x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow> bit_count (list\<^sub>S (zfact\<^sub>S p) x) 
      \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
    proof -
      fix x 
      assume a_5: "x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})"
      have a_4: "\<And>z. z \<in> set x \<Longrightarrow> z \<in> zfact_embed p ` {0..<p}"
        apply (subst zfact_embed_ran[OF p_ge_0])
        using a_5 a_1 apply (simp add:PiE_def Pi_def image_def bounded_degree_polynomials_def)
        by (metis (no_types, opaque_lifting) atLeastLessThan_iff length_pos_if_in_set less_nat_zero_code list.size(3) polynomial_def subsetD univ_poly_carrier)

      have "length x - 1 < 4" 
        using a_5 a_1 apply (simp add:PiE_def Pi_def image_def bounded_degree_polynomials_def) 
        by fastforce
      hence a_6: "length x \<le> 4" by linarith
      have "bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le>  ereal (real (length x)) * (ereal (2 * log 2 (4 + 2 * real n) + 1) + 1) + 1"
        apply (rule list_bit_count_est[where a="2 * log 2 (4 + 2 * real n) + 1"])
        using a_4 apply (simp)
        apply (rule nat_bit_count_est[where m="2*n+3", simplified])
        apply (rule order_trans[where y="p"])
        using the_inv_into_into[OF zfact_embed_inj[OF p_ge_0], where B="{0..<p}", simplified] less_imp_le_nat apply presburger
        by (simp add:p_le_n)
      also have "... \<le> ereal 4 * (ereal (2 * log 2 (4 + 2 * real n) + 1) + 1) + 1"
        apply (rule add_mono)
         apply (rule ereal_mult_mono, simp, simp)
        using  a_6 by simp+
      also have "... = ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by simp
      finally show "bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le>  ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by blast
    qed

    have a_7: "\<And>x. 
      x \<in> (\<lambda>x. sum_list (map (eval_hash_function p (y x)) xs)) ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow>
         \<bar>x\<bar> \<le> (4 + 2 * int n) * int (length xs)"
    proof -
      fix x
      assume "x \<in> (\<lambda>x. sum_list (map (eval_hash_function p (y x)) xs)) ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})"
      then obtain i where "i \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}" and x_def: "x = sum_list (map (eval_hash_function p (y i)) xs)"
        by blast
      have "abs x \<le> sum_list (map abs (map (eval_hash_function p (y i)) xs))"
        by (subst x_def, rule sum_list_abs)
      also have "... \<le> sum_list (map (\<lambda>_. (int p+1)) xs)"
        apply (simp add:comp_def del:eval_hash_function.simps)
        apply (rule sum_list_mono)
        using p_ge_0 by simp 
      also have "... = int (length xs) * (int p+1)"
        by (simp add: sum_list_triv)
      also have "... \<le> int (length xs) * (4+2*(int n))"
        apply (rule mult_mono, simp)
        using p_le_n apply linarith
        by simp+
      finally show "abs x \<le>  (4 + 2 * int n) * int (length xs)"
        by (simp add: mult.commute)
    qed
    
    have "bit_count (encode_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}.
      sum_list (map (eval_hash_function p (y i)) xs)))
       \<le> ereal (2 * (log 2 (1 + real s\<^sub>1)) + 1) 
       + (ereal (2 * (log 2 (1 + real s\<^sub>2)) + 1)
       + (ereal (2 * (log 2 (1 + real (2*n+3))) + 1) 
       + ((ereal (real s\<^sub>1 * real s\<^sub>2) * (10 + 8 * log 2 (4 + 2 * real n)) + 1) 
       + (ereal (real s\<^sub>1 * real s\<^sub>2) * (3 + 2 * log 2 (real (length xs) * (4 + 2 * real n) + 1) ) + 1))))"
      using a_2
      apply (simp add: encode_state_def s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] 
        dependent_bit_count prod_bit_count
          del:encode_dependent_sum.simps encode_prod.simps N\<^sub>S.simps plus_ereal.simps of_nat_add)
      apply (rule add_mono, rule nat_bit_count)
      apply (rule add_mono, rule nat_bit_count)
      apply (rule add_mono, rule nat_bit_count_est, metis p_le_n)
      apply (rule add_mono)
       apply (rule list_bit_count_estI[where a="9 + 8 * log 2 (4 + 2 * real n)"], rule a_3, simp, simp)
      apply (rule list_bit_count_estI[where a="2* log 2 (real_of_int (int ((4+2*n) * length xs)+1))+2"])
       apply (rule int_bit_count_est)
       apply (simp add:a_7)
      by (simp add:algebra_simps)
    also have "... = ereal (f2_complexity (n, length xs, \<epsilon>, \<delta>))"
      by (simp add:distrib_left[symmetric] s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
    finally show "bit_count (encode_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}.
      sum_list (map (eval_hash_function p (y i)) xs)))
       \<le> ereal (f2_complexity (n, length xs, \<epsilon>, \<delta>))" by blast
  qed

  show ?thesis
    apply (subst AE_measure_pmf_iff)
    apply (subst sketch_def)
    apply (subst f2_alg_sketch[OF assms(1) assms(2), where n="n" and xs="xs"])
    apply (simp add: s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] del:f2_complexity.simps)
    apply (subst set_prod_pmf, simp)
    apply (simp add: PiE_iff  del:f2_complexity.simps)
    apply (subst set_pmf_of_set, metis ex_poly, metis fin_poly p_def find_prime_above_is_prime(1))
    by (metis a)
qed

lemma f2_asympotic_space_complexity:
  "f2_complexity \<in> 
  O[at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_right (0::rat) \<times>\<^sub>F at_right (0::rat)](\<lambda> (n, m, \<epsilon>, \<delta>).
  (ln (1 / real_of_rat \<epsilon>)) / (real_of_rat \<delta>)\<^sup>2 * (ln (real n) + ln (real m)))"
  (is "?lhs \<in> O[?evt](?rhs)")
proof -
  define c where "c=(5865::real)"

  have b:"\<And>n m \<epsilon> \<delta>.  n \<ge> 4  \<Longrightarrow> m \<ge> 1 \<Longrightarrow> (0 < \<epsilon> \<and> \<epsilon> < 1/3) \<Longrightarrow> (0 < \<delta> \<and> \<delta> < 1) \<Longrightarrow>
     abs (f2_complexity  (n, m, \<epsilon>, \<delta>)) \<le> c * abs (?rhs  (n, m, \<epsilon>, \<delta>))"
  proof -
    fix n m \<epsilon> \<delta>
    assume n_ge_4: "n \<ge> (4::nat)"
    assume m_ge_1: "m \<ge> (1::nat)"
    assume eps_bound: "(0::rat) < \<epsilon> \<and> \<epsilon> < 1/3"
    assume delta_bound: "(0::rat) < \<delta> \<and> \<delta> < 1"
    define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
    define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(32* ln (real_of_rat \<epsilon>) /9)\<rceil>"
    define s\<^sub>1' where "s\<^sub>1' = 17/ (real_of_rat \<delta>)\<^sup>2"
    define s\<^sub>2' where "s\<^sub>2' = 5 * ln (1 / real_of_rat  \<epsilon>)"

    have n_ge_1: "n \<ge> 1" using n_ge_4 by simp
    have \<epsilon>_inv_ge_1: "1/ real_of_rat \<epsilon> \<ge> 1" using eps_bound by simp

    have "s\<^sub>1 > 0"
      apply (simp add:s\<^sub>1_def) using delta_bound by blast
    hence s1_ge_1: "s\<^sub>1 \<ge> 1" by simp

    have "s\<^sub>2 > 0" using eps_bound by (simp add:s\<^sub>2_def)
    hence s2_ge_1: "s\<^sub>2 \<ge> 1" by simp

    have "real_of_rat \<epsilon> * exp 1 \<le> (1/3) * 3"
      apply (rule mult_mono)
         apply (metis (mono_tags, opaque_lifting) eps_bound less_eq_rat_def of_rat_divide of_rat_less_eq of_rat_numeral_eq one_eq_of_rat_iff)
      using exp_le by simp+
    also have "... = 1"
      by simp
    finally have \<epsilon>_le_1_over_e: "real_of_rat \<epsilon> * exp 1 \<le> 1"
      by blast

    have "s\<^sub>1 \<le> 16/ (real_of_rat \<delta>)\<^sup>2 + 1"
      apply (simp add:s\<^sub>1_def, subst of_nat_nat, simp)
       apply (rule order_less_le_trans[where y="0"], simp)
      using delta_bound apply simp
      by (metis (no_types, opaque_lifting) of_int_ceiling_le_add_one of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power)
    also have "... \<le> (16+1)/(real_of_rat \<delta>)\<^sup>2"
      apply (subst add_divide_distrib)
      apply (rule add_mono, simp)
      using delta_bound 
      by (simp add: power_le_one_iff)
    also have "... = s\<^sub>1'"
      by (simp add:s\<^sub>1'_def)
    finally have s1_le_s1': "s\<^sub>1 \<le> s\<^sub>1'"
      by blast

    have "s\<^sub>2 = real_of_int \<lceil>(32 * ln (1 / real_of_rat \<epsilon>) / 9)\<rceil> "
      apply (simp add:s\<^sub>2_def, subst of_nat_nat, simp)
       apply (rule order_less_le_trans[where y="0"], simp)
      using  eps_bound apply simp
       apply simp
      apply simp
      apply (rule arg_cong[where f="\<lambda>x. \<lceil>x\<rceil>"])
      using eps_bound by (simp add: ln_div)
    also have "... \<le>  (32 * ln (1 / real_of_rat  \<epsilon>)/ 9) + 1"
      by (simp add:s\<^sub>2'_def)
    also have  "... \<le> (4+1) * ln (1 / real_of_rat \<epsilon>)"
      apply (subst distrib_right)
      apply (rule add_mono)
      using eps_bound apply simp
      apply simp
      apply (subst ln_ge_iff)
      using \<epsilon>_inv_ge_1 apply linarith
      apply (subst pos_le_divide_eq)
      using eps_bound apply simp
      using \<epsilon>_le_1_over_e by (simp add:mult.commute)
    also have "... = s\<^sub>2'"
      by (simp add:s\<^sub>2'_def)
    finally have s2_le_s2':"s\<^sub>2 \<le> s\<^sub>2'"
      by blast

    have b_3: "4 + real n * 2 \<le> (real n)\<^sup>2" 
       apply (rule order_trans[where y="real n * 2 + real n * 2"])
        apply (rule add_mono) using n_ge_4 apply linarith
       using n_ge_4 m_ge_1 by (simp add: power2_eq_square)+

    have "real m * (4 + 2 * real n) + 1 \<le> real m * ((4 + 2 * real n) + 1)"
      apply (subst (2) distrib_left)
      using m_ge_1 by simp
    also have "... \<le> real m * (real n)^2"
      apply (rule mult_left_mono)
       apply (simp)
       apply (rule order_trans[where y="2*real n + 2*real n"])
        apply (rule add_mono) using n_ge_4 apply linarith
       using n_ge_4 m_ge_1 by (simp add: power2_eq_square)+
    finally have b_4: "real m * (4 + 2 * real n) + 1 \<le> real m * (real n)\<^sup>2" by auto

    have "22 + (10 * log 2 (4 + real n * 2) + 2 * log 2 (real m * (4 + 2 * real n)+1))
      \<le> 22 * log 2 n + (10 * log 2 (n powr 2) + 2 * log 2 (real m * n powr 2))"
      apply (rule add_mono)
       using n_ge_4 apply simp
      apply (rule add_mono)
       using n_ge_4 b_3 apply simp 
      apply simp
      apply (subst log_le_cancel_iff)
         apply simp
        using m_ge_1 n_ge_1 apply (auto intro!: mult_pos_pos add_pos_pos)[1]
       using m_ge_1 n_ge_1 apply (auto intro!: mult_pos_pos add_pos_pos)[1]
      by (metis b_4)       
    also have "... \<le> 23 * (2 * (log 2 n + log 2 m))"
      using n_ge_1 apply (subst log_powr, simp)
      apply (subst log_mult, simp, simp)
      using m_ge_1 apply simp
       apply simp
      apply (subst log_powr, simp)
      using m_ge_1 by simp
    also have "... \<le> 23 * (3 * (ln n + ln m))"
      apply (rule mult_left_mono)
      apply (simp add:distrib)
       apply (rule add_mono, rule log_2_ln) using n_ge_1 apply simp
      apply (rule log_2_ln) using m_ge_1 by simp+
    finally have b_7: "22 + (10 * log 2 (4 + real n * 2) + 2 * log 2 (real m * (4 + 2 * real n)+1))
      \<le> 69 * (ln n + ln m)"
      by simp

    have b_8: " 0 \<le> log 2 (real m * (4 + 2 * real n) + 1)" 
      apply (subst zero_le_log_cancel_iff, simp)
      using n_ge_1 m_ge_1 by (simp add: add_pos_pos)+

    have
      "5 + 2 * log 2 (1 + real s\<^sub>1) + 2 * log 2 (1 + real s\<^sub>2) + 2 * log 2 (4 + 2 * real n) +
      real s\<^sub>1 * real s\<^sub>2 * (13 + 8 * log 2 (4 + 2 * real n) + 2 * log 2 (real m * (4 + 2 * real n) + 1))
    \<le> 5 * real s\<^sub>1 * real s\<^sub>2 + 2 * real s\<^sub>1 * real s\<^sub>2 + 2 * real s\<^sub>1 * real s\<^sub>2 + 
      real s\<^sub>1 * real s\<^sub>2 * 2 * log 2 (4 + 2 * real n) +
      real s\<^sub>1 * real s\<^sub>2 * (13 + 8 * log 2 (4 + 2 * real n) + 2 * log 2 (real m * (4 + 2 * real n) + 1))"
      apply (rule add_mono)
       apply (rule add_mono)
        apply (rule add_mono)
         apply (rule add_mono)
          using s1_ge_1 s2_ge_1 
          apply (simp add: ln_ge_zero_imp_ge_one ln_mult real_of_nat_ge_one_iff)
         apply (rule order_trans [where y="2*real s\<^sub>1"]) using mult_left_mono log_est apply force
         using s1_ge_1 s2_ge_1 
         apply (simp add: ln_ge_zero_imp_ge_one ln_mult real_of_nat_ge_one_iff)
        apply (rule order_trans [where y="2*real s\<^sub>2"]) using mult_left_mono log_est apply force
        using s1_ge_1 s2_ge_1 
        apply (simp add: ln_ge_zero_imp_ge_one ln_mult real_of_nat_ge_one_iff)
       using s1_ge_1 s2_ge_1 
       apply (simp add: ln_ge_zero_imp_ge_one ln_mult real_of_nat_ge_one_iff)
      by simp
    also have "... \<le> real s\<^sub>1 * (real s\<^sub>2 * (22 + (10 * log 2 (4 + real n * 2) + 2 * log 2 (real m * (4 + 2 * real n) + 1))))"
      by (simp add:algebra_simps)
    also have "... \<le> s\<^sub>1' * (s\<^sub>2' * (69 * (ln n + ln m)))"
      apply (rule mult_mono, simp add:s1_le_s1')
        apply (rule mult_mono, simp add:s2_le_s2')
      apply (metis b_7)
      using s2_ge_1 s2_le_s2' apply linarith
      using b_8 n_ge_1 m_ge_1 apply (auto intro!:add_nonneg_nonneg)[1]
      using s1_ge_1 s1_le_s1' apply linarith
      using b_8 n_ge_1 m_ge_1 by (auto intro!:add_nonneg_nonneg)[1]
    also have "... \<le> c * (ln (1 / real_of_rat \<epsilon>) * (ln (real n) + ln (real m))) / (real_of_rat \<delta>)\<^sup>2"
      apply (simp add:s\<^sub>1'_def s\<^sub>2'_def c_def)
      apply (rule divide_right_mono)
       apply (subst distrib_left[symmetric])
      apply (subst (2) mult.assoc[symmetric])
       apply (subst (2) mult.commute)
       apply simp
      using delta_bound zero_compare_simps(12) by blast
    finally have b_1: "5 + 2 * log 2 (1 + real s\<^sub>1) + 2 * log 2 (1 + real s\<^sub>2) + 2 * log 2 (4 + 2 * real n) +
      real s\<^sub>1 * real s\<^sub>2 * (13 + 8 * log 2 (4 + 2 * real n) + 2 * log 2 (real m * (4 + 2 * real n) + 1))
      \<le> c * (ln (1 / real_of_rat \<epsilon>) * (ln (real n) + ln (real m))) / (real_of_rat \<delta>)\<^sup>2"
      by blast

    show "abs (f2_complexity  (n, m, \<epsilon>, \<delta>)) \<le> c * abs (?rhs  (n, m, \<epsilon>, \<delta>))"
      apply (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])
      apply (subst abs_of_nonneg)
       using b_8 n_ge_1 m_ge_1 apply (auto intro!: add_nonneg_nonneg zero_le_log_cancel_iff mult_nonneg_nonneg)[1]
      apply (subst abs_of_nonneg)
       using n_ge_1 m_ge_1 \<epsilon>_inv_ge_1 apply (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)[1]
      by (metis b_1)
  qed

  have a:"eventually 
    (\<lambda>x. abs (f2_complexity x) \<le> c * abs (?rhs x)) ?evt"
    apply (rule eventually_mono[where P="\<lambda>(n, m, \<epsilon>, \<delta>).  n \<ge> 4  \<and> m \<ge> 1 \<and> (0 < \<epsilon> \<and> \<epsilon> < 1/3) \<and> (0 < \<delta> \<and> \<delta> < 1)"])
    apply (rule eventually_prod_I2[where Q="\<lambda>n. n \<ge> 4"], simp)
    apply (rule eventually_prod_I2[where Q="\<lambda>m. m \<ge> 1"], simp)
    apply (rule eventually_prod_I2[where Q="\<lambda>\<epsilon>. 0 < \<epsilon> \<and> \<epsilon> < 1/3"])
    apply (rule eventually_at_rightI[where b="1/3"], simp, simp)
    apply (rule eventually_at_rightI[where b="1"], simp, simp)
    using b by blast
  show ?thesis
    apply (rule landau_o.bigI[where c="c"], simp add:c_def, simp)
    using a by simp
qed


end