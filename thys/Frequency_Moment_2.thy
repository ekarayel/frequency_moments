section \<open>Frequency Moment $2$\<close>

theory Frequency_Moment_2
  imports Main "HOL-Probability.Probability_Mass_Function" UniversalHashFamily Field 
    Median Probability_Ext "HOL-Library.Multiset" Partitions Primes_Ext "HOL-Library.Extended_Nat"
    Encoding List_Ext Prod_PMF  "HOL-Library.Landau_Symbols" UniversalHashFamilyOfPrime
begin

definition f2_value where
  "f2_value xs = (\<Sum> x \<in> set xs. (rat_of_nat (count_list xs x)^2))"

fun eval_hash_function where
  "eval_hash_function p h k = (
    if hash p k h \<in> {k. 2*k < p} then
      int p - 1
    else
      - int p - 1
  )"

type_synonym f2_space = "nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> int set list) \<times> (nat \<times> nat \<Rightarrow> int)"

definition encode_state where
  "encode_state = 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>1. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>2. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>p. 
    encode_extensional (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]) (list\<^sub>S (zfact\<^sub>S p)) \<times>\<^sub>S
    encode_extensional (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]) I\<^sub>S)))"

lemma "is_encoding encode_state"
  apply (simp add:encode_state_def)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule prod_encoding, metis encode_extensional list_encoding zfact_encoding)
  by (metis encode_extensional int_encoding)

fun f2_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f2_space pmf" where
  "f2_init \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>;
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


lemma eval_exp_o:
  assumes "Factorial_Ring.prime p"
  assumes "k < p"
  assumes "p > 2" 
  shows
    "prob_space.expectation (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)) 
    (\<lambda>\<omega>. real_of_int (eval_hash_function p \<omega> k) ^m) = 
     (((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p))"
proof -
  have g:"p > 0" using assms(1) prime_gt_0_nat by auto

  have "odd p" using assms prime_odd_nat by blast
  then obtain t where t_def: "p=2*t+1" 
    using oddE by blast

  define \<Omega> where "\<Omega> = pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)"

  have b: "finite (set_pmf \<Omega>)"
    apply (simp add:\<Omega>_def)
    by (metis fin_bounded_degree_polynomials[OF g] ne_bounded_degree_polynomials set_pmf_of_set)

  have zero_le_4: "0 < (4::nat)" by simp

  have "card ({k. 2 * k < p} \<inter> {0..<p}) = card ({0..t})"
    apply (subst Int_absorb2, rule subsetI, simp)
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym, rule subsetI, simp add:t_def) 
    by (rule subsetI, simp add:t_def)
  also have "... = t+1"
    by simp
  also have "... = (real p + 1)/2"
    by (simp add:t_def)
  finally have c_1: "card ({k. 2 * k < p} \<inter> {0..<p}) = (real p+1)/2" by simp

  have "card ({k. p \<le> 2 * k} \<inter> {0..<p}) = card {t+1..<p}"
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym, rule subsetI, simp add:t_def) 
    by (rule subsetI, simp add:t_def)
  also have "... = p - (t+1)" by simp
  also have "... = (real p-1)/2"
    by (simp add:t_def)
  finally have c_2: "card ({k. p \<le> 2 * k} \<inter> {0..<p}) = (real p-1)/2" by simp

  have "integral\<^sup>L \<Omega> (\<lambda>x. real_of_int (eval_hash_function p x k) ^ m) =
    integral\<^sup>L \<Omega> (\<lambda>\<omega>. indicator {\<omega>. 2 * hash p k \<omega> < p} \<omega> * (real p - 1)^m + 
      indicator {\<omega>. 2 * hash p k \<omega> \<ge> p} \<omega> * (-real p - 1)^m)" 
    by (rule Bochner_Integration.integral_cong, simp, simp)
  also have "... = 
     \<P>(\<omega> in measure_pmf \<Omega>. hash p k \<omega> \<in> {k. 2 * k < p})  * (real p - 1) ^ m  + 
     \<P>(\<omega> in measure_pmf \<Omega>. hash p k \<omega> \<in> {k. 2 * k \<ge> p})  * (-real p - 1) ^ m "
    apply (subst Bochner_Integration.integral_add)
    apply (rule integrable_measure_pmf_finite[OF b])
    apply (rule integrable_measure_pmf_finite[OF b])
    by simp
  also have "... = (real p + 1) * (real p - 1) ^ m / (2 * real p) + (real p - 1) * (- real p - 1) ^ m / (2 * real p)"
    apply (simp only:\<Omega>_def hash_prob_range[OF assms(1) assms(2) zero_le_4] c_1 c_2)
    by simp
  also have "... =  
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
    by (simp add:add_divide_distrib ac_simps)
  finally have a:"integral\<^sup>L \<Omega> (\<lambda>x. real_of_int (eval_hash_function p x k) ^ m) = 
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)" by simp

  show ?thesis
    apply (subst \<Omega>_def[symmetric])
    by (metis a)
qed

lemma 
  assumes "Factorial_Ring.prime p"
  assumes "p > 2"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < p"
  defines "M \<equiv> measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4))"
  defines "f \<equiv> (\<lambda>\<omega>. real_of_int (sum_list (map (eval_hash_function p \<omega>) xs))^2)"
  shows var_f2_o:"prob_space.variance M f \<le> 2*(real_of_rat (f2_value xs)^2) * ((real p)\<^sup>2-1)\<^sup>2" (is "?A")
  and exp_f2_o:"prob_space.expectation M f = real_of_rat (f2_value xs) * ((real p)\<^sup>2-1)" (is "?B")
proof -
  define h where "h = (\<lambda>\<omega> x. real_of_int (eval_hash_function p \<omega> x))"
  define c where "c = (\<lambda>x. real (count_list xs x))"
  define r where "r = (\<lambda>(m::nat). ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p))"
  define h_prod where "h_prod = (\<lambda>xs \<omega>. prod_list (map (h \<omega>) xs))" 

  define exp_h_prod :: "nat list \<Rightarrow> real" where "exp_h_prod = (\<lambda>xs. (\<Prod>i \<in> set xs. r (count_list xs i)))"

  interpret prob_space M
    using prob_space_measure_pmf M_def by auto

  have f_eq: "f = (\<lambda>\<omega>. (\<Sum>x \<in> set xs. c x * h \<omega> x)^2)"
    by (simp add:f_def c_def h_def sum_list_eval del:eval_hash_function.simps)

  have p_ge_0: "p > 0" using assms(2) by simp

  have int_M: "\<And>f. integrable M (\<lambda>\<omega>. ((f \<omega>)::real))"
    apply (simp add:M_def)
    apply (rule integrable_measure_pmf_finite)
    by (metis p_ge_0 set_pmf_of_set ne_bounded_degree_polynomials fin_bounded_degree_polynomials)

  have r_one: "r (Suc 0) = 0" by (simp add:r_def algebra_simps)

  have r_two: "r 2 = (real p^2-1)"
    apply (simp add:r_def)
    apply (subst nonzero_divide_eq_eq) using assms apply simp
    by (simp add:algebra_simps power2_eq_square)

  (* TODO: Clean up! *)
  have r_four_est: "r 4 \<le> 3 * r 2 * r 2" 
    apply (simp add:r_two)
    apply (simp add:r_def)
    apply (subst pos_divide_le_eq) using assms apply simp
    apply (simp add:algebra_simps power2_eq_square power4_eq_xxxx)
    apply (rule order_trans[where y="real p * 12 + real p * (real p * (real p * 16))"])
     apply simp
    apply (rule add_mono, simp)
    apply (rule mult_left_mono)
    apply (rule mult_left_mono)
      apply (rule mult_left_mono)
    apply simp
    using assms(2) 
       apply (metis assms(1) linorder_not_less num_double numeral_mult of_nat_power power2_eq_square power2_nat_le_eq_le prime_ge_2_nat real_of_nat_less_numeral_iff)
    by simp+

  have fold_sym: "\<And>x y. (x \<noteq> y \<and> y \<noteq> x) = (x \<noteq> y)" by auto

  have exp_h_prod_elim: "exp_h_prod = (\<lambda>xs. prod_list (map (r \<circ> count_list xs) (remdups xs)))" 
    apply (simp add:exp_h_prod_def)
    apply (rule ext)
    apply (subst prod.set_conv_list[symmetric])
    by (rule prod.cong, simp, simp add:comp_def)

  have exp_h_prod: "\<And>x. set x \<subseteq> set xs \<Longrightarrow> length x \<le> 4 \<Longrightarrow> expectation (h_prod x) = exp_h_prod x"
  proof -
    fix x 
    assume "set x \<subseteq> set xs"
    hence x_sub_p: "set x \<subseteq> {0..<p}" using assms(3) atLeastLessThan_iff by blast
    hence x_le_p: "\<And>k. k \<in> set x \<Longrightarrow> k < p" by auto
    assume "length x \<le> 4"
    hence card_x: "card (set x) \<le> 4" using card_length dual_order.trans by blast

    have "expectation (h_prod x) = expectation (\<lambda>\<omega>. \<Prod> i \<in> set x. h \<omega> i^(count_list x i))"
      apply (rule arg_cong[where f="expectation"])
      by (simp add:h_prod_def prod_list_eval)
    also have "... = (\<Prod>i \<in> set x. expectation (\<lambda>\<omega>. h \<omega> i^(count_list x i)))"
      apply (subst indep_vars_lebesgue_integral, simp)
        apply (simp add:h_def)
        apply (rule indep_vars_compose2[where X="hash p" and M'=" (\<lambda>_. pmf_of_set {0..<p})"])
         using hash_k_wise_indep[where n="4" and p="p"] card_x x_sub_p assms(1)
         apply (simp add:k_wise_indep_vars_def M_def[symmetric])
        apply simp
       apply (rule int_M)
      by simp
    also have "... = (\<Prod>i \<in> set x. r (count_list x i))"
      apply (rule prod.cong, simp)
      using eval_exp_o[OF assms(1) x_le_p assms(2)] 
      by (simp add:h_def r_def M_def[symmetric] del:eval_hash_function.simps)
    also have "... = exp_h_prod x"
      by (simp add:exp_h_prod_def)
    finally show "expectation (h_prod x) = exp_h_prod x" by simp
  qed

  have exp_h_prod_cong: "\<And>x y. has_eq_relation x y \<Longrightarrow> exp_h_prod x = exp_h_prod y" 
  proof -
    fix x y :: "nat list"
    assume a:"has_eq_relation x y"
    then obtain f where b:"bij_betw f (set x) (set y)" and c:"\<And>z. z \<in> set x \<Longrightarrow> count_list x z = count_list y (f z)"
      using eq_rel_obtain_bij[OF a] by blast
    have "exp_h_prod x = prod ( (\<lambda>i. r(count_list y i)) \<circ> f) (set x)"
      by (simp add:exp_h_prod_def c)
    also have "... = (\<Prod>i \<in> f ` (set x). r(count_list y i))"
      apply (rule prod.reindex[symmetric])
      using b bij_betw_def by blast
    also have "... = exp_h_prod y"
      apply (simp add:exp_h_prod_def)
      apply (rule prod.cong)
       apply (metis b bij_betw_def)
      by simp
    
    finally show "exp_h_prod x = exp_h_prod y" by simp
  qed

  hence exp_h_prod_cong: "\<And>p x. of_bool (has_eq_relation p x) * exp_h_prod p = of_bool (has_eq_relation p x) * exp_h_prod x" 
    by simp

  have "expectation f = (\<Sum>i\<in>set xs. (\<Sum>j\<in>set xs. c i * c j * expectation (h_prod [i,j])))"
    by (simp add:f_eq h_prod_def power2_eq_square sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum[OF int_M] algebra_simps)
  also have "... = (\<Sum>i\<in>set xs. (\<Sum>j\<in>set xs. c i * c j * exp_h_prod [i,j]))"
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (subst exp_h_prod, simp, simp)
    by simp
  also have "... = (\<Sum>i \<in> set xs. (\<Sum>j \<in> set xs.  
    c i * c j * (sum_list (map (\<lambda>p. of_bool (has_eq_relation p [i,j]) * exp_h_prod p) (enum_partitions 2)))))"
    apply (subst exp_h_prod_cong)
    apply (subst sum_partitions', simp)
    by simp
  also have "... = (\<Sum>i\<in>set xs. c i * c i * r 2)"
    apply (simp add:numeral_eq_Suc exp_h_prod_elim r_one) 
    by (simp add: has_eq_relation_elim distrib_left sum.distrib sum_collapse fold_sym)
  also have "... = real_of_rat (f2_value xs) * ((real p)^2-1)"
    apply (subst sum_distrib_right[symmetric])
    by (simp add:c_def f2_value_def power2_eq_square of_rat_sum of_rat_mult r_two)
  finally show b:?B by simp

  have "expectation (\<lambda>x. (f x)\<^sup>2) = (\<Sum>i1 \<in> set xs. (\<Sum>i2 \<in> set xs. (\<Sum>i3 \<in> set xs. (\<Sum>i4 \<in> set xs.
    c i1 * c i2 * c i3 * c i4 * expectation (h_prod [i1, i2, i3, i4])))))"
    apply (simp add:f_eq h_prod_def power4_eq_xxxx sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum[OF int_M])
    by (simp add:algebra_simps)
  also have "... = (\<Sum>i1 \<in> set xs. (\<Sum>i2 \<in> set xs. (\<Sum>i3 \<in> set xs. (\<Sum>i4 \<in> set xs. 
    c i1 * c i2 * c i3 * c i4 * exp_h_prod [i1,i2,i3,i4]))))"
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (subst exp_h_prod, simp, simp)
    by simp
  also have "... = (\<Sum>i1 \<in> set xs. (\<Sum>i2 \<in> set xs. (\<Sum>i3 \<in> set xs. (\<Sum>i4 \<in> set xs. 
    c i1 * c i2 * c i3 * c i4 * 
    (sum_list (map (\<lambda>p. of_bool (has_eq_relation p [i1,i2,i3,i4]) * exp_h_prod p) (enum_partitions 4)))))))"
    apply (subst exp_h_prod_cong)
    apply (subst sum_partitions', simp)
    by simp
  also have "... = 
    3 * (\<Sum>i \<in> set xs. (\<Sum>j \<in> set xs. c i^2 * c j^2 * r 2 * r 2)) + ((\<Sum> i \<in> set xs. c i^4 * r 4) - 3 *  (\<Sum> i \<in> set xs. c i ^ 4 * r 2 * r 2))"
    apply (simp add:numeral_eq_Suc exp_h_prod_elim r_one) 
    apply (simp add: has_eq_relation_elim distrib_left sum.distrib sum_collapse fold_sym)
    by (simp add: algebra_simps sum_subtractf sum_collapse)
  also have "... = 3 * (\<Sum>i \<in> set xs. c i^2 * r 2)^2 + (\<Sum> i \<in> set xs. c i ^ 4 * (r 4 - 3 * r 2 * r 2))"
    apply (rule arg_cong2[where f="(+)"])
     apply (simp add:power2_eq_square sum_distrib_left sum_distrib_right algebra_simps)
    apply (simp add:sum_distrib_left sum_subtractf[symmetric])
    apply (rule sum.cong, simp)
    by (simp add:algebra_simps)
  also have "... \<le> 3 * (\<Sum>i \<in> set xs. c i^2)^2 * (r 2)^2 +  (\<Sum>i \<in> set xs. c i ^ 4 * 0)"
    apply (rule add_mono)
     apply (simp add:power_mult_distrib sum_distrib_right[symmetric])
    apply (rule sum_mono, rule mult_left_mono)
    using r_four_est by simp+
  also have "... = 3 * (real_of_rat (f2_value xs)^2) * ((real p)\<^sup>2-1)\<^sup>2" 
    by (simp add:c_def r_two f2_value_def of_rat_sum of_rat_power)

  finally have v_1: "expectation (\<lambda>x. (f x)\<^sup>2) \<le> 3 * (real_of_rat (f2_value xs)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    by simp
  
  have "variance f \<le> 2*(real_of_rat (f2_value xs)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    apply (subst variance_eq[OF int_M int_M], subst b)
    apply (simp add:power_mult_distrib)
    using v_1 by simp

  thus ?A by simp
qed

lemma f2_alg_sketch:
  fixes n :: nat
  fixes xs :: "nat list"
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  defines "s\<^sub>1 \<equiv> nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
  defines "s\<^sub>2 \<equiv> nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"
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

theorem f2_alg_correct:
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  assumes "xs \<noteq> []"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "\<P>(\<omega> in measure_pmf (sketch \<bind> f2_result). \<bar>\<omega> - f2_value xs\<bar> \<ge> \<delta> * f2_value xs) \<le> of_rat \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"
  define p where "p = find_prime_above (max n 3)"
  define \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = 
    prod_pmf ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4))"

  define s\<^sub>1_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>1_from = fst"
  define s\<^sub>2_from :: "f2_space \<Rightarrow> nat" where "s\<^sub>2_from = fst \<circ> snd"
  define p_from :: "f2_space \<Rightarrow> nat" where "p_from = fst \<circ> snd \<circ> snd"
  define h_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int set list)" where "h_from = fst \<circ> snd \<circ> snd \<circ> snd"
  define sketch_from :: "f2_space \<Rightarrow> (nat \<times> nat \<Rightarrow> int)" where "sketch_from = snd \<circ> snd \<circ> snd \<circ> snd"

  have p_prime: "Factorial_Ring.prime p" 
    apply (simp add:p_def) 
    using find_prime_above_is_prime by blast

  have p_ge_3: "p \<ge> 3"
    apply (simp add:p_def)
    by (meson find_prime_above_lower_bound dual_order.trans max.cobounded2)

  hence p_ge_2: "p > 2" by simp

  hence p_sq_ne_1: "(real p)^2 \<noteq> 1" 
    by (metis Num.of_nat_simps(2) nat_1 nat_one_as_int nat_power_eq_Suc_0_iff not_numeral_less_one of_nat_eq_iff of_nat_power zero_neq_numeral)

  have p_ge_0: "p > 0" using p_ge_2 by simp

  have fin_omega_2: "finite (set_pmf ( pmf_of_set (bounded_degree_polynomials (ZFact (int p)) 4)))"
    by (metis fin_bounded_degree_polynomials[OF p_ge_0] ne_bounded_degree_polynomials set_pmf_of_set)

  have fin_omega_1: "finite (set_pmf \<Omega>\<^sub>0)"
    apply (simp add:\<Omega>\<^sub>0_def set_prod_pmf)
    apply (rule finite_PiE, simp)
    by (metis fin_omega_2)

  have xs_le_p: "\<And>x. x \<in> set xs \<Longrightarrow> x < p" 
    apply (rule order_less_le_trans[where y="n"], metis assms(3))
    apply (simp add:p_def) 
    by (meson find_prime_above_lower_bound max.boundedE)

  have fin_poly': "finite (bounded_degree_polynomials (ZFact (int p)) 4)"
    apply (rule fin_bounded_degree_polynomials)
    using p_ge_3 by auto

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

  define f2 where "f2 = (\<lambda>x. \<lambda>i\<in>{0..<s\<^sub>2}. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. f3 x i\<^sub>1 i) / (((real p)\<^sup>2 - 1) * real s\<^sub>1))"
  
  have f2_var'': "\<And>i. i < s\<^sub>2 \<Longrightarrow> prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / 3"
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    have b: "prob_space.indep_vars (measure_pmf \<Omega>\<^sub>0) (\<lambda>_. borel) (\<lambda>i\<^sub>1 x. f3 x i\<^sub>1 i) {0..<s\<^sub>1}"
      apply (simp add:\<Omega>\<^sub>0_def, rule indep_vars_restrict_intro [where f="\<lambda>j. {(j,i)}"])
      using a f3_def disjoint_family_on_def s1_nonzero s2_nonzero by auto

    have "prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = (\<Sum>j = 0..<s\<^sub>1. prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f3 \<omega> j i)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
      apply (simp add: a f2_def del:Bochner_Integration.integral_divide_zero)
      apply (subst prob_space.variance_divide[OF prob_space_measure_pmf])
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
      apply (subst prob_space.var_sum_all_indep[OF prob_space_measure_pmf])
          apply (simp)
         apply (simp)
        apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
       apply (metis b)
      by simp
    also have "... \<le> (\<Sum>j = 0..<s\<^sub>1. 2*(real_of_rat (f2_value xs)^2) * ((real p)\<^sup>2-1)\<^sup>2) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
      apply (rule divide_right_mono)
       apply (rule sum_mono)
       apply (simp add:f3_def \<Omega>\<^sub>0_def)
       apply (subst variance_prod_pmf_slice, simp add:a, simp)
       apply (rule integrable_measure_pmf_finite[OF fin_omega_2])
       apply (rule var_f2_o[OF p_prime p_ge_2 xs_le_p], simp)
      by simp
    also have "... = 2 * (real_of_rat (f2_value xs)^2) / real s\<^sub>1"
      apply (simp)
      apply (subst frac_eq_eq, simp add:s1_nonzero, metis p_sq_ne_1, simp add:s1_nonzero)
      by (simp add:power2_eq_square)
    also have "... \<le> 2 * (real_of_rat (f2_value xs)^2) / (6 / (real_of_rat \<delta>)\<^sup>2)"
      apply (rule divide_left_mono)
      apply (simp add:s\<^sub>1_def) 
        apply (metis (mono_tags, opaque_lifting) of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power real_nat_ceiling_ge)
       apply simp
      apply (rule mult_pos_pos)
      using s1_nonzero apply simp
      using assms(2) by simp
    also have "... = (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / 3"
      by (simp add:of_rat_mult algebra_simps)
    finally show "prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) \<le> (real_of_rat (\<delta> * f2_value xs))\<^sup>2 / 3"
      by simp
  qed

  have f2_exp'': "\<And>i. i < s\<^sub>2 \<Longrightarrow> prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = real_of_rat (f2_value xs)"
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    have "prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = (\<Sum>j = 0..<s\<^sub>1. prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f3 \<omega> j i)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)"
      apply (simp add: a f2_def)
      apply (subst Bochner_Integration.integral_sum)
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
      by simp
    also have "... = (\<Sum>j = 0..<s\<^sub>1. real_of_rat (f2_value xs) * ((real p)\<^sup>2-1)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)"
      apply (rule arg_cong2[where f="(/)"])
       apply (rule sum.cong, simp)
       apply (simp add:f3_def \<Omega>\<^sub>0_def)
       apply (subst integral_prod_pmf_slice, simp, simp add:a)
        apply (rule integrable_measure_pmf_finite[OF fin_omega_2])
       apply (subst exp_f2_o[OF p_prime p_ge_2 xs_le_p], simp, simp)
      by simp
    also have "... =  real_of_rat (f2_value xs)"
      by (simp add:s1_nonzero p_sq_ne_1)
    finally show " prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = real_of_rat (f2_value xs)"
      by simp
  qed

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
     apply simp
    by simp

  have median_bound_3: " - (18 * ln (real_of_rat \<epsilon>)) \<le> real s\<^sub>2"
    apply (simp add:s\<^sub>2_def)
    using of_nat_ceiling by blast

  have median_bound_4: "\<And>i. i < s\<^sub>2 \<Longrightarrow>
           \<P>(\<omega> in \<Omega>\<^sub>0. real_of_rat (\<delta> * f2_value xs) \<le> \<bar>f2 \<omega> i - real_of_rat (f2_value xs)\<bar>) \<le> 1/3"
    (is "\<And>i. _ \<Longrightarrow> ?lhs i \<le> _")
  proof -
    fix i
    assume a: "i < s\<^sub>2"
    define var where  "var = prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i)"
    have "real_of_rat (f2_value xs) = prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i)"
      using f2_exp'' a by metis
    moreover have "0 < real_of_rat (\<delta> * f2_value xs)"
      using assms(2) f2_value_nonzero by simp
    moreover have "integrable \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i^2)"
      by (rule integrable_measure_pmf_finite[OF fin_omega_1])
    moreover have "(\<lambda>\<omega>. f2 \<omega> i) \<in> borel_measurable \<Omega>\<^sub>0"
      by (simp add:\<Omega>\<^sub>0_def)
    ultimately have "?lhs i \<le> var / (real_of_rat (\<delta> * f2_value xs))\<^sup>2"
      using prob_space.Chebyshev_inequality[where M="\<Omega>\<^sub>0" and a="real_of_rat (\<delta> * f2_value xs)"
          and f="\<lambda>\<omega>. f2 \<omega> i",simplified] assms(2) prob_space_measure_pmf[where p="\<Omega>\<^sub>0"] f2_value_nonzero
      by (simp add:var_def)
    also  have "... \<le> 1/3" (is ?ths)
      apply (subst pos_divide_le_eq )
      using f2_value_nonzero assms(2) apply simp
      apply (simp add:var_def)
      using f2_var'' a by fastforce
    finally show "?lhs i \<le> 1/3"
      by blast
  qed
  show ?thesis
    apply (simp add: distr' e real_f f'_def g_def \<Omega>\<^sub>0_def[symmetric])
    apply (rule prob_space.median_bound_3[where M="\<Omega>\<^sub>0" and \<epsilon>="real_of_rat \<epsilon>" and X="(\<lambda>i \<omega>. f2 \<omega> i)", simplified])
         apply (metis prob_space_measure_pmf)
        apply (metis assms(1))
       apply (metis assms(1))
      apply (metis median_bound_2')
     apply (metis median_bound_3)
    using  median_bound_4 by simp
qed

fun f2_space_usage :: "(nat \<times> nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f2_space_usage (n, m, \<epsilon>, \<delta>) = (
    let s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2 \<rceil> in
    let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil> in 
    5 +
    2 * log 2 (1 + s\<^sub>1) +
    2 * log 2 (1 + s\<^sub>2) +
    2 * log 2 (4 + 2 * real n) +
    s\<^sub>1 * s\<^sub>2 * (13 + 8 * log 2 (4 + 2 * real n) + 2 * log 2 (real m * (4 + 2 * real n) + 1 )))"

theorem f2_space_usage:
  assumes "\<epsilon> > 0 \<and> \<epsilon> < 1"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  defines "sketch \<equiv> fold (\<lambda>x state. state \<bind> f2_update x) xs (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in sketch. bit_count (encode_state \<omega>) \<le> f2_space_usage (n, length xs, \<epsilon>, \<delta>)"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"
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
       \<le> ereal (f2_space_usage (n, length xs, \<epsilon>, \<delta>))"
  proof -
    fix y
    assume a_1:"y \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (ZFact (int p)) 4"

    have a_2: "y \<in> extensional ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})" using a_1  PiE_iff by blast

    have a_3: "\<And>x. x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2}) \<Longrightarrow> bit_count (list\<^sub>S (zfact\<^sub>S p) x) 
      \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
    proof -
      fix x 
      assume a_5: "x \<in> y ` ({0..<s\<^sub>1} \<times> {0..<s\<^sub>2})"
      have "bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le> ereal ( real 4 * (2 * log 2 (real p) + 2) + 1)"
        apply (rule bounded_degree_polynomial_bit_count[OF p_ge_0])
        using a_1 a_5 by blast
      also have "... \<le> ereal (real 4 * (2 * log 2 (3 + 2 * real n) + 2) + 1)"
        apply simp
        apply (subst log_le_cancel_iff, simp, simp add:p_ge_0, simp)
        using p_le_n by simp
      also have "... \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by simp
      finally show "bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
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
    also have "... = ereal (f2_space_usage (n, length xs, \<epsilon>, \<delta>))"
      by (simp add:distrib_left[symmetric] s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
    finally show "bit_count (encode_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}.
      sum_list (map (eval_hash_function p (y i)) xs)))
       \<le> ereal (f2_space_usage (n, length xs, \<epsilon>, \<delta>))" by blast
  qed

  show ?thesis
    apply (subst AE_measure_pmf_iff)
    apply (subst sketch_def)
    apply (subst f2_alg_sketch[OF assms(1) assms(2), where n="n" and xs="xs"])
    apply (simp add: s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] del:f2_space_usage.simps)
    apply (subst set_prod_pmf, simp)
    apply (simp add: PiE_iff  del:f2_space_usage.simps)
    apply (subst set_pmf_of_set, metis ne_bounded_degree_polynomials, metis fin_bounded_degree_polynomials[OF p_ge_0])
    by (metis a)
qed

theorem f2_asympotic_space_complexity:
  "f2_space_usage \<in> O[at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda> (n, m, \<epsilon>, \<delta>). 
  (ln (1 / of_rat \<epsilon>)) / (of_rat \<delta>)\<^sup>2 * (ln (real n) + ln (real m)))"
  (is "?lhs \<in> O[?evt](?rhs)")
proof -
  define c where "c=(9177::real)"

  have b:"\<And>n m \<epsilon> \<delta>.  n \<ge> 4  \<Longrightarrow> m \<ge> 1 \<Longrightarrow> (0 < \<epsilon> \<and> \<epsilon> < 1/3) \<Longrightarrow> (0 < \<delta> \<and> \<delta> < 1) \<Longrightarrow>
     abs (f2_space_usage  (n, m, \<epsilon>, \<delta>)) \<le> c * abs (?rhs  (n, m, \<epsilon>, \<delta>))"
  proof -
    fix n m \<epsilon> \<delta>
    assume n_ge_4: "n \<ge> (4::nat)"
    assume m_ge_1: "m \<ge> (1::nat)"
    assume eps_bound: "(0::rat) < \<epsilon> \<and> \<epsilon> < 1/3"
    assume delta_bound: "(0::rat) < \<delta> \<and> \<delta> < 1"
    define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
    define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"
    define s\<^sub>1' where "s\<^sub>1' = 7/ (real_of_rat \<delta>)\<^sup>2"
    define s\<^sub>2' where "s\<^sub>2' = 19 * ln (1 / real_of_rat  \<epsilon>)"

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

    have "s\<^sub>1 \<le> 6/ (real_of_rat \<delta>)\<^sup>2 + 1"
      apply (simp add:s\<^sub>1_def, subst of_nat_nat, simp)
       apply (rule order_less_le_trans[where y="0"], simp)
      using delta_bound apply simp
      by (metis (no_types, opaque_lifting) of_int_ceiling_le_add_one of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power)
    also have "... \<le> (6+1)/(real_of_rat \<delta>)\<^sup>2"
      apply (subst add_divide_distrib)
      apply (rule add_mono, simp)
      using delta_bound 
      by (simp add: power_le_one_iff)
    also have "... = s\<^sub>1'"
      by (simp add:s\<^sub>1'_def)
    finally have s1_le_s1': "s\<^sub>1 \<le> s\<^sub>1'"
      by blast

    have "s\<^sub>2 = real_of_int \<lceil>(18 * ln (1 / real_of_rat \<epsilon>))\<rceil> "
      apply (simp add:s\<^sub>2_def, subst of_nat_nat, simp)
       apply (rule order_less_le_trans[where y="0"], simp)
      using  eps_bound apply simp
       apply simp
      apply simp
      apply (rule arg_cong[where f="\<lambda>x. \<lceil>x\<rceil>"])
      using eps_bound by (simp add: ln_div)
    also have "... \<le> (18 * ln (1 / real_of_rat  \<epsilon>)) + 1"
      by (simp add:s\<^sub>2'_def)
    also have  "... \<le> (18+1) * ln (1 / real_of_rat \<epsilon>)"
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

    show "abs (f2_space_usage  (n, m, \<epsilon>, \<delta>)) \<le> c * abs (?rhs  (n, m, \<epsilon>, \<delta>))"
      apply (simp add:s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric])
      apply (subst abs_of_nonneg)
       using b_8 n_ge_1 m_ge_1 apply (auto intro!: add_nonneg_nonneg zero_le_log_cancel_iff mult_nonneg_nonneg)[1]
      apply (subst abs_of_nonneg)
       using n_ge_1 m_ge_1 \<epsilon>_inv_ge_1 apply (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)[1]
      by (metis b_1)
  qed

  have a:"eventually 
    (\<lambda>x. abs (f2_space_usage x) \<le> c * abs (?rhs x)) ?evt"
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
