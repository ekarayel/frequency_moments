section \<open>Frequency Moment $2$\<close>

theory Frequency_Moment_2
  imports Main Median_Method.Median Primes_Ext Encoding List_Ext 
    Universal_Hash_Families.Carter_Wegman_Hash_Family Frequency_Moments Landau_Ext
    Universal_Hash_Families.Field
    Equivalence_Relation_Enumeration.Equivalence_Relation_Enumeration Product_PMF_Ext
begin

text \<open>This section contains a formalization of the algorithm for the second frequency moment.
It is based on the algorithm described in \cite[\textsection 2.2]{alon1999}.
The only difference is that the algorithm is adapted to work with prime field of odd order, which
greatly reduces the implementation complexity.\<close>

fun f2_hash where
  "f2_hash p h k = (if even (ring.hash (mod_ring p) k h) then int p - 1 else - int p - 1)"

type_synonym f2_state = "nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> nat list) \<times> (nat \<times> nat \<Rightarrow> int)"

fun f2_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f2_state pmf" where
  "f2_init \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>;
      let p = find_prime_above (max n 3);
      h \<leftarrow> prod_pmf ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (mod_ring p) 4));
      return_pmf (s\<^sub>1, s\<^sub>2, p, h, (\<lambda>_ \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. (0 :: int)))
    }"

fun f2_update :: "nat \<Rightarrow> f2_state \<Rightarrow> f2_state pmf" where
  "f2_update x (s\<^sub>1, s\<^sub>2, p, h, sketch) = 
    return_pmf (s\<^sub>1, s\<^sub>2, p, h, \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. f2_hash p (h i) x + sketch i)"

fun f2_result :: "f2_state \<Rightarrow> rat pmf" where
  "f2_result (s\<^sub>1, s\<^sub>2, p, h, sketch) = 
    return_pmf (median s\<^sub>2 (\<lambda>i\<^sub>2 \<in> {..<s\<^sub>2}. 
      (\<Sum>i\<^sub>1\<in>{..<s\<^sub>1} . (rat_of_int (sketch (i\<^sub>1, i\<^sub>2)))\<^sup>2) / (((rat_of_nat p)\<^sup>2-1) * rat_of_nat s\<^sub>1)))"

context 
  fixes p :: nat
  assumes p_prime: "Factorial_Ring.prime p"
begin

interpretation carter_wegman_hash_family "mod_ring p" 4
  apply (rule carter_wegman_hash_familyI[OF mod_ring_is_field mod_ring_finite])
  using p_prime by auto

lemma f2_hash_exp:
  assumes "k < p"
  assumes "p > 2" 
  shows
    "expectation (\<lambda>\<omega>. real_of_int (f2_hash p \<omega> k) ^m) = 
     ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
proof -
  have g:"p > 0" using assms(1) prime_gt_0_nat by auto

  have "odd p" using p_prime prime_odd_nat assms by blast
  then obtain t where t_def: "p=2*t+1" 
    using oddE by blast

  have zero_le_4: "0 < (4::nat)" by simp

  have "card ({k. even k} \<inter> {..<p}) = card ((\<lambda>x. 2*x) ` {..t})"
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym)
    apply (rule subsetI)
     apply (simp add:t_def)
     apply (metis evenE Suc_1 atMost_iff image_eqI less_Suc_eq_le mult_less_cancel1 not_less zero_less_Suc)
    by (rule image_subsetI, simp add:t_def)
  also have "... = card {..t}" 
    apply (rule card_image)
    by (simp add: inj_on_mult)
  also have "... =  t+1" by simp
  finally have c_11: "card ({k. even k} \<inter> {..<p}) = t+1" by simp
  hence c_1: "card ({k. even k} \<inter> {..<p}) * 2 = (p+1)" by (simp add:t_def)

  have "p = card {..<p}" by simp
  also have "... = card (({k. odd k} \<inter> {..<p}) \<union> ({k. even k} \<inter> {..<p}))" 
    apply (rule arg_cong[where f="card"])
    by (rule order_antisym, rule subsetI, simp, rule subsetI, simp, blast)
  also have "... = card ({k. odd k} \<inter> {..<p}) +  card ({k. even k} \<inter> {..<p})"
    by (rule card_Un_disjoint, simp, simp, blast)
  also have "... = card ({k. odd k} \<inter> {..<p}) + t+1"
    by (simp add:c_11)
  finally have "p = card ({k. odd k} \<inter> {..<p}) + t+1"
    by simp
  hence c_2: "card ({k. odd k} \<inter> {..<p}) * 2 = (p-1)" 
    by (simp add:t_def)

  have d_1: "prob {\<omega>. hash k \<omega> \<in> Collect even} = (real p + 1)/(2*real p)"
    apply (subst prob_range, simp add:mod_ring_carr assms)
    apply (subst frac_eq_eq, simp add:mod_ring_def g, simp add:g)
    using c_1 by (simp add:mod_ring_def lessThan_atLeast0) 
  have d_2: "prob {\<omega>. hash k \<omega> \<in> Collect odd} = (real p - 1)/(2*real p)"
    apply (subst prob_range, simp add:mod_ring_carr assms)
    apply (subst frac_eq_eq, simp add:mod_ring_def g, simp add:g)
    using c_2 by (simp add:mod_ring_def lessThan_atLeast0 t_def)

  have "expectation (\<lambda>x. real_of_int (f2_hash p x k) ^ m) =
    expectation (\<lambda>\<omega>. indicator {\<omega>. even (hash k \<omega>)} \<omega> * (real p - 1)^m + 
      indicator {\<omega>. odd (hash k \<omega>)} \<omega> * (-real p - 1)^m)" 
    by (rule Bochner_Integration.integral_cong, simp, simp)
  also have "... = 
     prob {\<omega>. hash  k \<omega> \<in> Collect even}  * (real p - 1) ^ m  + 
     prob {\<omega>. hash  k \<omega> \<in> Collect odd}  * (-real p - 1) ^ m "
    by (simp add: integrable_measure_pmf_finite M_def)
  also have "... = (real p + 1) * (real p - 1) ^ m / (2 * real p) + (real p - 1) * (- real p - 1) ^ m / (2 * real p)"
    by (subst d_1, subst d_2, simp)
  also have "... =  
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
    by (simp add:add_divide_distrib ac_simps)
  finally show "expectation (\<lambda>x. real_of_int (f2_hash p x k) ^ m) = 
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)" by simp
qed

lemma 
  assumes "p > 2"
  assumes "\<And>a. a \<in> set as \<Longrightarrow> a < p"
  defines "f \<equiv> (\<lambda>\<omega>. real_of_int (sum_list (map (f2_hash p \<omega>) as))^2)"
  shows var_f2:"variance f \<le> 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2" (is "?A")
  and exp_f2:"expectation f = real_of_rat (F 2 as) * ((real p)\<^sup>2-1)" (is "?B")
proof -
  define h where "h = (\<lambda>\<omega> x. real_of_int (f2_hash p \<omega> x))"
  define c where "c = (\<lambda>x. real (count_list as x))"
  define r where "r = (\<lambda>(m::nat). ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p))"
  define h_prod where "h_prod = (\<lambda>as \<omega>. prod_list (map (h \<omega>) as))" 

  define exp_h_prod :: "nat list \<Rightarrow> real" where "exp_h_prod = (\<lambda>as. (\<Prod>i \<in> set as. r (count_list as i)))"

  interpret prob_space M
    using prob_space_measure_pmf M_def by auto

  have f_eq: "f = (\<lambda>\<omega>. (\<Sum>x \<in> set as. c x * h \<omega> x)^2)"
    by (simp add:f_def c_def h_def sum_list_eval del:f2_hash.simps)

  have p_ge_0: "p > 0" using assms by simp

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
    using assms 
       apply (metis p_prime linorder_not_less num_double numeral_mult of_nat_power power2_eq_square power2_nat_le_eq_le prime_ge_2_nat real_of_nat_less_numeral_iff)
    by simp+

  have exp_h_prod_elim: "exp_h_prod = (\<lambda>as. prod_list (map (r \<circ> count_list as) (remdups as)))" 
    apply (simp add:exp_h_prod_def)
    apply (rule ext)
    apply (subst prod.set_conv_list[symmetric])
    by (rule prod.cong, simp, simp add:comp_def)

  have exp_h_prod: "\<And>x. set x \<subseteq> set as \<Longrightarrow> length x \<le> 4 \<Longrightarrow> expectation (h_prod x) = exp_h_prod x"
  proof -
    fix x 
    assume "set x \<subseteq> set as"
    hence x_sub_p: "set x \<subseteq> {..<p}" using assms(2) atLeastLessThan_iff by blast
    hence x_le_p: "\<And>k. k \<in> set x \<Longrightarrow> k < p" by auto
    assume "length x \<le> 4"
    hence card_x: "card (set x) \<le> 4" using card_length dual_order.trans by blast

    have x_sub_p': "set x \<subseteq> carrier (mod_ring p) " apply (simp add:mod_ring_def)
      using x_sub_p by presburger
    have "expectation (h_prod x) = expectation (\<lambda>\<omega>. \<Prod> i \<in> set x. h \<omega> i^(count_list x i))"
      apply (rule arg_cong[where f="expectation"])
      by (simp add:h_prod_def prod_list_eval)
    also have "... = (\<Prod>i \<in> set x. expectation (\<lambda>\<omega>. h \<omega> i^(count_list x i)))"
      apply (subst indep_vars_lebesgue_integral, simp)
        apply (simp add:h_def)
        apply (rule indep_vars_compose2[where X="hash" and M'=" (\<lambda>_. discrete)"])
         using k_wise_indep_vars_subset[OF k_wise_indep] card_x x_sub_p' assms(1)
         apply (simp add:M_def[symmetric])
         by simp+
    also have "... = (\<Prod>i \<in> set x. r (count_list x i))"
      apply (rule prod.cong, simp)
      using f2_hash_exp[OF x_le_p assms(1)] 
      by (simp add:h_def r_def M_def[symmetric] del:f2_hash.simps)
    also have "... = exp_h_prod x"
      by (simp add:exp_h_prod_def)
    finally show "expectation (h_prod x) = exp_h_prod x" by simp
  qed

  have "\<And>x y. kernel_of x = kernel_of y \<Longrightarrow> exp_h_prod x = exp_h_prod y" 
  proof -
    fix x y :: "nat list"
    assume a:"kernel_of x = kernel_of y"
    then obtain f where b:"bij_betw f (set x) (set y)" and c:"\<And>z. z \<in> set x \<Longrightarrow> count_list x z = count_list y (f z)"
      using kernel_of_eq_imp_bij by blast
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

  hence exp_h_prod_cong: "\<And>p x. of_bool (kernel_of x = kernel_of p) * exp_h_prod p = 
    of_bool (kernel_of x = kernel_of p) * exp_h_prod x" 
    by (metis (full_types) of_bool_eq_0_iff vector_space_over_itself.scale_zero_left)

  have c:"\<And>(xs :: nat list) n r. length xs = n \<Longrightarrow> 
    (\<Sum>p\<leftarrow>enum_rgfs n. of_bool (kernel_of xs = kernel_of p) * r) = (r::real)"
  proof -
    fix xs :: "nat list"
    fix n 
    fix r :: real
    assume a:"length xs = n"

    have "(\<Sum>p\<leftarrow>enum_rgfs n. of_bool (kernel_of xs = kernel_of p) * 1) = (1::real)"
      using equiv_rels_2[OF a[symmetric]] by (simp add:equiv_rels_def comp_def) 
    thus "(\<Sum>p\<leftarrow>enum_rgfs n. of_bool (kernel_of xs = kernel_of p) * r) = (r::real)" 
      by (simp add:sum_list_mult_const)
  qed

  have "expectation f = (\<Sum>i\<in>set as. (\<Sum>j\<in>set as. c i * c j * expectation (h_prod [i,j])))"
    by (simp add:f_eq h_prod_def power2_eq_square sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum algebra_simps)
  also have "... = (\<Sum>i\<in>set as. (\<Sum>j\<in>set as. c i * c j * exp_h_prod [i,j]))"
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (subst exp_h_prod, simp, simp)
    by simp
  also have "... = (\<Sum>i \<in> set as. (\<Sum>j \<in> set as.  
    c i * c j * (sum_list (map (\<lambda>p. of_bool (kernel_of [i,j] = kernel_of p) * exp_h_prod p) (enum_rgfs 2)))))"
    apply (subst exp_h_prod_cong)
    by (subst c, simp+) 
  also have "... = (\<Sum>i\<in>set as. c i * c i * r 2)"
    apply (simp add:numeral_eq_Suc exp_h_prod_elim r_one) 
    by (simp add: kernel_of_eq All_less_Suc numeral_eq_Suc distrib_left sum.distrib sum_collapse)
  also have "... = real_of_rat (F 2 as) * ((real p)^2-1)"
    apply (subst sum_distrib_right[symmetric])
    by (simp add:c_def F_def power2_eq_square of_rat_sum of_rat_mult r_two)
  finally show b:?B by simp

  have "expectation (\<lambda>x. (f x)\<^sup>2) = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as.
    c i1 * c i2 * c i3 * c i4 * expectation (h_prod [i1, i2, i3, i4])))))"
    apply (simp add:f_eq h_prod_def power4_eq_xxxx sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum)
    by (simp add:algebra_simps)
  also have "... = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as. 
    c i1 * c i2 * c i3 * c i4 * exp_h_prod [i1,i2,i3,i4]))))"
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (rule sum.cong, simp)
    apply (subst exp_h_prod, simp, simp)
    by simp
  also have "... = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as. 
    c i1 * c i2 * c i3 * c i4 * 
    (sum_list (map (\<lambda>p. of_bool (kernel_of [i1,i2,i3,i4] = kernel_of p) * exp_h_prod p) (enum_rgfs 4)))))))"
    apply (subst exp_h_prod_cong) 
    by (subst c, simp+) 
  also have "... = 
    3 * (\<Sum>i \<in> set as. (\<Sum>j \<in> set as. c i^2 * c j^2 * r 2 * r 2)) + ((\<Sum> i \<in> set as. c i^4 * r 4) - 3 *  (\<Sum> i \<in> set as. c i ^ 4 * r 2 * r 2))"
    apply (simp add: numeral_eq_Suc exp_h_prod_elim r_one) 
    apply (simp add: kernel_of_eq All_less_Suc numeral_eq_Suc distrib_left sum.distrib sum_collapse neq_commute)
    apply (simp add: algebra_simps sum_subtractf sum_collapse)
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = 3 * (\<Sum>i \<in> set as. c i^2 * r 2)^2 + (\<Sum> i \<in> set as. c i ^ 4 * (r 4 - 3 * r 2 * r 2))"
    apply (rule arg_cong2[where f="(+)"])
     apply (simp add:power2_eq_square sum_distrib_left sum_distrib_right algebra_simps)
    apply (simp add:sum_distrib_left sum_subtractf[symmetric])
    apply (rule sum.cong, simp)
    by (simp add:algebra_simps)
  also have "... \<le> 3 * (\<Sum>i \<in> set as. c i^2)^2 * (r 2)^2 +  (\<Sum>i \<in> set as. c i ^ 4 * 0)"
    apply (rule add_mono)
     apply (simp add:power_mult_distrib sum_distrib_right[symmetric])
    apply (rule sum_mono, rule mult_left_mono)
    using r_four_est by simp+
  also have "... = 3 * (real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2" 
    by (simp add:c_def r_two F_def of_rat_sum of_rat_power)

  finally have v_1: "expectation (\<lambda>x. (f x)\<^sup>2) \<le> 3 * (real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    by simp
  
  show "variance f \<le> 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    apply (simp add: variance_eq, subst b)
    apply (simp add:power_mult_distrib)
    using v_1 by simp
qed

end

lemma f2_alg_sketch:
  fixes n :: nat
  fixes as :: "nat list"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  defines "s\<^sub>1 \<equiv> nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
  defines "s\<^sub>2 \<equiv> nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"
  defines "p \<equiv> find_prime_above (max n 3)"
  defines "sketch \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
  defines "\<Omega> \<equiv> prod_pmf ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (mod_ring p) 4))" 
  shows "sketch = \<Omega> \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (h i)) as)))"
proof -
  define ys where "ys = rev as"
  have b:"sketch = foldr (\<lambda>x state. state \<bind> f2_update x) ys (f2_init \<delta> \<epsilon> n)"
    by (simp add: foldr_conv_fold ys_def sketch_def)
  also have "... = \<Omega> \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (h i)) ys)))"
  proof (induction ys)
    case Nil
    then show ?case 
      by (simp add:s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] \<Omega>_def restrict_def) 
  next
    case (Cons a as)
    have a:"f2_update a = (\<lambda>x. f2_update a (fst x, fst (snd x), fst (snd (snd x)), fst (snd (snd (snd x))), 
        snd (snd (snd (snd x)))))" by simp
    show ?case
      using Cons apply (simp del:f2_hash.simps f2_init.simps)
      apply (subst a)
      apply (subst bind_assoc_pmf)
      apply (subst bind_return_pmf)
      by (simp add:restrict_def del:f2_hash.simps f2_init.simps cong:restrict_cong)
  qed
  also have "... = \<Omega> \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (h i)) as)))"
    by (simp add: ys_def rev_map[symmetric])
  finally show ?thesis by auto
qed

theorem f2_alg_correct:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n) \<bind> f2_result"
  shows "\<P>(\<omega> in measure_pmf \<Omega>. \<bar>\<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as) \<ge> 1-of_rat \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"
  define p where "p = find_prime_above (max n 3)"
  have p_prime: "Factorial_Ring.prime p" 
    apply (simp add:p_def) 
    using find_prime_above_is_prime by blast

  interpret carter_wegman_hash_family "mod_ring p" 4
    apply (rule carter_wegman_hash_familyI[OF mod_ring_is_field mod_ring_finite])
    using p_prime by auto

  define \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = prod_pmf ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set space)"

  define s\<^sub>1_from :: "f2_state \<Rightarrow> nat" where "s\<^sub>1_from = fst"
  define s\<^sub>2_from :: "f2_state \<Rightarrow> nat" where "s\<^sub>2_from = fst \<circ> snd"
  define p_from :: "f2_state \<Rightarrow> nat" where "p_from = fst \<circ> snd \<circ> snd"
  define h_from :: "f2_state \<Rightarrow> (nat \<times> nat \<Rightarrow> nat list)" where "h_from = fst \<circ> snd \<circ> snd \<circ> snd"
  define sketch_from :: "f2_state \<Rightarrow> (nat \<times> nat \<Rightarrow> int)" where "sketch_from = snd \<circ> snd \<circ> snd \<circ> snd"

  have p_ge_3: "p \<ge> 3"
    apply (simp add:p_def)
    by (meson find_prime_above_lower_bound dual_order.trans max.cobounded2)

  hence p_ge_2: "p > 2" by simp

  hence p_sq_ne_1: "(real p)^2 \<noteq> 1" 
    by (metis Num.of_nat_simps(2) nat_1 nat_one_as_int nat_power_eq_Suc_0_iff not_numeral_less_one of_nat_eq_iff of_nat_power zero_neq_numeral)

  have p_ge_0: "p > 0" using p_ge_2 by simp

  have fin_omega_2: "finite (set_pmf ( pmf_of_set (space)))" by simp

  have fin_omega_1: "finite (set_pmf \<Omega>\<^sub>0)"
    apply (simp add:\<Omega>\<^sub>0_def set_prod_pmf)
    by (rule finite_PiE, simp, simp)

  have as_le_p: "\<And>x. x \<in> set as \<Longrightarrow> x < p" 
    apply (rule order_less_le_trans[where y="n"])
     using assms(3) atLeastLessThan_iff apply blast
    apply (simp add:p_def) 
    by (meson find_prime_above_lower_bound max.boundedE)

  have fin_poly': "finite (bounded_degree_polynomials (mod_ring p) 4)"
    using fin_degree_bounded mod_ring_finite by auto

  have s2_nonzero: "s\<^sub>2 > 0"
    using assms by (simp add:s\<^sub>2_def)

  have s1_nonzero: "s\<^sub>1 > 0"  
    using assms by (simp add:s\<^sub>1_def)

  have split_f2_space: "\<And>x. x = (s\<^sub>1_from x, s\<^sub>2_from x, p_from x, h_from x, sketch_from x)"
    by (simp add:prod_eq_iff s\<^sub>1_from_def s\<^sub>2_from_def p_from_def h_from_def sketch_from_def)

  have f2_result_conv: "f2_result = (\<lambda>x. f2_result (s\<^sub>1_from x, s\<^sub>2_from x, p_from x, h_from x, sketch_from x))"
    by (simp add:split_f2_space[symmetric] del:f2_result.simps)

  define f where "f = (\<lambda>x. median s\<^sub>2
           (\<lambda>i\<in>{..<s\<^sub>2}.
               (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (rat_of_int (sum_list (map (f2_hash p (x (i\<^sub>1, i))) as)))\<^sup>2) /
               (((rat_of_nat p)\<^sup>2 - 1) * rat_of_nat s\<^sub>1)))"

  define f3 where 
    "f3 = (\<lambda>x (i\<^sub>1::nat) (i\<^sub>2::nat). (real_of_int (sum_list (map (f2_hash p (x (i\<^sub>1, i\<^sub>2))) as)))\<^sup>2)"

  define f2 where "f2 = (\<lambda>x. \<lambda>i\<in>{..<s\<^sub>2}. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. f3 x i\<^sub>1 i) / (((real p)\<^sup>2 - 1) * real s\<^sub>1))"
  
  have f2_var'': "\<And>i. i < s\<^sub>2 \<Longrightarrow> prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) \<le> (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    have b: "prob_space.indep_vars (measure_pmf \<Omega>\<^sub>0) (\<lambda>_. borel) (\<lambda>i\<^sub>1 x. f3 x i\<^sub>1 i) {..<s\<^sub>1}"
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
       apply (metis lessThan_atLeast0 b)
      by simp
    also have "... \<le> (\<Sum>j = 0..<s\<^sub>1. 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
      apply (rule divide_right_mono)
       apply (rule sum_mono)
       apply (simp add:f3_def \<Omega>\<^sub>0_def)
       apply (subst variance_prod_pmf_slice, simp add:a, simp)
        apply (rule integrable_measure_pmf_finite[OF fin_omega_2])
      using var_f2[OF p_prime p_ge_2 as_le_p] by (simp add:M_def, simp)
    also have "... = 2 * (real_of_rat (F 2 as)^2) / real s\<^sub>1"
      apply (simp)
      apply (subst frac_eq_eq, simp add:s1_nonzero, metis p_sq_ne_1, simp add:s1_nonzero)
      by (simp add:power2_eq_square)
    also have "... \<le> 2 * (real_of_rat (F 2 as)^2) / (6 / (real_of_rat \<delta>)\<^sup>2)"
      apply (rule divide_left_mono)
      apply (simp add:s\<^sub>1_def) 
        apply (metis (mono_tags, opaque_lifting) of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power real_nat_ceiling_ge)
       apply simp
      apply (rule mult_pos_pos)
      using s1_nonzero apply simp
      using assms(2) by simp
    also have "... = (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
      by (simp add:of_rat_mult algebra_simps)
    finally show "prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) \<le> (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
      by simp
  qed

  have f2_exp'': "\<And>i. i < s\<^sub>2 \<Longrightarrow> prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = real_of_rat (F 2 as)"
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    have "prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = (\<Sum>j = 0..<s\<^sub>1. prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f3 \<omega> j i)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)"
      apply (simp add: a f2_def)
      apply (subst Bochner_Integration.integral_sum)
       apply (rule integrable_measure_pmf_finite[OF fin_omega_1])
      by simp
    also have "... = (\<Sum>j = 0..<s\<^sub>1. real_of_rat (F 2 as) * ((real p)\<^sup>2-1)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)"
      apply (rule arg_cong2[where f="(/)"])
       apply (rule sum.cong, simp)
       apply (simp add:f3_def \<Omega>\<^sub>0_def)
       apply (subst integral_prod_pmf_slice, simp, simp add:a)
        apply (rule integrable_measure_pmf_finite[OF fin_omega_2])
      apply (subst M_def[symmetric])
       apply (subst exp_f2[OF p_prime p_ge_2 as_le_p], simp, simp)
      by simp
    also have "... =  real_of_rat (F 2 as)"
      by (simp add:s1_nonzero p_sq_ne_1)
    finally show " prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i) = real_of_rat (F 2 as)"
      by simp
  qed

  define f' where "f' = (\<lambda>x. median s\<^sub>2 (f2 x))"
  have real_f: "\<And>x. real_of_rat (f x) = f' x"
    using s2_nonzero apply (simp add:f'_def f2_def f3_def f_def median_rat median_restrict lessThan_atLeast0 cong:restrict_cong)
    by (simp add:of_rat_divide of_rat_sum of_rat_power of_rat_mult of_rat_diff)

  have distr': "\<Omega> = map_pmf f (prod_pmf  ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (mod_ring p) 4)))"
    using f2_alg_sketch[OF assms(1) assms(2), where as="as" and n="n"]
    apply (simp add:\<Omega>_def lessThan_atLeast0 Let_def s\<^sub>1_def [symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
    apply (subst bind_assoc_pmf)
    apply (subst bind_return_pmf)
    apply (subst f2_result_conv, simp)
    apply (simp add:s\<^sub>2_from_def s\<^sub>1_from_def p_from_def h_from_def sketch_from_def lessThan_atLeast0 cong:restrict_cong)
    by (simp add:map_pmf_def[symmetric] f_def lessThan_atLeast0)

  define g where "g = (\<lambda>\<omega>. real_of_rat (\<delta> * F 2 as) \<ge> \<bar>\<omega> - real_of_rat (F 2 as)\<bar>)"
  have e: "{\<omega>. \<delta> * F 2 as \<ge> \<bar>\<omega> - F 2 as\<bar>} = {\<omega>. (g \<circ> real_of_rat) \<omega>}"
    apply (simp add:g_def)
    apply (rule order_antisym, rule subsetI, simp) 
    apply (metis abs_of_rat of_rat_diff of_rat_less_eq)
    apply (rule subsetI, simp)
    by (metis abs_of_rat of_rat_diff of_rat_less_eq)

  have median_bound_2': "prob_space.indep_vars \<Omega>\<^sub>0 (\<lambda>_. borel) (\<lambda>i \<omega>. f2 \<omega> i) {..<s\<^sub>2}"
    apply (subst \<Omega>\<^sub>0_def)
    apply (rule indep_vars_restrict_intro [where f="\<lambda>j. {..<s\<^sub>1} \<times> {j}"])
         apply (simp add:f2_def f3_def)
        apply (simp add:disjoint_family_on_def, fastforce)
       using s2_nonzero apply blast
      apply (rule subsetI, simp add:mem_Times_iff)
     apply simp
    by simp

  have median_bound_3: " - (18 * ln (real_of_rat \<epsilon>)) \<le> real s\<^sub>2"
    apply (simp add:s\<^sub>2_def)
    using of_nat_ceiling by blast

  have median_bound_4: "\<And>i. i < s\<^sub>2 \<Longrightarrow>
    \<P>(\<omega> in \<Omega>\<^sub>0. real_of_rat (\<delta> * F 2 as) < \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>) \<le> 1/3"
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    show "\<P>(\<omega> in \<Omega>\<^sub>0. real_of_rat (\<delta> * F 2 as) < \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>) \<le> 1/3"
    proof (cases "as = []")
      case True
      then show ?thesis using a by (simp add:f2_def F_def f3_def)
    next
      case False
      have F_2_nonzero: "F 2 as > 0" using F_gr_0[OF False] by simp

      define var where  "var = prob_space.variance \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i)"
      have b_1: "real_of_rat (F 2 as) = prob_space.expectation \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i)"
        using f2_exp'' a by metis
      have b_2: "0 < real_of_rat (\<delta> * F 2 as)"
        using assms(2) F_2_nonzero by simp
      have b_3: "integrable \<Omega>\<^sub>0 (\<lambda>\<omega>. f2 \<omega> i^2)"
        by (rule integrable_measure_pmf_finite[OF fin_omega_1])
      have b_4: "(\<lambda>\<omega>. f2 \<omega> i) \<in> borel_measurable \<Omega>\<^sub>0"
        by (simp add:\<Omega>\<^sub>0_def)
      have "\<P>(\<omega> in \<Omega>\<^sub>0. real_of_rat (\<delta> * F 2 as) < \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>) \<le> 
          \<P>(\<omega> in \<Omega>\<^sub>0. real_of_rat (\<delta> * F 2 as) \<le> \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>)"
        by (rule measure_pmf.pmf_mono', simp, simp)
      also have "... \<le> var / (real_of_rat (\<delta> * F 2 as))\<^sup>2"
        using prob_space.Chebyshev_inequality[where M="\<Omega>\<^sub>0" and a="real_of_rat (\<delta> * F 2 as)"
            and f="\<lambda>\<omega>. f2 \<omega> i",simplified] assms(2) prob_space_measure_pmf[where p="\<Omega>\<^sub>0"] F_2_nonzero
          b_1 b_2 b_3 b_4 by (simp add:var_def)
      also  have "... \<le> 1/3" (is ?ths)
        apply (subst pos_divide_le_eq )
        using F_2_nonzero assms(2) apply simp
        apply (simp add:var_def)
        using f2_var'' a by fastforce
      finally show ?thesis
        by blast
    qed
  qed

  show ?thesis
    apply (simp add: distr' e real_f f'_def g_def \<Omega>\<^sub>0_def[symmetric] space_def[symmetric])
    apply (rule prob_space.median_bound_2[where M="\<Omega>\<^sub>0" and \<epsilon>="real_of_rat \<epsilon>" and X="(\<lambda>i \<omega>. f2 \<omega> i)", simplified])
        apply (metis prob_space_measure_pmf)
       using assms apply simp 
      apply (simp add: lessThan_atLeast0[symmetric] median_bound_2')
     apply (metis median_bound_3)
    using median_bound_4 by simp
qed

fun f2_space_usage :: "(nat \<times> nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f2_space_usage (n, m, \<epsilon>, \<delta>) = (
    let s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2 \<rceil> in
    let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil> in 
    5 +
    2 * log 2 (s\<^sub>1 + 1) +
    2 * log 2 (s\<^sub>2 + 1) +
    2 * log 2 (4 + 2 * real n) +
    s\<^sub>1 * s\<^sub>2 * (13 + 8 * log 2 (4 + 2 * real n) + 2 * log 2 (real m * (4 + 2 * real n) + 1 )))"

definition encode_f2_state :: "f2_state \<Rightarrow> bool list option" where
  "encode_f2_state = 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>1. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>s\<^sub>2. 
    N\<^sub>S \<times>\<^sub>D (\<lambda>p. 
    (List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S (list\<^sub>S N\<^sub>S)) \<times>\<^sub>S
    (List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S I\<^sub>S))))"

lemma "inj_on encode_f2_state (dom encode_f2_state)"
  apply (rule encoding_imp_inj)
  apply (simp add:encode_f2_state_def)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, metis nat_encoding)
  apply (rule dependent_encoding, rule encode_extensional, rule list_encoding, rule nat_encoding)
  by (metis encode_extensional int_encoding)

theorem f2_exact_space_usage:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_f2_state \<omega>) \<le> f2_space_usage (n, length as, \<epsilon>, \<delta>)"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"
  define p where "p = find_prime_above (max n 3)"

  have find_prime_above_3: "find_prime_above 3 = 3" 
    by (simp add:find_prime_above.simps)

  have "p \<ge> 2" using p_def find_prime_above_min by presburger
  hence p_ge_1: "p > 1" by simp
  interpret cring "mod_ring p"
    using mod_ring_is_cring[OF p_ge_1] by auto

  have p_ge_0: "p > 0" 
    by (metis find_prime_above_min p_def gr0I not_numeral_le_zero)
  have p_le_n: "p \<le> 2 * n + 3" 
    apply (cases "n \<le> 3")
    apply (simp add: p_def find_prime_above_3) 
    apply (simp add: p_def) 
    by (metis One_nat_def find_prime_above_upper_bound Suc_1 add_Suc_right linear not_less_eq_eq numeral_3_eq_3)

  have a: "\<And>y. y\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (mod_ring p) 4 \<Longrightarrow>
       bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. 
      sum_list (map (f2_hash p (y i)) as)))
       \<le> ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))"
  proof -
    fix y
    assume a_1:"y \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (mod_ring p) 4"

    have a_2: "y \<in> extensional ({..<s\<^sub>1} \<times> {..<s\<^sub>2})" using a_1  PiE_iff by blast

    have a_3: "\<And>x. x \<in> y ` ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) \<Longrightarrow> bit_count (list\<^sub>S N\<^sub>S x) 
      \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
    proof -
      fix x 
      assume a_5: "x \<in> y ` ({..<s\<^sub>1} \<times> {..<s\<^sub>2})"
      have "bit_count (list\<^sub>S N\<^sub>S x) \<le> ereal ( real 4 * (2 * log 2 (real p) + 2) + 1)"
        apply (rule bounded_degree_polynomial_bit_count[OF p_ge_0]) 
        using a_1 a_5 by blast
      also have "... \<le> ereal (real 4 * (2 * log 2 (3 + 2 * real n) + 2) + 1)"
        apply simp
        apply (subst log_le_cancel_iff, simp, simp add:p_ge_0, simp)
        using p_le_n by simp
      also have "... \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by simp
      finally show "bit_count (list\<^sub>S N\<^sub>S x) \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by blast
    qed

    have a_7: "\<And>x. 
      x \<in> (\<lambda>x. sum_list (map (f2_hash p (y x)) as)) ` ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) \<Longrightarrow>
         \<bar>x\<bar> \<le> (4 + 2 * int n) * int (length as)"
    proof -
      fix x
      assume "x \<in> (\<lambda>x. sum_list (map (f2_hash p (y x)) as)) ` ({..<s\<^sub>1} \<times> {..<s\<^sub>2})"
      then obtain i where "i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}" and x_def: "x = sum_list (map (f2_hash p (y i)) as)"
        by blast
      have "abs x \<le> sum_list (map abs (map (f2_hash p (y i)) as))"
        by (subst x_def, rule sum_list_abs)
      also have "... \<le> sum_list (map (\<lambda>_. (int p+1)) as)"
        apply (simp add:comp_def del:f2_hash.simps)
        apply (rule sum_list_mono)
        using p_ge_0 by simp 
      also have "... = int (length as) * (int p+1)"
        by (simp add: sum_list_triv)
      also have "... \<le> int (length as) * (4+2*(int n))"
        apply (rule mult_mono, simp)
        using p_le_n apply linarith
        by simp+
      finally show "abs x \<le>  (4 + 2 * int n) * int (length as)"
        by (simp add: mult.commute)
    qed
    
    have "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}.
      sum_list (map (f2_hash p (y i)) as)))
       \<le> ereal (2 * (log 2 (real s\<^sub>1 + 1)) + 1) 
       + (ereal (2 * (log 2 (real s\<^sub>2 + 1)) + 1)
       + (ereal (2 * (log 2 (1 + real (2*n+3))) + 1) 
       + ((ereal (real s\<^sub>1 * real s\<^sub>2) * (10 + 8 * log 2 (4 + 2 * real n)) + 1) 
       + (ereal (real s\<^sub>1 * real s\<^sub>2) * (3 + 2 * log 2 (real (length as) * (4 + 2 * real n) + 1) ) + 1))))"
      using a_2
      apply (simp add: encode_f2_state_def s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] 
         dependent_bit_count fun\<^sub>S_def lessThan_atLeast0
          del:  plus_ereal.simps of_nat_add)
      apply (rule add_mono, rule nat_bit_count)
      apply (rule add_mono, rule nat_bit_count)
      apply (rule add_mono, rule nat_bit_count_est, metis p_le_n)
      apply (rule add_mono)
       apply (rule list_bit_count_estI[where a="9 + 8 * log 2 (4 + 2 * real n)"], rule a_3, simp add:lessThan_atLeast0, simp add:lessThan_atLeast0)
      apply (rule list_bit_count_estI[where a="2* log 2 (real_of_int (int ((4+2*n) * length as)+1))+2"])
       apply (rule int_bit_count_est)
       apply (simp add:a_7 lessThan_atLeast0)
      by (simp add:algebra_simps lessThan_atLeast0)
    also have "... = ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))"
      by (simp add:distrib_left[symmetric] s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric])
    finally show "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}.
      sum_list (map (f2_hash p (y i)) as)))
       \<le> ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))" by blast
  qed

  show ?thesis
    apply (subst AE_measure_pmf_iff)
    apply (subst M_def)
    apply (subst f2_alg_sketch[OF assms(1) assms(2), where n="n" and as="as"])
    apply (simp add: s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] p_def[symmetric] del:f2_space_usage.simps)
    apply (subst set_prod_pmf, simp)
    apply (simp add: PiE_iff  del:f2_space_usage.simps)
    apply (subst set_pmf_of_set) apply (rule non_empty_bounded_degree_polynomials) apply (rule fin_degree_bounded[OF mod_ring_finite])
    by (metis a)
qed

theorem f2_asympotic_space_complexity:
  "f2_space_usage \<in> O[at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda> (n, m, \<epsilon>, \<delta>). 
  (ln (1 / of_rat \<epsilon>)) / (of_rat \<delta>)\<^sup>2 * (ln (real n) + ln (real m)))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  define n_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "n_of = (\<lambda>(n, m, \<epsilon>, \<delta>). n)"
  define m_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "m_of = (\<lambda>(n, m, \<epsilon>, \<delta>). m)"
  define \<epsilon>_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<epsilon>_of = (\<lambda>(n, m, \<epsilon>, \<delta>). \<epsilon>)"
  define \<delta>_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<delta>_of = (\<lambda>(n, m, \<epsilon>, \<delta>). \<delta>)"

  define g where "g = (\<lambda>x. (ln (1 / of_rat (\<epsilon>_of x))) / (of_rat (\<delta>_of x))\<^sup>2 * (ln (real (n_of x)) + ln (real (m_of x))))"

  have n_inf: "\<And>c. eventually (\<lambda>x. c \<le> (real (n_of x))) ?F" 
    apply (simp add:n_of_def case_prod_beta')
    apply (subst eventually_prod1', simp add:prod_filter_eq_bot)
    by (meson eventually_at_top_linorder nat_ceiling_le_eq)

  have m_inf: "\<And>c. eventually (\<lambda>x. c \<le> (real (m_of x))) ?F" 
    apply (simp add:m_of_def case_prod_beta')
    apply (subst eventually_prod2', simp add:prod_filter_eq_bot)
    apply (subst eventually_prod1', simp add:prod_filter_eq_bot)
    by (meson eventually_at_top_linorder nat_ceiling_le_eq)

  have eps_inf: "\<And>c. eventually (\<lambda>x. c \<le> 1 / (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod1', simp)
    by (rule inv_at_right_0_inf)

  have delta_inf: "\<And>c. eventually (\<lambda>x. c \<le> 1 / (real_of_rat (\<delta>_of x))) ?F"
    apply (simp add:\<delta>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    by (rule inv_at_right_0_inf)

  have zero_less_eps: "eventually (\<lambda>x. 0 < (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod1', simp)
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have zero_less_delta: "eventually (\<lambda>x. 0 < (real_of_rat (\<delta>_of x))) ?F"
    apply (simp add:\<delta>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have unit_1: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF zero_less_delta delta_inf[where c="1"]]])
    by (metis one_le_power power_one_over)

  have unit_2: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF eventually_conj[OF zero_less_eps eps_inf[where c="exp 1"]]])
    by (meson abs_ge_self dual_order.trans exp_gt_zero ln_ge_iff order_trans_rules(22))

  have unit_3: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x))"
    by (rule landau_o.big_mono, simp, rule n_inf)

  have unit_4: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (m_of x))"
    by (rule landau_o.big_mono, simp, rule m_inf)

  have unit_5: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono [OF n_inf[where c="exp 1"]]) 
    by (metis abs_ge_self linorder_not_le ln_ge_iff not_exp_le_zero order.trans)

  have unit_6: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    apply (rule landau_sum_1)
      apply (rule eventually_ln_ge_iff[OF n_inf])
     apply (rule eventually_ln_ge_iff[OF m_inf])
    by (rule unit_5)

  have unit_7: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / real_of_rat (\<epsilon>_of x))"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono [OF eventually_conj[OF zero_less_eps eps_inf[where c="1"]]])
    by simp

  have unit_8: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)) *
    (ln (real (n_of x)) + ln (real (m_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2)" 
    apply (subst (2) div_commute)
    apply (rule landau_o.big_mult_1[OF unit_1])
    by (rule landau_o.big_mult_1[OF unit_2 unit_6]) 

  have unit_9: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x) * real (m_of x))"
    by (rule landau_o.big_mult_1'[OF unit_3 unit_4])

  have zero_less_eps: "eventually (\<lambda>x. 0 < (real_of_rat (\<epsilon>_of x))) ?F"
    apply (simp add:\<epsilon>_of_def case_prod_beta')
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod2', simp)
    apply (subst eventually_prod1', simp)
    by (rule eventually_at_rightI[where b="1"], simp, simp)

  have l1: "(\<lambda>x. real (nat \<lceil>6 / (\<delta>_of x)\<^sup>2\<rceil>)) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (rule landau_real_nat)
    apply (subst landau_o.big.in_cong[where g="\<lambda>x. real_of_int \<lceil>6 / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>"])
    apply (rule always_eventually, rule allI, rule arg_cong[where f="real_of_int"]) 
     apply (metis (no_types, opaque_lifting) of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power)
    apply (rule landau_ceil[OF unit_1])
    by (rule landau_const_inv, simp, simp)

  have l2: "(\<lambda>x. real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    apply (rule landau_real_nat, rule landau_ceil, simp add:unit_2)
    apply (subst minus_mult_right)
    apply (subst cmult_in_bigo_iff, rule disjI2)
    apply (rule landau_o.big_mono)
    apply (rule eventually_mono[OF zero_less_eps])
    by (subst ln_div, simp+)

  have l3: "(\<lambda>x. log 2 (real (m_of x) * (4 + 2 * real (n_of x)) + 1)) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    apply (simp add:log_def)
    apply (rule landau_o.big_trans[where g="\<lambda>x. ln (real (n_of x) * real (m_of x))"])
     apply (rule landau_ln_2[where a="2"], simp, simp)
      apply (rule eventually_mono[OF eventually_conj[OF m_inf[where c="2"] n_inf[where c="1"]]])
      apply (metis dual_order.trans mult_left_mono mult_of_nat_commute of_nat_0_le_iff verit_prod_simplify(1))
     apply (rule sum_in_bigo)
      apply (subst mult.commute)
      apply (rule landau_o.mult)
      apply (rule sum_in_bigo, simp add:unit_3, simp)
      apply simp
      apply (simp add:unit_9)
    apply (subst landau_o.big.in_cong[where g="\<lambda>x. ln (real (n_of x)) + ln (real (m_of x))"])
     apply (rule eventually_mono[OF eventually_conj[OF m_inf[where c="1"] n_inf[where c="1"]]])
    by (subst ln_mult, simp+)

  have l4: "(\<lambda>x. log 2 (4 + 2 * real (n_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    apply (rule landau_sum_1)
      apply (rule eventually_ln_ge_iff[OF n_inf])
     apply (rule eventually_ln_ge_iff[OF m_inf])
    apply (simp add:log_def)
    apply (rule landau_ln_2[where a="2"], simp, simp, rule n_inf)
    apply (rule sum_in_bigo, simp, simp add:unit_3)
    by simp

  have l5: "(\<lambda>x. ln (real (nat \<lceil>6 / (\<delta>_of x)\<^sup>2\<rceil>) + 1)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)) *
    (ln (real (n_of x)) + ln (real (m_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (subst (2) div_commute)
    apply (rule landau_o.big_mult_1)
     apply (rule landau_ln_3, simp)
     apply (rule sum_in_bigo, rule l1, rule unit_1)
    by (rule landau_o.big_mult_1[OF unit_2 unit_6])

  have l6: "(\<lambda>x. ln (4 + 2 * real (n_of x))) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)) * 
    (ln (real (n_of x)) + ln (real (m_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (subst (2) div_commute)
    apply (rule landau_o.big_mult_1'[OF unit_1])
    apply (rule landau_o.big_mult_1'[OF unit_2])
    using l4 by (simp add:log_def)

  have l7: "(\<lambda>x. ln (real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>) + 1)) \<in> O[?F](\<lambda>x. 
    ln (1 / real_of_rat (\<epsilon>_of x)) * (ln (real (n_of x)) + ln (real (m_of x))) / (real_of_rat (\<delta>_of x))\<^sup>2)"
    apply (subst (2) div_commute)
    apply (rule landau_o.big_mult_1'[OF unit_1])
    apply (rule landau_o.big_mult_1)
     apply (rule landau_ln_2[where a="2"], simp, simp, simp add:eps_inf)
     apply (rule sum_in_bigo)
      apply (rule landau_nat_ceil[OF unit_7])
    apply (subst minus_mult_right)
      apply (subst cmult_in_bigo_iff, rule disjI2)
      apply (subst landau_o.big.in_cong[where g="\<lambda>x. ln( 1 / (real_of_rat (\<epsilon>_of x)))"])
       apply (rule eventually_mono[OF zero_less_eps])
       apply (subst ln_div, simp, simp, simp)
      apply (rule landau_ln_3[OF eps_inf], simp)
    apply (rule  unit_7)
    by (rule unit_6)

  have "f2_space_usage = (\<lambda>x. f2_space_usage (n_of x, m_of x, \<epsilon>_of x, \<delta>_of x))"
    apply (rule ext)
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def)
  also have "... \<in> O[?F](g)"
    apply (simp add:g_def Let_def)
    apply (rule sum_in_bigo_r)
     apply (subst (2) div_commute, subst mult.assoc)
     apply (rule landau_o.mult, simp add:l1)
     apply (rule landau_o.mult, simp add:l2)
     apply (rule sum_in_bigo_r, simp add:l3)
     apply (rule sum_in_bigo_r, simp add:l4, simp add:unit_6)
    apply (rule sum_in_bigo_r, simp add:log_def l6)
    apply (rule sum_in_bigo_r, simp add:log_def l7)
    apply (rule sum_in_bigo_r, simp add:log_def l5)
    by (simp add:unit_8)
  also have "... = O[?F](?rhs)"
    apply (rule arg_cong2[where f="bigo"], simp)
    apply (rule ext)
    by (simp add:case_prod_beta' g_def n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def)
  finally show ?thesis by simp
qed

end
