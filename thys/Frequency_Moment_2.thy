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
proof -
  have " is_encoding encode_f2_state"
    unfolding encode_f2_state_def
    by (auto intro!:dependent_encoding nat_encoding encode_extensional list_encoding int_encoding)
  thus ?thesis
    by (rule encoding_imp_inj)
qed

context
  fixes \<epsilon> \<delta> :: rat
  fixes n :: nat
  fixes as :: "nat list"
  fixes \<Omega>
  assumes \<epsilon>_range: "\<epsilon> \<in> {0<..<1}"
  assumes \<delta>_range: "\<delta> > 0"
  assumes as_range: "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n) \<bind> f2_result"
begin  

private definition s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"

lemma s1_nonzero: "s\<^sub>1 > 0"
    using \<delta>_range by (simp add:s\<^sub>1_def)

private definition s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"

lemma s2_nonzero: "s\<^sub>2 > 0"
    using \<epsilon>_range by (simp add:s\<^sub>2_def)

private definition p where "p = find_prime_above (max n 3)"
 
lemma p_prime: "Factorial_Ring.prime p" 
  unfolding p_def using find_prime_above_is_prime by blast

lemma p_ge_2: "p > 2"
proof -
  have "p \<ge> 3"
    unfolding p_def by (meson max.boundedE find_prime_above_lower_bound)
  thus ?thesis 
    by linarith
qed

lemma p_ge_0: "p > 0" using p_ge_2 by linarith

lemma p_ge_1: "p > 1" using p_ge_2 by simp

lemma p_ge_n: "p \<ge> n" unfolding p_def
  by (meson max.boundedE find_prime_above_lower_bound )

interpretation carter_wegman_hash_family "mod_ring p" 4
  using carter_wegman_hash_familyI[OF mod_ring_is_field mod_ring_finite]
  using p_prime by auto

private definition f where "f x = median s\<^sub>2 (\<lambda>i\<in>{..<s\<^sub>2}. 
  (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (rat_of_int (sum_list (map (f2_hash p (x (i\<^sub>1, i))) as)))\<^sup>2) /
  (((rat_of_nat p)\<^sup>2 - 1) * rat_of_nat s\<^sub>1))"

definition sketch where "sketch = fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
private definition \<Omega>\<^sub>0 where"\<Omega>\<^sub>0 = prod_pmf ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set space)" 
private definition \<Omega>\<^sub>1 where"\<Omega>\<^sub>1 = measure_pmf \<Omega>\<^sub>0" 
private definition f3 where "f3 x i\<^sub>1 i\<^sub>2 =(real_of_int (sum_list (map (f2_hash p (x (i\<^sub>1, i\<^sub>2))) as)))\<^sup>2"
private definition f2 where "f2 x = (\<lambda>i. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. f3 x i\<^sub>1 i) / (((real p)\<^sup>2 - 1) * real s\<^sub>1))"
private definition f4 where "f4 \<omega> = real_of_int (sum_list (map (f2_hash p \<omega>) as))^2"

private lemma f2_hash_pow_exp:
  assumes "k < p"
  shows
    "expectation (\<lambda>\<omega>. real_of_int (f2_hash p \<omega> k) ^m) = 
     ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
proof -

  have "odd p" using p_prime p_ge_2 prime_odd_nat assms by blast
  then obtain t where t_def: "p=2*t+1" 
    using oddE by blast

  have "Collect even \<inter> {..<2 * t + 1} \<subseteq> (*) 2 ` {..<t + 1}" 
    by (rule in_image_by_witness[where g="\<lambda>x. x div 2"], simp, linarith)
  moreover have " (*) 2 ` {..<t + 1} \<subseteq> Collect even \<inter> {..<2 * t + 1}"
    by (rule image_subsetI, simp)
  ultimately have "card ({k. even k} \<inter> {..<p}) = card ((\<lambda>x. 2*x) ` {..<t+1})"
    unfolding t_def using order_antisym by metis
  also have "... = card {..<t+1}" 
    by (rule card_image, simp add: inj_on_mult)
  also have "... =  t+1" by simp
  finally have card_even: "card ({k. even k} \<inter> {..<p}) = t+1" by simp
  hence "card ({k. even k} \<inter> {..<p}) * 2 = (p+1)" by (simp add:t_def)
  hence prob_even: "prob {\<omega>. hash k \<omega> \<in> Collect even} = (real p + 1)/(2*real p)"
    apply (subst prob_range, simp add:mod_ring_carr assms)
    by (simp add:frac_eq_eq p_ge_0 mod_ring_def lessThan_atLeast0) 

  have "p = card {..<p}" by simp
  also have "... = card (({k. odd k} \<inter> {..<p}) \<union> ({k. even k} \<inter> {..<p}))" 
    by (rule arg_cong[where f="card"], auto)
  also have "... = card ({k. odd k} \<inter> {..<p}) +  card ({k. even k} \<inter> {..<p})"
    by (rule card_Un_disjoint, simp, simp, blast)
  also have "... = card ({k. odd k} \<inter> {..<p}) + t+1"
    by (simp add:card_even)
  finally have "p = card ({k. odd k} \<inter> {..<p}) + t+1"
    by simp
  hence "card ({k. odd k} \<inter> {..<p}) * 2 = (p-1)" 
    by (simp add:t_def)
  hence prob_odd: "prob {\<omega>. hash k \<omega> \<in> Collect odd} = (real p - 1)/(2*real p)"
    apply (subst prob_range, simp add:mod_ring_carr assms)
    by (simp add: frac_eq_eq mod_ring_def lessThan_atLeast0 t_def)

  have "expectation (\<lambda>x. real_of_int (f2_hash p x k) ^ m) =
    expectation (\<lambda>\<omega>. indicator {\<omega>. even (hash k \<omega>)} \<omega> * (real p - 1)^m + 
      indicator {\<omega>. odd (hash k \<omega>)} \<omega> * (-real p - 1)^m)" 
    by (rule Bochner_Integration.integral_cong, simp, simp)
  also have "... = 
     prob {\<omega>. hash  k \<omega> \<in> Collect even}  * (real p - 1) ^ m  + 
     prob {\<omega>. hash  k \<omega> \<in> Collect odd}  * (-real p - 1) ^ m "
    by (simp, simp add:M_def)
  also have "... = (real p + 1) * (real p - 1) ^ m / (2 * real p) + (real p - 1) * (- real p - 1) ^ m / (2 * real p)"
    by (subst prob_even, subst prob_odd, simp)
  also have "... =  
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
    by (simp add:add_divide_distrib ac_simps)
  finally show "expectation (\<lambda>x. real_of_int (f2_hash p x k) ^ m) = 
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)" by simp
qed

lemma 
  shows var_f4:"variance f4 \<le> 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2" (is "?A")
  and exp_f4:"expectation f4 = real_of_rat (F 2 as) * ((real p)\<^sup>2-1)" (is "?B")
proof -
  define h where "h = (\<lambda>\<omega> x. real_of_int (f2_hash p \<omega> x))"
  define c where "c = (\<lambda>x. real (count_list as x))"
  define r where "r = (\<lambda>(m::nat). ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p))"
  define h_prod where "h_prod = (\<lambda>as \<omega>. prod_list (map (h \<omega>) as))" 

  define exp_h_prod :: "nat list \<Rightarrow> real" where "exp_h_prod = (\<lambda>as. (\<Prod>i \<in> set as. r (count_list as i)))"

  have f_eq: "f4 = (\<lambda>\<omega>. (\<Sum>x \<in> set as. c x * h \<omega> x)^2)"
    by (rule ext, simp add:f4_def c_def h_def sum_list_eval del:f2_hash.simps)

  have r_one: "r (Suc 0) = 0"
    by (simp add:r_def algebra_simps)

  have r_two: "r 2 = (real p^2-1)"
    using p_ge_0 unfolding r_def power2_eq_square 
    by (simp add:nonzero_divide_eq_eq, simp add:algebra_simps)

  have"(real p)^2 \<ge> 2^2"
    by (rule power_mono, use p_ge_2 in linarith, simp)
  hence p_square_ge_4: "(real p)\<^sup>2 \<ge> 4" by simp

  have "r 4 = (real p)^4+2*(real p)\<^sup>2 - 3" 
    using p_ge_0 unfolding r_def
    by (subst nonzero_divide_eq_eq, auto simp:power4_eq_xxxx power2_eq_square algebra_simps)
  also have "... \<le> (real p)^4+2*(real p)\<^sup>2 + 3"
    by simp
  also have "... \<le> 3 * r 2 * r 2"
    using p_square_ge_4
    by (simp add:r_two power4_eq_xxxx power2_eq_square algebra_simps mult_left_mono)
  finally have r_four_est: "r 4 \<le> 3 * r 2 * r 2"  by simp

  have exp_h_prod_elim: "exp_h_prod = (\<lambda>as. prod_list (map (r \<circ> count_list as) (remdups as)))" 
    by (simp add:exp_h_prod_def prod.set_conv_list[symmetric])

  have exp_h_prod: "\<And>x. set x \<subseteq> set as \<Longrightarrow> length x \<le> 4 \<Longrightarrow> expectation (h_prod x) = exp_h_prod x"
  proof -
    fix x 
    assume "set x \<subseteq> set as"
    hence x_sub_p: "set x \<subseteq> {..<p}" using as_range p_ge_n by auto
    hence x_le_p: "\<And>k. k \<in> set x \<Longrightarrow> k < p" by auto
    assume "length x \<le> 4"
    hence card_x: "card (set x) \<le> 4" using card_length dual_order.trans by blast

    have "set x \<subseteq> carrier (mod_ring p) "
      using x_sub_p by (simp add:mod_ring_def)

    hence h_indep: "indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. h \<omega> i ^ count_list x i) (set x)"
      using k_wise_indep_vars_subset[OF k_wise_indep] card_x as_range h_def
      by (auto intro:indep_vars_compose2[where X="hash" and M'=" (\<lambda>_. discrete)"])

    have "expectation (h_prod x) = expectation (\<lambda>\<omega>. \<Prod> i \<in> set x. h \<omega> i^(count_list x i))"
      by (simp add:h_prod_def prod_list_eval)
    also have "... = (\<Prod>i \<in> set x. expectation (\<lambda>\<omega>. h \<omega> i^(count_list x i)))"
      by (simp add: indep_vars_lebesgue_integral[OF _ h_indep])
    also have "... = (\<Prod>i \<in> set x. r (count_list x i))"
      using f2_hash_pow_exp x_le_p 
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
      by (metis b bij_betw_def prod.reindex)
    also have "... = exp_h_prod y"
      unfolding exp_h_prod_def
      by (rule prod.cong, metis b bij_betw_def) simp
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

  have "expectation f4 = (\<Sum>i\<in>set as. (\<Sum>j\<in>set as. c i * c j * expectation (h_prod [i,j])))"
    by (simp add:f_eq h_prod_def power2_eq_square sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum algebra_simps)
  also have "... = (\<Sum>i\<in>set as. (\<Sum>j\<in>set as. c i * c j * exp_h_prod [i,j]))"
    by (simp add:exp_h_prod)
  also have "... = (\<Sum>i \<in> set as. (\<Sum>j \<in> set as.  
    c i * c j * (sum_list (map (\<lambda>p. of_bool (kernel_of [i,j] = kernel_of p) * exp_h_prod p) (enum_rgfs 2)))))"
    by (subst exp_h_prod_cong, simp add:c)
  also have "... = (\<Sum>i\<in>set as. c i * c i * r 2)"
    by (simp add: numeral_eq_Suc kernel_of_eq All_less_Suc exp_h_prod_elim r_one distrib_left sum.distrib sum_collapse)
  also have "... = real_of_rat (F 2 as) * ((real p)^2-1)"
    by (simp add: sum_distrib_right[symmetric] c_def F_def power2_eq_square of_rat_sum of_rat_mult r_two)
  finally show b:?B by simp

  have "expectation (\<lambda>x. (f4 x)\<^sup>2) = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as.
    c i1 * c i2 * c i3 * c i4 * expectation (h_prod [i1, i2, i3, i4])))))"
    by (simp add:f_eq h_prod_def power4_eq_xxxx sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum algebra_simps)
  also have "... = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as. 
    c i1 * c i2 * c i3 * c i4 * exp_h_prod [i1,i2,i3,i4]))))"
    by (simp add:exp_h_prod)
  also have "... = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as. 
    c i1 * c i2 * c i3 * c i4 * 
    (sum_list (map (\<lambda>p. of_bool (kernel_of [i1,i2,i3,i4] = kernel_of p) * exp_h_prod p) (enum_rgfs 4)))))))"
    by (subst exp_h_prod_cong, simp add:c)
  also have "... = 
    3 * (\<Sum>i \<in> set as. (\<Sum>j \<in> set as. c i^2 * c j^2 * r 2 * r 2)) + ((\<Sum> i \<in> set as. c i^4 * r 4) - 3 *  (\<Sum> i \<in> set as. c i ^ 4 * r 2 * r 2))"
    apply (simp add: numeral_eq_Suc exp_h_prod_elim r_one) (* large intermediate terms *)
    apply (simp add: kernel_of_eq All_less_Suc numeral_eq_Suc distrib_left sum.distrib sum_collapse neq_commute)
    apply (simp add: algebra_simps sum_subtractf sum_collapse)
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = 3 * (\<Sum>i \<in> set as. c i^2 * r 2)^2 + (\<Sum> i \<in> set as. c i ^ 4 * (r 4 - 3 * r 2 * r 2))"
    by (simp add:power2_eq_square sum_distrib_left algebra_simps sum_subtractf)
  also have "... = 3 * (\<Sum>i \<in> set as. c i^2)^2 * (r 2)^2 + (\<Sum>i \<in> set as. c i ^ 4 * (r 4 - 3 * r 2 * r 2))"
    by (simp add:power_mult_distrib sum_distrib_right[symmetric])
  also have "... \<le> 3 * (\<Sum>i \<in> set as. c i^2)^2 * (r 2)^2 + (\<Sum>i \<in> set as. c i ^ 4 * 0)"
    using r_four_est  
    by (auto intro!: sum_nonpos simp add:mult_nonneg_nonpos)
  also have "... = 3 * (real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2" 
    by (simp add:c_def r_two F_def of_rat_sum of_rat_power)
  finally have v_1: "expectation (\<lambda>x. (f4 x)\<^sup>2) \<le> 3 * (real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    by simp
  
  show "variance f4 \<le> 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    using v_1 by (simp add: variance_eq, simp add:power_mult_distrib b)
qed

lemma f2_alg_sketch_2:
  "sketch = \<Omega>\<^sub>0 \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (h i)) as)))"
proof -
  have "sketch =  fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
    by (simp add:sketch_def)
  also have "... = \<Omega>\<^sub>0 \<bind> (\<lambda>h. return_pmf (s\<^sub>1, s\<^sub>2, p, h, 
      \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (h i)) as)))"
  proof (induction as rule:rev_induct)
    case Nil
    then show ?case 
      by (simp add:s\<^sub>1_def s\<^sub>2_def space_def p_def[symmetric] \<Omega>\<^sub>0_def restrict_def Let_def) 
  next
    case (snoc a as)
    show ?case
      using snoc apply (simp del:f2_hash.simps f2_init.simps)
      apply (subst bind_assoc_pmf)
      apply (subst bind_return_pmf)
      apply (simp add:restrict_def del:f2_hash.simps f2_init.simps cong:restrict_cong)
      by (subst add.commute, simp)
  qed
  finally show ?thesis by auto
qed

lemma distr:  "\<Omega> = map_pmf f \<Omega>\<^sub>0"
proof -
  have "\<Omega> = sketch \<bind> f2_result"
    by (simp add:\<Omega>_def sketch_def)
  also have "... = \<Omega>\<^sub>0 \<bind> (\<lambda>x. f2_result (s\<^sub>1, s\<^sub>2, p, x, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (x i)) as)))"
    by (simp add: f2_alg_sketch_2  bind_assoc_pmf bind_return_pmf)
  also have "... = map_pmf f \<Omega>\<^sub>0"
    by (simp add:map_pmf_def f_def lessThan_atLeast0 cong:restrict_cong)
  finally show ?thesis by simp
qed

lemma space_omega_1 [simp]:"Sigma_Algebra.space \<Omega>\<^sub>1 = UNIV"
    by (simp add:\<Omega>\<^sub>1_def)

interpretation Q: prob_space "\<Omega>\<^sub>1"
  by (simp add:\<Omega>\<^sub>1_def prob_space_measure_pmf)

lemma integrable_Q:
  fixes f :: "((nat \<times> nat) \<Rightarrow> (nat list)) \<Rightarrow> real"
  shows "integrable \<Omega>\<^sub>1 f"
  unfolding \<Omega>\<^sub>1_def \<Omega>\<^sub>0_def
  by (rule integrable_measure_pmf_finite, auto intro:finite_PiE simp:set_prod_pmf)

lemma f3_exp:
  assumes "i\<^sub>2 < s\<^sub>2"
  assumes "i\<^sub>1 \<in> {0..<s\<^sub>1}"
  shows "Q.expectation (\<lambda>\<omega>. f3 \<omega> i\<^sub>1 i\<^sub>2) = real_of_rat (F 2 as) * ((real p)\<^sup>2 - 1)"
proof -
  have "Q.expectation (\<lambda>\<omega>. f3 \<omega> i\<^sub>1 i\<^sub>2) = expectation f4"
    using integrable_Q integrable_M assms
    unfolding \<Omega>\<^sub>0_def \<Omega>\<^sub>1_def f3_def f4_def M_def
    by (subst integral_prod_pmf_slice, auto)
  also have "... = (real_of_rat (F 2 as)) * ((real p)\<^sup>2 - 1)"
    using exp_f4 by simp
  finally show ?thesis by simp
qed

lemma f3_var:
  assumes "i\<^sub>2 < s\<^sub>2"
  assumes "i\<^sub>1 \<in> {0..<s\<^sub>1}"
  shows "Q.variance (\<lambda>\<omega>. f3 \<omega> i\<^sub>1 i\<^sub>2) \<le> 2 * (real_of_rat (F 2 as))\<^sup>2 * ((real p)\<^sup>2 - 1)\<^sup>2"
proof -
  have "Q.variance (\<lambda>\<omega>. f3 \<omega> i\<^sub>1 i\<^sub>2) = variance f4"
    using integrable_Q integrable_M assms
    unfolding \<Omega>\<^sub>0_def \<Omega>\<^sub>1_def f3_def f4_def M_def
    by (subst variance_prod_pmf_slice, auto)
  also have "... \<le>  2 * (real_of_rat (F 2 as))\<^sup>2 * ((real p)\<^sup>2 - 1)\<^sup>2"
    using var_f4 by simp
  finally show ?thesis by simp
qed

lemma Q_exp:
  assumes "i < s\<^sub>2"
  shows "Q.expectation (\<lambda>\<omega>. f2 \<omega> i) = real_of_rat (F 2 as)"
proof -
  have a:"(real p)\<^sup>2 > 1" using p_ge_1 by simp

  have "Q.expectation (\<lambda>\<omega>. f2 \<omega> i) = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. Q.expectation (\<lambda>\<omega>. f3 \<omega> i\<^sub>1 i)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)"
    using assms integrable_Q by (simp add:f2_def)
  also have "... = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. real_of_rat (F 2 as) * ((real p)\<^sup>2 - 1)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)" 
    using f3_exp[OF assms] by simp
  also have "... = real_of_rat (F 2 as)"
    using s1_nonzero a by simp
  finally show ?thesis by simp
qed

lemma Q_var:
  assumes "i < s\<^sub>2"
  shows "Q.variance (\<lambda>\<omega>. f2 \<omega> i) \<le> (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
proof -
  have a: "Q.indep_vars (\<lambda>_. borel) (\<lambda>i\<^sub>1 x. f3 x i\<^sub>1 i) {0..<s\<^sub>1}"
      (* TODO indep_vars_restrict_intro should be replace with a new version that has M = measure_pmf p as precondition
      similar to indep_vars_pmf *)
    apply (simp add:\<Omega>\<^sub>0_def \<Omega>\<^sub>1_def, rule indep_vars_restrict_intro [where f="\<lambda>j. {(j,i)}"])
    using assms  s1_nonzero s2_nonzero by (auto simp add:f3_def disjoint_family_on_def)

  have p_sq_ne_1: "(real p)^2 \<noteq> 1" 
    by (metis p_ge_1 less_numeral_extra(4) of_nat_power one_less_power pos2 semiring_char_0_class.of_nat_eq_1_iff)

  have s1_bound: " 6 / (real_of_rat \<delta>)\<^sup>2 \<le> real s\<^sub>1"
    unfolding s\<^sub>1_def
    by  (metis (mono_tags, opaque_lifting) of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power real_nat_ceiling_ge)

  have "Q.variance (\<lambda>\<omega>. f2 \<omega> i) = Q.variance (\<lambda>\<omega>. \<Sum>i\<^sub>1 = 0..<s\<^sub>1. f3 \<omega> i\<^sub>1 i) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
    unfolding f2_def by (subst Q.variance_divide[OF integrable_Q], simp)
  also have "... = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. Q.variance (\<lambda>\<omega>. f3 \<omega> i\<^sub>1 i)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
    by (subst Q.var_sum_all_indep[OF _ _ integrable_Q a]) (auto simp: \<Omega>\<^sub>0_def \<Omega>\<^sub>1_def)
  also have "... \<le>  (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2)  / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
    by (rule divide_right_mono, rule sum_mono[OF f3_var[OF assms]], auto)
  also have "... = 2 * (real_of_rat (F 2 as)^2) / real s\<^sub>1"
    using p_sq_ne_1 s1_nonzero
    by (subst frac_eq_eq, auto simp add:power2_eq_square)
  also have "... \<le> 2 * (real_of_rat (F 2 as)^2) / (6 / (real_of_rat \<delta>)\<^sup>2)"
    apply (rule divide_left_mono[OF s1_bound], simp)
    using divide_left_mono[OF s1_bound] s1_nonzero \<delta>_range mult_pos_pos by auto
  also have "... = (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
    by (simp add:of_rat_mult algebra_simps)
  finally show ?thesis by simp
qed

lemma f2_alg_per_mean:
  assumes "i < s\<^sub>2"
  shows "Q.prob {\<omega>. real_of_rat \<delta> * real_of_rat (F 2 as) < \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>} \<le> 1/3"
proof (cases "as = []")
  case True
  then show ?thesis
    using assms by (subst f2_def, subst f3_def, simp add:F_def)
next
  case False
  hence F_2_nonzero: "F 2 as > 0" using F_gr_0 by auto

  have b_1: "real_of_rat (F 2 as) = Q.expectation (\<lambda>\<omega>. f2 \<omega> i)" 
    using Q_exp assms by metis
  have b_2: "0 < real_of_rat (\<delta> * F 2 as)"
    using \<delta>_range F_2_nonzero by simp
  have b_4: "(\<lambda>\<omega>. f2 \<omega> i) \<in> borel_measurable \<Omega>\<^sub>1"
    by (simp add:\<Omega>\<^sub>0_def \<Omega>\<^sub>1_def)
  have "Q.prob {\<omega>. real_of_rat \<delta> * real_of_rat (F 2 as) < \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>} \<le> 
      Q.prob {\<omega>. real_of_rat (\<delta> * F 2 as) \<le> \<bar>f2 \<omega> i - real_of_rat (F 2 as)\<bar>}"
    by (rule Q.pmf_mono'[OF \<Omega>\<^sub>1_def], simp add:of_rat_mult)
  also have "... \<le>  Q.variance (\<lambda>\<omega>. f2 \<omega> i) / (real_of_rat (\<delta> * F 2 as))\<^sup>2"
    using Q.Chebyshev_inequality[where a="real_of_rat (\<delta> * F 2 as)"
        and f="\<lambda>\<omega>. f2 \<omega> i",simplified] \<delta>_range prob_space_measure_pmf[where p="\<Omega>\<^sub>0"] F_2_nonzero
      b_1 integrable_Q b_4 by simp
  also have "... \<le> ((real_of_rat (\<delta> * F 2 as))\<^sup>2/3) / (real_of_rat (\<delta> * F 2 as))\<^sup>2"
    by (rule divide_right_mono, rule Q_var[OF assms], simp)
  also  have "... = 1/3"
    using b_2 by force
  finally show ?thesis
    by blast
qed

lemma f2_alg_correct':
   "\<P>(\<omega> in measure_pmf \<Omega>. \<bar>\<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as) \<ge> 1-of_rat \<epsilon>"
proof -
  have a: "Q.indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. f2 \<omega> i) {0..<s\<^sub>2}" 
    apply (subst \<Omega>\<^sub>1_def, subst \<Omega>\<^sub>0_def)
    apply (rule indep_vars_restrict_intro [where f="\<lambda>j. {..<s\<^sub>1} \<times> {j}"]) 
      (* TODO indep_vars_restrict_intro should be replace with a new version that has M = measure_pmf p as precondition
      similar to indep_vars_pmf *)
         apply (simp add:f2_def f3_def)
        apply (simp add:disjoint_family_on_def, fastforce)
       using s2_nonzero  apply simp
      apply (rule subsetI, simp add:mem_Times_iff)
     apply simp
    by simp

  have b: "- 18 * ln (real_of_rat \<epsilon>) \<le> real s\<^sub>2" 
    unfolding  s\<^sub>2_def using of_nat_ceiling by auto

  have "1 - of_rat \<epsilon> \<le> Q.prob {\<omega>.  \<bar>median s\<^sub>2 (f2 \<omega>) -  of_rat (F 2 as) \<bar> \<le> of_rat \<delta> * of_rat (F 2 as)}"
    using \<epsilon>_range Q.median_bound_2[OF _ a b, where \<delta>="real_of_rat \<delta> * real_of_rat (F 2 as)"
        and \<mu>="real_of_rat (F 2 as)"] f2_alg_per_mean
    by simp
  also have "... = Q.prob {\<omega>.  \<bar>real_of_rat (f \<omega>) - of_rat (F 2 as) \<bar> \<le> of_rat \<delta> * of_rat (F 2 as)}"
    by (simp add:f_def median_restrict lessThan_atLeast0 median_rat[OF s2_nonzero]
        f2_def f3_def of_rat_divide of_rat_sum of_rat_mult of_rat_diff of_rat_power)
  also have "... = Q.prob {\<omega>. \<bar>f \<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as} " 
    by (simp add:of_rat_less_eq of_rat_mult[symmetric]  of_rat_diff[symmetric] set_eq_iff)
  finally have "Q.prob {y. \<bar>f y - F 2 as\<bar> \<le> \<delta> * F 2 as} \<ge> 1-of_rat \<epsilon> " by simp
  thus ?thesis
    by (simp add: distr \<Omega>\<^sub>1_def)
qed

lemma f2_exact_space_usage':
   "AE \<omega> in sketch . bit_count (encode_f2_state \<omega>) \<le> f2_space_usage (n, length as, \<epsilon>, \<delta>)"
proof -
  have find_prime_above_3: "find_prime_above 3 = 3" 
    by (simp add:find_prime_above.simps)

  have p_le_n: "p \<le> 2 * n + 3" 
    apply (cases "n \<le> 3")
    apply (simp add: p_def find_prime_above_3) 
    apply (simp add: p_def) 
    by (metis One_nat_def find_prime_above_upper_bound Suc_1 add_Suc_right linear not_less_eq_eq numeral_3_eq_3)
  have "bit_count (N\<^sub>S p) \<le> ereal (2 * log 2 (real p + 1) + 1)"
    by (rule nat_bit_count)
  also have "... \<le> ereal (2 * log 2 (2 * real n + 4) + 1)"
    using p_le_n by simp
  finally have p_bit_count: "bit_count (N\<^sub>S p) \<le> ereal (2 * log 2 (2 * real n + 4) + 1)"
    by simp

  have a: "\<And>y. y\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (mod_ring p) 4 \<Longrightarrow>
      bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. 
      sum_list (map (f2_hash p (y i)) as))) \<le> ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))"
  proof -
    fix y
    assume a_1:"y \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (mod_ring p) 4"
    have a_2: "y \<in> extensional ({..<s\<^sub>1} \<times> {..<s\<^sub>2})" using a_1  PiE_iff by blast
    have y_ext: "y \<in> extensional (set (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]))"
      using a_2 by (simp add:lessThan_atLeast0)

    have h_bit_count_aux: "\<And>x. x \<in>  set (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]) \<Longrightarrow> bit_count (list\<^sub>S N\<^sub>S (y x)) 
      \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))" 
    proof -
      fix x 
      assume a_5: "x \<in> set (List.product [0..<s\<^sub>1] [0..<s\<^sub>2])"
      have "bit_count (list\<^sub>S N\<^sub>S (y x)) \<le> ereal ( real 4 * (2 * log 2 (real p) + 2) + 1)"
        apply (rule bounded_degree_polynomial_bit_count[OF p_ge_0]) 
        using a_1 a_5 by force
      also have "... \<le> ereal (real 4 * (2 * log 2 (3 + 2 * real n) + 2) + 1)"
        apply simp
        apply (subst log_le_cancel_iff, simp, simp add:p_ge_0, simp)
        using p_le_n by simp
      also have "... \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by simp
      finally show "bit_count (list\<^sub>S N\<^sub>S (y x)) \<le> ereal (9 + 8 * log 2 (4 + 2 * real n))"
        by blast
    qed

    have h_bit_count: 
      "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S list\<^sub>S N\<^sub>S) y) \<le> ereal (real s\<^sub>1 * real s\<^sub>2 * (10 + 8 * log 2 (4 + 2 * real n)) + 1)"
      using extensional_bit_count_est[where e="list\<^sub>S N\<^sub>S", OF y_ext h_bit_count_aux]
      by simp

    have sketch_bit_count_aux:
      "\<And>x. x \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2} \<Longrightarrow>bit_count (I\<^sub>S (sum_list (map (f2_hash p (y x)) as)))
      \<le> ereal (2 + 2 * log 2 (real (length as) * (4 + 2 * real n) + 1))" (is "\<And>x. _ \<Longrightarrow> ?lhs x \<le> ?rhs")
    proof -
      fix x
      assume "x \<in>{0..<s\<^sub>1} \<times> {0..<s\<^sub>2}"
      have "\<bar>sum_list (map (f2_hash p (y x)) as)\<bar> \<le> sum_list (map abs (map (f2_hash p (y x)) as))" 
        by (rule sum_list_abs)
      also have "... \<le>  sum_list (map (\<lambda>_. (int p+1)) as)"
        apply (simp add:comp_def del:f2_hash.simps)
        apply (rule sum_list_mono)
        using p_ge_0 by simp 
      also have "... = int (length as) * (int p+1)"
        by (simp add: sum_list_triv)
      also have "... \<le> int (length as) * (4+2*(int n))"
        apply (rule mult_mono, simp)
        using p_le_n apply linarith
        by simp+
      finally  have "\<bar>sum_list (map (f2_hash p (y x)) as)\<bar> \<le> int (length as) * (4 + 2 * int n)" by simp
      hence "?lhs x \<le> ereal (2 * log 2 (real_of_int (int (length as) * (4 + 2 * int n) + 1)) + 2)"
        by (rule int_bit_count_est) 
      also have "... = ?rhs" by simp
      finally show "?lhs x \<le> ?rhs" by simp
    qed

    have 
      "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S I\<^sub>S) (\<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as)))
      \<le> ereal (real (length (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]))) * (ereal (2 + 2 * log 2 (real (length as) * (4 + 2 * real n) + 1)) + 1) + 1"
      by (rule extensional_bit_count_est)  
        (simp add:extensional_def lessThan_atLeast0 sketch_bit_count_aux del:f2_hash.simps I\<^sub>S.simps)+
    also have "... = ereal (real s\<^sub>1 * real s\<^sub>2 * (3 + 2 * log 2 (real (length as) * (4 + 2 * real n) + 1)) + 1)"
      by simp
    finally have sketch_bit_count: 
       "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S I\<^sub>S) (\<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as))) \<le>
      ereal (real s\<^sub>1 * real s\<^sub>2 * (3 + 2 * log 2 (real (length as) * (4 + 2 * real n) + 1)) + 1)" by simp

    have "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as))) \<le> 
      bit_count (N\<^sub>S s\<^sub>1) + bit_count (N\<^sub>S s\<^sub>2) +bit_count (N\<^sub>S p) +
      bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S list\<^sub>S N\<^sub>S) y) +
      bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>S I\<^sub>S) (\<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as)))"   
      by (simp add:Let_def s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] encode_f2_state_def dependent_bit_count add.assoc)
    also have "... \<le>  ereal (2 * log 2 (real s\<^sub>1 + 1) + 1) + ereal (2 * log 2 (real s\<^sub>2 + 1) + 1) + ereal (2 * log 2 (2 * real n + 4) + 1) + 
      (ereal (real s\<^sub>1 * real s\<^sub>2) * (10 + 8 * log 2 (4 + 2 * real n)) + 1) + 
      (ereal (real s\<^sub>1 * real s\<^sub>2) * (3 + 2 * log 2 (real (length as) * (4 + 2 * real n) + 1) ) + 1)"
      by (rule add_mono)+
        (auto intro!:nat_bit_count p_bit_count h_bit_count sketch_bit_count)
    also have "... = ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))"
      by (simp add:distrib_left add.commute s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] Let_def)
    finally show "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as))) \<le>  
      ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))" 
      by simp
  qed

  have b:"set_pmf \<Omega>\<^sub>0 = {..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (Field.mod_ring p) 4"
    by (simp add: \<Omega>\<^sub>0_def set_prod_pmf)  (simp add: space_def)

  show ?thesis
    by (simp  add:f2_alg_sketch_2 AE_measure_pmf_iff b del:f2_space_usage.simps, metis a)
qed

end

theorem f2_alg_correct:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n) \<bind> f2_result"
  shows "\<P>(\<omega> in measure_pmf \<Omega>. \<bar>\<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as) \<ge> 1-of_rat \<epsilon>"
  using f2_alg_correct'[OF assms(1) assms(2) assms(3)] \<Omega>_def by auto

theorem f2_exact_space_usage:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_f2_state \<omega>) \<le> f2_space_usage (n, length as, \<epsilon>, \<delta>)"
  using f2_exact_space_usage'[OF assms(1) assms(2) assms(3)]
  by (subst (asm)  sketch_def[OF assms(1,2,3)], subst M_def, simp)

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
