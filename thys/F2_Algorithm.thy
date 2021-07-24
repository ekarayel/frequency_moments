theory F2_Algorithm
  imports Main "HOL-Probability.Giry_Monad" UniversalHashFamily Field Frequency_Moment_2
    Median Independent_Family_Ext "HOL-Library.Multiset"
begin

definition \<alpha> :: "nat \<Rightarrow> real" where "\<alpha> p = sqrt((p-1)/(p+1))"
definition \<beta> :: "nat \<Rightarrow> real" where "\<beta> p = -sqrt((p+1)/(p-1))"

fun eval_hash_function where
  "eval_hash_function p h k = (
    if (hash_function (ZFact (int p)) (zfact_embed p k) h) \<in> zfact_embed p ` {k. 2*k < p} then
      \<alpha> p
    else
      \<beta> p
  )"

lemma eval_exp:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2" 
  shows eval_hash_exp: 
    "prob_space.expectation (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^m) = 
    (real (p+1)/ real(2*p) * \<alpha> p ^m) + 
    (real (p-1)/ real(2*p) * \<beta> p ^m)" (is "?A = ?C")
    and eval_hash_int:
    "integrable (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^m)" (is ?B)
proof -
  define A where "A = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k < p}}"
  define B where "B = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k \<ge> p \<and> k < p}}"
  define f where "f = (\<lambda>\<omega>. indicator A \<omega> * \<alpha> p^m)"
  define g where "g = (\<lambda>\<omega>. indicator B \<omega> * \<beta> p^m)"

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
  have r3: "\<And>\<omega>. \<omega> \<in> space (poly_hash_family (ZFact (int p)) 4) \<Longrightarrow>  eval_hash_function p \<omega> k^m =  f \<omega> + g \<omega>"
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
  ultimately have r1:"has_bochner_integral (poly_hash_family (ZFact p) 4) f (real (p+1)/ real(2*p) * \<alpha> p^m)"
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
  ultimately have r2:"has_bochner_integral (poly_hash_family (ZFact p) 4) g (real (p-1)/ real(2*p) * \<beta> p^m)"
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

text \<open>There is a version @{thm [source] sum_list_map_eq_sum_count} but it doesn't work
if the function maps into the reals.\<close>

lemma sum_list_eval:
  fixes f :: "'a \<Rightarrow> real"
  shows "sum_list (map f xs) = (\<Sum>x \<in> set xs. (count_list xs x) * f x)"
proof -
  define M where "M = mset xs"
  have "sum_mset (image_mset f M) = (\<Sum>x \<in> set_mset M. (count M x) * f x)"
  proof (induction "M" rule:disj_induct_mset)
    case 1
    then show ?case by simp
  next
    case (2 n M x)
    have a:"\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2(2) by blast
    show ?case using 2 by (simp add:a count_eq_zero_iff)
  qed
  moreover have "\<And>x. count_list xs x = count (mset xs) x" 
    by (induction xs, simp, simp)
  ultimately show ?thesis
    by (simp add:M_def sum_mset_sum_list[symmetric])
qed

lemma
  assumes "p > 2"
  assumes "prime p"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> i < p" 
  shows var_f2':
    "prob_space.variance
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. sum_list (map (eval_hash_function p \<omega>) xs)^2) \<le> 2*(f2_value xs)^2" (is "?A")
  and exp_f2':
    "prob_space.expectation
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. sum_list (map (eval_hash_function p \<omega>) xs)^2) = f2_value xs" (is "?B")

  and int_exp_f2':
    "integrable
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. sum_list (map (eval_hash_function p \<omega>) xs)^2)" (is "?C")
  and int_var_f2':
    "integrable
        (poly_hash_family (ZFact p) 4)
        (\<lambda>\<omega>. (sum_list (map (eval_hash_function p \<omega>) xs)^2)^2)" (is "?D")
proof -
  have f2_sketch_elim: "\<And>\<omega>. f2_sketch (\<lambda>k \<omega>. eval_hash_function p \<omega> k) xs \<omega> = sum_list (map (eval_hash_function p \<omega>) xs)"
    by (simp add:sum_list_eval f2_sketch_def f2_sketch_summand_def del:eval_hash_function.simps)

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

lemma (in prob_space) var_sum:
  assumes "finite I"
  assumes "indep_vars (\<lambda>_. borel ::real measure) X' I" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. X' i \<omega>)" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. X' i \<omega>^2)" 
  shows "variance (\<lambda>\<omega>. \<Sum>i\<in> I. X' i \<omega>) = (\<Sum> i \<in> I. variance (\<lambda>\<omega>. X' i \<omega>))" 
proof -
  have a:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> expectation (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>)) = 
     expectation (X' i) * expectation (X' j) \<and> integrable M (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>))"
    (is "\<And>i j. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?ths1 i j \<and> ?ths2 i j")
  proof -
    fix i j
    assume a1:"i \<in> I"
    assume a2:"j \<in> I"
    assume a3:"i \<noteq> j"
    have "{i,j} \<subseteq> I" using a1 a2 by simp
    hence "indep_vars (\<lambda>_. borel) X' {i, j}" 
      using indep_vars_subset assms(2) by blast
    moreover have "\<And>i'. i' \<in> {i,j} \<Longrightarrow> integrable M (X' i')" 
      using a1 a2 assms(3) by blast
    ultimately show "?ths1 i j \<and> ?ths2 i j"
      using a3 indep_vars_lebesgue_integral[where I="{i,j}" and X="X'"] indep_vars_integrable[where I="{i,j}" and X="X'"]
      by simp
  qed

  have b:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> expectation (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>)) =
    (if i \<noteq> j then 0 else expectation (\<lambda>\<omega>. (X' i \<omega>)^2) - expectation (X' i) * expectation (X' j)) +  expectation (X' i) * expectation (X' j)"
    (is "\<And>i j. _ \<Longrightarrow> _ \<Longrightarrow> ?lhs i j = ?rhs i j")
  proof -
    fix i j
    assume "i \<in> I"
    moreover assume "j \<in> I"
    ultimately show "?lhs i j = ?rhs i j"
      apply (cases "i = j")
       apply (simp add:power2_eq_square)
      by (simp add:a)
  qed
  have c:"\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> integrable M (\<lambda>\<omega>. (X' i \<omega>) * (X' j \<omega>))" (is "\<And>i j. _ \<Longrightarrow> _ \<Longrightarrow> ?ths i j")
  proof -
    fix i j
    assume "i \<in> I"
    moreover assume "j \<in> I"
    ultimately show "?ths i j"
      apply (cases "i = j")
       using assms(4) apply (simp add: power2_eq_square)
      by (simp add:a)
  qed
  have d:"integrable M (\<lambda>\<omega>. (\<Sum>i \<in> I. X' i \<omega>)\<^sup>2)" 
    by (simp add:c sum_distrib_left sum_distrib_right power2_eq_square)
  show ?thesis 
    apply (subst variance_eq)
    apply (simp add: assms)
    apply (simp add: d)
    apply (simp add: variance_eq assms)
    apply (subst (1 2) power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right)
    apply (simp add: c Bochner_Integration.integral_sum)
    apply (simp add: sum_subtractf[symmetric])
    apply (simp add: b assms(1) sum_collapse)
    by (simp add:power2_eq_square)
qed



lemma inf_primes: "wf ((\<lambda>n. (Suc n, n)) ` {n. \<not> (prime n)})" (is "wf ?S") 
proof (rule wfI_min)
  fix x :: nat
  fix Q :: "nat set"
  assume a:"x \<in> Q"

  have "\<exists>z \<in> Q. prime z \<or> Suc z \<notin> Q" 
  proof (cases "\<exists>z \<in> Q. Suc z \<notin> Q")
    case True
    then show ?thesis by auto
  next
    case False
    hence b:"\<And>z. z \<in> Q \<Longrightarrow> Suc z \<in> Q" by blast
    have c:"\<And>k. k + x \<in> Q"
    proof -
      fix k
      show "k+x \<in> Q"
        by (induction "k", simp add:a, simp add:b)
    qed
    show ?thesis 
      apply (cases "\<exists>z \<in> Q. prime z")
      apply blast
        by (metis add.commute less_natE bigger_prime c)
  qed
  thus "\<exists>z \<in> Q. \<forall>y. (y,z) \<in> ?S \<longrightarrow> y \<notin> Q" by blast
qed


function find_prime_above where
  "find_prime_above n = (if prime n then n else find_prime_above (Suc n))"
  by auto
termination
  apply (relation "(\<lambda>n. (Suc n, n)) ` {n. \<not> (prime n)}")
  by (simp add:inf_primes)+

declare find_prime_above.simps [simp del]


fun f2_alg where
  "f2_alg \<delta> \<epsilon> n xs =
    do {
      let s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-2 * ln \<epsilon>\<rceil>;
      let p = find_prime_above n;
      h \<leftarrow> \<Pi>\<^sub>M _ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. poly_hash_family (ZFact (int p)) 4;
      sketch \<leftarrow> 
          return (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. borel)
            (\<lambda>(i\<^sub>1,i\<^sub>2) \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. sum_list (map (eval_hash_function p (h (i\<^sub>1, i\<^sub>2))) xs));
      sketch_avg \<leftarrow> 
          return (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. borel)
            (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1} . sketch (i\<^sub>1, i\<^sub>2)^2) / s\<^sub>1);
      return borel (median sketch_avg s\<^sub>2)
    }"

lemma
  assumes "\<epsilon> < 1 \<and> \<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  shows "\<P>(r in (f2_alg \<delta> \<epsilon> n xs). abs (r - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(2 * ln \<epsilon>)\<rceil>"
  define p where "p = find_prime_above n"
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

  have prob_space_0: "prob_space \<Omega>\<^sub>0" 
    sorry

  have s1_nonzero: "s\<^sub>1 > 0"
    sorry
  have s2_nonzero: "s\<^sub>2 > 0"
    sorry
  have s2_le: "\<And>i. i \<in> {0..<s\<^sub>2} \<Longrightarrow> i < s\<^sub>2"
    sorry    
  have s1_le: "\<And>i. i \<in> {0..<s\<^sub>1} \<Longrightarrow> i < s\<^sub>1"
    sorry    

  define f3 where "f3 = (\<lambda>h. (\<lambda>(i\<^sub>1,i\<^sub>2) \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}. sum_list (map (eval_hash_function p (h (i\<^sub>1, i\<^sub>2))) xs)))"
  define f2 where "f2 = (\<lambda>h. (\<lambda>i\<^sub>2\<in>{0..<s\<^sub>2}. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (h (i\<^sub>1, i\<^sub>2))\<^sup>2) / real s\<^sub>1))"
  define f1 :: "(nat \<Rightarrow> real) \<Rightarrow> real" where "f1 = (\<lambda>h. median h s\<^sub>2)"

  have f2_meas: "f2 \<in> measurable \<Omega>\<^sub>1 \<Omega>\<^sub>2"
    by (simp add:f2_def \<Omega>\<^sub>1_def \<Omega>\<^sub>2_def, measurable)
  have f3_meas: "f3 \<in> measurable \<Omega>\<^sub>0 \<Omega>\<^sub>1"
    apply (simp add:f3_def \<Omega>\<^sub>0_def \<Omega>\<^sub>1_def, measurable, simp)
    sorry
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

  have exp_3: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> prob_space.expectation (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2)
    = f2_value xs"
    apply (subst integral_distr)
      apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
    apply (simp add:f3_def \<Omega>\<^sub>0_def)
    apply (subst lift_bochner_integral_PiM, simp)
    sorry

  have int_3: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2)"
    apply (subst integrable_distr_eq)
    apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
     defer
    apply (simp add:f3_def)
    sorry

  have int_3_2: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. ((\<omega> (i, j))^2)^2)"
    apply (subst integrable_distr_eq)
    apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
    apply (simp add:f3_def)
    sorry

  have var3_h1: "\<And>i j. i < s\<^sub>1 \<Longrightarrow> j < s\<^sub>2 \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> (i, j))^2)
    \<le> 2 * f2_value xs^2" sorry
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
       apply (rule indep_pointwise [where f="(\<lambda>j. (j,i))"])
         using prob_space_0 defer
      using a apply (simp cong:restrict_cong) defer
             apply simp
             apply (rule image_subsetI, simp add:a)
            apply (rule inj_onI, simp)
      using s1_nonzero apply simp
           apply (simp add:prob_space_0)
        apply (simp add:\<Omega>\<^sub>1_def, measurable, simp add:a)
        apply measurable
      defer
      apply measurable
      sorry
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
    sorry
  
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
  moreover have "  s\<^sub>1 * (2 * (f2_value xs)\<^sup>2 / s\<^sub>1\<^sup>2) =   2 * (f2_value xs)\<^sup>2 / s\<^sub>1" 
    by (simp add: power2_eq_square)
  ultimately have var23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)
    \<le>  2 * (f2_value xs)\<^sup>2 / s\<^sub>1"
    by auto

  have space_0: "space \<Omega>\<^sub>0 \<noteq> {}" sorry

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
    moreover have c:"0 < \<delta> * f2_value xs" sorry 
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
    sorry
  moreover have "- 32 / 9 * ln \<epsilon> \<le> real s\<^sub>2" using s\<^sub>2_def sorry
  moreover have "0 < \<epsilon>" using assms(1) by auto
  moreover have "prob_space (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3))" 
    using f23_meas prob_space_0 by (simp add: prob_space.prob_space_distr)
  ultimately have 
    "\<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (median r s\<^sub>2 - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> \<epsilon>"
    using  prob_space.median_bound[where \<delta>="\<delta>*f2_value xs" and X="\<lambda>i \<omega>. \<omega> i"]
    sorry
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



lemma prod_space:
  assumes "field F"
  assumes "finite (carrier F)"
  shows "prob_space (\<Pi>\<^sub>M i \<in> {k. k < (s1::nat)}. poly_hash_family F 4)"
proof -
  show ?thesis 
    by (simp add: assms(1) assms(2) prob_space_PiM prob_space_poly_family)
qed


end