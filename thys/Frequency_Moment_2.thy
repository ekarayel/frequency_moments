theory Frequency_Moment_2
  imports Main SumByPartitions "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family" "HOL-Algebra.Congruence"
begin

section \<open>Frequency Moment 2\<close>

subsection \<open>Sketch\<close>

definition f2_sketch_summand
  where
    "f2_sketch_summand f xs x \<omega> = (real (count_list xs x) * f x \<omega> :: real)"

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. f2_sketch_summand f xs x \<omega>)"

definition f2_tr
  where
    "f2_tr h xs n l \<omega> = prod_mset (image_mset (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) (mset (l :: nat list)))"

lemma c1: "f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr h xs n [k] \<omega>"
  by (simp add:f2_tr_def)

lemma c2: "f2_tr h xs n a \<omega> * f2_tr h xs n b \<omega> = f2_tr h xs n (a@b) \<omega>"
  by (simp add:f2_tr_def)

fun counts where
  "counts xs = map (\<lambda>x. (x,count_list xs x)) (remdups xs)" 

lemma disj_induct_mset:
  assumes "P {#}"
  assumes "\<And>n M x. P M \<Longrightarrow> \<not>(x \<in># M) \<Longrightarrow> n > 0 \<Longrightarrow> P (M + replicate_mset n x)"
  shows "P M"
proof (induction "size M" arbitrary: M rule:nat_less_induct)
  case 1
  show ?case
  proof (cases "M = {#}")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then obtain x where x_def: "x \<in># M" using multiset_nonemptyE by auto
    define M1 where "M1 = M - replicate_mset (count M x) x"
    then have M_def: "M = M1 + replicate_mset (count M x) x"
      by (metis count_le_replicate_mset_subset_eq dual_order.refl subset_mset.diff_add)
    have "size M1 < size M"
      by (metis M_def x_def count_greater_zero_iff less_add_same_cancel1 size_replicate_mset size_union)
    hence s:"P M1" using 1 by blast
    show "P M" 
      apply (subst M_def, rule assms(2))
        apply (simp add:s)
      using M1_def apply (simp add:count_eq_zero_iff[symmetric])
      using x_def by simp
  qed
qed

lemma prod_mset_conv: "prod_mset (image_mset f A) = prod (\<lambda>x. (f x :: real)^(count A x)) (set_mset A)"
proof (induction A rule: disj_induct_mset)
  case 1
  then show ?case by simp
next
  case (2 n M x)
  moreover have "count M x = 0" using 2 by (simp add: count_eq_zero_iff)
  moreover have "\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2 by blast
  ultimately show ?case by simp
qed

definition f2_sketch_summand_pow
  where
    "f2_sketch_summand_pow h xs x n \<omega> = ((f2_sketch_summand h xs x \<omega>) ^ n)"

lemma countsI: "prod (\<lambda>i. f i (count (mset a) i)) (set a) = prod_list (map (\<lambda>(i,j). f i j) (counts a))"
proof -
  define b where "b = remdups a"
  have a:"set a = set b" using b_def by simp
  have b:"\<And>x. count (mset a) x = count_list a x" by (induction a, simp, simp)
  show ?thesis 
    apply (simp add:comp_def b_def[symmetric] a b) 
    using b_def prod.distinct_set_conv_list by blast
qed

lemma (in prob_space) indep_sets_reindex:
  assumes "inj_on f I"
  shows "indep_sets F (f ` I) = indep_sets (F \<circ> f) I"
proof -
  have "indep_sets F (f ` I) \<Longrightarrow> indep_sets (F \<circ> f) I"
  proof (rule indep_setsI)
    show "\<And>i. indep_sets F (f ` I) \<Longrightarrow> i \<in> I \<Longrightarrow> (F \<circ> f) i \<subseteq> events" 
      by (simp add: indep_sets_def)+
  next
    fix A
    fix J
    assume a:"indep_sets F (f ` I)"
    assume a1:"J \<subseteq> I"
    hence c1:"f ` J \<subseteq> f ` I" by blast
    assume "J \<noteq> {}"
    hence c2:"f ` J \<noteq> {}" by blast
    assume "finite J"
    hence c3:"finite (f ` J)" by auto
    assume "\<forall>j\<in>J. A j \<in> (F \<circ> f) j"
    moreover have c5:"inj_on f J" using a1 inj_on_subset assms by blast
    moreover define A' where "A' = (\<lambda>x. A (the_inv_into J f x))"
    ultimately have c4:"\<forall>j \<in> (f ` J). A' j \<in> F j"
      by (simp add:A'_def the_inv_into_f_f)
    have "prob (\<Inter> (A' ` (f ` J))) = (\<Prod>j\<in>(f ` J). prob (A' j))"
      using a indep_setsD c1 c2 c3 c4 by blast    
    thus "prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))"
      using c5 by (simp add:A'_def  prod.reindex_cong the_inv_into_f_f)
  qed
  moreover have "indep_sets (F \<circ> f) I \<Longrightarrow> indep_sets F (f ` I)"
  proof (rule indep_setsI)
    show "\<And>i. indep_sets (F \<circ> f) I \<Longrightarrow> i \<in> f ` I \<Longrightarrow> F i \<subseteq> events"
      apply (simp add:indep_sets_def) by blast
  next
    fix A
    fix J
    assume a:"indep_sets (F \<circ> f) I"
    assume a1: "J \<subseteq> f ` I"
    moreover define J' where "J' = (f -` J) \<inter> I"
    ultimately have c1:"J' \<subseteq> I" by simp
    assume "J \<noteq> {}"
    hence c2:"J' \<noteq> {}" using J'_def a1 by blast
    assume "finite J"
    hence c3:"finite J'" using a1 J'_def assms by (simp add: finite_vimage_IntI)
    assume "\<forall>j\<in>J. A j \<in> F j"
    hence c4: "\<forall>j\<in>J'. (A \<circ> f) j \<in> (F \<circ> f) j"
      using J'_def by fastforce
    have "prob (\<Inter> ((A \<circ> f) ` J')) = (\<Prod>j\<in>J'. prob ((A \<circ> f) j))"
      using a indep_setsD c1 c2 c3 c4 by blast    
    moreover have c5:"inj_on f J'" using c1 assms inj_on_subset by blast
    moreover have "J = f ` J'" using c5 apply (simp add:J'_def)
      apply (rule order_antisym, rule subsetI)
      using a1 apply auto[1]      
      by force
    ultimately show "prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))"
      by (simp add: prod.reindex_cong)
  qed
  ultimately show ?thesis by auto
qed

lemma (in prob_space) indep_vars_reindex:
  assumes "inj_on f I"
  assumes "indep_vars M' X1 (f ` I)"
  shows "indep_vars (M' \<circ> f) (X1 \<circ> f) I"
  using assms by (simp add: indep_vars_def2 indep_sets_reindex comp_def)

lemma
  assumes "prob_space \<Omega>"
  assumes "finite A"
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1::real, 1} \<Longrightarrow> prob_space.prob \<Omega> (h i -` {\<sigma>}) = 1/2"
  shows var_f2:"(prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4))
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2))^2 \<le> 2*(sum (\<lambda>i. (count_list xs i)^2) (set xs))^2" (is ?A)
  and exp_f2:"prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2) = sum (\<lambda>i. (count_list xs i)^2) (set xs)" (is ?B)
proof -
  have b:"\<And>x j n m. x \<in> maps_inj n (set xs) \<Longrightarrow> j < n \<Longrightarrow> even m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = count_list xs (the (x j)) ^ m"
    sorry

  have c:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow> odd m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = 0"
    sorry

  have d:"Sigma_Algebra.measure \<Omega> (space \<Omega>) = 1" using assms(1) 
    by (simp add: prob_space.prob_space)

  have e1:"\<And>x n j m. x \<in> maps_inj n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    integrable \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m)"
    sorry
  have e: "\<And>x n a. x \<in> maps n (set xs) \<Longrightarrow> filter (\<lambda>i. i \<ge> n) a = [] \<Longrightarrow> integrable \<Omega> (f2_tr h xs x a)" sorry

  have  "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> ((\<lambda>_. borel) \<circ> (\<lambda>i. the (x i))) (h \<circ> (\<lambda>i. the (x i))) {k. k < n}"
    apply (rule prob_space.indep_vars_reindex)
    using assms(1) apply simp
     apply (simp add:maps_inj_mem)
    apply (rule assms(3))
    apply (rule image_subsetI) apply(simp add:maps_inj_elim)
     apply blast
    by (metis card_Collect_less_nat card_image_le finite_Collect_less_nat le_neq_implies_less less_trans verit_comp_simplify1(3))
  hence indep_1:
    "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
    by (simp add:comp_def)

  have indep:
    "\<And>x n j. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow>
    prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. f2_sketch_summand_pow h xs (the (x i)) (j i)) {k. k < n}"
  proof -
    fix x n j
    assume a1: "x \<in> maps_inj n (set xs)"
    assume a2: "n \<le> 4"
    have "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
      using a1 a2 indep_1 by auto
    moreover define Y where "Y = (\<lambda>k t. (real (count_list xs (the (x k))) * t)^ (j k))"
    moreover have "\<And>k. k < n \<Longrightarrow> Y k \<in> measurable borel borel" sorry
    ultimately have "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. Y i \<circ> h (the (x i))) {k. k < n}"
      using prob_space.indep_vars_compose assms(1) by fast
    thus "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i \<omega>. f2_sketch_summand_pow h xs (the (x i)) (j i) \<omega>) {k. k < n}"
      by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def Y_def comp_def) 
  qed

  have c4: "\<And>x n a. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> set a \<subseteq> {k. k < n} \<Longrightarrow> integral\<^sup>L \<Omega> (f2_tr h xs x a) =
    prod_list (map (\<lambda>(i,j). (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) j \<omega>))) (counts a))"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    have "(LINT \<omega>|\<Omega>. f2_tr h xs x a \<omega>) =
      prod (\<lambda>i. (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) (count (mset a) i) \<omega>))) (set a)"
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule prob_space.indep_vars_lebesgue_integral)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) prob_space.indep_vars_subset apply blast
      using e1 a1 a3 by blast

    thus "integral\<^sup>L \<Omega> (f2_tr h xs x a) =
    prod_list (map (\<lambda>(i,j). (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) j \<omega>))) (counts a))"
      using countsI by fastforce
  qed

  show ?A
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: c1 c2)
    apply (simp add: Bochner_Integration.integral_sum e)
    apply (simp add: f2_tr_def sum_distrib_left sum_distrib_right sum_unroll_2 sum_subtractf[symmetric])
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    apply (simp add: c4 b c d)
    by (simp add: sum_distrib_left sum_nonneg)

  show ?B
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: c1 c2)
    apply (simp add: Bochner_Integration.integral_sum e)
    apply (simp add: f2_tr_def sum_distrib_left sum_distrib_right sum_unroll_2 sum_subtractf[symmetric])
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    by (simp add: c4 b c d)
qed

end