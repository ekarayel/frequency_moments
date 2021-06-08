theory Frequency_Moment_2
  imports Main SumByPartitions "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family" "HOL-Algebra.Congruence"
begin

section \<open>Frequency Moment 2\<close>

text \<open>This algorithm estimates the second frequency moment F_2, it was introduced by Alon et. al.:

Let $a_1, \cdots, a_n \subset U = \{0,\ldots,m-1\}$ be a sequence. It makes one (read-only) pass
over the sequence requiring $O(- \<lambda>^{-1} log \varepsilon (log n + log m))$ bits of memory. At the
end it returns an estimate $F_2^{*}$ that deviates from $F_2$ by more than $\lambda F_2$ with
probability at most $\varepsilon$.\<close>

subsection \<open>Sketch\<close>

definition f2_sketch_summand
  where
    "f2_sketch_summand f xs x \<omega> = (real (count_list xs x) * f x \<omega> :: real)"

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. f2_sketch_summand f xs x \<omega>)"

text \<open>This is a disjoint induction scheme for multisets: We can represent each multiset as
a sum like: replicate_mset n x_1 + replicate_mset n x_2 + .. + replicate_mset n x_n where the 
x_i are distinct.\<close>

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
    "f2_sketch_summand_pow h xs x n \<omega> = (f2_sketch_summand h xs x \<omega>) ^ n"

fun counts where
  "counts xs = map (\<lambda>x. (x,count_list xs x)) (remdups xs)" 

lemma countsI: "prod (\<lambda>i. f i (count (mset a) i)) (set a) = prod_list (map (\<lambda>i. f (fst i) (snd i)) (counts a))"
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
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i \<sigma>. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1,1::real} \<Longrightarrow> prob_space.prob \<Omega> ((h i -` {\<sigma>}) \<inter> space \<Omega>) = 1/2"
  shows var_f2:"(prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4))
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2))^2 \<le> 2*(sum (\<lambda>i. (count_list xs i)^2) (set xs))^2" (is "?A - ?B \<le> ?C")
  and exp_f2:"prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2) = sum (\<lambda>i. (count_list xs i)^2) (set xs)" (is ?D)
  and int_exp_f2:"integrable \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2)" (is ?E)
  and int_var_f2:"integrable \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4)" (is ?F)
proof -
  have "\<And>i. i \<in> set xs \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h {i}" using assms(2) by simp
  hence meas:"\<And>i. i \<in> set xs \<Longrightarrow> h i \<in> measurable \<Omega> borel" using assms(1) by (simp add:prob_space.indep_vars_def2) 

  have "\<And>x m. x \<in> set xs  \<Longrightarrow>
    has_bochner_integral \<Omega> (f2_sketch_summand_pow h xs x m) (if odd m then 0 else count_list xs x ^ m)"
  proof -
    fix x
    fix m
    assume a:"x \<in> set xs"

    define f where "f = (\<lambda>\<omega>. indicator (h x -` {-1} \<inter> space \<Omega>) \<omega> + ((indicator (h x -` {1} \<inter> space \<Omega>) \<omega>) :: real))"

    define t where "t = (1:: real)"
    have b:"t = prob_space.prob \<Omega> ((h x -` {-1}) \<inter> space \<Omega>) + prob_space.prob \<Omega> ((h x -` {1}) \<inter> space \<Omega>)"
      using a by (simp add:assms(3) t_def)
    have d:"h x -` {-1,1}  \<inter> space \<Omega> = (h x -` {-1}  \<inter> space \<Omega>) \<union> (h x -` {1}  \<inter> space \<Omega>)" by blast
    have c:"prob_space.prob \<Omega> ((h x -` {-1,1}) \<inter> space \<Omega>) = t" apply (simp add: b d)
      apply (rule measure_Union)
      using finite_measure.emeasure_finite prob_space_def assms(1) apply auto[1]
      using finite_measure.emeasure_finite prob_space_def assms(1) apply auto[1]
      using a meas apply measurable[1]
      using a meas apply measurable[1]
      by fastforce
    hence "prob_space.prob \<Omega> (h x -` {-1,1} \<inter> space \<Omega>) = 1" by (simp add:t_def)

    hence "AE \<omega> in \<Omega>. h x \<omega> \<in> {-1, 1}"
      using assms(1)  prob_space.AE_prob_1 by force
    hence f_eval: "AE x in \<Omega>. f x = 1" apply (simp add:f_def split:split_indicator) by linarith
    have f_meas: "f \<in> measurable \<Omega> borel" using a meas by (simp add:f_def, measurable)
  
    have eval_neg: "\<And>\<omega>.
      f2_sketch_summand_pow h xs x m \<omega> * indicator (h x -` {-1} \<inter> space \<Omega>) \<omega> = 
      (-(real (count_list xs x)))^m  * indicator (h x -` {-1} \<inter> space \<Omega>) \<omega>"
      by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def split:split_indicator)
  
    have eval_pos: "\<And>\<omega>. 
      f2_sketch_summand_pow h xs x m \<omega> * indicat_real (h x -` {1} \<inter> space \<Omega>) \<omega> = 
      (real (count_list xs x))^m  * indicat_real (h x -` {1} \<inter> space \<Omega>) \<omega>"
      by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def split:split_indicator)

    have "\<And>\<sigma>. \<sigma> \<in> {-1,1} \<Longrightarrow> emeasure \<Omega> (h x -` {\<sigma>} \<inter> space \<Omega>) < \<infinity>"
      using a assms(3) apply (simp add:measure_def) 
      using top.not_eq_extremum by fastforce 
    moreover have "\<And>\<sigma>. \<sigma> \<in> {-1,1} \<Longrightarrow> (h x -` {\<sigma>} \<inter> space \<Omega>) \<in> sets \<Omega>" 
      by (meson borel_measurable_vimage a meas)
    ultimately have integrable_pos: "\<And>\<sigma>. \<sigma> \<in> {-1,1} \<Longrightarrow>
      integrable \<Omega> (\<lambda>\<omega>. (real (count_list xs x))^m  * indicat_real (h x -` {\<sigma>} \<inter> space \<Omega>) \<omega>)"
      by simp
    
    have "integral\<^sup>L \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega> * f \<omega>) = (if odd m then 0 else count_list xs x ^ m)"
      apply (simp add:f_def algebra_simps(18) eval_pos eval_neg)
      using  integrable_pos apply (simp add: integral_add integral_diff)
      apply (cases "odd m") using a by (simp add:assms(3))+
    moreover have "integrable \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega> * f \<omega>)" 
      apply (simp add:f_def algebra_simps(18) eval_pos eval_neg)
      apply (cases "odd m") using  integrable_pos integrable_neg by simp+ 
    ultimately have "has_bochner_integral \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega> * f \<omega>) (if odd m then 0 else count_list xs x ^ m)"
      by (simp add: has_bochner_integral_iff)
    moreover have "has_bochner_integral \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega> * f \<omega>) (if odd m then 0 else count_list xs x ^ m) = (
          has_bochner_integral \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega>) (if odd m then 0 else count_list xs x ^ m))"
      apply (rule has_bochner_integral_cong_AE)
        apply (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def) using a meas f_meas apply measurable
        apply (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def) using a meas f_meas apply measurable
      apply (simp add:f2_sketch_summand_pow_def) using f_eval by force
    ultimately show "has_bochner_integral \<Omega> (f2_sketch_summand_pow h xs x m) (if odd m then 0 else count_list xs x ^ m)"
      by auto
  qed

  hence c:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    has_bochner_integral \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) (if odd m then 0 else  count_list xs (the (x j)) ^ m)"
    by (meson maps_inj_elim)

  hence d1:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = (if odd m then 0 else  count_list xs (the (x j)) ^ m)"
    using has_bochner_integral_iff by blast

  have  "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> ((\<lambda>_. borel) \<circ> (\<lambda>i. the (x i))) (h \<circ> (\<lambda>i. the (x i))) {k. k < n}"
    apply (rule prob_space.indep_vars_reindex)
    using assms(1) apply simp
     apply (simp add:maps_inj_mem)
    apply (rule assms(2))
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
    moreover have "\<And>k. k < n \<Longrightarrow> Y k \<in> measurable borel borel" by (simp add:Y_def, measurable)
    ultimately have "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. Y i \<circ> h (the (x i))) {k. k < n}"
      using prob_space.indep_vars_compose assms(1) by fast
    thus "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i \<omega>. f2_sketch_summand_pow h xs (the (x i)) (j i) \<omega>) {k. k < n}"
      by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def Y_def comp_def) 
  qed
  define f2_tr
    where
      "f2_tr =(\<lambda>n l \<omega>. prod_mset (image_mset (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) (mset (l :: nat list))))"
  
  have c1: "\<And>n k \<omega>. f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr n [k] \<omega>"
    by (simp add:f2_tr_def)
  
  have c2: "\<And>n a b \<omega>. f2_tr n a \<omega> * f2_tr n b \<omega> = f2_tr n (a@b) \<omega>"
    by (simp add:f2_tr_def)

  have indep2:
    "\<And> x n a. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4  \<Longrightarrow>  set a \<subseteq> {k. k < n} \<Longrightarrow>
      integrable \<Omega> (f2_tr x a)"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    show "integrable \<Omega> (\<lambda>\<omega>. f2_tr x a \<omega>) "
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule prob_space.indep_vars_integrable)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) prob_space.indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
  qed

  have indep1:
    "\<And> x n a. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4  \<Longrightarrow>  set a \<subseteq> {k. k < n} \<Longrightarrow>
      integral\<^sup>L \<Omega> (f2_tr x a) = (prod_list (map (\<lambda>i. (if odd (snd i) then 0 else real (count_list xs (the (x (fst i))) ^ (snd i)))) (counts a)))"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    have c4: "\<And> i. i \<in> set (counts a) \<Longrightarrow> fst i < n" using a3 by auto

    have "(LINT \<omega>|\<Omega>. f2_tr x a \<omega>) =
      prod (\<lambda>i. (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) (count (mset a) i) \<omega>))) (set a)"
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule prob_space.indep_vars_lebesgue_integral)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) prob_space.indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
    
    hence "integral\<^sup>L \<Omega> (f2_tr x a) =
      prod_list (map (\<lambda>i. (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x (fst i))) (snd i) \<omega>))) (counts a))"
      using countsI by fastforce
    also have "... = prod_list (map (\<lambda>i. (if odd (snd i) then 0 else real ( count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      apply (rule arg_cong [where f="prod_list"])
      apply (rule map_cong, simp)
      using a1 c4 by (simp add:d1)
    finally show "integral\<^sup>L \<Omega> (f2_tr x a) = prod_list (map (\<lambda>i. (if odd (snd i) then 0 else real (count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      by simp
  qed

  have exp_2: "?D"
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    by (simp add: Bochner_Integration.integral_sum indep1 indep2)
  thus ?D by auto

  have "?A \<le> ?B + ?C"
    apply (simp add:exp_2)
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    apply (simp add: Bochner_Integration.integral_sum indep1 indep2)
    apply (simp add: sum_distrib_left sum_distrib_right)
    by (simp add: sum_mono)
  thus "?A - ?B \<le> ?C" by auto

  show ?E
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    by (simp add: c1 c2 indep1 indep2)

  show ?F
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    by (simp add: c1 c2 indep1 indep2)
qed

end