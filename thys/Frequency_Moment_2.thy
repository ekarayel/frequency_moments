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

definition f2_tr
  where
    "f2_tr h xs n l \<omega> = prod_mset (image_mset (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) (mset (l :: nat list)))"

lemma c1: "f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr h xs n [k] \<omega>"
  by (simp add:f2_tr_def)

lemma c2: "f2_tr h xs n a \<omega> * f2_tr h xs n b \<omega> = f2_tr h xs n (a@b) \<omega>"
  by (simp add:f2_tr_def)

fun counts where
  "counts xs = map (\<lambda>x. (x,count_list xs x)) (remdups xs)" 

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

lemma add_dec:
  assumes "has_bochner_integral \<Omega> (\<lambda>\<omega>. g \<omega>) (rg)"
  assumes "has_bochner_integral \<Omega> (\<lambda>\<omega>. f \<omega>) (rf)"
  assumes "r = rf + rg"
  shows "has_bochner_integral \<Omega> (\<lambda>\<omega>. (f \<omega> + g \<omega>)) (r)"
  using has_bochner_integral_add
  by (simp add: assms(1) assms(2) assms(3) has_bochner_integral_add)

lemma sum_dec:
  assumes "\<And>t. t \<in> A \<Longrightarrow> has_bochner_integral \<Omega> (\<lambda>\<omega>. f \<omega> t) (r t)"
  assumes "sum r A = ra"
  shows "has_bochner_integral \<Omega> (\<lambda>\<omega>. (sum (f \<omega>) A)) ra"
proof -
  have "has_bochner_integral \<Omega> (\<lambda>\<omega>. (sum (f \<omega>) A)) (sum r A)"
    apply (rule has_bochner_integral_sum)
    using assms by simp
  thus ?thesis using assms(2) by force
qed

lemma test_1:
  assumes "x \<in> maps_inj n (set xs)"
  assumes "i < n"
  assumes "r = (if odd j then 0 else  count_list xs (the (x i)) ^ j)"
  shows "(has_bochner_integral \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs (the (x i)) j \<omega>) r)"
  sorry

lemma indep:
  assumes "x \<in> maps_inj n (set xs) \<and> n \<le> 4"
  assumes "\<And>i j. i < n \<Longrightarrow> has_bochner_integral \<Omega> (\<lambda>\<omega>. f2_sketch_summand_pow h xs (the (x i)) j \<omega>) (r i j)"
  assumes "prod_list (map (\<lambda>(i,j). r i j) (counts a)) = r'"
  shows "has_bochner_integral \<Omega> (f2_tr h xs x a) r'"
  sorry
(*
lemma
  assumes "prob_space \<Omega>"
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i \<sigma>. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1,1::real} \<Longrightarrow> prob_space.prob \<Omega> ((h i -` {\<sigma>}) \<inter> space \<Omega>) = 1/2"
  shows "has_bochner_integral \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4) x \<and> x < 5"
  apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
  apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
  apply (simp add: split_fun_set_sum_into_partitions)
  apply ((auto intro!: add_dec sum_dec indep test_1 simp add:c1 c2)[1])
  sorry

lemma
  assumes "prob_space \<Omega>"
  assumes "finite A"
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i \<sigma>. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1,1::real} \<Longrightarrow> prob_space.prob \<Omega> ((h i -` {\<sigma>}) \<inter> space \<Omega>) = 1/2"
  shows var_f2:"(prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4))
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2))^2 \<le> 2*(sum (\<lambda>i. (count_list xs i)^2) (set xs))^2" (is ?A)
  and exp_f2:"prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2) = sum (\<lambda>i. (count_list xs i)^2) (set xs)" (is ?B)
proof -
  have "prob_space.prob \<Omega> (space \<Omega>) = 1" using assms(1) 
    by (simp add: prob_space.prob_space)

  have "\<And>i. i \<in> set xs \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h {i}" using assms(3) by simp
  hence meas:"\<And>i. i \<in> set xs \<Longrightarrow> h i \<in> measurable \<Omega> borel" using assms(3) assms(1) by (simp add:prob_space.indep_vars_def2) 
  have "\<And>i. i \<in> set xs \<Longrightarrow> prob_space.prob \<Omega> (h i -` {-1, 1} \<inter> space \<Omega>) = 1"
  proof -
    fix i
    assume a:"i \<in> set xs"
    define t where "t = (1 :: real)"  
    have b:"t  = prob_space.prob \<Omega> ((h i -` {-1}) \<inter> space \<Omega>) + prob_space.prob \<Omega> ((h i -` {1}) \<inter> space \<Omega>)" using a by (simp add:assms(4) t_def)
    have d:"h i -` {-1,1}  \<inter> space \<Omega> = (h i -` {-1}  \<inter> space \<Omega>) \<union> (h i -` {1}  \<inter> space \<Omega>)" by blast 
    have c:"prob_space.prob \<Omega> ((h i -` {-1,1}) \<inter> space \<Omega>) = t" apply (simp add: b d)
      apply (rule measure_Union)
      using finite_measure.emeasure_finite prob_space_def assms(1) apply auto[1]
      using finite_measure.emeasure_finite prob_space_def assms(1) apply auto[1]
      using a meas apply measurable[1]
      using a meas apply measurable[1]
      by fastforce
    have  "(AE \<omega> in \<Omega> . \<omega> \<in> (h i -` {-1, 1} \<inter> space \<Omega>))" 
      apply (rule prob_space.AE_prob_1)
      using assms(1) apply simp
      using c t_def by auto
    hence  e:"AE \<omega> in \<Omega> . (norm \<circ> h i) \<omega> = 1" by force
    have "integrable \<Omega> (h i)"
      apply (rule finite_measure.integrable_const_bound)
      using assms(1) apply (simp add: prob_space.finite_measure)
      using e apply force
      using a meas by measurable
    show "prob_space.prob \<Omega> (h i -` {-1, 1} \<inter> space \<Omega>) = 1" sorry
  qed




  (* proposition integrableI_bounded *)
  have int_ind: "\<And>x y. x \<in> set xs \<Longrightarrow> integrable \<Omega> (\<lambda>\<omega>. y * indicat_real (h x -` {- 1} \<inter> space \<Omega>) \<omega>)"
    sorry
  have int_ind_2: "\<And>x y. x \<in> set xs \<Longrightarrow> integrable \<Omega> (\<lambda>\<omega>. y * indicat_real (h x -` {1} \<inter> space \<Omega>) \<omega>)"
    sorry
  have eval_neg: "\<And>x m \<omega>.  x\<in> set xs  \<Longrightarrow> 
    f2_sketch_summand_pow h xs x m \<omega> * indicator (h x -` {-1} \<inter> space \<Omega>) \<omega> = 
    (-count_list xs x :: real)^m  * indicator (h x -` {-1} \<inter> space \<Omega>) \<omega>"
    by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def split:split_indicator)

  have eval_pos: "\<And>x m \<omega>.  x\<in> set xs  \<Longrightarrow>
    f2_sketch_summand_pow h xs x m \<omega> * indicator (h x -` {1} \<inter> space \<Omega>) \<omega> = 
    (count_list xs x :: real)^m  * indicator (h x -` {1} \<inter> space \<Omega>) \<omega>"
    by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def split:split_indicator)

  have "\<And>x m. x \<in> set xs \<Longrightarrow> even m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs x m) = count_list xs x ^ m"
    sorry
  hence b:"\<And>x j n m. x \<in> maps_inj n (set xs) \<Longrightarrow> j < n \<Longrightarrow> even m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = count_list xs (the (x j)) ^ m"
    by (meson maps_inj_elim)

  have "\<And>x m. x \<in> set xs \<Longrightarrow> odd m \<Longrightarrow> integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs x m) = 0"
  proof -
    fix x
    fix m
    assume a: "x \<in> set xs"
    assume b:"odd (m :: nat)"

    have int_ind: "integrable \<Omega> (\<lambda>\<omega>.  (- real (count_list xs x)) ^ m * indicat_real (h x -` {- 1} \<inter> space \<Omega>) \<omega>)"
      sorry
    have int_ind_2: "integrable \<Omega> (\<lambda>\<omega>.  (real (count_list xs x)) ^ m * indicat_real (h x -` {1} \<inter> space \<Omega>) \<omega>)"
      sorry

    have "integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs x m) = 
        (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs x m \<omega> * indicator (h x -` {-1} \<inter> space \<Omega>) \<omega>) +
        ( f2_sketch_summand_pow h xs x m \<omega> * indicator (h x -` {1} \<inter> space \<Omega>) \<omega>))" 
      sorry
    also have "... = 
        (LINT \<omega>|\<Omega>. (- real (count_list xs x)) ^ m * indicat_real (h x -` {-1} \<inter> space \<Omega>) \<omega>) +
        (LINT \<omega>|\<Omega>. (real (count_list xs x)) ^ m * indicat_real (h x -` {1} \<inter> space \<Omega>) \<omega>)" 
      apply (simp add:eval_pos a eval_neg)
      apply (rule Bochner_Integration.integral_add)
      apply (simp add:f2_sketch_summand_pow_def)
    also have "... = 0"
      apply (simp add: a eval_pos eval_neg assms) using b by simp
    finally show "integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs x m) = 0" by blast
  qed

  hence c:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow> odd m \<Longrightarrow>
    integral\<^sup>L \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m) = 0"
    by (meson maps_inj_elim)
                                                         
  have d:"Sigma_Algebra.measure \<Omega> (space \<Omega>) = 1" using assms(1) 
    by (simp add: prob_space.prob_space)

  have "\<And>x n m. x \<in> set xs \<Longrightarrow>
    integrable \<Omega> (f2_sketch_summand_pow h xs x m)" sorry

  hence e1:"\<And>x n j m. x \<in> maps_inj n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    integrable \<Omega> (f2_sketch_summand_pow h xs (the (x j)) m)"
    by (meson maps_inj_elim)

  have e: "\<And>x n a. x \<in> maps n (set xs) \<Longrightarrow> filter (\<lambda>i. i \<ge> n) a = [] \<Longrightarrow> integrable \<Omega> (f2_tr h xs x a)"
  proof -
    fix x n a
    assume a:"x \<in> maps n (set xs)"
    assume b:"filter (\<lambda>i. i \<ge> n) a = []"
    have c:"AE \<omega> in \<Omega>. norm (f2_tr h xs x a \<omega>) \<le> length xs * length a" 
      apply (simp add:f2_tr_def f2_sketch_summand_def)
      using [[simp_trace]]
      apply (simp add:norm_prod) sorry
    have "\<And>i. i \<in> set a \<Longrightarrow> the (x i) \<in> set xs"
      using b apply (simp add:filter_empty_conv not_le)
      using a apply (simp add:maps_def) 
      by (metis (mono_tags, lifting) domIff mem_Collect_eq option.collapse ran_def subset_iff)
    hence "\<And>i. i \<in> set a \<Longrightarrow> h (the (x i)) \<in> measurable \<Omega> borel"
      using meas a by blast
    hence d:"(\<lambda>\<omega>. f2_tr h xs x a \<omega>) \<in> measurable \<Omega> borel"
      apply (simp add:f2_tr_def prod_mset_conv)
      by (simp add:f2_sketch_summand_def)
    show "integrable \<Omega> (f2_tr h xs x a)"
      apply (rule finite_measure.integrable_const_bound)
      using assms(1) apply (simp add: prob_space.finite_measure)
      using c apply force
      using d by measurable
  qed

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
    moreover have "\<And>k. k < n \<Longrightarrow> Y k \<in> measurable borel borel" by (simp add:Y_def, measurable)
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
*)

lemma "f1 = g1 \<Longrightarrow> f2 = g2 \<Longrightarrow> f1 f2 = g1 g2" by auto

lemma
  assumes "prob_space \<Omega>"
  assumes "finite A"
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i \<sigma>. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1,1::real} \<Longrightarrow> prob_space.prob \<Omega> ((h i -` {\<sigma>}) \<inter> space \<Omega>) = 1/2"
  shows var_f2:"(prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4))
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2))^2 \<le> 2*(sum (\<lambda>i. (count_list xs i)^2) (set xs))^2" (is "?A - ?B \<le> ?C")
  and exp_f2:"prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2) = sum (\<lambda>i. (count_list xs i)^2) (set xs)" (is ?D)
proof -

  have "\<And>x j m. x \<in> set xs  \<Longrightarrow>
    has_bochner_integral \<Omega> (f2_sketch_summand_pow h xs x m) (if odd m then 0 else  count_list xs x ^ m)"
    sorry

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
    moreover have "\<And>k. k < n \<Longrightarrow> Y k \<in> measurable borel borel" by (simp add:Y_def, measurable)
    ultimately have "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. Y i \<circ> h (the (x i))) {k. k < n}"
      using prob_space.indep_vars_compose assms(1) by fast
    thus "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i \<omega>. f2_sketch_summand_pow h xs (the (x i)) (j i) \<omega>) {k. k < n}"
      by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def Y_def comp_def) 
  qed

  have indep2:
    "\<And> x n a. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4  \<Longrightarrow>  set a \<subseteq> {k. k < n} \<Longrightarrow>
      integrable \<Omega> (f2_tr h xs x a)"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    show "integrable \<Omega> (\<lambda>\<omega>. f2_tr h xs x a \<omega>) "
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule prob_space.indep_vars_integrable)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) prob_space.indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
  qed

  have indep1:
    "\<And> x n a. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4  \<Longrightarrow>  set a \<subseteq> {k. k < n} \<Longrightarrow>
      integral\<^sup>L \<Omega> (f2_tr h xs x a) = (prod_list (map (\<lambda>i. (if odd (snd i) then 0 else real (count_list xs (the (x (fst i))) ^ (snd i)))) (counts a)))"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    have c4: "\<And> i. i \<in> set (counts a) \<Longrightarrow> fst i < n" using a3 by auto

    have "(LINT \<omega>|\<Omega>. f2_tr h xs x a \<omega>) =
      prod (\<lambda>i. (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) (count (mset a) i) \<omega>))) (set a)"
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule prob_space.indep_vars_lebesgue_integral)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) prob_space.indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
    
    hence "integral\<^sup>L \<Omega> (f2_tr h xs x a) =
      prod_list (map (\<lambda>i. (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x (fst i))) (snd i) \<omega>))) (counts a))"
      using countsI by fastforce
    also have "... = prod_list (map (\<lambda>i. (if odd (snd i) then 0 else real ( count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      apply (rule arg_cong [where f="prod_list"])
      apply (rule map_cong, simp)
      using a1 c4 by (simp add:d1)
    finally show "integral\<^sup>L \<Omega> (f2_tr h xs x a) = prod_list (map (\<lambda>i. (if odd (snd i) then 0 else real (count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
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
qed

end