section \<open>Frequency Moment 2\<close>

theory Frequency_Moment_2
  imports Main SumByPartitions "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family" "HOL-Algebra.Congruence"
begin

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
    hence "P M1" using 1 by blast
    then show "P M" 
      apply (subst M_def, rule assms(2), simp)
      by (simp add:M1_def x_def count_eq_zero_iff[symmetric])+
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

lemma (in prob_space)
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> indep_vars (\<lambda>_. borel) h I"
  assumes "\<And>i (m :: nat). i \<in> set xs \<Longrightarrow> integrable M (\<lambda>\<omega>. (h i \<omega>)^m)"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (h i) = 0"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^2) = 1"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^4) \<le> 3"
  shows var_f2:"variance (\<lambda>\<omega>. f2_sketch h xs \<omega>^2)
        \<le> (2*(sum (\<lambda>i. count_list xs i^2) (set xs))^2)" (is "?A \<le> ?B")
  and exp_f2:"expectation (\<lambda>\<omega>. f2_sketch h xs \<omega>^2) = sum (\<lambda>i. count_list xs i^2) (set xs)" (is ?D)
  and int_exp_f2:"integrable M (\<lambda>\<omega>. f2_sketch h xs \<omega>^2)" (is ?E)
  and int_var_f2:"integrable M (\<lambda>\<omega>. (f2_sketch h xs \<omega>^2)^2)" (is ?F)
proof -

  have "\<And>i. i \<in> set xs \<Longrightarrow> indep_vars (\<lambda>_. borel) h {i}" using assms(1) by simp
  hence meas:"\<And>i. i \<in> set xs \<Longrightarrow> h i \<in> measurable M borel" by (simp add:indep_vars_def2) 

  define exp' where "exp' = (\<lambda>i m. expectation (\<lambda>\<omega>. (h i \<omega>)^m))"
  define exp where "exp = (\<lambda>i m. if m = 1 then 0 else (if m = 2 then 1 else exp' i m))"
  define g where "g = (\<lambda>i. exp' i 4 - 3)"
  have exp_4: "\<And>x. x \<in> set xs \<Longrightarrow> exp' x (Suc (Suc (Suc (Suc 0)))) = 3 + g x" using assms(5) 
    by (simp add: numeral_eq_Suc exp'_def g_def) 
  have g_4: "\<And>x. x \<in> set xs \<Longrightarrow> g x \<le> 0" using assms(5) by (simp add:exp'_def g_def)

  have "\<And>x m. x \<in> set xs  \<Longrightarrow>
    has_bochner_integral M (f2_sketch_summand_pow h xs x m) (exp x m * (count_list xs x ^ m))"
  proof -
    fix x
    fix m
    assume a:"x \<in> set xs"

    show "has_bochner_integral M (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega>) (exp x m * (count_list xs x ^ m))"
      apply (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def has_bochner_integral_iff)
      apply (rule conjI)
      using a assms(2) apply (simp add:algebra_simps)
      apply (cases "m=1", simp add:exp_def assms(3) a)
      apply (cases "m=2", simp add:algebra_simps exp_def assms(4) a)
      by (simp add:exp_def exp'_def algebra_simps)
  qed

  hence c:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    has_bochner_integral M (f2_sketch_summand_pow h xs (the (x j)) m) (exp (the (x j)) m * (count_list xs (the (x j)) ^ m))"
    by (meson maps_inj_elim)

  hence d1:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    integral\<^sup>L M (f2_sketch_summand_pow h xs (the (x j)) m) = (exp (the (x j)) m) *  (count_list xs (the (x j)) ^ m)"
    using has_bochner_integral_iff by blast

  have  "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> indep_vars ((\<lambda>_. borel) \<circ> (\<lambda>i. the (x i))) (h \<circ> (\<lambda>i. the (x i))) {k. k < n}"
    apply (rule prob_space.indep_vars_reindex)
    apply (simp add: prob_space_axioms)
     apply (simp add:maps_inj_mem)
    apply (rule assms(1))
    apply (rule image_subsetI) apply(simp add:maps_inj_elim)
     apply blast
    by (metis card_Collect_less_nat card_image_le finite_Collect_less_nat le_neq_implies_less less_trans verit_comp_simplify1(3))
  hence indep_1:
    "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> indep_vars (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
    by (simp add:comp_def)

  have indep:
    "\<And>x n j. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow>
    indep_vars (\<lambda>_. borel) (\<lambda>i. f2_sketch_summand_pow h xs (the (x i)) (j i)) {k. k < n}"
  proof -
    fix x n j
    assume a1: "x \<in> maps_inj n (set xs)"
    assume a2: "n \<le> 4"
    have "indep_vars (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
      using a1 a2 indep_1 by auto
    moreover define Y where "Y = (\<lambda>k t. (real (count_list xs (the (x k))) * t)^ (j k))"
    moreover have "\<And>k. k < n \<Longrightarrow> Y k \<in> measurable borel borel" by (simp add:Y_def, measurable)
    ultimately have "indep_vars (\<lambda>_. borel) (\<lambda>i. Y i \<circ> h (the (x i))) {k. k < n}"
      using indep_vars_compose by fast
    thus "indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. f2_sketch_summand_pow h xs (the (x i)) (j i) \<omega>) {k. k < n}"
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
      integrable M (f2_tr x a)"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    show "integrable M (\<lambda>\<omega>. f2_tr x a \<omega>) "
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule indep_vars_integrable)
         apply (simp add:prob_space_axioms)+
      using indep a2 a1 a3 assms(1) indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
  qed

  have indep1:
    "\<And> x n a. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4  \<Longrightarrow>  set a \<subseteq> {k. k < n} \<Longrightarrow>
      integral\<^sup>L M (f2_tr x a) = prod_list (map (\<lambda>i. exp (the (x (fst i))) (snd i) * real (count_list xs (the (x (fst i))) ^ (snd i))) (counts a))"
  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    have c4: "\<And> i. i \<in> set (counts a) \<Longrightarrow> fst i < n" using a3 by auto

    have "(LINT \<omega>|M. f2_tr x a \<omega>) =
      prod (\<lambda>i. (LINT \<omega>|M. (f2_sketch_summand_pow h xs (the (x i)) (count (mset a) i) \<omega>))) (set a)"
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule indep_vars_lebesgue_integral)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
    
    hence "integral\<^sup>L M (f2_tr x a) =
      prod_list (map (\<lambda>i. (LINT \<omega>|M. (f2_sketch_summand_pow h xs (the (x (fst i))) (snd i) \<omega>))) (counts a))"
      using countsI by fastforce
    also have "... = prod_list (map (\<lambda>i. (exp (the (x (fst i))) (snd i) * real ( count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      apply (rule arg_cong [where f="prod_list"])
      apply (rule map_cong, simp)
      using a1 c4 by (simp add:d1)
    finally show "integral\<^sup>L M (f2_tr x a) = prod_list (map (\<lambda>i. (exp (the (x (fst i))) (snd i) * real (count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      by simp
  qed

  show int_exp_f2:?E
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    by (simp add: c1 c2 indep1 indep2)

  show int_var_f2:?F
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    by (simp add: c1 c2 indep1 indep2)

  have exp_2: "?D"
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    by (simp add: Bochner_Integration.integral_sum indep1 indep2 exp_def)
  thus ?D by auto

  show "?A \<le> ?B"
    apply (subst variance_eq, metis int_exp_f2, metis int_var_f2)
    apply (simp add: exp_2)
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)  
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2)
    apply (simp add: Bochner_Integration.integral_sum indep1 indep2)
    apply (simp add: exp_def)
    apply (simp add: sum_distrib_left distrib_left distrib_right ac_simps)
    apply (rule sum_mono)
    apply (simp add:exp_4 maps_inj_elim algebra_simps)
    by (simp add: maps_inj_elim g_4 mult_nonneg_nonpos2)
qed


definition four_canonical_maps where
  "four_canonical_maps = [
    [0,1,2,3],
    [0,0,2,3],
    [0,1,0,3],
    [0,1,2,0],
    [0,1,1,3],
    [0,1,2,1],
    [0,1,2,2],
    [0,0,0,3],
    [0,0,2,0],
    [0,1,0,0],
    [0,1,1,1],
    [0,0,2,2],
    [0,1,0,1],
    [0,1,1,0],
    [0,0,0,0]]"

definition same_partition :: "(nat \<Rightarrow> nat) \<Rightarrow> 'b list \<Rightarrow> bool"  where "same_partition f ys = 
  (\<forall>k l. k < length ys \<and> l < length ys \<longrightarrow> (f k = f l) = (ys ! k = ys ! l))"

lemma sum_collapse: 
  assumes "z \<in> A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<noteq> z \<Longrightarrow> f y = (0::real)"
  shows "sum f A = f z"
  sorry

fun check where
  "check fx f y [] = True" |
  "check fx f y (yy#ys) = ((if fx = f 0 then y = yy else (if fx < f 0 then y \<noteq> yy else yy \<noteq> y)) \<and> check fx (f \<circ> Suc) y ys)"

lemma same_partition_elim:
  "same_partition f (y#ys) = (same_partition (f \<circ> Suc) ys \<and> check (f 0) (f \<circ> Suc) y ys)"
  sorry

lemma same_partition_elim_2:
  "same_partition f [] = True"
  sorry

value "map (fst ((enum_canonical_mapping (Suc (Suc (Suc 0))))!4)) [0,1,2]"

value "counts (map (fst ((enum_canonical_mapping (Suc (Suc (Suc 0))))!4)) [0,1,2])"

lemma "same_partition (fst ((enum_canonical_mapping (Suc (Suc (Suc 0))))!4)) [a,b,c]"
  apply (simp add:same_partition_elim same_partition_elim_2)
  sorry

lemma fix_idempt_ineq: "(x \<noteq> y \<and> y \<noteq> x) = (y \<noteq> x)"
  sorry

lemma rev_ineq: "(if (x \<noteq> y) then 1 else 0) = ((1::real) - (if (x = y) then 1 else 0))"
  sorry

lemma factor: "sum (\<lambda>x. (f x - g x)) A =  sum f A - sum g A"
  sorry

lemma (in prob_space)
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> indep_vars (\<lambda>_. borel) h I"
  assumes "\<And>i (m :: nat). i \<in> set xs \<Longrightarrow> integrable M (\<lambda>\<omega>. (h i \<omega>)^m)"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (h i) = 0"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^2) = 1"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> expectation (\<lambda>\<omega>. h i \<omega>^4) \<le> 3"
  shows var_f21:"variance (\<lambda>\<omega>. f2_sketch h xs \<omega>^2)
        \<le> (2*(sum (\<lambda>i. count_list xs i^2) (set xs))^2)" (is "?A \<le> ?B")
  and exp_f21:"expectation (\<lambda>\<omega>. f2_sketch h xs \<omega>^2) = sum (\<lambda>i. count_list xs i^2) (set xs)" (is ?D)
  and int_exp_f21:"integrable M (\<lambda>\<omega>. f2_sketch h xs \<omega>^2)" (is ?E)
  and int_var_f21:"integrable M (\<lambda>\<omega>. (f2_sketch h xs \<omega>^2)^2)" (is ?F)
proof -

  have "\<And>i. i \<in> set xs \<Longrightarrow> indep_vars (\<lambda>_. borel) h {i}" using assms(1) by simp
  hence meas:"\<And>i. i \<in> set xs \<Longrightarrow> h i \<in> measurable M borel" by (simp add:indep_vars_def2) 

  define exp' where "exp' = (\<lambda>i m. expectation (\<lambda>\<omega>. (h i \<omega>)^m))"
  define exp where "exp = (\<lambda>i m. if m = 1 then 0 else (if m = 2 then 1 else exp' i m))"
  define g where "g = (\<lambda>i. exp' i 4 - 3)"
  have exp_4: "\<And>x. x \<in> set xs \<Longrightarrow> exp' x (Suc (Suc (Suc (Suc 0)))) = 3 + g x" using assms(5) 
    by (simp add: numeral_eq_Suc exp'_def g_def) 
  have g_4: "\<And>x. x \<in> set xs \<Longrightarrow> g x \<le> 0" using assms(5) by (simp add:exp'_def g_def)

  have "\<And>x m. x \<in> set xs  \<Longrightarrow>
    has_bochner_integral M (f2_sketch_summand_pow h xs x m) (exp x m * (count_list xs x ^ m))"
  proof -
    fix x
    fix m
    assume a:"x \<in> set xs"

    show "has_bochner_integral M (\<lambda>\<omega>. f2_sketch_summand_pow h xs x m \<omega>) (exp x m * (count_list xs x ^ m))"
      apply (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def has_bochner_integral_iff)
      apply (rule conjI)
      using a assms(2) apply (simp add:algebra_simps)
      apply (cases "m=1", simp add:exp_def assms(3) a)
      apply (cases "m=2", simp add:algebra_simps exp_def assms(4) a)
      by (simp add:exp_def exp'_def algebra_simps)
  qed

  hence c:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    has_bochner_integral M (f2_sketch_summand_pow h xs (the (x j)) m) (exp (the (x j)) m * (count_list xs (the (x j)) ^ m))"
    by (meson maps_inj_elim)

  hence d1:"\<And>x n j m. x \<in> maps_inj  n (set xs) \<Longrightarrow> j < n \<Longrightarrow>
    integral\<^sup>L M (f2_sketch_summand_pow h xs (the (x j)) m) = (exp (the (x j)) m) *  (count_list xs (the (x j)) ^ m)"
    using has_bochner_integral_iff by blast

  have  "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> indep_vars ((\<lambda>_. borel) \<circ> (\<lambda>i. the (x i))) (h \<circ> (\<lambda>i. the (x i))) {k. k < n}"
    apply (rule prob_space.indep_vars_reindex)
    apply (simp add: prob_space_axioms)
     apply (simp add:maps_inj_mem)
    apply (rule assms(1))
    apply (rule image_subsetI) apply(simp add:maps_inj_elim)
     apply blast
    by (metis card_Collect_less_nat card_image_le finite_Collect_less_nat le_neq_implies_less less_trans verit_comp_simplify1(3))
  hence indep_1:
    "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> indep_vars (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
    by (simp add:comp_def)

  have indep:
    "\<And>x n j. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow>
    indep_vars (\<lambda>_. borel) (\<lambda>i. f2_sketch_summand_pow h xs (the (x i)) (j i)) {k. k < n}"
  proof -
    fix x n j
    assume a1: "x \<in> maps_inj n (set xs)"
    assume a2: "n \<le> 4"
    have "indep_vars (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
      using a1 a2 indep_1 by auto
    moreover define Y where "Y = (\<lambda>k t. (real (count_list xs (the (x k))) * t)^ (j k))"
    moreover have "\<And>k. k < n \<Longrightarrow> Y k \<in> measurable borel borel" by (simp add:Y_def, measurable)
    ultimately have "indep_vars (\<lambda>_. borel) (\<lambda>i. Y i \<circ> h (the (x i))) {k. k < n}"
      using indep_vars_compose by fast
    thus "indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. f2_sketch_summand_pow h xs (the (x i)) (j i) \<omega>) {k. k < n}"
      by (simp add:f2_sketch_summand_pow_def f2_sketch_summand_def Y_def comp_def) 
  qed
  define f2_tr
    where
      "f2_tr = (\<lambda>l \<omega>. prod_mset (image_mset (\<lambda>i. f2_sketch_summand h xs i \<omega>) (mset l)))"
  
  have c1: "\<And>k \<omega>. f2_sketch_summand h xs k \<omega> = f2_tr [k] \<omega>"
    by (simp add:f2_tr_def)
  
  have c2: "\<And>a b \<omega>. f2_tr a \<omega> * f2_tr b \<omega> = f2_tr (a@b) \<omega>"
    by (simp add:f2_tr_def)

  define f2_tr'
    where
      "f2_tr' = (\<lambda>l p \<omega>. (if same_partition (\<lambda>i. p !i) l then f2_tr l \<omega> else 0))"

  have c3 :"\<And>x. length x = 4 \<Longrightarrow> f2_tr x = (\<lambda>\<omega>. sum_list (map (\<lambda>p. f2_tr' x p \<omega>) four_canonical_maps))"
    sorry

  have indep2:
    "\<And> x p. set x \<subseteq> set xs  \<Longrightarrow> length x \<le> 4  \<Longrightarrow> 
      integrable M (f2_tr' x p)"
    sorry

  have indep1:
    "\<And> x p. set x \<subseteq> set xs \<Longrightarrow> length x \<le> 4  \<Longrightarrow>  
      integral\<^sup>L M (f2_tr' x p) = (if same_partition (\<lambda>i. p !i) x then 1 else 0) * 
      prod_list (map (\<lambda>i. exp (x ! fst i) (snd i) * real (count_list xs (x ! fst i) ^ snd i)) (counts p))"
    sorry (*  proof -
    fix x n a
    assume a1:"x \<in> maps_inj n (set xs)"
    assume a2:"n \<le> 4"
    assume a3:"set a \<subseteq> {k. k < n}"

    have c4: "\<And> i. i \<in> set (counts a) \<Longrightarrow> fst i < n" using a3 by auto

    have "(LINT \<omega>|M. f2_tr x a \<omega>) =
      prod (\<lambda>i. (LINT \<omega>|M. (f2_sketch_summand_pow h xs (the (x i)) (count (mset a) i) \<omega>))) (set a)"
      apply (simp add:f2_tr_def prod_mset_conv f2_sketch_summand_pow_def[symmetric])
      apply (rule indep_vars_lebesgue_integral)
         apply (simp add:assms(1))+
      using indep a2 a1 a3 assms(1) indep_vars_subset apply blast
      using c a1 a3 has_bochner_integral_iff by blast
    
    hence "integral\<^sup>L M (f2_tr x a) =
      prod_list (map (\<lambda>i. (LINT \<omega>|M. (f2_sketch_summand_pow h xs (the (x (fst i))) (snd i) \<omega>))) (counts a))"
      using countsI by fastforce
    also have "... = prod_list (map (\<lambda>i. (exp (the (x (fst i))) (snd i) * real ( count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      apply (rule arg_cong [where f="prod_list"])
      apply (rule map_cong, simp)
      using a1 c4 by (simp add:d1)
    finally show "integral\<^sup>L M (f2_tr x a) = prod_list (map (\<lambda>i. (exp (the (x (fst i))) (snd i) * real (count_list xs (the (x (fst i))) ^ (snd i)))) (counts a))"
      by simp
  qed*)

  show int_exp_f2:?E
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions) sorry

  show int_var_f2:?F
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions) sorry

  have exp_2: "?D"
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: split_fun_set_sum_into_partitions)
    apply (simp add: c1 c2) sorry
  thus ?D by auto

  show "?A \<le> ?B"
    apply (subst variance_eq, metis int_exp_f2, metis int_var_f2)
    apply (simp add: exp_2)
    apply (simp add: f2_sketch_def power4_eq_xxxx power2_eq_square)
    apply (simp add: sum_distrib_left sum_distrib_right c1 c2)
    apply (simp add: c3 indep1 indep2 exp_def sum.distrib four_canonical_maps_def)
    apply (simp add: same_partition_elim same_partition_elim_2)
    apply (simp add: sum_collapse  rev_ineq )
    apply (simp add: algebra_simps factor sum_collapse)
    apply (simp add: exp_4 algebra_simps sum_distrib_left)
    apply (rule sum_mono)
    by (simp add: g_4 mult_nonneg_nonpos2)
qed


end