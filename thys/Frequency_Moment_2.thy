theory Frequency_Moment_2
  imports Main SumByPartitions "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family" "HOL-Algebra.Congruence"
begin

section \<open>Frequency Moment 2\<close>

subsection \<open>Sketch\<close>

definition f2_sketch_summand
  where
    "f2_sketch_summand f xs x \<omega> = real (count_list xs x) * f x \<omega>"

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. f2_sketch_summand f xs x \<omega>)"

definition f2_tr
  where
    "f2_tr h xs n l \<omega> = prod_list (map (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) (l :: nat list))"

definition f2_sketch_summand_pow
  where
    "f2_sketch_summand_pow h xs x n \<omega> = ((f2_sketch_summand h xs x \<omega>) ^ n)"

lemma c1: "f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr h xs n [k] \<omega>"
  by (simp add:f2_tr_def)

lemma c2: "f2_tr h xs n a \<omega> * f2_tr h xs n b \<omega> = f2_tr h xs n (a@b) \<omega>"
  by (simp add:f2_tr_def)

fun counts where
  "counts xs = map (\<lambda>x. (x,count_list xs x)) (remdups xs)" 

lemma c4: 
  assumes "x \<in> maps_inj n A"
  shows "integral\<^sup>L \<Omega> (f2_tr h xs x a) =
    prod_list (map (\<lambda>(i,j). (LINT \<omega>|\<Omega>. (f2_sketch_summand_pow h xs (the (x i)) j \<omega>))) (counts a))"
  sorry

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
    assume "indep_sets F (f ` I)"
    assume "J \<subseteq> I"
    hence c1:"f ` J \<subseteq> f ` I" by blast
    assume "J \<noteq> {}"
    hence c2:"f ` J \<noteq> {}" by blast
    assume "finite J"
    hence c3:"finite (f ` J)" sorry
    assume "\<forall>j\<in>J. A j \<in> (F \<circ> f) j"
    hence c4:"\<forall>j \<in> (f ` J). A (f j) \<in> F j" sorry
    show "prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))" sorry
  qed
qed

lemma (in prob_space) indep_vars_reindex:
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

  have e: "\<And>x n a. x \<in> maps n (set xs) \<Longrightarrow> filter (\<lambda>i. i \<ge> n) a = [] \<Longrightarrow> integrable \<Omega> (f2_tr h xs x a)" sorry

  have indep1:
    "\<And>x n. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
  proof -
    fix x n
    assume "x \<in> maps_inj n (set xs)"
    assume "n \<le> 4"
    show "prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. h (the (x i))) {k. k < n}"
      using assms(3)[where I="(\<lambda>i. the (x i)) ` {k. k < n}"]

  qed

  have indep:
    "\<And>x n j. x \<in> maps_inj n (set xs) \<Longrightarrow> n \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) (\<lambda>i. f2_sketch_summand_pow h xs (the (x i)) (j i)) {k. k < n}"   
    sorry

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