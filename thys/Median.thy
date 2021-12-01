section \<open>Median\<close>

theory Median
  imports Main "HOL-Probability.Hoeffding" "HOL-Library.Multiset" Probability_Ext "HOL.List"
begin

fun median_list where 
  "median_list xs = sort xs ! (length xs div 2)"

definition median where
  "median f n = median_list (map f [0..<n])"

definition interval :: "('a :: linorder) set \<Rightarrow> bool" where
  "interval I = (\<forall>x y z. x \<in> I \<longrightarrow> z \<in> I \<longrightarrow> x \<le> y \<longrightarrow> y \<le> z \<longrightarrow> y \<in> I)"

lemma interval_rule:
  assumes "interval I"
  assumes "a \<le> x" "x \<le> b"
  assumes "a \<in> I"
  assumes "b \<in> I"
  shows "x \<in> I"
  using assms(1) apply (simp add:interval_def)
  using assms by blast

text \<open>The interesting result about the median is that, if strictly
more than half of the elements are in an interval, so must be the median.
This is because, when the elements of the list are sorted, the subset
of the elements that are in such an interval must form a consecutive subsequence,
and a consecutive subsequence must contain the median if it is longer than
half the length of the list.\<close>

lemma sorted_int:
  assumes "interval I"
  assumes "sorted xs"
  assumes "k < length xs" "i \<le> j" "j \<le> k "
  assumes "xs ! i \<in> I" "xs ! k \<in> I"
  shows "xs ! j \<in> I"
  apply (rule interval_rule[where a="xs ! i" and b="xs ! k"])
  using assms by (simp add: sorted_nth_mono)+


lemma mid_in_interval:
  assumes "2*length (filter (\<lambda>x. x \<in> I) xs) > length xs"
  assumes "interval I"
  assumes "sorted xs"
  shows "xs ! (length xs div 2) \<in> I"
proof -
  have "length (filter (\<lambda>x. x \<in> I) xs) > 0"  using assms(1) by linarith
  then obtain v where v_1: "v < length xs" and v_2: "xs ! v \<in> I" 
    by (metis filter_False in_set_conv_nth length_greater_0_conv)

  define J where "J = {k. k < length xs \<and> xs ! k \<in> I}"

  have card_J_min: "2*card J > length xs"
    using assms(1) by (simp add:J_def length_filter_conv_card)

  consider
    (a) "xs ! (length xs div 2) \<in> I" |
    (b) "xs ! (length xs div 2) \<notin> I \<and> v > (length xs div 2)" |
    (c) "xs ! (length xs div 2) \<notin> I \<and> v < (length xs div 2)"
    by (metis linorder_cases v_2)
  thus ?thesis
  proof (cases)
    case a
    then show ?thesis by simp
  next
    case b
    have p:"\<And>k. k \<le> length xs div 2 \<Longrightarrow> xs ! k \<notin> I"
      using b v_2 sorted_int[OF assms(2) assms(3) v_1, where j="length xs div 2"] apply simp by blast
    have "card J \<le> card {Suc (length xs div 2)..<length xs}"
      apply (rule card_mono, simp)
      apply (rule subsetI, simp add:J_def not_less_eq_eq[symmetric])
      using p by metis
    hence "card J \<le> length xs - (Suc (length xs div 2))"
      using card_atLeastLessThan by metis
    hence "length xs \<le> 2*( length xs - (Suc (length xs div 2)))"
      using card_J_min by linarith
    hence "False"
      apply (simp add:nat_distrib)
      apply (subst (asm) le_diff_conv2)
      using b v_1 apply linarith
      by simp
    then show ?thesis by simp
  next
    case c
    have p:"\<And>k. k \<ge> length xs div 2 \<Longrightarrow> k < length xs \<Longrightarrow> xs ! k \<notin> I"
      using c v_1 v_2 sorted_int[OF assms(2) assms(3), where i ="v" and j="length xs div 2"] apply simp by blast
    have "card J \<le> card {0..<(length xs div 2)}"
      apply (rule card_mono, simp)
      apply (rule subsetI, simp add:J_def not_less_eq_eq[symmetric])
      using p linorder_le_less_linear by blast
    hence "card J \<le> (length xs div 2)"
      using card_atLeastLessThan by simp
    then show ?thesis using card_J_min by linarith
  qed
qed

lemma median_est':
  assumes "interval I"
  assumes "card {k. k < 2*n+1 \<and> f k \<in> I} \<ge> n+1"
  shows "median f (2*n+1) \<in> I"
proof -
  define m where "m=2*n + 1"
  have a: "{i. i < m \<and> map f [0..<m] ! i \<in> I} = {i. i < m \<and> f i \<in> I}"
    apply (rule order_antisym)
     apply (rule subsetI, simp)
     apply (metis nth_map_upt add_0 diff_zero)
    by (rule subsetI, simp) 

  have "m < 2*(n+1)"
    by (simp add:m_def)
  also have "... \<le> 2 * card {i. i < m \<and> f i \<in> I}"
    apply (rule mult_left_mono)
    using assms(2) by (simp add:m_def)+
  finally have b:"m < 2 * card {i. i < m \<and> f i \<in> I}" by simp

  show ?thesis
    apply (subst m_def[symmetric], simp add:median_def)
    apply (rule mid_in_interval[OF _ assms(1), where xs="sort (map f [0..<m])", simplified])
    apply (simp add:filter_sort comp_def length_filter_conv_card a)
    by (metis b)
qed

lemma median_est:
  fixes \<delta> :: "real"
  assumes "2*card {k. k < n \<and> abs (f k - \<mu>) \<le> \<delta>} > n"
  shows "abs (median f n - \<mu>) \<le> \<delta>"
proof -
  have a:"{k. k < n \<and> abs (f k - \<mu>) \<le> \<delta>} = {i. i < n \<and> \<bar>map f [0..<n] ! i - \<mu>\<bar> \<le> \<delta>}"
    apply (rule order_antisym)
     apply (rule subsetI, simp)
    apply (rule subsetI, simp) 
    by (metis add_0 diff_zero nth_map_upt)

  show ?thesis
    apply (simp add:median_def)
    apply (rule mid_in_interval[where I="{x. abs (x-\<mu>) \<le> \<delta>}" and xs="sort (map f [0..<n])", simplified])
     using assms apply (simp add:filter_sort comp_def length_filter_conv_card a)
    by (simp add:interval_def, auto)
qed

lemma set_Suc_split: " {k. k < Suc n \<and> p k} = {k. k < n \<and> p k} \<union> (if p n then {n} else {})"
  apply (rule order_antisym)
  apply (rule subsetI, simp) using less_Suc_eq apply blast
  by (rule subsetI, cases "p n", simp, force, simp) 

lemma (in prob_space) median_bound_gen:
  fixes \<mu> :: real
  fixes \<delta> :: real
  fixes \<alpha> :: real
  assumes "\<alpha> > 0"
  assumes "\<epsilon> > 0"
  assumes "\<epsilon> < 1"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "n \<ge> - ln \<epsilon> / (2 * \<alpha>^2)"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. abs (X i \<omega> - \<mu>) > \<delta>) \<le> 1/2-\<alpha>" 
  shows "\<P>(\<omega> in M. abs (median (\<lambda>i. X i \<omega>) n - \<mu>) > \<delta>) \<le> \<epsilon>" (is "\<P>(\<omega> in M. ?lhs \<omega>) \<le> ?C") 
proof -
  define E where "E = (\<lambda>i \<omega>. (if abs (X i \<omega> - \<mu>) > \<delta> then 1 else 0::real))"
  have E_indep: "indep_vars (\<lambda>_. borel) E {0..<n}"
    using indep_vars_compose[OF assms(4), where Y = "(\<lambda>i v. if abs (v - \<mu>) > \<delta> then 1 else 0::real)"] 
    by (simp add:comp_def E_def)
  have b:"Hoeffding_ineq M {0..<n} E (\<lambda>i. 0) (\<lambda>i. 1)" 
    apply (simp add:Hoeffding_ineq_def indep_interval_bounded_random_variables_def)
    apply (simp add:prob_space_axioms indep_interval_bounded_random_variables_axioms_def E_indep)
    by (simp add:E_def)
  have "0 < - ln \<epsilon> / (2 * \<alpha>^2)" 
    apply (rule divide_pos_pos)
    using assms(3) 
     apply (simp add: assms(2))
    using assms(1) by force
  hence c:"n > 0"  using assms by linarith
  have d:"\<alpha> * real n \<ge> 0" using assms by simp
  have "prob {x \<in> space M. (\<Sum>i = 0..<n. expectation (E i)) + \<alpha> * n \<le> (\<Sum>i = 0..<n. E i x)}
    \<le> exp (- (2 * (\<alpha> * real n)\<^sup>2 / (real n)))" (is "prob ?A \<le> _")
    using c d Hoeffding_ineq.Hoeffding_ineq_ge[OF b,where \<epsilon>="\<alpha>*n", simplified]
    by (simp add:power_divide)
  also have "... \<le> \<epsilon>"
    apply (subst ln_ge_iff[symmetric], metis assms(2))
    using c assms(5) apply (simp add:algebra_simps power2_eq_square[where a="real n"])
    apply (subst (asm) minus_divide_left)
    apply (subst (asm) pos_divide_le_eq)
    using assms apply simp
    by simp

  finally have d:"prob ?A \<le> \<epsilon>" 
    by blast
  have m1: "{\<omega> \<in> space M. ?lhs \<omega>} \<subseteq> ?A"
  proof (rule subsetI)
    fix x 
    have diff: "{k. k < n \<and> \<bar>X k x - \<mu>\<bar> > \<delta>} = {0..< n} - {k. k < n \<and> \<bar>X k x - \<mu>\<bar> \<le> \<delta>}"
      by (rule order_antisym, rule subsetI, simp, rule subsetI, simp, force)
    assume a:"x \<in> {\<omega> \<in> space M. \<delta> < \<bar>median (\<lambda>i. X i \<omega>) n - \<mu>\<bar>}"
    hence "2 * card {k. k < n \<and> \<bar>X k x - \<mu>\<bar> \<le> \<delta>} \<le> n"
      using median_est[where f="\<lambda>i. X i x" and n="n" and \<mu>="\<mu>" and \<delta>="\<delta>"]
      by (simp, fastforce)
    hence "n \<le> 2 * card {k. k < n \<and> \<bar>X k x - \<mu>\<bar> > \<delta>}"
      apply (simp add:diff)
      apply (subst card_Diff_subset, simp, rule subsetI, simp)
      by simp
    also have "... = 2*(\<Sum>i = 0..<n. E i x)"
      by (induction n, simp, simp add:set_Suc_split E_def) 
    finally have "(\<Sum>i = 0..<n. E i x) \<ge> n/2" by linarith
    moreover 
    have "\<And>i \<omega>. i < n \<Longrightarrow> \<omega> \<in> space M \<Longrightarrow> E i \<omega> = indicat_real {\<omega>. abs (X i \<omega> - \<mu>) > \<delta>} \<omega>" 
      by (simp add:E_def split:split_indicator)
    hence "\<And>i. i < n \<Longrightarrow> expectation (\<lambda>\<omega>. E i \<omega>) \<le> 1/2-\<alpha>"
      using assms(6) by (simp add:measure_inters cong:Bochner_Integration.integral_cong) 
    hence "(\<Sum>i = 0..<n. expectation (E i)) \<le> n*(1/2-\<alpha>)"
      using sum_mono[where K="{0..<n}" and g="\<lambda>_.  1/2-\<alpha>"]
      by simp 
    hence "(\<Sum>i = 0..<n. expectation (E i)) + \<alpha> * n \<le> n /2"
      by (simp add:algebra_simps)
    ultimately show "x \<in> ?A"
      using a by (simp)
  qed
  have m2:"?A \<in> events" 
    apply measurable
    apply (simp add:E_def, measurable)
    using assms(4) apply (simp add:indep_vars_def)
    by simp
  show ?thesis
    using finite_measure_mono[OF m1 m2] d by linarith
qed

lemma (in prob_space) median_bound_3:
  fixes \<mu> :: real
  fixes \<delta> :: real
  assumes "0 < \<epsilon>" "\<epsilon> < 1"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "n \<ge> -18 * ln \<epsilon>"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. abs (X i \<omega> - \<mu>) > \<delta>) \<le> 1/3" 
  shows "\<P>(\<omega> in M. abs (median (\<lambda>i. X i \<omega>) n - \<mu>) > \<delta>) \<le> \<epsilon>" (is "\<P>(\<omega> in M. ?lhs \<omega>) \<le> ?C") 
  apply (rule median_bound_gen[where \<alpha>="1/6"], simp, simp add:assms, simp add:assms, simp add:assms)
  using assms(4) apply (simp add:algebra_simps power2_eq_square) 
  using assms(5) by simp

lemma sorted_mono_map: 
  assumes "sorted xs"
  assumes "mono f"
  shows "sorted (map f xs)"
  using assms apply (simp add:sorted_wrt_map)
  apply (rule sorted_wrt_mono_rel[where P="(\<le>)"])
  by (simp add:mono_def, simp)

lemma map_sort:
  assumes "mono f"
  shows "sort (map f xs) = map f (sort xs)"
  apply (rule properties_for_sort)
   apply simp
  by (rule sorted_mono_map, simp, simp add:assms)

lemma median_cong:
  assumes "\<And>i. i < n \<Longrightarrow> f i = g i"
  shows "median f n = median g n"
  apply (simp add:median_def)
  apply (rule arg_cong2[where f="(!)"])
   apply (rule arg_cong[where f="sort"])
  by (rule map_cong, simp, simp add:assms, simp)

lemma median_restrict: 
  assumes "n > 0"
  shows "median (\<lambda>i \<in> {0..<n}.f i) n = median f n"
  by (rule median_cong, simp)

lemma median_rat:
  assumes "n > 0"
  shows "real_of_rat (median f n) = median (\<lambda>i. real_of_rat (f i)) n"
proof -
  have a:"map (\<lambda>i. real_of_rat (f i)) [0..<n] = 
    map real_of_rat (map (\<lambda>i. f i) [0..<n])"
    by (simp)
  show ?thesis 
    apply (simp add:a median_def del:map_map)
    apply (subst map_sort[where f="real_of_rat"], simp add:mono_def of_rat_less_eq)
    apply (subst nth_map[where f="real_of_rat"]) using assms 
    apply fastforce
    by simp
qed

lemma median_const:
  assumes "k > 0"
  shows "median (\<lambda>i \<in> {0..<k}. a) k = a"
proof -
  have b: "sorted (map (\<lambda>_. a) [0..<k])" 
    by (subst sorted_wrt_map, simp)
  have a: "sort (map (\<lambda>_. a) [0..<k]) = map (\<lambda>_. a) [0..<k]"
    by (subst sorted_sort_id[OF b], simp)
  have "median (\<lambda>i \<in> {0..<k}. a) k = median (\<lambda>_. a) k"
    by (subst median_restrict[OF assms(1)], simp)
  also have "... = a"
    apply (simp add:median_def a)
    apply (subst nth_map)
    using assms by simp+
  finally show ?thesis by simp
qed

end
