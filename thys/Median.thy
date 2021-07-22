theory Median
  imports Main "HOL-Probability.Hoeffding" "HOL-Library.Multiset"
begin

fun swap where
  "swap i j f = (\<lambda>k. if k = i then min (f i) (f j) else (if k = j then max (f i) (f j) else f k))"

fun bubblesort where
  "bubblesort f n = fold id [swap j i. i <- [0..<n], j <- [0..<i]] f"

lemma bubblesort_ind:
  "bubblesort f (Suc n) = fold id [swap j n. j <- [0..<n]] (bubblesort f n)"
  by simp

fun median where 
  "median f n = (bubblesort f n) (n div 2)"

lemma bubblesort_sorted:
  fixes f :: "nat \<Rightarrow> 'b :: linorder"
  shows "j < n \<Longrightarrow> i < j \<Longrightarrow> bubblesort f n i \<le> bubblesort f n j"
proof (induction n arbitrary: i j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define g where "g = (\<lambda>k. fold id [swap j n. j <- [0..<k]] (bubblesort f n))"
  define k where "k = n"
  have a:"(\<forall>i j. j < n \<longrightarrow> i < j \<longrightarrow> g k i \<le> g k j) \<and> (\<forall>l. l < k \<longrightarrow> g k l \<le> g k n)"
  proof (induction k)
    case 0
    then show ?case using Suc by (simp add:g_def del:bubblesort.simps)
  next
    case (Suc k)
    have "g (Suc k) = swap k n (g k)" 
      by (simp add:g_def)
    then show ?case using Suc
      apply (cases "g k k \<le> g k n")
       apply (simp add:min_def max_def)
      using less_antisym apply blast
      apply (cases "g k n \<le> g k k")
       apply (simp add:min_def max_def)
       apply (metis less_antisym max.coboundedI2 max.orderE)
      by simp
  qed

  hence "\<And>i j. j < Suc n \<Longrightarrow> i < j \<Longrightarrow> g n i \<le> g n j"
    apply (simp add:k_def) using less_antisym by blast
  moreover have "bubblesort f (Suc n) = g n" 
    by (simp add:bubblesort_ind g_def del:bubblesort.simps)
  ultimately show ?case
    apply (simp del:bubblesort.simps)
    using Suc by blast
qed

lemma bubblesort_sorted_le:
  fixes f :: "nat \<Rightarrow> 'b :: linorder"
  shows "j < n \<Longrightarrow> i \<le> j \<Longrightarrow> bubblesort f n i \<le> bubblesort f n j"
  using bubblesort_sorted 
  by (metis eq_iff le_imp_less_or_eq)

lemma bubblesort_perm:
  fixes f :: "nat \<Rightarrow> 'b :: linorder"
  shows "image_mset (bubblesort f n) (mset [0..<n]) = image_mset f (mset [0..<n])"
proof -
  define is_swap where "is_swap = (\<lambda>(ts :: ((nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b)). \<exists>i < n. \<exists>j < n. ts = swap i j)"
  define t :: "((nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b) list" 
    where "t = [swap j i. i <- [0..<n], j <- [0..<i]]"

  have a: "\<And>x f. is_swap x \<Longrightarrow> image_mset (x f) (mset_set {0..<n}) = image_mset f (mset_set {0..<n})"
  proof -
    fix x
    fix f :: "nat \<Rightarrow> 'b :: linorder"
    assume "is_swap x"
    then obtain i j where x_def: "x = swap i j" and i_bound: "i < n" and j_bound:"j < n" 
      using is_swap_def by blast
    define inv where "inv = mset_set {k. k < n \<and> k \<noteq> i \<and> k \<noteq> j}"
    have b:"{0..<n} = {k. k < n \<and> k \<noteq> i \<and> k \<noteq> j} \<union> {i,j}"
      apply (rule order_antisym, rule subsetI, simp, blast, rule subsetI, simp)
      using i_bound j_bound by meson
    have c:"\<And>k. k \<in># inv \<Longrightarrow> (x f) k = f k" 
      by (simp add:x_def inv_def)
    have "image_mset (x f) inv = image_mset f inv"
      apply (rule multiset_eqI)
      using c multiset.map_cong0 by force
    moreover have "image_mset (x f) (mset_set {i,j}) = image_mset f (mset_set {i,j})"
      apply (cases "i = j")
      by (simp add:x_def max_def min_def)+
    moreover have "mset_set {0..<n} = inv + mset_set {i,j}"
      by (simp only:inv_def b, rule mset_set_Union, simp, simp, simp) 
    ultimately show "image_mset (x f) (mset_set {0..<n}) = image_mset f (mset_set {0..<n})"
      by simp
  qed

  have "(\<forall>x \<in> set t. is_swap x) \<Longrightarrow> image_mset (fold id t f) (mset [0..<n]) = image_mset f (mset [0..<n])"
    by (induction t arbitrary:f, simp, simp add:a) 
  moreover have "\<And>x. x \<in> set t \<Longrightarrow> is_swap x" 
    apply (simp add:t_def is_swap_def) 
    by (meson atLeastLessThan_iff imageE less_imp_le less_le_trans)  
  ultimately have "image_mset (fold id t f) (mset [0..<n]) = image_mset f (mset [0..<n])" by blast
  then show ?thesis by (simp add:t_def)
qed

lemma size_filter_all:
  "(\<And>y. y \<in># xs \<Longrightarrow> p y) \<Longrightarrow> size (filter_mset p xs) = size xs"
  by (induction xs, simp, simp)

lemma size_filter_card:
  assumes "finite x"
  shows "size (filter_mset p (image_mset f (mset_set x))) = card {k. k \<in> x \<and> p (f k)}"
  using assms
proof(induction x rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  moreover have "{k. (k = x \<or> k \<in> F) \<and> p (f k)} = {k. k = x \<and> p (f x)} \<union> {k. k \<in> F \<and> p (f k)}"
    by (rule order_antisym, rule subsetI, simp, blast, rule subsetI, simp, blast)
  ultimately show ?case by simp
qed

lemma median_est:
  fixes \<delta> :: "real"
  assumes "2*card {k. k < n \<and> abs (f k - \<mu>) \<ge> \<delta>} < n"
  assumes "n > 0"
  shows "abs (median f n - \<mu>) < \<delta>"
proof -
  have "median f n - \<mu> < \<delta>"
  proof (rule ccontr)
    have "\<And>k. k \<ge> n div 2 \<Longrightarrow> k < n \<Longrightarrow> bubblesort f n k \<ge> median f n"
      apply (simp  del:bubblesort.simps )
      using bubblesort_sorted_le by blast
    moreover assume "\<not> median f n - \<mu> < \<delta>"
    hence "median f n \<ge> \<delta> + \<mu>" by linarith
    ultimately have a:"\<And>k. k \<ge> n div 2 \<Longrightarrow> k < n \<Longrightarrow> bubblesort f n k \<ge> \<delta> + \<mu>" by force
    hence "\<And>y. y \<in># image_mset (bubblesort f n) (mset [n div 2..<n]) \<Longrightarrow> y \<ge> \<delta> + \<mu>"
      apply (simp del:bubblesort.simps)
      using atLeastLessThan_iff by blast
    hence "size (filter_mset (\<lambda>y. y \<ge> \<delta> + \<mu>) (image_mset (bubblesort f n) (mset [n div 2..<n]))) \<ge> n - n div 2"
      by (metis eq_iff length_upt size_filter_all size_image_mset size_mset)
    moreover have "filter_mset (\<lambda>y. y \<ge> \<delta> + \<mu>) (image_mset (bubblesort f n) (mset [n div 2..<n])) 
      \<subseteq># filter_mset (\<lambda>y. y \<ge> \<delta> + \<mu>) (image_mset (bubblesort f n) (mset [0..<n]))" 
      apply (rule multiset_filter_mono)
      apply (rule image_mset_subseteq_mono)
      by simp
    ultimately have "size (filter_mset (\<lambda>y. y \<ge> \<delta> + \<mu>) (image_mset (bubblesort f n) (mset [0..<n]))) \<ge> n - n div 2"
      by (meson le_trans size_mset_mono)
    hence "size (filter_mset (\<lambda>y. y \<ge> \<delta> + \<mu>) (image_mset f (mset [0..<n]))) \<ge> n - n div 2"
      using bubblesort_perm by metis
    hence "n - n div 2 \<le> card {k. k < n \<and> f k \<ge> \<delta> + \<mu>}"
      by (simp add: size_filter_card)
    moreover have "card {k. k < n \<and> f k \<ge> \<delta> + \<mu>} \<le> card {k. k < n \<and> abs (f k - \<mu>) \<ge> \<delta>}"
      by (rule card_mono, simp, rule subsetI, simp, auto)
    ultimately have "n - n div 2 \<le> card {k. k < n \<and> abs (f k - \<mu>) \<ge> \<delta>}"
      using le_trans by blast
    hence "2* (n - n div 2) < n" using assms(1) by linarith
    thus "False" by simp
  qed
  moreover have "\<mu> - median f n < \<delta>"
  proof (rule ccontr)
    have a:"n div 2 < n"  using assms(2) by simp
    hence "\<And>k. k \<le> n div 2 \<Longrightarrow> bubblesort f n k \<le> median f n"
      apply (simp  del:bubblesort.simps )
      using bubblesort_sorted_le by blast
    moreover assume "\<not> \<mu> - median f n < \<delta>"
    hence "median f n \<le> \<mu> - \<delta>" by linarith
    ultimately have a:"\<And>k. k \<le> n div 2 \<Longrightarrow> bubblesort f n k \<le> \<mu> - \<delta>" by force
    hence "\<And>y. y \<in># image_mset (bubblesort f n) (mset [0..< Suc (n div 2)]) \<Longrightarrow> y \<le> \<mu> - \<delta>"
      apply (simp del:bubblesort.simps)
      using atLeastLessThan_iff by auto
    hence "size (filter_mset (\<lambda>y. y \<le> \<mu> - \<delta>) (image_mset (bubblesort f n) (mset [0..<Suc (n div 2)]))) \<ge> Suc (n div 2)"
      using length_upt size_filter_all size_image_mset size_mset 
      by (metis  cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel linear)
    moreover have "filter_mset (\<lambda>y. y \<le> \<mu> - \<delta>) (image_mset (bubblesort f n) (mset [0..<Suc (n div 2)])) 
      \<subseteq># filter_mset (\<lambda>y. y \<le> \<mu> - \<delta>) (image_mset (bubblesort f n) (mset [0..<n]))" 
      apply (rule multiset_filter_mono)
      apply (rule image_mset_subseteq_mono)
      by (metis Suc_leI assms(2) div_less_dividend finite_atLeastLessThan ivl_subset mset_upt msubset_mset_set_iff one_less_numeral_iff order_refl semiring_norm(76))
    ultimately have "size (filter_mset (\<lambda>y. y \<le> \<mu> - \<delta>) (image_mset (bubblesort f n) (mset [0..<n]))) \<ge> Suc (n div 2)"
      by (meson le_trans size_mset_mono)
    hence "size (filter_mset (\<lambda>y. y \<le> \<mu> - \<delta>) (image_mset f (mset [0..<n]))) \<ge> Suc (n div 2)"
      using bubblesort_perm by metis
    hence "Suc (n div 2) \<le> card {k. k < n \<and> f k \<le> \<mu> - \<delta>}"
      by (simp add: size_filter_card)
    moreover have "card {k. k < n \<and> f k \<le> \<mu> - \<delta>} \<le> card {k. k < n \<and> abs (f k - \<mu>) \<ge> \<delta>}"
      by (rule card_mono, simp, rule subsetI, simp, auto)
    ultimately have "Suc (n div 2) \<le> card {k. k < n \<and> abs (f k - \<mu>) \<ge> \<delta>}"
      using le_trans by blast
    hence "n div 2 < n div 2" using assms(1) by linarith
    thus "False" by simp
  qed
  ultimately show ?thesis by linarith
qed


lemma (in prob_space) events_restr_events:
  assumes "X \<in> events"
  shows "{\<omega> \<in> space M. \<omega> \<in> X} \<in> events"
  using assms by measurable 


lemma (in prob_space) hoeffding_count:
  assumes "indep_vars (\<lambda>_.borel) X {0..<n}"
  assumes "n \<ge> -32/9 * ln \<epsilon>"
  assumes "\<And>i \<omega>. i < n \<Longrightarrow> \<omega> \<in> space M \<Longrightarrow> X i \<omega> \<in> {0,1::real}"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. X i \<omega> = 1) \<le> 1/8"
  assumes "\<epsilon> > 0"
  assumes "\<epsilon> < 1"
  shows "\<P>(\<omega> in M. 2*card {k. X k \<omega> = 1 \<and> k < n} \<ge> n) \<le> \<epsilon>"
proof -
  have "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> (\<And>i. i<n \<Longrightarrow> X i \<omega> \<in> {0,1}) \<Longrightarrow> (\<Sum>i \<in> {0..<n}. X i \<omega>) = (card {k. X k \<omega> = 1 \<and> k < n})"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have a:"{k. X k \<omega> = 1 \<and> k < Suc n} = {k. X k \<omega> = 1 \<and> k < n} \<union> (if X n \<omega> = 1 then {n} else {})"
      apply (rule order_antisym, rule subsetI, simp) 
      using not_less_less_Suc_eq apply blast
      apply (rule subsetI, simp) 
      by (metis empty_iff less_Suc_eq singletonD)
    show ?case using Suc apply (simp add:a) using Suc by blast
  qed
  hence y_elim: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> (\<Sum>i = 0..<n. X i \<omega>) = (card {k. X k \<omega> = 1 \<and> k < n})"
    using assms(3) by blast
  have a:"n > 0" 
  proof (rule ccontr)
    assume "\<not> (n > 0)"
    hence "n = 0"
      by auto
    hence "ln \<epsilon> \<ge> 0" 
      using assms(2) by linarith
    hence "\<epsilon> \<ge> 1" 
      using assms(5) ln_ge_zero_iff by blast
    thus "False" using  assms(6) by auto
  qed
  have b1:"\<And>i \<omega>. i < n \<Longrightarrow> \<omega> \<in> space M \<Longrightarrow> X i \<omega> = indicat_real {\<omega> \<in> space M. X i \<omega> = 1} \<omega>" 
    using assms(3) apply (simp split:split_indicator) by blast
  have b2:"\<And>i. i  < n \<Longrightarrow> {\<omega> \<in> space M. X i \<omega> = 1} \<inter> space M = {\<omega> \<in> space M. X i \<omega> = 1}" 
    by (rule order_antisym, rule subsetI, simp, rule subsetI, simp)
  have b3:"\<And>i. i < n \<Longrightarrow> expectation (X i) = expectation (indicat_real {\<omega> \<in> space M. X i \<omega> = 1})"
    apply (rule Bochner_Integration.integral_cong, simp)
    using b1 by blast
  have "\<And>i. i < n \<Longrightarrow> expectation (\<lambda>\<omega>. X i \<omega>) \<le> 1/8" 
    apply (simp add: b3) 
    using assms(4) b2 by auto 
  hence u_bound_aux: "8*(\<Sum>i = 0..<n. expectation (X i)) \<le> real n"
    by (induction n, simp, simp, force)
  define u where "u = 2*(\<Sum>i = 0..<n. expectation (X i)) - real n/4"
  have c:"(\<Sum>i = 0..<n. expectation (X i)) = (real n)/8 + u/2"
    by (simp add: u_def algebra_simps diff_divide_distrib) 
  have u_bound: "u \<le> 0" 
    by (simp add:u_def u_bound_aux)
  have b:"Hoeffding_ineq M {0..<n} X (\<lambda>i. 0) (\<lambda>i. 1)" 
    apply (simp add:Hoeffding_ineq_def indep_interval_bounded_random_variables_def)
    apply (simp add: prob_space_axioms indep_interval_bounded_random_variables_axioms_def)
    apply (rule conjI) using assms(1) apply simp
    apply (rule allI, rule impI, rule conjI)
    apply (rule AE_I2) using assms(3) apply force
    apply (rule AE_I2) using assms(3) by force
  have "{x \<in> space M. real n / 2 \<le> (\<Sum>i = 0..<n. X i x)} \<subseteq> 
    {x \<in> space M. (\<Sum>i = 0..<n. expectation (X i)) + real n * 3 / 8 \<le> (\<Sum>i = 0..<n. X i x)}" 
    (is "?C \<subseteq> ?A")
    apply (rule subsetI)
      apply (simp add:c algebra_simps add_divide_distrib[symmetric]) using u_bound by linarith
  moreover have "?A \<in> events" apply measurable using assms(1) by (simp add:indep_vars_def2)
  ultimately have "prob ?C \<le> prob ?A"
    using finite_measure_mono by presburger
  moreover have "prob ?A \<le>  exp (- (real n * 9 / 32))" (is "prob ?A \<le> ?B")
    using Hoeffding_ineq.Hoeffding_ineq_ge[where X="X" and M="M" and I="{0..<n}" and 
          a="(\<lambda>i. 0)" and b="(\<lambda>i. 1)" and \<epsilon>="3*n/8"] a
    by (simp add: b algebra_simps power2_eq_square)
  ultimately have "prob ?C \<le> ?B" by force
  moreover have "?C = {\<omega> \<in> space M. 2*card {k. X k \<omega> = 1 \<and> k < n} \<ge> n}"
    by (auto simp add:y_elim)
  moreover 
  have "ln \<epsilon> \<ge> -9/32 * real n" using assms(2) by linarith
  hence "?B \<le> \<epsilon>" 
    by (metis assms(5) ln_ge_iff minus_divide_left mult_minus_right mult_of_nat_commute times_divide_eq_right)
  ultimately show ?thesis by simp
qed

lemma (in prob_space) median_bound:
  assumes "\<epsilon> > 0"
  assumes "\<epsilon> < 1"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "n \<ge> -32/9 * ln \<epsilon>"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. abs (X i \<omega> - (\<mu>::real)) \<ge> (\<delta>::real)) \<le> 1/8" 
  shows "\<P>(\<omega> in M. abs (median (\<lambda>i. X i \<omega>) n - \<mu>) \<ge> \<delta>) \<le> \<epsilon>" (is "\<P>(\<omega> in M. ?A \<omega>) \<le> ?C") 
proof -
  define E where "E = (\<lambda>i \<omega>. (if abs (X i \<omega> - \<mu>) \<ge> \<delta> then 1 else 0::real))"
  have E_elim: "\<And> i \<omega>. (E i \<omega> = 1) = (abs (X i \<omega> - \<mu>) \<ge> \<delta>)"
    by (simp add:E_def)
  have ran_borel: 
    "\<And>x i. i < n \<Longrightarrow> x \<in> {{\<omega> \<in> space M. \<delta> \<le> \<bar>X i \<omega> - \<mu>\<bar>}} \<Longrightarrow> 
        x \<in> {X i -` A \<inter> space M |A. A \<in> sets borel}"
  proof -
    fix x i
    assume "i < n"
    assume "x \<in> {{\<omega> \<in> space M. \<delta> \<le> \<bar>X i \<omega> - \<mu>\<bar>}}"
    moreover define A where "A = {v. v \<le> \<mu> - \<delta> \<or> v \<ge> \<mu> + \<delta>}"
    ultimately have "x = X i -` A \<inter> space M" 
      apply (simp add:A_def)
      apply (rule order_antisym, rule subsetI, simp, linarith)
      by (rule subsetI, simp, linarith)
    moreover have "A \<in> sets borel" 
      by (simp add:A_def)
    ultimately show "x \<in> {X i -` A \<inter> space M |A. A \<in> sets borel}"
      by blast
  qed
  have "(\<And>i. i \<in> {0..<n} \<Longrightarrow> (\<lambda>v. if \<bar>v - \<mu>\<bar> \<ge> \<delta> then 1 else 0) \<in> borel_measurable borel)" 
    by measurable
  have E_indep: "indep_vars (\<lambda>_. borel) E {0..<n}"
    using assms(3) 
     indep_vars_compose[where Y = "(\<lambda>i v. if abs (v - \<mu>) \<ge> \<delta> then 1 else 0::real)" and X="X"] 
    by (simp add:comp_def E_def)
  have b:"\<P>(\<omega> in M. 2*card {k. E k \<omega> = 1 \<and> k < n} \<ge> n) \<le> \<epsilon>"  (is "\<P>(\<omega> in M. ?B \<omega>) \<le> ?C")
    apply (rule hoeffding_count)
    apply (simp add:E_indep)
    using assms(4) apply (simp, simp add:E_def)
    using assms(5) apply (simp add:E_def) 
      apply (metis (mono_tags, lifting) Collect_cong)
    using assms by auto
  have n_min: "n > 0" 
  proof (rule ccontr)
    assume "\<not> (n > 0)"
    hence "n = 0"
      by auto
    hence "ln \<epsilon> \<ge> 0" 
      using assms(4) by linarith
    hence "\<epsilon> \<ge> 1" 
      using assms(1) ln_ge_zero_iff by blast
    thus "False" using  assms(2) by auto
  qed
  have a:"\<And>x. x \<in> space M \<and> \<delta> \<le> \<bar>median (\<lambda>i. X i x) n - \<mu>\<bar> \<Longrightarrow> n \<le> 2 * card {k. \<delta> \<le> \<bar>X k x - \<mu>\<bar> \<and> k < n}"
  proof -
    fix x
    assume a1:"x \<in> space M \<and> \<delta> \<le> \<bar>median (\<lambda>i. X i x) n - \<mu>\<bar>"
    hence "\<not>(\<bar>median (\<lambda>i. X i x) n - \<mu>\<bar> < \<delta>)" by linarith
    hence "\<not>(2 * card {k. \<delta> \<le> \<bar>X k x - \<mu>\<bar> \<and> k < n} < n)"
      using n_min median_est[where n="n" and f="(\<lambda>i. X i x)" and \<delta>="\<delta>" and \<mu>="\<mu>"]
      by (metis (mono_tags, lifting) Collect_cong)
    then show "n \<le> 2 * card {k. \<delta> \<le> \<bar>X k x - \<mu>\<bar> \<and> k < n}" by simp
  qed
  have "{\<omega> \<in> space M. ?A \<omega>} \<subseteq> {\<omega> \<in> space M. ?B \<omega>}"
    by (rule subsetI, simp add:E_elim a del:median.simps ) 
  hence "\<P>(\<omega> in M. ?A \<omega>) \<le> \<P>(\<omega> in M. ?B \<omega>)"
    apply (rule finite_measure_mono)
    apply (simp only:E_elim)
    apply measurable
    using assms(3) apply (simp add:indep_vars_def)
    by measurable
  thus ?thesis using b by linarith
qed  

lemma swap_measurable:
  fixes n :: nat
  assumes "n > 0"
  assumes "i < n" and "j < n"
  shows "(\<lambda>\<omega>. swap i j \<omega>) \<in> measurable  (Pi\<^sub>M {0..<n} (\<lambda>_. borel)) (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: (real measure)))"
proof  -
  have i_off: "\<And>x. n \<le> x \<Longrightarrow> \<not>(x = i)"
    using assms(2) by force
  have j_off: "\<And>x. n \<le> x \<Longrightarrow> \<not>(x = j)"
    using assms(3) by force

  have "\<And>k. k < n \<Longrightarrow> k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow>  (\<lambda>\<omega>. swap i j \<omega> k) \<in> borel_measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: real measure))"
    by (simp, measurable)

  moreover have "(\<lambda>\<omega>. swap i j \<omega> i) \<in> borel_measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: (real measure)))"
    using assms by simp 

  moreover have "(\<lambda>\<omega>. swap i j \<omega> j) \<in> borel_measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: (real measure)))"
    using assms by simp 

  ultimately have comp_meas: "\<And>k. k \<in> {0..<n} \<Longrightarrow> (\<lambda>\<omega>. swap i j \<omega> k) \<in> borel_measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: real measure))"
    using atLeastLessThan_iff by blast

  show ?thesis 
    apply (rule measurable_PiM_single')
    using comp_meas apply blast
    by (simp add:i_off j_off space_PiM PiE_def extensional_def)
qed

lemma bubblesort_measurable:
  assumes "n > 0"
  shows "(\<lambda>x. bubblesort x n) \<in> measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: real measure)) (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: real measure))" (is "_ \<in> ?M")
proof -
  define is_swap where "is_swap = (\<lambda>(ts :: ((nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real)). \<exists>i < n. \<exists>j < n. ts = swap i j)"
  define t :: "((nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real) list" 
    where "t = [swap j i. i <- [0..<n], j <- [0..<i]]" 
  have a:"\<And>x. is_swap x \<Longrightarrow> x \<in> ?M"
  proof -
    fix x
    assume "is_swap x"
    then obtain i j where "i < n" and "j < n" and "x = swap i j"
      using is_swap_def 
      by blast
    thus "x \<in> ?M" using swap_measurable  assms by blast
  qed
  have "(\<And>x. x \<in> set t \<Longrightarrow> is_swap x) \<Longrightarrow> fold id t \<in> ?M" 
    apply (induction t, simp, simp)
    using a by (metis measurable_comp)
  moreover have "\<And>x. x \<in> set t \<Longrightarrow> is_swap x" 
    apply (simp add:t_def is_swap_def) 
    by (meson atLeastLessThan_iff imageE less_imp_le less_le_trans)  
  ultimately show ?thesis
    by (simp add:t_def)
qed

lemma median_measurable:
  assumes "n > 0"
  shows "(\<lambda>x. median x n) \<in> borel_measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: real measure))"
proof -
  have a:"n div 2 < n" using assms by simp
  have "(\<lambda>x. x (n div 2)) \<in> borel_measurable (Pi\<^sub>M {0..<n} (\<lambda>_. borel :: real measure))"
     apply (measurable) using a by auto
  thus ?thesis
    apply (simp del:bubblesort.simps)
    using assms bubblesort_measurable apply measurable
    using a by auto
qed

end