theory F2_Algorithm
  imports Main "HOL-Probability.Giry_Monad" UniversalHashFamily Field Frequency_Moment_2
    Median
begin

fun eval_hash_function where
  "eval_hash_function p h k = (
    if (hash_function (ZFact (int p)) (zfact_embed p k) h) \<in> zfact_embed p ` {k. 2*k < p} then
      sqrt((p-1)/(p+1))
    else
      -sqrt((p+1)/(p-1))
  )"


lemma eval_exp:
  assumes "prime p"
  assumes "k < p"
  assumes "p > 2" 
  shows eval_hash_exp: 
    "prob_space.expectation (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^m) = 
    (real (p+1)/ real(2*p) * sqrt(real (p-1)/ real (p+1))^m) + 
    (real (p-1)/ real(2*p) * (-sqrt(real (p+1)/ real (p-1)))^m)" (is "?A = ?C")
    and eval_hash_int:
    "integrable (poly_hash_family (ZFact p) 4) (\<lambda>\<omega>. eval_hash_function p \<omega> k^m)" (is ?B)
proof -
  define A where "A = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k < p}}"
  define B where "B = {\<omega>. 
    \<omega> \<in> bounded_degree_polynomials (ZFact p) 4 \<and>
    (hash_function (ZFact p) (zfact_embed p k) \<omega>) \<in> zfact_embed p ` {k. 2*k \<ge> p \<and> k < p}}"
  define f where "f = (\<lambda>\<omega>. indicator A \<omega> * sqrt((p-1)/(p+1))^m)"
  define g where "g = (\<lambda>\<omega>. indicator B \<omega> * (- sqrt((p+1)/(p-1)))^m)"

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
  have h1: "\<And>x. 2 * x < Suc (2 * t) \<Longrightarrow> x < Suc t" sorry  
  have g3: "\<And>x. x \<in> carrier (ZFact p) \<Longrightarrow> (x \<in> zfact_embed p ` {k. 2*k < p}) = (x \<notin> zfact_embed p ` {k. 2*k \<ge> p \<and> k < p})" sorry
  have h: "real (card {k. 2 * k < p}) = (p+1)/2"
    apply (subgoal_tac "{k. 2*k< p } = {k. k < Suc t}")
     apply (simp add:t_def)+
    apply (rule order_antisym)
    by (rule subsetI, simp add:h1)+
  have h1: "2*real p^4 > 0" using g by force
  have h2: "2*real p > 0" using g by linarith
  have h4: "real (card {k. p \<le> 2 * k \<and> k < p}) = (p-1)/2" sorry

  have a:"finite (bounded_degree_polynomials (ZFact p) 4)"
    apply (rule fin_degree_bounded)
    using a2 apply blast
    using g zfact_finite by blast

  have f:"real (p - Suc 0) = real p - 1" using g by linarith
  have d:"1+ real p > 0" using g by linarith

  have r3: "\<And>\<omega>. \<omega> \<in> space (poly_hash_family (ZFact (int p)) 4) \<Longrightarrow>  eval_hash_function p \<omega> k^m =  f \<omega> + g \<omega>"
    apply (simp add:poly_hash_family_def space_uniform_count_measure)
    apply (simp add:f_def g_def A_def B_def hash_function_def)
    apply (rule conjI, rule impI) using g4 g3 apply (simp add:f g3 algebra_simps)
    apply (rule impI) using  g4 g3 by (simp add:f algebra_simps)

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
    using g h1 h2 apply (simp add:h zfact_card nonzero_divide_eq_eq nonzero_eq_divide_eq)
    by (simp add: power3_eq_cube power4_eq_xxxx)
  ultimately have r1:"has_bochner_integral (poly_hash_family (ZFact p) 4) f (real (p+1)/ real(2*p) * sqrt((p-1)/(p+1))^m)"
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
    using g h1 h2 apply (simp add:h4 zfact_card nonzero_divide_eq_eq nonzero_eq_divide_eq)
    by (simp add: algebra_simps power3_eq_cube power4_eq_xxxx)
  ultimately have r2:"has_bochner_integral (poly_hash_family (ZFact p) 4) g (real (p-1)/ real(2*p) * (-sqrt((p+1)/(p-1)))^m)"
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


lemma eval_exp_1:
  assumes "prime p"
  assumes "k < p"
  shows "prob_space.expectation (poly_hash_family (ZFact p) n) (\<lambda>\<omega>. eval_hash_function p \<omega> k) = 0"
  sorry

lemma eval_exp_2:
  assumes "prime p"
  assumes "k < p"
  shows "prob_space.expectation (poly_hash_family (ZFact p) n) (\<lambda>\<omega>. eval_hash_function p \<omega> k^2) = 1"
  sorry

lemma eval_exp_4:
  assumes "prime p"
  assumes "k < p"
  shows "prob_space.expectation (poly_hash_family (ZFact p) n) (\<lambda>\<omega>. eval_hash_function p \<omega> k^4) < 3"
  sorry

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

(*
  exp ((Sum i X i - exp Sum i. X i)^2) =
  exp ((Sum i. X i)^2  


*)
lemma set_comp_subsetI: "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> {f x|x. P x} \<subseteq> B"
  by blast

lemma set_comp_cong: 
  assumes "\<And>x. P x \<Longrightarrow> f x = h (g x)"
  shows "{f x| x. P x} = h ` {g x| x. P x}"
  using assms by (simp add: setcompr_eq_image, auto)

lemma indep_sets_distr:
  assumes "f \<in> measurable M N"
  assumes "prob_space M"
  assumes "prob_space.indep_sets M (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` A i) I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets N"
  shows "prob_space.indep_sets (distr M N f) A I"
proof -
  define F where "F = (\<lambda>i. (\<lambda>a. f -` a \<inter> space M) ` A i)"
  have indep_F: "prob_space.indep_sets M F I"
    using F_def assms(3) by simp

  have sets_A: "\<And>i. i \<in> I \<Longrightarrow> A i \<subseteq> sets N"
    using assms(4) by blast

  have indep_A: "\<And>A' J. J \<noteq> {} \<Longrightarrow> J \<subseteq> I \<Longrightarrow> finite J \<Longrightarrow> 
  \<forall>j\<in>J. A' j \<in> A j \<Longrightarrow> measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
  proof -
    fix A' J
    assume a1:"J \<subseteq> I"
    assume a2:"finite J"
    assume a3:"J \<noteq> {}"
    assume a4:"\<forall>j \<in> J. A' j \<in> A j"

    define F' where "F' = (\<lambda>i. f -` A' i \<inter> space M)"

    have "\<Inter> (F' ` J) = f -` (\<Inter> (A' ` J)) \<inter> space M" 
      apply (rule order_antisym)
      apply (rule subsetI, simp add:F'_def a3)
      by (rule subsetI, simp add:F'_def a3)
    moreover have "\<Inter> (A' ` J) \<in> sets N" 
      using a4 a1 sets_A 
      by (metis a2 a3 sets.finite_INT subset_iff)
    ultimately have r1: "measure (distr M N f) (\<Inter> (A' ` J)) = measure M (\<Inter> (F' ` J))" 
      using assms(1) measure_distr by metis

    have "\<And>j. j \<in> J \<Longrightarrow> F' j \<in> F j"
      using a4 F'_def F_def by blast
    hence r2:"measure M (\<Inter> (F' ` J)) = (\<Prod>j\<in> J. measure M (F' j))"
      using indep_F prob_space.indep_setsD assms(2) a1 a2 a3 by metis

    have "\<And>j. j \<in> J \<Longrightarrow> F' j =  f -` A' j  \<inter> space M" 
      by (simp add:F'_def)
    moreover have "\<And>j. j \<in> J \<Longrightarrow> A' j \<in> sets N" 
      using a4 a1 sets_A by blast
    ultimately have r3:"\<And>j. j \<in> J \<Longrightarrow> measure M (F' j) = measure (distr M N f) (A' j)"
      using assms(1) measure_distr by metis

    show "measure (distr M N f) (\<Inter> (A' ` J)) = (\<Prod>j\<in>J. measure (distr M N f) (A' j))"
      using r1 r2 r3 by auto
  qed

  show ?thesis 
    apply (rule prob_space.indep_setsI)
    using assms apply (simp add:prob_space.prob_space_distr)
    apply (simp add:sets_A)
    using indep_A by blast
qed

lemma indep_vars_distr:
  assumes "f \<in> measurable M N"
  assumes "\<And>i. i \<in> I \<Longrightarrow> X' i \<in> measurable N (M' i)"
  assumes "prob_space.indep_vars M M' (\<lambda>i. (X' i) \<circ> f) I"
  assumes "prob_space M"
  shows "prob_space.indep_vars (distr M N f) M' X' I"
proof -
  have b1: "f \<in> space M \<rightarrow> space N" using assms(1) by (simp add:measurable_def)
  have a:"\<And>i. i \<in> I \<Longrightarrow> {(X' i \<circ> f) -` A \<inter> space M |A. A \<in> sets (M' i)} = (\<lambda>a. f -` a \<inter> space M) ` {X' i -` A \<inter> space N |A. A \<in> sets (M' i)}"
    apply (rule set_comp_cong)
    apply (rule order_antisym, rule subsetI, simp) using b1 apply fast
    by (rule subsetI, simp) 
  show ?thesis 
  using assms apply (simp add:prob_space.indep_vars_def2 prob_space.prob_space_distr)
   apply (rule indep_sets_distr)
  apply (simp add:a cong:prob_space.indep_sets_cong)
  apply (simp add:a cong:prob_space.indep_sets_cong)
   apply (simp add:a cong:prob_space.indep_sets_cong)
  using assms(2)  measurable_sets by blast
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
      h \<leftarrow> \<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. \<Pi>\<^sub>M _ \<in> {0..<s\<^sub>1}. poly_hash_family (ZFact (int p)) 4;
      sketch \<leftarrow> 
          return (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. \<Pi>\<^sub>M _ \<in> {0..<s\<^sub>1}. borel)
            (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. (\<lambda>i\<^sub>1 \<in> {0..<s\<^sub>1}. sum_list (map (eval_hash_function p (h i\<^sub>2 i\<^sub>1)) xs)));
      sketch_avg \<leftarrow> 
          return (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. borel)
            (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. (\<Sum>i\<^sub>1\<in>{0..<s\<^sub>1} . sketch i\<^sub>2 i\<^sub>1^2) / s\<^sub>1);
      return borel (median sketch_avg s\<^sub>2)
    }"

lemma "c \<noteq> (0 :: real) \<Longrightarrow> (\<Sum>i \<in> I. f i) / c  =  (\<Sum>i \<in> I. f i/c)"
  sledgehammer
  by (simp add: diff_divide_distrib)

lemma
  assumes "\<epsilon> < 1 \<and> \<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  shows "\<P>(r in (f2_alg \<delta> \<epsilon> n xs). abs (r - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(2 * ln \<epsilon>)\<rceil>"
  define p where "p = find_prime_above n"
  define \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. poly_hash_family (ZFact (int p)) 4))"
  define \<Omega>\<^sub>1 where "\<Omega>\<^sub>1 = PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. borel :: real measure))"
  define \<Omega>\<^sub>2 where "\<Omega>\<^sub>2 = PiM {0..<s\<^sub>2} (\<lambda>_. borel :: real measure)"
  define \<Omega>\<^sub>3 where "\<Omega>\<^sub>3 = (borel :: real measure)"
  define medians where
    "medians = (\<lambda>(sketch_avg :: nat \<Rightarrow> real). return \<Omega>\<^sub>3 (median sketch_avg s\<^sub>2))"
  define averages where 
    "averages = (\<lambda>(sketch :: nat \<Rightarrow> nat \<Rightarrow> real).
    return \<Omega>\<^sub>2 (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. (\<Sum> i\<^sub>1 \<in> {0..<s\<^sub>1}. sketch i\<^sub>2 i\<^sub>1^2) / real s\<^sub>1) \<bind> medians)"

  define sketches where 
      "sketches = (\<lambda>h. return \<Omega>\<^sub>1 (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. 
        \<lambda>i\<^sub>1 \<in> {0..<s\<^sub>1}. sum_list (map (eval_hash_function p (h i\<^sub>2 i\<^sub>1)) xs)) \<bind> averages)"

  have s1_nonzero: "s\<^sub>1 > 0"
    sorry
  have s2_nonzero: "s\<^sub>2 > 0"
    sorry
  have s2_le: "\<And>i. i \<in> {0..<s\<^sub>2} \<Longrightarrow> i < s\<^sub>2"
    sorry    
  have s1_le: "\<And>i. i \<in> {0..<s\<^sub>1} \<Longrightarrow> i < s\<^sub>1"
    sorry    

  define f3 where "f3 = (\<lambda>h. (\<lambda>i\<^sub>2\<in>{0..<s\<^sub>2}. (\<lambda>i\<^sub>1 \<in> {0..<s\<^sub>1}. sum_list (map (eval_hash_function p (h i\<^sub>2 i\<^sub>1)) xs))))"
  define f2 where "f2 = (\<lambda>h. (\<lambda>i\<^sub>2\<in>{0..<s\<^sub>2}. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. (h i\<^sub>2 i\<^sub>1)\<^sup>2) / real s\<^sub>1))"
  define f1 :: "(nat \<Rightarrow> real) \<Rightarrow> real" where "f1 = (\<lambda>h. median h s\<^sub>2)"

  have f2_meas: "f2 \<in> measurable \<Omega>\<^sub>1 \<Omega>\<^sub>2"
    apply (simp add:f2_def \<Omega>\<^sub>1_def \<Omega>\<^sub>2_def, measurable)
     defer
    sorry
  have f3_meas: "f3 \<in> measurable \<Omega>\<^sub>0 \<Omega>\<^sub>1"
    sorry
  have f23_meas: "(f2 \<circ> f3) \<in> measurable \<Omega>\<^sub>0 \<Omega>\<^sub>2"
    using f2_meas f3_meas by measurable
  have f1_meas: "f1 \<in> measurable \<Omega>\<^sub>2 \<Omega>\<^sub>3"
    using s2_nonzero median_measurable apply (simp add:f1_def \<Omega>\<^sub>2_def \<Omega>\<^sub>3_def del:median.simps)
    by blast
  have dist_23: "distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3) = distr (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) \<Omega>\<^sub>2 f2"
    using f2_meas f3_meas by (simp add:distr_distr comp_assoc)

  have dist_123: "distr \<Omega>\<^sub>0 \<Omega>\<^sub>3 (f1 \<circ> f2 \<circ> f3) = distr (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) \<Omega>\<^sub>3 f1"
    using f1_meas f23_meas by (simp add:distr_distr comp_assoc)

  have exp_3: "\<And>i j. i < s\<^sub>2 \<Longrightarrow> j < s\<^sub>1 \<Longrightarrow> prob_space.expectation (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> i j)^2)
    = f2_value xs"
    sorry

  have var_3: "\<And>i j. i < s\<^sub>2 \<Longrightarrow> j < s\<^sub>1 \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> i j)^2)
    \<le> 2 * f2_value xs^2"
    sorry
  have int_3: "\<And>i j. i < s\<^sub>2 \<Longrightarrow> j < s\<^sub>1 \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. (\<omega> i j)^2)"
    apply (subst integrable_distr_eq)
    apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
     defer
    apply (simp add:f3_def)
    sorry

  have int_3_2: "\<And>i j. i < s\<^sub>2 \<Longrightarrow> j < s\<^sub>1 \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>\<omega>. ((\<omega> i j)^2)^2)"
    apply (subst integrable_distr_eq)
    apply (simp add:f3_meas)
     apply (simp add:\<Omega>\<^sub>1_def, measurable)
     defer
    apply (simp add:f3_def)
    sorry

  have indep_3: "\<And>i. i < s\<^sub>2 \<Longrightarrow> prob_space.indep_vars (distr \<Omega>\<^sub>0 \<Omega>\<^sub>1 f3) (\<lambda>_. borel) (\<lambda>n x. (x i n)\<^sup>2 / real s\<^sub>1) {0..<s\<^sub>1}"
    apply (rule indep_vars_distr)
    defer
    defer
    apply (simp add: \<Omega>\<^sub>0_def)
    sorry

  have int23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> integrable (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)"
    apply (simp add:dist_23)
    apply (subst integrable_distr_eq)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def)
    apply (rule Bochner_Integration.integrable_divide)
    apply (rule Bochner_Integration.integrable_sum)
    using int_3 s1_nonzero by simp

  have exp23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> prob_space.expectation (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)
    = f2_value xs"
    apply (simp add:dist_23)
    apply (subst integral_distr)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def)
    using int_3 s1_nonzero by (simp add: Bochner_Integration.integral_sum exp_3)

  have var23: "\<And> i. i < s\<^sub>2  \<Longrightarrow> prob_space.variance (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)) (\<lambda>\<omega>. \<omega> i)
    \<le> 2 * (f2_value xs)\<^sup>2 / s\<^sub>1"
    apply (simp add:dist_23)
    apply (subst (1 2) integral_distr)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    using f2_meas apply measurable
     apply (simp add: \<Omega>\<^sub>2_def)
    apply (simp add:f2_def)
    apply (simp add:f2_def sum_divide_distrib)
    apply (subst prob_space.var_sum)
    
    sorry

  have "\<And>i. i < s\<^sub>2 \<Longrightarrow> \<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (r i - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> 1/8"
    (is "\<And>i. i < s\<^sub>2 \<Longrightarrow> ?rhs i \<le> 1/8")
  proof -
    fix i
    assume a:"i < s\<^sub>2"
    define M where "M = distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)"
    define v where "v = prob_space.variance M (\<lambda>\<omega>. \<omega> i)"
    have b:"integral\<^sup>L M (\<lambda>\<omega>. \<omega> i) = f2_value xs" 
      using exp23 a by (simp add: M_def) 
    have "prob_space M" apply (simp add: M_def) sorry
    moreover have "(\<lambda>\<omega>. \<omega> i) \<in> borel_measurable M" using a by (simp add:M_def \<Omega>\<^sub>2_def, measurable)
    moreover have "integrable M (\<lambda>x. (x i)\<^sup>2)" sorry
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
  ultimately have 
    "\<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (median r s\<^sub>2 - f2_value xs) \<ge> \<delta> * f2_value xs) \<le> \<epsilon>"
    using prob_space.median_bound sorry
  moreover have "\<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>3 (f1 \<circ> f2 \<circ> f3)). abs (r - f2_value xs) \<ge> \<delta> * f2_value xs) =
    \<P>(r in (distr \<Omega>\<^sub>0 \<Omega>\<^sub>2 (f2 \<circ> f3)). abs (median r s\<^sub>2 - f2_value xs) \<ge> \<delta> * f2_value xs)"
    apply (subst dist_123)
    apply (subst measure_distr)
    apply (simp add: f1_meas) apply (simp) 
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
  have "(\<Omega>\<^sub>0 \<bind> sketches) = distr \<Omega>\<^sub>0 \<Omega>\<^sub>3 (f1 \<circ> f2 \<circ> f3)" (* distr h (borel :: real measure)  f" *)
    apply (simp add:sketches_def)
    apply (subst bind_return)
    defer
    defer
    apply (simp add:averages_def)
    apply (subst bind_return)
    defer
    defer
    apply (simp add:medians_def del:median.simps)
    apply (subst bind_return_distr')
    defer
          defer
          apply (rule arg_cong[where f="distr \<Omega>\<^sub>0 \<Omega>\<^sub>3"])
          apply (simp add:f1_def f2_def f3_def comp_def del:median.simps)
    sorry
  moreover have "f2_alg \<delta> \<epsilon> n xs = \<Omega>\<^sub>0 \<bind> sketches"
    by (simp add:\<Omega>\<^sub>0_def \<Omega>\<^sub>1_def \<Omega>\<^sub>2_def \<Omega>\<^sub>3_def sketches_def averages_def medians_def Let_def s\<^sub>1_def s\<^sub>2_def p_def
            del:median.simps)

  ultimately show ?thesis by (simp del:median.simps f2_alg.simps) 
qed


(*
  have "\<And>x. 
    (\<And>k. k < s\<^sub>2 \<Longrightarrow> prob_space (x k)) \<Longrightarrow>
    (\<And>k. k < s\<^sub>2 \<Longrightarrow> \<P>(r in PiM {0..<s\<^sub>2} x. abs (r k - f2_value xs) > \<delta> * f2_value xs) < 1/8) \<Longrightarrow>
    \<P>(r in PiM {0..<s\<^sub>2} x \<bind> medians. abs (r - f2_value xs) > \<delta> * f2_value xs) \<le> \<epsilon>"
    apply (simp add:medians_def del:median.simps)
    apply (subst bind_return_distr')
      defer defer
      apply (subst space_bind[where N="borel"])
        defer defer
        apply (subst measure_distr)
    defer
    defer
    apply (simp del:median.simps)
          apply (simp add:space_bind del:median.simps)
    sorry *) (*
  proof -
    fix x
    assume "\<And>k. k < s\<^sub>2 \<Longrightarrow> \<P>(r in x. abs (r k - f2_value xs) > \<delta> * f2_value xs) < 1/8"
    assume "prob_space x"
    have "x \<bind> medians = distr 
    

    apply (subst bind_return_distr') *)
    (*
    medians
    sketch_avg k indep
    sketch_avg 
    sketch_avg \<bind> medians has some dist
  *)


  (*
    sketches

    P( 
  *)
  (*
    F

    P( r in h. bar)

    P( r in h \<bind> sketches. foo)

  *)

(*
  have averages_e: "averages =  (\<lambda>sketch. return borel (median (\<lambda>i\<^sub>2 \<in> {0..<s\<^sub>2}. \<Sum>i\<^sub>1\<in>{0..<s\<^sub>1}. (sketch i\<^sub>2 i\<^sub>1)\<^sup>2 / real s\<^sub>1) s\<^sub>2))"
    apply (simp add:averages_def medians_def del:median.simps)
    apply (subst bind_return [where N="borel"])
      apply measurable
    defer
    apply (simp add:space_PiM PiE_def,simp) sorry

  define avg where "avg = (\<lambda>h (i\<^sub>2::nat). \<Sum>i\<^sub>1\<in>{0..<s\<^sub>1}. (sum_list (map (eval_hash_function p (h i\<^sub>2 i\<^sub>1)) xs))\<^sup>2 / real s\<^sub>1)"
  define lhs where "lhs = (\<lambda>h. median (\<lambda>i\<^sub>2. avg h i\<^sub>2) s\<^sub>2)"

  have sketches_e: "sketches = (\<lambda>h. return borel (lhs h))"
    apply (simp add:sketches_def averages_e lhs_def avg_def del:median.simps)
    apply (subst bind_return [where N="borel"])
      apply measurable
    defer
      apply (simp add:space_PiM PiE_def)
     apply (rule ext) 
    apply (rule arg_cong2[where f="return"], simp)
    apply (rule arg_cong2[where f="median"], simp)
    sorry

  have "h \<bind> sketches = distr h borel lhs"
    apply (simp add:sketches_e)
    apply (rule bind_return_distr')
     apply (simp add:h_def poly_hash_family_def)
     defer
     apply (simp add:lhs_def h_def del:median.simps)
    sorry
  have s1_nonzero: "s\<^sub>1 \<noteq> 0" sorry


  have "distr h borel lhs = 
    distr (distr h (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. borel) avg) borel 
      (\<lambda>sketch_avg. median sketch_avg s\<^sub>2)"
    sorry

  have "\<P>(\<omega> in distr h (\<Pi>\<^sub>M _ \<in> {0..<s\<^sub>2}. borel) avg. True) = 1" 
    sorry

  show ?thesis sorry

qed
*)
lemma lift_measurable:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> measurable (M i) (N i)"
  shows "(\<lambda> x i. f i (x i)) \<in> measurable (PiM I M) (PiM I N)"
  sorry

lemma sum_list_measurable:
  assumes "\<And>i. i \<in> (set I) \<Longrightarrow> (f i :: 'a \<Rightarrow> ('b :: monoid_add)) \<in> measurable M N"
  shows "(\<lambda>x. sum_list (map (\<lambda>i. f i x) I)) \<in> measurable M N"
  sorry
(*
  f : R \<rightarrow> R

  f' : R^n \<rightarrow> R^n

  f'(x)_k = f_k(x_k)

*)


theorem f2_exp:
  assumes "\<epsilon> < 1"
  assumes "\<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  shows
  "\<P>(r in (f2_alg \<delta> \<epsilon> n xs). abs (r - f2_value xs) > \<delta> * f2_value xs) < \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(2 * ln \<epsilon>)\<rceil>"
  define p where "p = find_prime_above n"
  define h where "h = PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. poly_hash_family (ZFact (int p)) 4))"
  define sketch where 
      "sketch = h \<bind> (\<lambda>h. return (PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. borel)))
      (\<lambda>i\<^sub>2 i\<^sub>1. sum_list (map (eval_hash_function p (h i\<^sub>2 i\<^sub>1)) xs)))"
  define sketch_avg where 
      "sketch_avg = sketch \<bind> (\<lambda>sketch. return (PiM {0..<s\<^sub>2} (\<lambda>_. borel)) 
      (\<lambda>i\<^sub>2. sum_list (map (\<lambda>i\<^sub>1. sketch i\<^sub>2 i\<^sub>1^2 / s\<^sub>1)  [0..<s\<^sub>1])))"

  have s1_nonzero: "s\<^sub>1 \<noteq> 0" sorry

  have "f2_alg_1 \<delta> \<epsilon> n xs = sketch_avg \<bind> (\<lambda>sketch_avg. return borel (median (map sketch_avg [0..<s\<^sub>1])))"
    apply (simp add:sketch_avg_def sketch_def h_def[symmetric] p_def[symmetric]
           s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] Let_def del: set_upto median.simps find_prime_above.simps) 
    apply (subst bind_cong_All[where M="h"])
    apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. borel))" 
                             and R="PiM {0..<s\<^sub>2} (\<lambda>_. borel)"])
      apply (simp add:h_def, measurable, rule lift_measurable, rule lift_measurable)
      apply (simp add:poly_hash_family_def)
     apply measurable
     apply (rule lift_measurable, rule sum_list_measurable)
    using s1_nonzero apply measurable
    apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
    apply (rule measurable_bind2 [where N="PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. borel))"])
      apply (simp add:h_def, measurable, rule lift_measurable, rule lift_measurable)
      apply (simp add:poly_hash_family_def)
      apply measurable
    apply (rule lift_measurable, rule sum_list_measurable)
    using s1_nonzero apply measurable
    apply simp
     defer
     apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
       defer defer
    apply simp
    apply (measurable)
       apply (simp add:h_def poly_hash_family_def, measurable, rule lift_measurable, rule lift_measurable)

    apply (simp add:h_def) 
        apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
    defer
    defer
    apply simp
    sledgehammer
(*      apply (rule measurable_subprob_algebra)
        apply (rule prob_space_imp_subprob_space)
        apply (rule prob_space_PiM)
        apply (rule prob_space_PiM)
        apply (simp add:prob_space_return)
       apply (meson sets_PiM_cong sets_return)
      apply (simp add:h_def) 
    apply (rule measurable_PiM_single)
    apply (subst product_sigma_finite.emeasure_PiM)
    using product_sigma_finite.emeasure_PiM apply (measurable)
    apply (simp add:measurable_submarkov h_def) sledgehammer*)
    defer 
    defer
      apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
    defer
    defer
        apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
    defer
    defer
    apply simp
    apply (simp add:bind_assoc del:median.simps)
    try0
  apply (simp del:find_prime_above.simps median.simps)

(*
  h <- foo
  g h

  foo \<bind> (\<lambda>h. g h)


*)

theorem f2_exp:
  assumes "\<epsilon> < 1"
  assumes "\<epsilon> > 0"
  assumes "\<delta> > 0"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < n"
  shows
  "\<P>(r in (f2_alg \<delta> \<epsilon> n xs). abs (r - f2_value xs) > \<delta> * f2_value xs) < \<epsilon>"
proof -
  define s\<^sub>1 where "s\<^sub>1 = nat \<lceil>16 / \<delta>\<^sup>2\<rceil>"
  define s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(2 * ln \<epsilon>)\<rceil>"
  define p where "p = find_prime_above n"
  define h where "h = PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. poly_hash_family (ZFact (int p)) 4))"
  define sketch where 
      "sketch = h \<bind> (\<lambda>h. PiM {0..<s\<^sub>2} (\<lambda>i\<^sub>2. PiM {0..<s\<^sub>1} 
      (\<lambda>i\<^sub>1. return borel (sum_list (map (eval_hash_function p (h i\<^sub>2 i\<^sub>1)) xs)))))"
  define sketch_avg where 
      "sketch_avg = sketch \<bind> (\<lambda>sketch. PiM {0..<s\<^sub>2} 
      (\<lambda>i\<^sub>2. return borel (sum_list (map (\<lambda>i\<^sub>1. sketch i\<^sub>2 i\<^sub>1^2 / s\<^sub>1)  [0..<s\<^sub>1]))))"
  have "f2_alg \<delta> \<epsilon> n xs = sketch_avg \<bind> (\<lambda>sketch_avg. return borel (median (map sketch_avg [0..<s\<^sub>1])))"
     apply (simp add:sketch_avg_def sketch_def h_def[symmetric] p_def[symmetric]
           s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] Let_def del: set_upto median.simps find_prime_above.simps) 
    apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. PiM {0..<s\<^sub>1} (\<lambda>_. borel))" 
                             and R="PiM {0..<s\<^sub>2} (\<lambda>_. borel)"])
(*      apply (rule measurable_subprob_algebra)
        apply (rule prob_space_imp_subprob_space)
        apply (rule prob_space_PiM)
        apply (rule prob_space_PiM)
        apply (simp add:prob_space_return)
       apply (meson sets_PiM_cong sets_return)
      apply (simp add:h_def) 
    apply (rule measurable_PiM_single)
    apply (subst product_sigma_finite.emeasure_PiM)
    using product_sigma_finite.emeasure_PiM apply (measurable)
    apply (simp add:measurable_submarkov h_def) sledgehammer*)
    defer 
    defer
      apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
    defer
    defer
        apply (subst bind_assoc [where N="PiM {0..<s\<^sub>2} (\<lambda>_. borel)" and R="borel"])
    defer
    defer
    apply simp
    apply (simp add:bind_assoc del:median.simps)
    try0
  apply (simp del:find_prime_above.simps median.simps)

(*
  h <- foo
  g h

  foo \<bind> (\<lambda>h. g h)


*)



lemma prod_space:
  assumes "field F"
  assumes "finite (carrier F)"
  shows "prob_space (\<Pi>\<^sub>M i \<in> {k. k < (s1::nat)}. poly_hash_family F 4)"
proof -
  show ?thesis 
    by (simp add: assms(1) assms(2) prob_space_PiM prob_space_poly_family)
qed

lemma set_comp_subsetI: "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> {f x|x. P x} \<subseteq> B"
  by blast

lemma lift_rv:
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space.random_variable (\<Omega> i) (M' i) (X' i)"
  shows "\<And>i. i \<in> I \<Longrightarrow> prob_space.random_variable (\<Pi>\<^sub>M i \<in> I. \<Omega> i) (M' i) (\<lambda>\<omega>. X' i (\<omega> i))"
  using assms by measurable

lemma lift_exp:
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  assumes "j \<in> I"
  assumes "prob_space.random_variable (\<Omega> j) M' (X' :: 'a \<Rightarrow> real)"
  assumes "integrable (\<Omega> j) X'"
  shows "prob_space.expectation  (\<Pi>\<^sub>M i \<in> I. \<Omega> i) (\<lambda>\<omega>. X' (\<omega> j)) = prob_space.expectation (\<Omega> j) X'"
proof -
  interpret product_sigma_finite \<Omega> sorry
(*    apply (simp add:product_sigma_finite_def)*)

  define Y where "Y = (\<lambda> i \<omega>. (if i = j then X' \<omega> else 1))"
  show ?thesis 
    using product_integral_prod[where I="I" and f="Y"]
  
    sorry
qed
(*
  show that the distribution remains the same
*)

lemma enn2real_prod:
  assumes "finite J"
  shows "(\<Prod>j \<in> J. enn2real (f j)) = enn2real( \<Prod>j \<in> J. f j)"
  using assms apply (induction J rule:finite_induct)
  by (simp add:enn2real_mult)+

lemma indep_sets_product_space:
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  shows "prob_space.indep_sets (Pi\<^sub>M I \<Omega>) (\<lambda>i. {{f. f i \<in> A} \<inter> space (Pi\<^sub>M I \<Omega>) |A. A \<in> sets (\<Omega> i)}) I"
proof -
  define \<Omega>' where "\<Omega>' = (\<lambda>i. (if i \<in> I then \<Omega> i else count_space {undefined}))"
  interpret product_prob_space "\<Omega>'"
    apply (simp add:product_prob_space_def product_sigma_finite_def product_prob_space_axioms_def)
    apply (rule conjI)
    apply (simp add:\<Omega>'_def) 
    apply (meson finite.emptyI assms(2) finite_insert prob_space_imp_sigma_finite sigma_finite_measure_count_space_finite)
    apply (simp add:\<Omega>'_def assms(2))
    by (simp add:prob_space_def prob_space_axioms_def finite_measure_count_space)

  have b: "Pi\<^sub>M I \<Omega> = Pi\<^sub>M I \<Omega>'" 
    by (rule PiM_cong, simp, simp add:\<Omega>'_def)

  have a:"\<And> J A. J \<subseteq> I \<Longrightarrow>  finite J \<Longrightarrow> J \<noteq> {} \<Longrightarrow>
     A \<in> (\<Pi> i\<in>J. {{f. f i \<in> A} \<inter> space (Pi\<^sub>M I \<Omega>) |A. A \<in> sets (\<Omega> i)}) \<Longrightarrow>
   emeasure (Pi\<^sub>M I \<Omega>) (\<Inter> (A ` J)) = (\<Prod>j\<in>J. emeasure (Pi\<^sub>M I \<Omega>) (A j))"
  proof -
    fix J A
    assume a1:"J \<subseteq> I"
    assume a2:"finite J"
    assume a3:"J \<noteq> {}"
    assume "A \<in> (\<Pi> i\<in>J. {{f. f i \<in> A} \<inter> space (Pi\<^sub>M I \<Omega>) |A. A \<in> sets (\<Omega> i)})"
    then obtain B where 
      B_sets: "\<And>i. i \<in> J \<Longrightarrow> B i \<in> sets (\<Omega> i)" and
      A_def: "\<And>i. i \<in> J \<Longrightarrow> A i = {f. f i \<in> B i}  \<inter> space (Pi\<^sub>M I \<Omega>)"
      apply (simp add:Pi_def)
      by metis

    have r3: "\<And>i. i \<in> J \<Longrightarrow> B i \<in> sets (\<Omega>' i)" 
      using B_sets a1 \<Omega>'_def 
      by (metis subset_eq)

    have r1: "\<Inter> (A ` J) = {x \<in> space (Pi\<^sub>M I \<Omega>). \<forall>i \<in> J. x i \<in> B i}"
      apply (rule order_antisym)
      by (rule subsetI, simp add:A_def a3)+

    have r2: "\<And>j. j \<in> J \<Longrightarrow> A j = {x \<in> space (Pi\<^sub>M I \<Omega>). \<forall>i \<in> {j}. x i \<in> B i}"
      apply (rule order_antisym)
      by (rule subsetI, simp add:A_def)+

    show "emeasure (Pi\<^sub>M I \<Omega>) (\<Inter> (A ` J)) = (\<Prod>j\<in>J. emeasure (Pi\<^sub>M I \<Omega>) (A j))"
      apply (simp add:r1 b)
      apply (subst emeasure_PiM_Collect)
      apply (simp add:a1)
        apply (simp add:a2)
       apply (simp add:r3)
      apply (rule prod.cong)
       apply (simp)
      apply (subst r2, simp)
      apply (simp only:b)
      apply (subst emeasure_PiM_Collect)
      using a1 apply (blast)
        apply simp
      by (simp add: r3, simp)
    qed

  show ?thesis
  apply (subst prob_space.indep_sets_def)
   apply (simp add:assms prob_space_PiM)
  apply (rule conjI, rule ballI, rule set_comp_subsetI)
   apply (simp add:space_PiM sets_PiM_single)
   apply (rule sigma_sets.Basic, simp, blast)
  apply (rule allI, rule impI, rule impI, rule impI, rule ballI)
    apply (simp add:measure_def enn2real_prod)
    apply (rule arg_cong [where f="enn2real"])
    by (simp add:a)
qed


lemma indep_vars_product_space:
  assumes "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space (\<Omega> i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> prob_space.random_variable (\<Omega> i) (M' i) (X' i)"
  shows "prob_space.indep_vars (\<Pi>\<^sub>M i \<in> I. \<Omega> i) M' (\<lambda>i. \<lambda>\<omega>. X' i (\<omega> i)) I"
proof -
  have a:"\<And>i. i \<in> I \<Longrightarrow> prob_space.random_variable (\<Pi>\<^sub>M i \<in> I. \<Omega> i) (M' i) (\<lambda>\<omega>. X' i (\<omega> i))"
    using assms lift_rv by auto
  have b:"\<And>i A. i \<in> I \<Longrightarrow> A \<in> sets (M' i) \<Longrightarrow> 
  (\<lambda>\<omega>. X' i (\<omega> i)) -` A \<inter> space (Pi\<^sub>M I \<Omega>) \<in> {{f. f i \<in> A} \<inter> space (Pi\<^sub>M I \<Omega>) |A. A \<in> sets (\<Omega> i)}"
  proof -
    fix i A
    assume b1:"i \<in> I"
    assume b2:"A \<in> sets (M' i)"
    define B where "B = X' i -` A  \<inter> (space (\<Omega> i))"
    have "B \<in> sets (\<Omega> i)"
      using B_def assms(3) b1 b2 by (simp add:measurable_def)
    moreover have "(\<lambda>\<omega>. X' i (\<omega> i)) -` A \<inter> space (Pi\<^sub>M I \<Omega>) \<in> {{f. f i \<in> B} \<inter> space (Pi\<^sub>M I \<Omega>)}"
      apply (simp add:B_def)
      apply (rule order_antisym, rule subsetI, simp add:space_PiM) 
      using b1 apply blast
      by (rule subsetI, simp add:space_PiM)
    ultimately
      show "(\<lambda>\<omega>. X' i (\<omega> i)) -` A \<inter> space (Pi\<^sub>M I \<Omega>) \<in> {{f. f i \<in> A} \<inter> space (Pi\<^sub>M I \<Omega>) |A. A \<in> sets (\<Omega> i)}"
      by blast
  qed
  show ?thesis
  apply (subst prob_space.indep_vars_def2)
   apply (simp add:assms prob_space_PiM)
  apply (rule conjI) 
   apply (rule ballI)
    using assms apply measurable
    apply (rule prob_space.indep_sets_mono_sets 
          [where F="(\<lambda>i. {{f. f i \<in> A} \<inter> space (Pi\<^sub>M I \<Omega>) |A. A \<in> sets (\<Omega> i)})"])
      apply (simp add:assms prob_space_PiM)
     apply (simp add:assms indep_sets_product_space)
    apply (rule set_comp_subsetI)
    using b by auto
qed

end