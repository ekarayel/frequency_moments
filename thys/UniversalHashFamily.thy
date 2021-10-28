section \<open>$k$-independent Hash Families\<close>

theory UniversalHashFamily
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility" PolynomialCounting
  "HOL-Analysis.Nonnegative_Lebesgue_Integration" "HOL-Probability.Probability_Measure"
  "HOL-Probability.Independent_Family" Probability_Ext "HOL-Probability.Distributions" Prod_PMF
begin

text \<open>A k-independent hash family $\mathcal H$ is probability space, whose elements are hash functions 
with domain $U$ and range ${i. i < m}$ such that:

\begin{itemize}
\item For every fixed $x \in U$ and value $y < m$ exactly $\frac{1}{m}$ of the hash functions map
  $x$ to $y$: $P_{h \in \mathcal H} \left(h(x) = y\right) = \frac{1}{m}$.
\item For $k$ universe elements: $x_1,\cdots,x_k$ the functions $h(x_1), \cdots, h(x_m)$ form
  independent random variables.
\end{itemize}

In this section, we construct $k$-independent hash families following the approach outlined
by Wegman and Carter using the polynomials of degree less than $k$ over a finite field.\<close>

text \<open>The space of polynomials of degree less than $k$ forms a probability space.\<close>
definition poly_hash_family where
  "poly_hash_family F k = uniform_count_measure (bounded_degree_polynomials F k)"

lemma non_empty_bounded_degree_polynomials:
  assumes "ring F"
  shows "bounded_degree_polynomials F k \<noteq> {}"
proof -
  have "\<zero>\<^bsub>poly_ring F\<^esub> \<in> bounded_degree_polynomials F k"
    using assms
    by (simp add: bounded_degree_polynomials_def univ_poly_zero univ_poly_zero_closed)
  thus ?thesis by auto
qed

lemma prob_space_poly_family:
  assumes "field F"
  assumes "finite (carrier F)"
  shows "prob_space (poly_hash_family F k)"
proof -
  have "finite (bounded_degree_polynomials F k)"
     using finite_poly_count assms(1) assms(2) by blast
  moreover have "\<zero>\<^bsub>poly_ring F\<^esub> \<in> bounded_degree_polynomials F k"
    using assms(1) assms(2)
    by (simp add: bounded_degree_polynomials_def univ_poly_zero univ_poly_zero_closed)
  ultimately show ?thesis using prob_space_uniform_count_measure 
    by (metis empty_iff poly_hash_family_def)
qed

text \<open>A hash function is just polynomial evaluation.\<close>
definition hash_function where "hash_function F x \<omega> = ring.eval F \<omega> x"

definition hash where "hash F x \<omega> = ring.eval F \<omega> x"

lemma hash_range:
  assumes "ring F"
  assumes "\<omega> \<in> bounded_degree_polynomials F n"
  assumes "x \<in> carrier F"
  shows "hash F x \<omega> \<in> carrier F"
  using assms 
  apply (simp add:hash_def bounded_degree_polynomials_def)
  by (metis ring.eval_in_carrier ring.polynomial_incl univ_poly_carrier)

lemma hash_functions_are_random_variables:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "i \<in> (carrier F)"
  shows "prob_space.random_variable (poly_hash_family F n) (uniform_count_measure (carrier F)) (hash_function F i)"
proof -
  interpret ring "F" using assms(1) by (simp add:domain_def field_def cring_def)
  have "\<And>x. x \<in> carrier (poly_ring F) \<Longrightarrow> set x \<subseteq> carrier F"
    using polynomial_incl univ_poly_carrier by blast
  thus ?thesis 
    apply (simp add:poly_hash_family_def uniform_count_measure_def point_measure_def Pi_def bounded_degree_polynomials_length hash_function_def)
    using assms(3) eval_in_carrier by presburger
qed

lemma poly_cards:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> (carrier F)"
  shows "card {\<omega> \<in> bounded_degree_polynomials F n. (\<forall>k \<in> K. ring.eval F \<omega> k = y k)} = 
         card (carrier F)^(n-card K)"
  using interpolating_polynomials_count[where n="n-card K" and f="y" and F="F" and K="K"]  assms 
  by fastforce

lemma poly_cards_single:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "k \<in> carrier F"
  assumes "1 \<le> n"
  assumes "y \<in> carrier F"
  shows "card {\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k = y} = 
         card (carrier F)^(n-1)"
  using poly_cards[OF assms(1) assms(2), where K="{k}" and y="\<lambda>_. y", simplified] assms(3) assms(4)[simplified]
  by (simp add: assms(5))


lemma expand_subset_filter: "{x \<in> A. P x} = A \<inter> {x. P x}"
  by force

lemma hash_prob:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> carrier F"
  shows "\<P>(\<omega> in pmf_of_set (bounded_degree_polynomials F n). (\<forall>x \<in> K. hash F x \<omega> = y x)) = 1/(real (card (carrier F)))^card K" 
proof -
  have "\<zero>\<^bsub>F\<^esub> \<in> carrier F"
    using assms(1) field.is_ring ring.ring_simprules(2) by blast

  hence a:"card (carrier F) > 0"
    apply (subst card_gt_0_iff) 
    using assms(2) by blast

  show ?thesis
    apply (subst measure_pmf_of_set)
      apply (rule non_empty_bounded_degree_polynomials[OF field.is_ring[OF assms(1)]])
     apply (rule fin_degree_bounded[OF field.is_ring[OF assms(1)] assms(2)])
    apply (simp add:hash_def expand_subset_filter[symmetric])
    apply (subst poly_cards[OF assms(1) assms(2) assms(3) assms(4) assms(5)])
    apply (subst bounded_degree_polynomials_count[OF field.is_ring[OF assms(1)] assms(2)])
    apply (subst frac_eq_eq)
    using a apply simp
    using a apply simp
    apply (simp)
    by (metis assms(4) le_add_diff_inverse2 power_add)
qed


lemma bounded_poly_indep_pmf:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "J\<subseteq>carrier F"
  assumes "finite J" 
  assumes "card J \<le> n"
  assumes "1 \<le> n"
  shows "prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials F n)) 
    (\<lambda>_. pmf_of_set (carrier F)) (hash_function F) J"
proof -
  have "\<zero>\<^bsub>poly_ring F\<^esub> \<in> bounded_degree_polynomials F n"
    apply (simp add:bounded_degree_polynomials_def)
    apply (rule conjI)
     apply (simp add: univ_poly_zero univ_poly_zero_closed)
    using univ_poly_zero by blast
  hence b: "bounded_degree_polynomials F n \<noteq> {}"
    by blast
  have c: "finite (bounded_degree_polynomials F n)"
    by (rule finite_poly_count[OF assms(1) assms(2)])
  have d: "\<And> A P. A \<inter> {\<omega>. P \<omega>} = {\<omega> \<in> A. P \<omega>}"
    by blast

  have e:"ring F" using assms(1) field.is_ring by blast
  have f: "0 < card (carrier F)" 
    by (metis assms(2) card_0_eq e empty_iff gr0I ring.ring_simprules(2))

  define \<Omega> where "\<Omega> = (pmf_of_set (bounded_degree_polynomials F n))"
  have a:"\<And>a J'.
       J' \<subseteq> J \<Longrightarrow>
       finite J' \<Longrightarrow>
       measure_pmf.prob \<Omega> {\<omega>. \<forall>x\<in>J'. hash_function F x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure_pmf.prob \<Omega> {\<omega>. hash_function F x \<omega> = a x})"
  proof -
    fix a
    fix J'
    assume a_1: "J' \<subseteq> J"
    assume a_11: "finite J'"
    have a_2: "card J' \<le> n" by (metis card_mono order_trans a_1 assms(4) assms(5))
    have a_3: "J' \<subseteq> carrier F" by (metis order_trans a_1 assms(3))
    have a_4: "1 \<le>n " using assms by blast

    show "measure_pmf.prob \<Omega> {\<omega>. \<forall>x\<in>J'. hash_function F x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure_pmf.prob \<Omega> {\<omega>. hash_function F x \<omega> = a x})"
    proof (cases "a ` J' \<subseteq> carrier F")
      case True
      have a_5: "\<And>x. x \<in> J' \<Longrightarrow> x \<in> carrier F"  using a_1 assms(3) order_trans by force
      have a_6: "\<And>x. x \<in> J' \<Longrightarrow> a x \<in> carrier F"  using True by force
      show ?thesis 
       apply (simp add:\<Omega>_def measure_pmf_of_set[OF b c] d hash_function_def)
       apply (subst poly_cards[OF assms(1) assms(2) a_3 a_2], metis True)
        apply (simp add:  bounded_degree_polynomials_count[OF e assms(2)] poly_cards_single[OF assms(1) assms(2) a_5 a_4 a_6] power_divide)
        apply (subst frac_eq_eq, simp add:f, simp add:f) 
          apply (simp add:power_add[symmetric] power_mult[symmetric])
          apply (rule arg_cong2[where f="\<lambda>x y. x ^ y"], simp)
        using a_2 a_4 mult_eq_if by force
    next
      case False
      then obtain j where a_8: "j \<in> J'" and a_9: "a j \<notin> carrier F" by blast
      have a_7: "\<And>x \<omega>. \<omega> \<in> bounded_degree_polynomials F n \<Longrightarrow> x \<in> carrier F \<Longrightarrow> hash_function F x \<omega> \<in> carrier F"
        apply (simp add:bounded_degree_polynomials_def hash_function_def)
        by (metis e ring.eval_in_carrier  ring.polynomial_incl univ_poly_carrier)
      have a_10: "{\<omega> \<in> bounded_degree_polynomials F n. \<forall>x\<in>J'. hash_function F x \<omega> = a x} = {}"
        apply (rule order_antisym)
        apply (rule subsetI, simp, metis a_7 a_8 a_9  a_3 in_mono)
        by (rule subsetI, simp) 
      have a_12: "{\<omega> \<in> bounded_degree_polynomials F n. hash_function F j \<omega> = a j} = {}"
        apply (rule order_antisym)
        apply (rule subsetI, simp, metis a_7 a_8 a_9  a_3 in_mono)
        by (rule subsetI, simp) 
      then show ?thesis
        apply (simp add:\<Omega>_def measure_pmf_of_set[OF b c] d a_10)
        apply (rule prod_zero, metis a_11)
        apply (rule bexI[where x="j"])
        by (simp add:a_12 a_8)+
    qed
  qed
  show ?thesis
    apply (rule indep_vars_pmf)
    using a by (simp add:\<Omega>_def)
qed

lemma poly_card_set:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "k \<in> carrier F"
  assumes "n \<ge> 1" 
  assumes "A \<subseteq> (carrier F)"
  shows "card {\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k \<in> A} = 
         card A * card (carrier F)^(n-1)" (is "card ?A = ?B")
proof -
  have b:"Suc 0 \<le> n" using assms(4) by linarith
  define P where "P = (\<lambda>x. {\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k = x})"
  have d1: "\<And>x. x \<in> carrier F \<Longrightarrow> card (P x) = (card (carrier F)^(n-1))"
  proof -
    fix x
    assume a:"x \<in> carrier F"
    show "card (P x) = (card (carrier F)^(n-1))"
      using assms a b poly_cards[where K="{k}" and y="(\<lambda>_.x)"]
      by (simp add:P_def) 
  qed
  hence d:"\<And>x. x \<in> P ` A \<Longrightarrow> card x = card (carrier F)^(n-1)"
    using assms(5)
    by blast
  have c:"?A = (\<Union>x \<in> A. P x)"
    apply (simp add:P_def)
    apply (rule order_antisym)
    by (rule subsetI, simp)+ 
  have e:"inj_on P A"
  proof (rule inj_onI)
    fix x y
    assume "y \<in> A"
    assume "P x = P y"
    moreover 
    have "carrier F \<noteq> {}" using assms(3) by fastforce
    moreover  assume "x \<in> A"
    hence "P x \<noteq> {}" using b d1 
      by (metis assms(2) assms(5) calculation(2) card_eq_0_iff in_mono power_not_zero)
    then obtain z where "z \<in> P x" by blast
    ultimately have "z \<in> P x \<inter> P y"
      by (simp add:P_def)
    then show "x = y" 
      by (simp add:P_def, force)
  qed
  have "disjoint (P ` A)" apply (rule disjointI)
    apply (simp add:P_def) 
    apply (rule order_antisym)
    by (rule subsetI, simp, fastforce, simp) 
  moreover have "\<And>B. B \<in> P ` A \<Longrightarrow> finite B"
    apply (simp add:P_def)
    apply (subgoal_tac "ring F")
    using fin_degree_bounded assms(2) apply fastforce
    using assms(1)  field.is_ring by blast
  ultimately show "card ?A = ?B"
    apply (simp add:c card_Union_disjoint)
    apply (simp add:d)
    using e card_image by blast
qed

lemma hash_indep_pmf:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "J\<subseteq>carrier F"
  assumes "finite J" 
  assumes "card J \<le> n"
  assumes "1 \<le> n"
  shows "prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials F n)) 
    (\<lambda>_. pmf_of_set (carrier F)) (hash F) J"
proof -
  have a: "hash = hash_function"
    apply (rule ext, rule ext, rule ext)
    by (simp add:hash_def hash_function_def)
  show ?thesis
    using bounded_poly_indep_pmf assms apply (simp add:a) by blast
qed

lemma poly_card_set':
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "k \<in> carrier F"
  assumes "n \<ge> 1" 
  shows "card {\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k \<in> A} = 
         card (A \<inter> carrier F) * card (carrier F)^(n-1)"
proof -
  have a:"ring F" using assms(1) field.is_ring by blast

  have b: "\<And>x \<omega>. \<omega> \<in> bounded_degree_polynomials F n \<Longrightarrow> x \<in> carrier F \<Longrightarrow> ring.eval F \<omega> x \<in> carrier F"
    apply (simp add:bounded_degree_polynomials_def)
    by (metis a ring.eval_in_carrier  ring.polynomial_incl univ_poly_carrier)

  have c: "{\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k \<in> A} = 
      {\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k \<in> A \<inter> carrier F}"
    apply (rule Collect_cong)
    using b assms(3) by blast

  show ?thesis
    apply (subst c)
    by (rule poly_card_set[OF assms(1) assms(2) assms(3) assms(4)], simp)
qed

text \<open>We introduce k-wise independent random variables using the existing definition of
independent random variables.\<close>

definition (in prob_space) k_wise_indep_vars where
  "k_wise_indep_vars k M' X' I = (\<forall>J \<subseteq> I. card J \<le> k \<longrightarrow> finite J \<longrightarrow> indep_vars M' X' J)" 

lemma (in prob_space) k_wise_subset:
  assumes "k_wise_indep_vars k M' X' I"
  assumes "J \<subseteq> I"
  shows "k_wise_indep_vars k M' X' J"
  using assms by (simp add:k_wise_indep_vars_def)

text \<open>Key result hash functions are k-wise independent random variables.\<close>

end