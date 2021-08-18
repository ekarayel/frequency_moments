section \<open>$k$-independent Hash Families\<close>

theory UniversalHashFamily
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility" PolynomialCounting
  "HOL-Analysis.Nonnegative_Lebesgue_Integration" "HOL-Probability.Probability_Measure"
  "HOL-Probability.Independent_Family" "HOL-Probability.Stream_Space" "HOL-Probability.Distributions"
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

lemma poly_probabilities:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> (carrier F)"
  shows "prob_space.prob (poly_hash_family F n) 
    {\<omega>. \<omega> \<in> space (poly_hash_family F n) \<and> (\<forall>k \<in> K. hash_function F k \<omega> = y k)} = 1/(real (card (carrier F))^ card K)"
    (is "prob_space.prob (poly_hash_family F n) ?T = ?B")
proof -
  interpret prob_space "(poly_hash_family F n)" using prob_space_poly_family assms by metis

  have "\<zero>\<^bsub>F\<^esub> \<in> carrier F"
    using assms(1) by (simp add: cring.cring_simprules(2) fieldE(1))
  hence non_zero_den: "carrier F \<noteq> {}" by blast
  have "card {\<omega> \<in> bounded_degree_polynomials F n. (\<forall>k \<in> {}. hash_function F k \<omega> = y k)} = card (carrier F)^(n-card {})"
    using poly_cards[where K="{}"] assms by auto
  hence "card (bounded_degree_polynomials  F n) = card (carrier F)^n" by simp
  moreover have "finite (bounded_degree_polynomials F n)"
    using finite_poly_count assms(1) assms(2) by blast
  moreover have "?T \<subseteq> bounded_degree_polynomials F n"
    by (simp add:poly_hash_family_def space_uniform_count_measure)
  ultimately show ?thesis
    apply (simp add:measure_uniform_count_measure poly_hash_family_def hash_function_def)
    using assms apply (simp add:poly_cards space_uniform_count_measure)
     using non_zero_den apply (subst frac_eq_eq, simp, simp) 
     by (metis add.commute add_diff_inverse_nat mult.left_neutral not_less power_add)
qed

text \<open>On a finite set $M$ the $\sigma$-Algebra generated by singletons and the empty set
is already the power set of $M$.\<close>
lemma sigma_sets_singletons_and_empty:
  assumes "finite M"
  shows "sigma_sets M (insert {} ((\<lambda>k. {k}) ` M)) = Pow M"
proof -
  have "countable M" using assms countable_finite by blast
  hence "sigma_sets M ((\<lambda>k. {k}) ` M) = Pow M"
    using sigma_sets_singletons by auto
  hence "Pow M \<subseteq> sigma_sets M (insert {} ((\<lambda>k. {k}) ` M))"
    by (metis sigma_sets_subseteq subset_insertI)
  moreover have "(insert {} ((\<lambda>k. {k}) ` M)) \<subseteq> Pow M" by blast
  hence "sigma_sets M (insert {} ((\<lambda>k. {k}) ` M)) \<subseteq> Pow M"
    by (meson sigma_algebra.sigma_sets_subset sigma_algebra_Pow)
  ultimately show ?thesis by force
qed

text \<open>The main result of this section is that
\begin{itemize}
\item Each hash function has uniform distribution over the finite fields.
\item The hash functions are k-wise independent random variables. 
\end{itemize}
\<close>

lemma uniform_distribution:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "n > 0"
  assumes "k \<in> carrier F"
  assumes "v \<in> carrier F"
  shows "\<P>(\<omega> in poly_hash_family F n. hash_function F k \<omega> = v) = 1/(real (card (carrier F)))"
proof -
  have "{k} \<subseteq> carrier F" using assms(4) by simp
  moreover have "card {k} \<le> n" using assms(3) by simp
  moreover have "(\<lambda>_. v) ` {k} \<subseteq> carrier F" apply (rule subsetI) using assms(5) by simp 
  ultimately show ?thesis
    using assms(1) assms(2) poly_probabilities[where F="F" and K="{k}" and y="(\<lambda>_. v)"] by simp
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

lemma indep:
  assumes "field F"
  assumes "finite (carrier F)"
  shows 
     "prob_space.k_wise_indep_vars (poly_hash_family F n) n (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) (carrier F)" (is ?B)
proof -
  interpret prob_space "(poly_hash_family F n)" using prob_space_poly_family assms by metis

  have a1:"ring F" using assms(1) by (simp add:domain_def field_def cring_def)

  have "\<And>J. J \<subseteq> carrier F  \<Longrightarrow> card J \<le> n \<Longrightarrow> finite J \<Longrightarrow> 
    indep_vars (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) J"
  proof -
    fix J
    assume d:"J \<subseteq> carrier F"
    assume d2:"card J \<le> n"
    assume d3:"finite J"
    have b:"\<And>i. i \<in> J \<Longrightarrow> random_variable (uniform_count_measure (carrier F)) (\<lambda>\<omega>. hash_function F i \<omega>)" 
      apply (simp add:hash_function_def)
      apply (simp add:poly_hash_family_def uniform_count_measure_def point_measure_def Pi_def bounded_degree_polynomials_def)
      by (meson a1 d ring.carrier_is_subring ring.eval_in_carrier ring.polynomial_in_carrier subsetD univ_poly_carrier)

    define M where "M = (\<lambda>k. {k}) ` carrier F \<union> {{}}"
    define S where "S = (\<lambda>i. {hash_function F i -` y \<inter> space (poly_hash_family F n) | y. y \<in> M})" 
      (* maybe we can use singletons and use indep-sets_sigma here *)
    have e:"\<And>i. i \<in> J \<Longrightarrow> hash_function F i \<in> space (poly_hash_family F n) \<rightarrow> space (uniform_count_measure (carrier F))"
      apply (simp add:Pi_def poly_hash_family_def space_uniform_count_measure hash_function_def)
      using a1 d 
      by (metis (no_types, lifting) bounded_degree_polynomials_def mem_Collect_eq ring.carrier_is_subring ring.eval_poly_in_carrier subsetD univ_poly_carrier)
    have f:"sigma_sets (space (uniform_count_measure (carrier F))) M = sets (uniform_count_measure (carrier F))"
      apply (simp add: space_uniform_count_measure M_def sets_uniform_count_measure)
      using sigma_sets_singletons_and_empty assms(2) by auto
    have "\<And>A K. K \<noteq> {} \<Longrightarrow> K \<subseteq> J \<Longrightarrow> finite K \<Longrightarrow> (\<forall>k \<in> K. A k \<in> S k) \<Longrightarrow> prob (\<Inter>k \<in> K. A k) = (\<Prod>k \<in> K. prob (A k))"
    proof -
      fix A K
      assume f6:"K \<subseteq> J"
      hence f4: "card K \<le> n" using d2 d3 by (meson card_mono dual_order.trans)
      assume f2:"K \<noteq> {}"
      assume f7:"finite K"
      assume "\<forall>k \<in> K. A k \<in> S k"
      hence "\<exists>y. \<forall>k. k \<in> K \<longrightarrow> A k = hash_function F k -` y k \<inter> space (poly_hash_family F n) \<and> y k \<in> M"
        by (simp add: S_def, meson)
      then obtain y where A_def: 
        "\<And>k. k \<in> K \<Longrightarrow> A k = hash_function F k -` y k \<inter> space (poly_hash_family F n) \<and> y k \<in> M"
        by blast
      show "prob  (\<Inter>k \<in> K. A k) = (\<Prod>k \<in> K. prob (A k))"
      proof (cases "\<exists>k \<in> K. y k = {}")
        case True
        then obtain k where k_def: "y k = {} \<and> k \<in> K" by blast
        hence f1: "A k = {}" using A_def by auto
        hence "\<Inter> (A ` K) = {}" using k_def by blast
        moreover have "prob (A k) = 0"  using f1 by simp
        ultimately show ?thesis using k_def 
          by (metis \<open>finite K\<close> measure_empty prod_zero_iff) 
      next
        case False
        hence "\<forall>k \<in> K. \<exists>h \<in> carrier F. y k = {h}" using M_def A_def by fastforce
        hence "\<exists>y'. \<forall>k \<in> K. (y k = {y' k} \<and> y' k \<in> carrier F)" by meson
        then obtain y' where y'_def: "\<And>k. k \<in> K \<Longrightarrow> y k = {y' k} \<and> y' k \<in> carrier F" by blast
        hence f1: "\<And>k. k \<in> K \<Longrightarrow> A k = hash_function F k -` {y' k} \<inter> space (poly_hash_family F n)" using A_def by auto
        have "\<And>k. k \<in> K \<Longrightarrow> prob (A k) = 1/(card (carrier F))"
        proof -
          fix k
          assume a:"k \<in> K"
          have g:"A k = {\<omega>. \<omega> \<in> space (poly_hash_family F n) \<and> (\<forall>k\<in>{k}. hash_function F k \<omega> = y' k)}"
            apply (rule order_antisym)
            apply (rule subsetI, simp add:f1 f2 a)
            by (rule subsetI, simp add:f1 f2 a)
          have "card {k} \<le> n" using f4 a f7 
            by (meson bot.extremum card_mono insert_subset le_trans)
          moreover have "y' ` {k} \<subseteq> carrier F" using y'_def a by auto
          moreover have "{k} \<subseteq> carrier F" using a f6 d by blast
          ultimately have "prob (A k) = 1/(real (card (carrier F)))^card {k}"
            apply (simp (no_asm_simp) only:g)
            using assms(1) assms(2) poly_probabilities[where K="{k}" and F="F"] by presburger
          thus "prob (A k) = 1/(real (card (carrier F)))" by simp
        qed
        moreover have "prob (\<Inter>(A ` K)) =  1/(real (card (carrier F)))^(card K)"
        proof -
          have g:"\<Inter>(A ` K) = {\<omega>. \<omega> \<in> space (poly_hash_family F n) \<and> (\<forall>k \<in> K. hash_function F k \<omega> = y' k)}"
            apply (rule order_antisym)
            apply (rule subsetI, simp add:f1 f2)
            by (rule subsetI, simp add:f1 f2)
          have "card K \<le> n" using f4 by auto
          moreover have "K \<subseteq> carrier F" using f6 d by blast
          moreover have "y' ` K \<subseteq> carrier F" using y'_def by blast
          ultimately show "prob (\<Inter>(A ` K)) = 1/(real (card (carrier F)))^card K"
            apply (simp (no_asm_simp) only:g)
            using assms(1) assms(2) poly_probabilities[where K="K" and F="F"] by presburger
        qed
        ultimately show ?thesis by (simp add:power_one_over)
      qed
    qed
    moreover have "\<And>j. j \<in> J \<Longrightarrow> S j \<subseteq> events"
      apply (simp add:S_def poly_hash_family_def space_uniform_count_measure sets_uniform_count_measure Pow_def) by blast
    ultimately have "indep_sets S J"
      by (simp add: indep_setsI)
    moreover have "\<And>i. i \<in> J \<Longrightarrow> Int_stable (S i)"
    proof (rule Int_stableI)
      fix i a b
      assume "i \<in> J"
      assume a: "a \<in> S i"
      then obtain y1 where y1_def: "y1 \<in> M" and a_def: "a = hash_function F i -` y1 \<inter> space (poly_hash_family F n)"
        apply (simp add:S_def) by blast
      assume "b \<in> S i"
      then obtain y2 where y2_def: "y2 \<in> M" and b_def: "b = hash_function F i -` y2 \<inter> space (poly_hash_family F n)"
        apply (simp add:S_def) by blast
      show "a \<inter> b \<in> S i"
      proof (cases "y1 = y2")
        case True
        hence "a = b" using a_def b_def by fastforce
        hence "a \<inter> b = a" by blast
        then show ?thesis using a by auto
      next
        case False
        hence a:"y1 \<inter> y2 = {}" using y1_def y2_def M_def by blast
        have "a \<inter> b \<subseteq> {}" 
          apply (rule subsetI, simp add:a_def b_def)
          using False a by blast
        hence "a \<inter> b = {}" by force
        moreover have "{} \<in> S i" apply (simp add:S_def M_def) by blast
        ultimately show ?thesis by auto
      qed
    qed
    ultimately have "indep_sets (\<lambda>i. sigma_sets (space (poly_hash_family F n)) (S i)) J"
      using indep_sets_sigma by auto
    moreover have "\<And>i. i \<in> J \<Longrightarrow> sigma_sets (space (poly_hash_family F n)) (S i) \<supseteq>
      { hash_function F i -` A \<inter> space (poly_hash_family F n) | A. A \<in> sets (uniform_count_measure (carrier F))}"
      apply (simp add:S_def)
      by (simp add:sigma_sets_vimage_commute[where  \<Omega>'="space (uniform_count_measure (carrier F))",symmetric] e f)
    ultimately have c:"indep_sets 
      (\<lambda>i. { hash_function F i -` A \<inter> space (poly_hash_family F n) | A. A \<in> sets (uniform_count_measure (carrier F))}) J"
      using indep_sets_mono_sets by force
    show "indep_vars (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) J"
      apply (simp add:indep_vars_def2)
      using  b c by presburger
  qed
  thus ?B using k_wise_indep_vars_def by blast
qed

end