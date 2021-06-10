theory UniversalHashFamily
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility" PolyCard
  "HOL-Analysis.Nonnegative_Lebesgue_Integration" "HOL-Probability.Probability_Measure"
  "HOL-Probability.Independent_Family" Field
begin

text \<open>In this section, we introduce the k-universal hash families of Wegman and Carter and
show that the polynomials of degree less than k over a finite field form such a k-universal hash
family. If we view the set of polynomials of degree k as a probability space, then we can construct
random variables H_x being the evaluation of the polynomial at points of the field and show that
these random variables are indeed k-wise independent random variables.\<close>

text \<open>We first introduce k-wise independent random variables using the existing definition of
independent random variables.\<close>

definition (in prob_space) k_wise_indep_vars where
  "k_wise_indep_vars k M' X' I = (\<forall>J \<subseteq> I. card J \<le> k \<longrightarrow> finite J \<longrightarrow> indep_vars M' X' J)" 

text \<open>The space of polynomials of degree less than n (n > 0) forms a probability space.\<close>
definition poly_hash_family where 
  "poly_hash_family F n = uniform_count_measure (bounded_degree_polynomials F n)"

lemma prob_space_poly_family:
  assumes "ring F"
  assumes "n > 0"
  assumes "finite (carrier F)"
  shows "prob_space (poly_hash_family F n)"
proof -
  obtain m where m_def: "n = Suc m" using assms(2) gr0_implies_Suc by blast
  have "finite (bounded_degree_polynomials F n)"
    apply (simp only:m_def) using fin_degree_bounded assms(1) assms(3) by blast
  moreover have "\<zero>\<^bsub>poly_ring F\<^esub> \<in> bounded_degree_polynomials F n"
    using assms(1) assms(2) bounded_degree_polynomials_def 
    by (simp add: bounded_degree_polynomials_def univ_poly_zero univ_poly_zero_closed)
  ultimately show ?thesis using prob_space_uniform_count_measure 
    by (metis empty_iff poly_hash_family_def)
qed

text \<open>A hash function is just polynomial evaluation.\<close>
definition hash_function where "hash_function F x \<omega> = ring.eval F \<omega> x"

text \<open>The main result of this section is that
\begin{itemize}
\item Each hash function has uniform distribution over the finite fields.
\item A subset of k hash functions is independent. 
\end{itemize}
\<close>

lemma
  assumes "field F"
  assumes "n > 0"
  assumes "finite (carrier F)"
  assumes "n \<le> card (carrier F)"
  shows 
    equi_prob:
      "\<And>x y. x \<in> carrier F \<Longrightarrow> y \<in> carrier F \<Longrightarrow> 
        prob_space.prob (poly_hash_family F n) (hash_function F x -` {y} \<inter> space (poly_hash_family F n)) = 1/(real (card (carrier F)))" 
      (is "\<And>x y. _ \<Longrightarrow> _ \<Longrightarrow> ?D x y")
  and
    indep: "prob_space.k_wise_indep_vars (poly_hash_family F n) n (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) (carrier F)" (is ?B)
proof -
  have a:"prob_space (poly_hash_family F n)" sorry
  show "\<And> x y. x \<in> carrier F \<Longrightarrow> y \<in> carrier F \<Longrightarrow> ?D x y" sorry

  have a1:"ring F" using assms(1) by (simp add:domain_def field_def cring_def)

  have "\<And>J. J \<subseteq> carrier F  \<Longrightarrow> card J \<le> n \<Longrightarrow> finite J \<Longrightarrow> 
    prob_space.indep_vars (poly_hash_family F n) (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) J"
  proof -
    fix J
    assume d:"J \<subseteq> carrier F"
    assume "card J \<le> n"
    assume "finite J"
    have b:"\<And>i. i \<in> J \<Longrightarrow> prob_space.random_variable (poly_hash_family F n) (uniform_count_measure (carrier F)) (\<lambda>\<omega>. hash_function F i \<omega>)" 
      apply (simp add:hash_function_def)
      apply (simp add:poly_hash_family_def uniform_count_measure_def point_measure_def Pi_def bounded_degree_polynomials_def)
      by (meson a1 d ring.carrier_is_subring ring.eval_in_carrier ring.polynomial_in_carrier subsetD univ_poly_carrier)

    define M where "M = (\<lambda>k. {k}) ` carrier F \<union> {{}}"
    define S where "S = (\<lambda>i. {hash_function F i -` y \<inter> space (poly_hash_family F n) | y. y \<in> M})" 
      (* maybe we can use singletons and use indep-sets_sigma here *)
    have e:"\<And>i. i \<in> J \<Longrightarrow> hash_function F i \<in> space (poly_hash_family F n) \<rightarrow> space (uniform_count_measure (carrier F))"
      sorry
    have f:"sigma_sets (space (uniform_count_measure (carrier F))) M = sets (uniform_count_measure (carrier F))"
      sorry

    have "prob_space.indep_sets (poly_hash_family F n) S J" sorry
    moreover have "\<And>i. i \<in> J \<Longrightarrow> Int_stable (S i)" sorry
    ultimately have "prob_space.indep_sets (poly_hash_family F n) (\<lambda>i. sigma_sets (space (poly_hash_family F n)) (S i)) J"
      using prob_space.indep_sets_sigma a by auto
    moreover have "\<And>i. i \<in> J \<Longrightarrow> sigma_sets (space (poly_hash_family F n)) (S i) \<supseteq>
      { hash_function F i -` A \<inter> space (poly_hash_family F n) | A. A \<in> sets (uniform_count_measure (carrier F))}"
      apply (simp add:S_def)
      by (simp add:sigma_sets_vimage_commute[where  \<Omega>'="space (uniform_count_measure (carrier F))",symmetric] e f)
    ultimately have c:"prob_space.indep_sets (poly_hash_family F n)
      (\<lambda>i. { hash_function F i -` A \<inter> space (poly_hash_family F n) | A. A \<in> sets (uniform_count_measure (carrier F))}) J"
      using prob_space.indep_sets_mono_sets a by force
    show "prob_space.indep_vars (poly_hash_family F n) (\<lambda>_. uniform_count_measure (carrier F)) (hash_function F) J"
      apply (simp add:a prob_space.indep_vars_def2)
      using  b c by presburger
  qed
  thus ?B using prob_space.k_wise_indep_vars_def a by blast
qed



end