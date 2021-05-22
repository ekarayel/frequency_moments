theory scratch
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility" PolyCard
  "HOL-Analysis.Nonnegative_Lebesgue_Integration" "HOL-Probability.Probability_Measure"
begin

definition hash_family where "hash_family F n = uniform_count_measure (P F n)"

lemma prob_space_hash_family:
  assumes "ring F"
  assumes "n > 0"
  assumes "finite (carrier F)"
  shows "prob_space (hash_family F n)"
proof -
  obtain m where "n = Suc m" using assms(2) gr0_implies_Suc by blast
  have a:"finite (P F n)" apply (simp only:P_def) using fin_degree_bounded P_def assms(1) assms(3) by blast 
  have b:"\<zero>\<^bsub>poly_ring F\<^esub> \<in> P F n" using assms(1) assms(2) P_def 
    by (simp add: P_def univ_poly_zero univ_poly_zero_closed)
  show ?thesis using a b prob_space_uniform_count_measure 
    by (metis empty_iff hash_family_def)
qed


end