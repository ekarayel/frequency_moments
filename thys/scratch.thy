theory scratch
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility" PolyCard
  "HOL-Analysis.Nonnegative_Lebesgue_Integration" "HOL-Probability.Probability_Measure"
begin

definition hash_family where "hash_family F n = uniform_count_measure (P F n)"

lemma prob_space_hash_family:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "prob_space (hash_family F n)"
  sorry


end