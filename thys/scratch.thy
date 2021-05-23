theory scratch
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility" PolyCard
  "HOL-Analysis.Nonnegative_Lebesgue_Integration" "HOL-Probability.Probability_Measure"
  "HOL-Probability.Independent_Family"
begin

text \<open>In this section, we define the strongly k-universal hash families of Wegman and Carter and
proof their result, that the polynomials of degree less than k form a strong k-universal hash
family. If we view the set of polynomials as a probability space, then we can construct random
variables H_x being the evaluation of the polynomial at point x and show that these random variables
are k-wise independent random variables.\<close>

(*
  Plan: Define strongly universal k-hash families.
  Show: Implies evaluations a k-wise independent random variables.
  Show: For each prime p and k \<ge> 1 there exists strongly universal k-hash families on the universe
        {0,..,p-1}.
*)

(*
  A random variable is a function from the probability space to a measure space


*)

definition strong_universal_hash_family :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> nat) set \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "strong_universal_hash_family m k H \<Omega> \<longleftrightarrow> 
    (\<forall>h. \<forall>y. h ` {i. i < k} \<subseteq> H \<and> inj_on h {i. i < k} \<and> y ` {i. i < k} \<subseteq> {i. i < m} \<longrightarrow>
    prob_space.prob \<Omega> (\<Inter>i < k. h i -` {y i}) = (1/(m^k)) )"

(* The space of polynomials of degree less than n (n > 0) forms a probability space *)
definition poly_family where "poly_family F n = uniform_count_measure (P F n)"

(* Carrier of a finite field as a measurable space *)
definition field_space where "field_space F = uniform_count_measure (carrier F)" 

lemma prob_space_poly_family:
  assumes "ring F"
  assumes "n > 0"
  assumes "finite (carrier F)"
  shows "prob_space (poly_family F n)"
proof -
  obtain m where "n = Suc m" using assms(2) gr0_implies_Suc by blast
  have a:"finite (P F n)" apply (simp only:P_def) using fin_degree_bounded P_def assms(1) assms(3) by blast 
  have b:"\<zero>\<^bsub>poly_ring F\<^esub> \<in> P F n" using assms(1) assms(2) P_def 
    by (simp add: P_def univ_poly_zero univ_poly_zero_closed)
  show ?thesis using a b prob_space_uniform_count_measure 
    by (metis empty_iff poly_family_def)
qed

definition "hash_function_on_field"
  where
    "hash_function_on_field F x \<omega> = ring.eval F \<omega> x"
  
lemma hash_fun_is_random_var:
  assumes "ring F"
  assumes "n > 0"
  assumes "finite (carrier F)"
  assumes "x \<in> (carrier F)"
  shows "prob_space.random_variable (poly_family F n) (field_space F) (hash_function_on_field F x)"
  sorry

definition (in prob_space) k_wise_independent_family:
  "k_wise_independent_family k M' X' I \<longleftrightarrow> (\<forall>J \<subseteq> I. card J \<le> k \<longrightarrow> finite J \<longrightarrow> indep_vars M' X' J)" 


(* TODO Make this a corollary, since constant functions are independent families as well. *)
lemma hash_functions_are_k_wise_independent:
  assumes "field F"
  assumes "n > 0"
  assumes "finite (carrier F)"
  shows "k_wise_independent_family (Suc n) (\<lambda>x. field_space F) (\<lambda>x. hash_function_on_field F x) (carrier F)"
  sorry



end