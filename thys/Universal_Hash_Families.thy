section \<open>Universal Hash Families\<close>

theory Universal_Hash_Families
  imports Main Product_PMF_Ext 
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities Encoding Field
begin

text \<open>A k-universal hash family $\mathcal H$ is probability space, whose elements are hash functions 
with domain $U$ and range ${i. i < m}$ such that:

\begin{itemize}
\item For every fixed $x \in U$ and value $y < m$ exactly $\frac{1}{m}$ of the hash functions map
  $x$ to $y$: $P_{h \in \mathcal H} \left(h(x) = y\right) = \frac{1}{m}$.
\item For at most $k$ universe elements: $x_1,\cdots,x_m$ the functions $h(x_1), \cdots, h(x_m)$ 
  are independent random variables.
\end{itemize}

In this section, we construct $k$-universal hash families following the approach outlined
by Wegman and Carter using the polynomials of degree less than $k$ over a finite field.\<close>

text \<open>A hash function is just polynomial evaluation.\<close>

definition (in prob_space) k_wise_indep_vars :: 
  "nat \<Rightarrow> ('b \<Rightarrow> 'c measure) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "k_wise_indep_vars k M' X' I = (\<forall>J \<subseteq> I. card J \<le> k \<longrightarrow> finite J \<longrightarrow> indep_vars M' X' J)" 

lemma (in prob_space) k_wise_subset:
  assumes "k_wise_indep_vars k M' X' I"
  assumes "J \<subseteq> I"
  shows "k_wise_indep_vars k M' X' J"
  using assms by (simp add:k_wise_indep_vars_def)

definition hash where "hash R x \<omega> = ring.eval R \<omega> x"

lemma (in ring) hash_range:
  assumes "\<omega> \<in> bounded_degree_polynomials R n"
  assumes "x \<in> carrier R"
  shows "hash R x \<omega> \<in> carrier R"
  using assms 
  apply (simp add:hash_def bounded_degree_polynomials_def)
  by (metis eval_in_carrier polynomial_incl univ_poly_carrier)

lemma (in ring) hash_range_2:
  assumes "\<omega> \<in> bounded_degree_polynomials R n"
  shows "(\<lambda>x. hash R x \<omega>) ` carrier R \<subseteq> carrier R"
  apply (rule image_subsetI)
  by (metis hash_range assms)

lemma (in field) poly_cards:
  assumes "finite (carrier R)"
  assumes "K \<subseteq> carrier R"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> (carrier R)"
  shows "card {\<omega> \<in> bounded_degree_polynomials R n. (\<forall>k \<in> K. eval \<omega> k = y k)} = 
         card (carrier R)^(n-card K)"
  using interpolating_polynomials_card[where n="n-card K" and f="y" and K="K"] assms finite_subset
  by fastforce

lemma (in field) poly_cards_single:
  assumes "finite (carrier R)"
  assumes "k \<in> carrier R"
  assumes "1 \<le> n"
  assumes "y \<in> carrier R"
  shows "card {\<omega> \<in> bounded_degree_polynomials R n. eval \<omega> k = y} = 
         card (carrier R)^(n-1)"
  using poly_cards[OF assms(1), where K="{k}" and y="\<lambda>_. y", simplified] assms(3) assms(4)[simplified]
  by (simp add:assms)

lemma expand_subset_filter: "{x \<in> A. P x} = A \<inter> {x. P x}"
  by force

context finite_field
begin
lemma hash_prob:
  assumes "K \<subseteq> carrier R"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> carrier R"
  shows "\<P>(\<omega> in pmf_of_set (bounded_degree_polynomials R n). (\<forall>x \<in> K. hash R x \<omega> = y x)) = 1/(real (card (carrier R)))^card K" 
proof -

  have "\<zero> \<in> carrier R"
    using assms(1) field.is_ring ring.ring_simprules(2) by blast
  hence a:"card (carrier R) > 0"
    apply (subst card_gt_0_iff) 
    using finite_carrier by blast

  show ?thesis
    apply (subst measure_pmf_of_set)
      apply (metis non_empty_bounded_degree_polynomials)
     apply (metis fin_degree_bounded finite_carrier)
    apply (simp add:hash_def expand_subset_filter[symmetric])
    apply (subst poly_cards[OF finite_carrier assms(1) assms(2) assms(3)])
    apply (subst bounded_degree_polynomials_card)
    apply (subst frac_eq_eq)
    apply (simp add:a, simp add:a, simp)
    by (metis assms(2) le_add_diff_inverse2 power_add)
qed

lemma hash_prob_single:
  assumes "x \<in> carrier R"
  assumes "1 \<le> n"
  assumes "y \<in> carrier R"
  shows "\<P>(\<omega> in pmf_of_set (bounded_degree_polynomials R n). hash R x \<omega> = y) = 1/(real (card (carrier R)))" 
  using hash_prob[where K="{x}"] assms finite_carrier by simp

lemma hash_prob_range:
  assumes "x \<in> carrier R"
  assumes "1 \<le> n"
  shows "\<P>(\<omega> in measure_pmf (pmf_of_set (bounded_degree_polynomials R n)).
    hash R x \<omega> \<in> A) = card (A \<inter> carrier R) / (card (carrier R))"
proof -
  define \<Omega> where "\<Omega> = measure_pmf (pmf_of_set (bounded_degree_polynomials R n))"

  have "\<P>(\<omega> in \<Omega>. hash R x \<omega> \<in> A) = measure \<Omega> (\<Union> k \<in> A \<inter> carrier R. {\<omega>. hash R x \<omega> = k})"
    apply (simp only:\<Omega>_def)
    apply (rule pmf_eq, simp)
    apply (subst (asm) set_pmf_of_set[OF non_empty_bounded_degree_polynomials fin_degree_bounded])
    using finite_carrier assms apply blast
    using hash_range assms(1) by simp
  also have "... = (\<Sum> k \<in> (A \<inter> carrier R). measure \<Omega> {\<omega>. hash R x \<omega> = k})"
    apply (rule measure_finite_Union)
    using finite_carrier apply blast
    apply (simp add:\<Omega>_def)
     apply (simp add:disjoint_family_on_def, fastforce) 
    by (simp add:\<Omega>_def)
  also have "... = (\<Sum> k \<in> (A \<inter> carrier R). \<P>(\<omega> in \<Omega>. \<forall>x' \<in> {x}. hash R x' \<omega> = k ))"
    by (simp add:\<Omega>_def)
  also have "... = (\<Sum> k \<in> (A \<inter> carrier R). 1/ real (card (carrier R)) ^ card {x})"
    apply (rule sum.cong, simp)
    apply (simp only:\<Omega>_def)
    apply (rule hash_prob, simp add:assms, simp)
    using assms(2) apply simp by blast
  also have "... = real (card (A \<inter> carrier R)) / real (card (carrier R))"
    by simp
  finally show ?thesis
    by (simp only:\<Omega>_def)
qed

lemma hash_indep_pmf:
  assumes "J\<subseteq>carrier R"
  assumes "finite J" 
  assumes "card J \<le> n"
  assumes "1 \<le> n"
  shows "prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials R n)) 
    (\<lambda>_. pmf_of_set (carrier R)) (hash R) J"
proof -

  have b: "bounded_degree_polynomials R n \<noteq> {}"
    using non_empty_bounded_degree_polynomials by simp
  have c: "finite (bounded_degree_polynomials R n)"
    by (rule fin_degree_bounded, rule finite_carrier) 
  have d: "\<And> A P. A \<inter> {\<omega>. P \<omega>} = {\<omega> \<in> A. P \<omega>}"
    by blast

  have "\<zero> \<in> carrier R"
    using assms(1) field.is_ring ring.ring_simprules(2) by blast
  hence f:"card (carrier R) > 0"
    apply (subst card_gt_0_iff) 
    using finite_carrier by blast

  define \<Omega> where "\<Omega> = (pmf_of_set (bounded_degree_polynomials R n))"
  have a:"\<And>a J'.
       J' \<subseteq> J \<Longrightarrow>
       finite J' \<Longrightarrow>
       measure \<Omega> {\<omega>. \<forall>x\<in>J'. hash R x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure \<Omega> {\<omega>. hash R x \<omega> = a x})"
  proof -
    fix a
    fix J'
    assume a_1: "J' \<subseteq> J"
    assume a_11: "finite J'"
    have a_2: "card J' \<le> n" by (metis card_mono order_trans a_1 assms(2) assms(3))
    have a_3: "J' \<subseteq> carrier R" by (metis order_trans a_1 assms(1))
    have a_4: "1 \<le>n " using assms by blast

    show "measure_pmf.prob \<Omega> {\<omega>. \<forall>x\<in>J'. hash R x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure_pmf.prob \<Omega> {\<omega>. hash R x \<omega> = a x})"
    proof (cases "a ` J' \<subseteq> carrier R")
      case True
      have a_5: "\<And>x. x \<in> J' \<Longrightarrow> x \<in> carrier R"  using a_1 assms(1) order_trans by force
      have a_6: "\<And>x. x \<in> J' \<Longrightarrow> a x \<in> carrier R"  using True by force
      show ?thesis 
       apply (simp add:\<Omega>_def measure_pmf_of_set[OF b c] d hash_def)
        apply (subst poly_cards[OF finite_carrier a_3 a_2], metis True)
        apply (simp add:bounded_degree_polynomials_card poly_cards_single[OF finite_carrier a_5 a_4 a_6] power_divide)
        apply (subst frac_eq_eq, simp add:f, simp add:f) 
          apply (simp add:power_add[symmetric] power_mult[symmetric])
          apply (rule arg_cong2[where f="\<lambda>x y. x ^ y"], simp)
        using a_2 a_4 mult_eq_if by force
    next
      case False
      then obtain j where a_8: "j \<in> J'" and a_9: "a j \<notin> carrier R" by blast
      have a_10: "{\<omega> \<in> bounded_degree_polynomials R n. \<forall>x\<in>J'. hash R x \<omega> = a x} = {}"
        apply (rule order_antisym)
        apply (rule subsetI, simp, metis hash_range a_8 a_9  a_3 in_mono)
        by (rule subsetI, simp) 
      have a_12: "{\<omega> \<in> bounded_degree_polynomials R n. hash R j \<omega> = a j} = {}"
        apply (rule order_antisym)
        apply (rule subsetI, simp, metis hash_range a_8 a_9  a_3 in_mono)
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

text \<open>We introduce k-wise independent random variables using the existing definition of
independent random variables.\<close>


lemma hash_k_wise_indep:
  assumes "1 \<le> n"
  shows "prob_space.k_wise_indep_vars (pmf_of_set (bounded_degree_polynomials R n)) n
    (\<lambda>_. pmf_of_set (carrier R)) (hash R) (carrier R)"
  apply (simp add:measure_pmf.k_wise_indep_vars_def)
  using hash_indep_pmf[OF _ _ _ assms(1)] by blast

lemma hash_inj_if_degree_1:
  assumes "\<omega> \<in> bounded_degree_polynomials R n"
  assumes "degree \<omega> = 1"
  shows "inj_on (\<lambda>x. hash R x \<omega>) (carrier R)"
  using assms eval_inj_if_degree_1
  by (simp add:bounded_degree_polynomials_def hash_def)
end

end
