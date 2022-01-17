section \<open>Universal Hash Families\<close>

theory Universal_Hash_Families
  imports Main Interpolation_Polynomial_Counts Product_PMF_Ext
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

definition hash :: "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a" 
  where "hash F x \<omega> = ring.eval F \<omega> x"

lemma hash_range:
  assumes "ring F"
  assumes "\<omega> \<in> bounded_degree_polynomials F n"
  assumes "x \<in> carrier F"
  shows "hash F x \<omega> \<in> carrier F"
  using assms 
  apply (simp add:hash_def bounded_degree_polynomials_def)
  by (metis ring.eval_in_carrier ring.polynomial_incl univ_poly_carrier)

lemma hash_range_2:
  assumes "ring F"
  assumes "\<omega> \<in> bounded_degree_polynomials F n"
  shows "(\<lambda>x. hash F x \<omega>) ` carrier F \<subseteq> carrier F"
  apply (rule image_subsetI)
  by (metis hash_range assms)

lemma poly_cards:
  assumes "field F \<and> finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> (carrier F)"
  shows "card {\<omega> \<in> bounded_degree_polynomials F n. (\<forall>k \<in> K. ring.eval F \<omega> k = y k)} = 
         card (carrier F)^(n-card K)"
  using interpolating_polynomials_count[where n="n-card K" and f="y" and F="F" and K="K"]  assms 
  by fastforce

lemma poly_cards_single:
  assumes "field F \<and> finite (carrier F)"
  assumes "k \<in> carrier F"
  assumes "1 \<le> n"
  assumes "y \<in> carrier F"
  shows "card {\<omega> \<in> bounded_degree_polynomials F n. ring.eval F \<omega> k = y} = 
         card (carrier F)^(n-1)"
  using poly_cards[OF assms(1), where K="{k}" and y="\<lambda>_. y", simplified] assms(3) assms(4)[simplified]
  by (simp add:assms)

lemma expand_subset_filter: "{x \<in> A. P x} = A \<inter> {x. P x}"
  by force

lemma hash_prob:
  assumes "field F \<and> finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> carrier F"
  shows "\<P>(\<omega> in pmf_of_set (bounded_degree_polynomials F n). (\<forall>x \<in> K. hash F x \<omega> = y x)) = 1/(real (card (carrier F)))^card K" 
proof -
  have "\<zero>\<^bsub>F\<^esub> \<in> carrier F"
    using assms(1) field.is_ring ring.ring_simprules(2) by blast

  hence a:"card (carrier F) > 0"
    apply (subst card_gt_0_iff) 
    using assms(1) by blast

  show ?thesis
    apply (subst measure_pmf_of_set)
      apply (metis non_empty_bounded_degree_polynomials field.is_ring  assms(1))
     apply (metis fin_degree_bounded field.is_ring assms(1))
    apply (simp add:hash_def expand_subset_filter[symmetric])
    apply (subst poly_cards[OF assms(1) assms(2) assms(3) assms(4)])
    apply (subst bounded_degree_polynomials_count, metis field.is_ring assms(1), metis assms(1))
    apply (subst frac_eq_eq)
    apply (simp add:a, simp add:a, simp)
    by (metis assms(3) le_add_diff_inverse2 power_add)
qed

lemma hash_prob_single:
  assumes "field F \<and> finite (carrier F)"
  assumes "x \<in> carrier F"
  assumes "1 \<le> n"
  assumes "y \<in> carrier F"
  shows "\<P>(\<omega> in pmf_of_set (bounded_degree_polynomials F n). hash F x \<omega> = y) = 1/(real (card (carrier F)))" 
  using hash_prob[OF assms(1), where K="{x}" and y="\<lambda>_. y", simplified] assms 
  by (metis (no_types, lifting) Collect_cong One_nat_def UNIV_I space_measure_pmf)

lemma hash_indep_pmf:
  assumes "field F \<and> finite (carrier F)"
  assumes "J\<subseteq>carrier F"
  assumes "finite J" 
  assumes "card J \<le> n"
  assumes "1 \<le> n"
  shows "prob_space.indep_vars (pmf_of_set (bounded_degree_polynomials F n)) 
    (\<lambda>_. pmf_of_set (carrier F)) (hash F) J"
proof -
  have "\<zero>\<^bsub>poly_ring F\<^esub> \<in> bounded_degree_polynomials F n"
    apply (simp add:bounded_degree_polynomials_def)
    apply (rule conjI)
     apply (simp add: univ_poly_zero univ_poly_zero_closed)
    using univ_poly_zero by blast
  hence b: "bounded_degree_polynomials F n \<noteq> {}"
    by blast
  have c: "finite (bounded_degree_polynomials F n)"
    by (metis finite_poly_count assms(1))
  have d: "\<And> A P. A \<inter> {\<omega>. P \<omega>} = {\<omega> \<in> A. P \<omega>}"
    by blast

  have fin_carr: "finite (carrier F)" using assms(1) by blast
  have e:"ring F" using assms(1) field.is_ring by blast
  have f: "0 < card (carrier F)" 
    by (metis assms(1) card_0_eq e empty_iff gr0I ring.ring_simprules(2))

  define \<Omega> where "\<Omega> = (pmf_of_set (bounded_degree_polynomials F n))"
  have a:"\<And>a J'.
       J' \<subseteq> J \<Longrightarrow>
       finite J' \<Longrightarrow>
       measure \<Omega> {\<omega>. \<forall>x\<in>J'. hash F x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure \<Omega> {\<omega>. hash F x \<omega> = a x})"
  proof -
    fix a
    fix J'
    assume a_1: "J' \<subseteq> J"
    assume a_11: "finite J'"
    have a_2: "card J' \<le> n" by (metis card_mono order_trans a_1 assms(3) assms(4))
    have a_3: "J' \<subseteq> carrier F" by (metis order_trans a_1 assms(2))
    have a_4: "1 \<le>n " using assms by blast

    show "measure_pmf.prob \<Omega> {\<omega>. \<forall>x\<in>J'. hash F x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure_pmf.prob \<Omega> {\<omega>. hash F x \<omega> = a x})"
    proof (cases "a ` J' \<subseteq> carrier F")
      case True
      have a_5: "\<And>x. x \<in> J' \<Longrightarrow> x \<in> carrier F"  using a_1 assms(2) order_trans by force
      have a_6: "\<And>x. x \<in> J' \<Longrightarrow> a x \<in> carrier F"  using True by force
      show ?thesis 
       apply (simp add:\<Omega>_def measure_pmf_of_set[OF b c] d hash_def)
       apply (subst poly_cards[OF assms(1) a_3 a_2], metis True)
        apply (simp add:bounded_degree_polynomials_count[OF e fin_carr] poly_cards_single[OF assms(1) a_5 a_4 a_6] power_divide)
        apply (subst frac_eq_eq, simp add:f, simp add:f) 
          apply (simp add:power_add[symmetric] power_mult[symmetric])
          apply (rule arg_cong2[where f="\<lambda>x y. x ^ y"], simp)
        using a_2 a_4 mult_eq_if by force
    next
      case False
      then obtain j where a_8: "j \<in> J'" and a_9: "a j \<notin> carrier F" by blast
      have a_7: "\<And>x \<omega>. \<omega> \<in> bounded_degree_polynomials F n \<Longrightarrow> x \<in> carrier F \<Longrightarrow> hash F x \<omega> \<in> carrier F"
        apply (simp add:bounded_degree_polynomials_def hash_def)
        by (metis e ring.eval_in_carrier  ring.polynomial_incl univ_poly_carrier)
      have a_10: "{\<omega> \<in> bounded_degree_polynomials F n. \<forall>x\<in>J'. hash F x \<omega> = a x} = {}"
        apply (rule order_antisym)
        apply (rule subsetI, simp, metis a_7 a_8 a_9  a_3 in_mono)
        by (rule subsetI, simp) 
      have a_12: "{\<omega> \<in> bounded_degree_polynomials F n. hash F j \<omega> = a j} = {}"
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

text \<open>We introduce k-wise independent random variables using the existing definition of
independent random variables.\<close>

definition (in prob_space) k_wise_indep_vars :: 
  "nat \<Rightarrow> ('b \<Rightarrow> 'c measure) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "k_wise_indep_vars k M' X' I = (\<forall>J \<subseteq> I. card J \<le> k \<longrightarrow> finite J \<longrightarrow> indep_vars M' X' J)" 

lemma hash_k_wise_indep:
  assumes "field F \<and> finite (carrier F)"
  assumes "1 \<le> n"
  shows "prob_space.k_wise_indep_vars (pmf_of_set (bounded_degree_polynomials F n)) n
    (\<lambda>_. pmf_of_set (carrier F)) (hash F) (carrier F)"
  apply (simp add:measure_pmf.k_wise_indep_vars_def)
  using hash_indep_pmf[OF assms(1) _ _ _ assms(2)] by blast

lemma hash_inj_if_degree_1:
  assumes "field F \<and> finite (carrier F)"
  assumes "\<omega> \<in> bounded_degree_polynomials F n"
  assumes "degree \<omega> = 1"
  shows "inj_on (\<lambda>x. hash F x \<omega>) (carrier F)"
proof (rule inj_onI)
  fix x y
  assume a1: "x \<in> carrier F"
  assume a2: "y \<in> carrier F"
  assume a3: "hash F x \<omega> = hash F y \<omega>"

  interpret field F
    by (metis assms(1))

  obtain u v where \<omega>_def: "\<omega> = [u,v]" using assms(3)
    apply (cases \<omega>, simp)
    by (cases "(tl \<omega>)", simp, simp)

  have u_carr: "u \<in> carrier F - {\<zero>\<^bsub>F\<^esub>}"
    using \<omega>_def assms apply (simp add:bounded_degree_polynomials_def)
    by (metis field.is_ring list.sel(1) ring.degree_oneE assms(1) assms(3))

  have v_carr: "v \<in> carrier F" 
    using \<omega>_def assms(2) apply (simp add:bounded_degree_polynomials_def)
    by (metis assms(1) assms(3) field.is_ring list.inject ring.degree_oneE)

  have "u \<otimes>\<^bsub>F\<^esub> x \<oplus>\<^bsub>F\<^esub> v = u \<otimes>\<^bsub>F\<^esub> y  \<oplus>\<^bsub>F\<^esub> v"
    using a1 a2 a3 u_carr v_carr by (simp add:hash_def \<omega>_def)

  thus "x = y"
    using u_carr a1 a2 v_carr
    by (simp add: local.field_Units)
qed

lemma (in prob_space) k_wise_subset:
  assumes "k_wise_indep_vars k M' X' I"
  assumes "J \<subseteq> I"
  shows "k_wise_indep_vars k M' X' J"
  using assms by (simp add:k_wise_indep_vars_def)

end
