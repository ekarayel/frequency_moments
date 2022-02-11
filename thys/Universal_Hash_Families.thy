section \<open>Universal Hash Families\<close>

theory Universal_Hash_Families
  imports 
    "HOL-Probability.Product_PMF"
    "HOL-Probability.Stream_Space"
    Field
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities
    Universal_Hash_Families_PMF
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

lemma (in prob_space) k_wise_indep_vars_subset:
  assumes "k_wise_indep_vars k M' X' I"
  assumes "J \<subseteq> I"
  assumes "finite J"
  assumes "card J \<le> k"
  shows "indep_vars M' X' J"
  using assms
  by (simp add:k_wise_indep_vars_def) 

lemma (in prob_space) indep_vars_empty: "indep_vars M' X' {}"
  by (simp add:indep_vars_def indep_sets_def)

locale poly_hash_family = ring +
  fixes n :: nat
  assumes finite_carrier[simp]: "finite (carrier R)"
  assumes n_ge_0: "n > 0"
begin

definition space where "space = bounded_degree_polynomials R n"
definition hash where "hash x \<omega> = eval \<omega> x"
definition M where "M = measure_pmf (pmf_of_set space)"

lemma finite_space[simp]:"finite space"
    unfolding space_def using fin_degree_bounded finite_carrier by simp

lemma non_empty_bounded_degree_polynomials[simp]:"space \<noteq> {}"
    unfolding space_def using non_empty_bounded_degree_polynomials by simp

lemma non_empty_carrier[simp]: "carrier R \<noteq> {}"
  by (simp add:carrier_not_empty)

sublocale prob_space "M"
  by (simp add:M_def prob_space_measure_pmf)

lemma hash_range[simp]:
  assumes "\<omega> \<in> space"
  assumes "x \<in> carrier R"
  shows "hash x \<omega> \<in> carrier R"
  using assms unfolding hash_def space_def bounded_degree_polynomials_def 
  by (simp, metis eval_in_carrier polynomial_incl univ_poly_carrier)

lemma  hash_range_2:
  assumes "\<omega> \<in> space"
  shows "(\<lambda>x. hash x \<omega>) ` carrier R \<subseteq> carrier R"
  unfolding space_def
  by (metis image_subsetI hash_range assms)

lemma integrable_M[simp]:
  fixes f :: "'a list \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable M f"
    unfolding M_def
    by (rule integrable_measure_pmf_finite, simp)

end

locale carter_wegman_hash_family = poly_hash_family +
  assumes field_R: "field R"
begin
sublocale field
  using field_R by simp

lemma poly_cards:
  assumes "K \<subseteq> carrier R"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> (carrier R)"
  shows "card {\<omega> \<in> space. (\<forall>k \<in> K. eval \<omega> k = y k)} = 
         card (carrier R)^(n-card K)"
  unfolding space_def
  using interpolating_polynomials_card[where n="n-card K" and f="y" and K="K"] assms
    finite_carrier finite_subset
  by fastforce

lemma poly_cards_single:
  assumes "k \<in> carrier R"
  assumes "n > 0"
  assumes "y \<in> carrier R"
  shows "card {\<omega> \<in> space. eval \<omega> k = y} = 
         card (carrier R)^(n-1)"
  using poly_cards[where K="{k}" and y="\<lambda>_. y", simplified] assms by simp

lemma hash_prob:
  assumes "K \<subseteq> carrier R"
  assumes "card K \<le> n"
  assumes "y ` K \<subseteq> carrier R"
  shows "prob {\<omega>. (\<forall>x \<in> K. hash x \<omega> = y x)} = 1/(real (card (carrier R)))^card K" 
proof -
  have "\<zero> \<in> carrier R" by simp

  hence a:"card (carrier R) > 0"
    using finite_carrier card_gt_0_iff by blast

  have b:"real (card {\<omega> \<in> space. \<forall>x\<in>K. eval \<omega> x = y x}) / real (card space) = 
    1 / real (card (carrier R)) ^ card K"
    using a assms(2)
    apply (simp add: frac_eq_eq poly_cards[OF assms(1,2,3)] power_add[symmetric])
    by (simp add:space_def bounded_degree_polynomials_card)

  show ?thesis
    unfolding M_def
    by (simp add:hash_def measure_pmf_of_set inters_eq_set_filter b)
qed

lemma hash_prob_single:
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  shows "prob {\<omega>. hash x \<omega> = y} = 1/(real (card (carrier R)))" 
  using hash_prob[where K="{x}"] assms finite_carrier n_ge_0 by simp

lemma hash_prob_range:
  assumes "x \<in> carrier R"
  shows "prob {\<omega>. hash x \<omega> \<in> A} = card (A \<inter> carrier R) / (card (carrier R))"
proof -
  have "prob {\<omega>. hash x \<omega> \<in> A} = prob (\<Union>a \<in> A \<inter> carrier R. {\<omega>. hash x \<omega> = a})"
    using hash_range assms by (auto intro:measure_pmf_eq simp:M_def)
  also have "... = (\<Sum> a \<in> (A \<inter> carrier R). prob {\<omega>. hash x \<omega> = a})"
    by (rule measure_finite_Union, auto simp:M_def disjoint_family_on_def)
  also have "... = (\<Sum> a \<in> (A \<inter> carrier R). 1/(real (card (carrier R))))"
    by (rule sum.cong, auto simp:hash_prob_single[OF assms])
  also have "... = card (A \<inter> carrier R) / (card (carrier R))"
    by simp
  finally show ?thesis by simp
qed

lemma hash_indep_pmf:
  assumes "J\<subseteq>carrier R"
  assumes "finite J" 
  assumes "card J \<le> n"
  shows "indep_vars (\<lambda>_. pmf_of_set (carrier R)) hash J"
proof (cases "n > 0")
  case True
  hence n_ge_0: "n > 0" by blast

  have "\<zero> \<in> carrier R" by simp
  hence card_R_ge_0:"card (carrier R) > 0"
    using card_gt_0_iff finite_carrier by blast

  show ?thesis
    unfolding M_def
  proof (rule indep_vars_pmf[simplified])
    fix a
    fix J'
    assume a: "J' \<subseteq> J" "finite J'"
    have card_J': "card J' \<le> n" by (metis card_mono order_trans a(1) assms(2,3))
    have J'_in_carr: "J' \<subseteq> carrier R" by (metis order_trans a(1) assms(1))

    show "measure_pmf.prob (pmf_of_set space) {\<omega>. \<forall>x\<in>J'. hash x \<omega> = a x} =
       (\<Prod>x\<in>J'. measure_pmf.prob (pmf_of_set space)  {\<omega>. hash x \<omega> = a x})"
    proof (cases "a ` J' \<subseteq> carrier R")
      case True
      have a_carr: "\<And>x. x \<in> J' \<Longrightarrow> a x \<in> carrier R"  using True by force
      have "measure_pmf.prob (pmf_of_set space) {\<omega>. \<forall>x\<in>J'. hash x \<omega> = a x} = 
        real (card {\<omega> \<in> space. \<forall>x\<in>J'. eval \<omega> x = a x}) / real (card space)"
        by (simp add:measure_pmf_of_set inters_eq_set_filter hash_def)
      also have "... = real (card (carrier R) ^ (n - card J')) / real (card space)"
        using True by (simp add: poly_cards[OF J'_in_carr card_J'])
      also have "... = real (card (carrier R)) ^ (n - card J') / real (card (carrier R)) ^ n"
        by (simp add:space_def bounded_degree_polynomials_card)
      also have "... = (real (card (carrier R)) ^ (n - Suc 0)) ^ card J' / (real (card (carrier R)) ^ n) ^ card J'"
        apply (simp add:power_add[symmetric] power_mult[symmetric] diff_mult_distrib frac_eq_eq)
        by (metis (no_types, lifting) Nat.add_diff_assoc card_J' add.commute le_square le_trans mult_le_mono1)
      also have "... =  (\<Prod>x\<in>J'. real (card {\<omega> \<in> space. eval \<omega> x = a x}) / real (card space))"
        using n_ge_0 a_carr poly_cards_single[OF subsetD[OF J'_in_carr]]
        by (simp add:space_def bounded_degree_polynomials_card power_divide)
      also have "... = (\<Prod>x\<in>J'. measure_pmf.prob (pmf_of_set space) {\<omega>. hash x \<omega> = a x})"
        by (simp add:measure_pmf_of_set inters_eq_set_filter hash_def)
      finally show ?thesis by simp
    next
      case False
      then obtain j where j_def: "j \<in> J'" "a j \<notin> carrier R" by blast
      have "{\<omega> \<in> space. hash j \<omega> = a j} \<subseteq> {\<omega> \<in> space. hash j \<omega> \<notin> carrier R}"
        by (rule subsetI, simp add:j_def)
      also have "... \<subseteq> {}" using j_def(1) J'_in_carr hash_range by blast
      finally have b:"{\<omega> \<in> space. hash j \<omega> = a j} = {}" by simp
      hence "real (card ({\<omega> \<in> space. hash j \<omega> = a j})) = 0" by simp
      hence "(\<Prod>x\<in>J'. real (card {\<omega> \<in> space. hash x \<omega> = a x})) = 0"
        using a(2) prod_zero[OF a(2)] j_def(1) by auto
      moreover have "{\<omega> \<in> space. \<forall>x\<in>J'. hash x \<omega> = a x} \<subseteq> {\<omega> \<in> space. hash j \<omega> = a j}"  
        using j_def by blast
      hence "{\<omega> \<in> space. \<forall>x\<in>J'. hash x \<omega> = a x} = {}" using b by blast
      ultimately show ?thesis 
        by (simp add:measure_pmf_of_set inters_eq_set_filter prod_dividef)
    qed
  qed
next
  case False
  hence "n = 0" by simp
  hence "J = {}" using assms by fastforce  
  then show ?thesis unfolding M_def using measure_pmf.indep_vars_empty by simp
qed

lemma hash_k_wise_indep:
  "k_wise_indep_vars  n
    (\<lambda>_. pmf_of_set (carrier R)) hash (carrier R)"
  using hash_indep_pmf by (simp add:k_wise_indep_vars_def)

lemma hash_inj_if_degree_1:
  assumes "\<omega> \<in> space"
  assumes "degree \<omega> = 1"
  shows "inj_on (\<lambda>x. hash x \<omega>) (carrier R)"
  using assms eval_inj_if_degree_1
  by (simp add:M_def space_def bounded_degree_polynomials_def hash_def)
end

lemma poly_hash_familyI:
  assumes "ring R"
  assumes "finite (carrier R)"
  assumes "0 < n"
  shows "poly_hash_family R n"
  using assms
  by (simp add:poly_hash_family_def poly_hash_family_axioms_def)

lemma carter_wegman_hash_familyI:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "0 < n"
  shows "carter_wegman_hash_family F n"
  using assms field.is_ring poly_hash_familyI[OF field.is_ring[OF assms(1)] assms(2) assms(3)]
  by (simp add:carter_wegman_hash_family_def carter_wegman_hash_family_axioms_def)

end
