theory PolyCard
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility"
begin

(* Set of polynomials with a maximal degree *)

definition bounded_len_polynomials
  where "bounded_len_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> length x \<le> n}"

lemma fin_degree_bounded:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "finite (bounded_len_polynomials F n)"
proof -
  have b: "bounded_len_polynomials F n = {p. polynomial \<^bsub>F\<^esub> (carrier F) p \<and> (length p \<le> n)}"
    apply(rule order_antisym, rule subsetI)
    using assms(1) by (simp add: bounded_len_polynomials_def univ_poly_carrier)+
  have c: "bounded_len_polynomials F n \<subseteq> {[]} \<union> {p. set p \<subseteq> carrier F \<and> length p -1 < n}"
    apply (simp add: b polynomial_def subset_eq) 
    by (metis Suc_pred leD length_greater_0_conv not_less_eq)
  have d: "bounded_len_polynomials F n \<subseteq> {[]} \<union> {p. set p \<subseteq> carrier F \<and> length p \<le> n}"
    using c  Suc_diff_Suc by auto
  thus "finite (bounded_len_polynomials F n)" apply (rule finite_subset)
    apply (rule finite_UnI)
    using assms(2) finite_lists_length_le by auto
qed

lemma fin_fixed_degree:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "finite {p. p \<in> carrier (poly_ring F) \<and> length p = n}"
proof -
  have "{p. p \<in> carrier (poly_ring F) \<and> length p = n} \<subseteq> bounded_len_polynomials F n"
    by (rule subsetI, simp add:bounded_len_polynomials_def) 
  then show ?thesis
  using fin_degree_bounded assms rev_finite_subset by blast
qed

lemma zero_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card {p. p \<in> carrier (poly_ring F) \<and> length p = 0} = 1"
proof -
  have "{p. p \<in> carrier (poly_ring F) \<and> length p = 0} = {[]}"
    apply (rule order_antisym, rule subsetI, simp, simp) 
    by (meson univ_poly_zero_closed)
  thus ?thesis by simp
qed

lemma fixed_degree_polynomials_count_gr_0:
  assumes "ring F"
  assumes "n \<ge> 1"
  assumes "finite (carrier F)"
  shows "card ({p. p \<in> carrier (poly_ring F) \<and> length p = n}) = (card (carrier F) - 1) * (card (carrier F) ^ (n-1))"
proof -
  define A where "A = {p. p \<in> (carrier (poly_ring F)) \<and> length p = n}"
  have b:"A = {p. polynomial\<^bsub>F\<^esub> (carrier F) p \<and> length p = n}"
    apply(rule order_antisym, rule subsetI)
    using A_def assms(1) by (simp add: univ_poly_carrier)+
  have c:"A = {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = n}"
    apply(rule order_antisym, rule subsetI)
    apply(simp add:b polynomial_def)
     apply (metis assms(2) One_nat_def list.size(3) not_one_le_zero )
    apply (rule subsetI)
    by (simp add:b polynomial_def)
  have d:"A = {p. \<exists>u v. p=u#v \<and> set v \<subseteq> carrier F \<and> u \<in> carrier F - {\<zero>\<^bsub>F\<^esub>} \<and> length v = n-1}"
    apply(rule order_antisym, rule subsetI)
     apply (simp add:c)
    apply (metis (no_types, lifting) One_nat_def assms(2) hd_Cons_tl length_tl list.set_sel(1) list.size(3) not_one_le_zero order_trans set_subset_Cons subsetD)
    apply (rule subsetI, simp add:c) using assms(2) by force
  define B where "B = {p. set p \<subseteq> carrier F \<and> length p = n-1}"
  have "A = (\<lambda>(u,v). u # v) ` ((carrier F -  {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    using d B_def by auto
  moreover have "inj_on (\<lambda>(u,v). u # v) ((carrier F -  {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    by (auto intro!: inj_onI) 
  ultimately have "card A = card ((carrier F - {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    using card_image by meson
  moreover have "card B = (card (carrier F) ^ (n-1))" using B_def
    using card_lists_length_eq assms(3) by blast
  ultimately have "card A = card (carrier F - {\<zero>\<^bsub>F\<^esub>}) * (card (carrier F) ^ (n-1))"
    by (simp add: card_cartesian_product)
  moreover have "card (carrier F - {\<zero>\<^bsub>F\<^esub>}) = card (carrier F) - 1" 
    by (meson assms(1) assms(3) card_Diff_singleton ring.ring_simprules(2))
  ultimately show "card ({p. p \<in> carrier (poly_ring F) \<and> length p = n}) = (card (carrier F) - 1) * (card (carrier F) ^ (n-1))" using A_def by simp
qed

lemma fixed_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card ({p. p \<in> carrier (poly_ring F) \<and> length p = n}) = (
    if n \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ (n-1)) else 1)"
proof -
  have a:"\<not> 1 \<le> n \<Longrightarrow> n = 0" by linarith
  show ?thesis 
    apply (cases "n\<ge>1")
    using fixed_degree_polynomials_count_gr_0 assms apply auto[1]
    using zero_degree_polynomials_count assms a by fastforce
qed

lemma bounded_len_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card (bounded_len_polynomials F n) = card (carrier F) ^ n"
proof -
  have "\<zero>\<^bsub>F\<^esub> \<in> carrier F" using assms(1) by (simp add: ring.ring_simprules(2))
  hence b: "card (carrier F) > 0" 
    using assms(2) card_gt_0_iff by blast
  have a: "bounded_len_polynomials F n = (\<Union> m \<le> n. {p.  p \<in> carrier (poly_ring F) \<and> length p = m})"
    apply (simp add: bounded_len_polynomials_def,rule order_antisym)
    apply (rule subsetI, simp) 
    by (rule subsetI, simp) 
  have "card (bounded_len_polynomials F n) = (\<Sum> m \<le> n. card {p.  p \<in> carrier (poly_ring F) \<and> length p = m})"
    apply (simp only:a)
    apply(rule card_UN_disjoint)
      apply blast
    using fin_fixed_degree assms apply blast
    by blast
  hence "card (bounded_len_polynomials F n) = (\<Sum> m \<le> n. if m \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ (m-1)) else 1)"
    using fixed_degree_polynomials_count assms by fastforce
  moreover have "(\<Sum> m \<le> n. if m \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ (m-1)) else 1) = (card (carrier F) ^ (n))"
    apply (induction n, simp, simp add:algebra_simps) using b by force
  ultimately show ?thesis by auto
qed

end