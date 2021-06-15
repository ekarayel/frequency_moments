section \<open>Counting Polynomials\<close>

theory PolyCard
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility"
begin

(* Set of polynomials with a maximal degree *)

definition bounded_degree_polynomials
  where "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> (degree x < n \<or> x = [])}"

lemma bounded_degree_polynomials_length:
  "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> length x \<le> n}"
  apply (rule order_antisym)
  apply (rule subsetI, simp add:bounded_degree_polynomials_def) 
  apply (metis Suc_pred leI less_Suc_eq_0_disj less_Suc_eq_le list.size(3))
  apply (rule subsetI, simp add:bounded_degree_polynomials_def) 
  by (metis diff_less length_greater_0_conv lessI less_imp_diff_less order.not_eq_order_implies_strict)

lemma fin_degree_bounded:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "finite (bounded_degree_polynomials F n)"
proof -
  have "bounded_degree_polynomials F n \<subseteq> {p. set p \<subseteq> carrier F \<and> length p \<le> n}"
    apply (rule subsetI)
    apply (simp add: bounded_degree_polynomials_length) using assms(1) 
    by (meson ring.polynomial_incl univ_poly_carrier)
  thus ?thesis  apply (rule finite_subset)
    using assms(2) finite_lists_length_le by auto
qed

lemma fin_fixed_degree:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "finite {p. p \<in> carrier (poly_ring F) \<and> length p = n}"
proof -
  have "{p. p \<in> carrier (poly_ring F) \<and> length p = n} \<subseteq> bounded_degree_polynomials F n"
    by (rule subsetI, simp add:bounded_degree_polynomials_length) 
  then show ?thesis
  using fin_degree_bounded assms rev_finite_subset by blast
qed

lemma nonzero_length_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card {p. p \<in> carrier (poly_ring F) \<and> length p = Suc n} 
        = (card (carrier F) - 1) * card (carrier F) ^ n"
proof -
  define A where "A = {p. p \<in> (carrier (poly_ring F)) \<and> length p = Suc n}"
  have b:"A = {p. polynomial\<^bsub>F\<^esub> (carrier F) p \<and> length p = Suc n}"
    apply(rule order_antisym, rule subsetI)
    using A_def assms(1) by (simp add: univ_poly_carrier)+
  have c:"A = {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = Suc n}"
    apply (rule order_antisym)
    apply (rule subsetI, simp add:b polynomial_def, force)
    by (rule subsetI, simp add:b polynomial_def)
  have d:"A = {p. \<exists>u v. p=u#v \<and> set v \<subseteq> carrier F \<and> u \<in> carrier F - {\<zero>\<^bsub>F\<^esub>} \<and> length v = n}"
    apply(rule order_antisym, rule subsetI)
     apply (simp add:c) 
     apply (metis Suc_length_conv hd_Cons_tl length_0_conv list.sel(3) list.set_sel(1) nat.simps(3) 
            order_trans set_subset_Cons subsetD)
    apply (rule subsetI, simp add:c) using assms(2) by force
  define B where "B = {p. set p \<subseteq> carrier F \<and> length p = n}"
  have "A = (\<lambda>(u,v). u # v) ` ((carrier F -  {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    using d B_def by auto
  moreover have "inj_on (\<lambda>(u,v). u # v) ((carrier F -  {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    by (auto intro!: inj_onI) 
  ultimately have "card A = card ((carrier F - {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    using card_image by meson
  moreover have "card B = (card (carrier F) ^ n)" using B_def
    using card_lists_length_eq assms(2) by blast
  ultimately have "card A = card (carrier F - {\<zero>\<^bsub>F\<^esub>}) * (card (carrier F) ^ n)"
    by (simp add: card_cartesian_product)
  moreover have "card (carrier F - {\<zero>\<^bsub>F\<^esub>}) = card (carrier F) - 1" 
    by (meson assms(1) assms(2) card_Diff_singleton ring.ring_simprules(2))
  ultimately show "card ({p. p \<in> carrier (poly_ring F) \<and> length p = Suc n}) = 
          (card (carrier F) - 1) * (card (carrier F) ^ n)" using A_def by simp
qed

lemma fixed_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card ({p. p \<in> carrier (poly_ring F) \<and> length p = n}) = 
    (if n \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ (n-1)) else 1)"
proof -
  have a: " [] \<in> carrier (poly_ring F)" 
    by (simp add: univ_poly_zero_closed)
  show ?thesis 
    apply (cases "n")
    using assms a apply (simp) 
     apply (metis (mono_tags, lifting) One_nat_def empty_Collect_eq is_singletonI' 
            is_singleton_altdef mem_Collect_eq) 
    using assms by (simp add:nonzero_length_polynomials_count)
qed

lemma bounded_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card (bounded_degree_polynomials F n) = card (carrier F) ^ n"
proof -
  have "\<zero>\<^bsub>F\<^esub> \<in> carrier F" using assms(1) by (simp add: ring.ring_simprules(2))
  hence b: "card (carrier F) > 0" 
    using assms(2) card_gt_0_iff by blast
  have a: "bounded_degree_polynomials F n = (\<Union> m \<le> n. {p.  p \<in> carrier (poly_ring F) \<and> length p = m})"
    apply (simp add: bounded_degree_polynomials_length,rule order_antisym)
    by (rule subsetI, simp)+
  have "card (bounded_degree_polynomials F n) = (\<Sum> m \<le> n. card {p.  p \<in> carrier (poly_ring F) \<and> length p = m})"
    apply (simp only:a)
    apply (rule card_UN_disjoint, blast)
    using fin_fixed_degree assms apply blast
    by blast
  hence "card (bounded_degree_polynomials F n) = (\<Sum> m \<le> n. if m \<ge> 1 then (card (carrier F) - 1) * card (carrier F) ^ (m-1) else 1)"
    using fixed_degree_polynomials_count assms by fastforce
  moreover have "(\<Sum> m \<le> n. if m \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ (m-1)) else 1) = card (carrier F) ^ n"
    apply (induction n, simp, simp add:algebra_simps) using b by force
  ultimately show ?thesis by auto
qed

end