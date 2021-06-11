theory PolynomialCounting
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials"
begin

definition bounded_len_polynomials
  where "bounded_len_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> length x \<le> n}"

definition split_poly
  where "split_poly F K p = (\<lambda>k. if k \<in> K then Some (ring.eval F p k) else None, \<lambda>k. ring.coeff F p (k+card K))"

lemma split_poly_image:
  assumes "field F"
  assumes "K \<subseteq> carrier F"
  shows "split_poly F K ` bounded_len_polynomials F (card K + n) \<subseteq>
        {f. dom f = K \<and> ran f \<subseteq> carrier F} \<times> {f. range f \<subseteq> carrier F \<and> (\<forall>k. k \<ge> n \<longrightarrow> f k = \<zero>\<^bsub>F\<^esub>)}" 
  apply (rule image_subsetI)
  apply (simp add:split_poly_def dom_def ran_def bounded_len_polynomials_def)
  apply (rule conjI, rule subsetI, simp)
   apply (metis assms(1) assms(2) field.is_ring mem_Collect_eq partial_object.select_convs(1) 
          ring.carrier_is_subring ring.eval_in_carrier ring.polynomial_in_carrier subset_iff 
          univ_poly_def) 
  apply (rule conjI, rule subsetI) 
   apply (metis (no_types, lifting) assms(1) field.is_ring imageE mem_Collect_eq 
        partial_object.select_convs(1) ring.carrier_is_subring ring.coeff_in_carrier
        ring.polynomial_in_carrier univ_poly_def)
  by (simp add: assms(1) field.is_ring ring.coeff_length)

lemma poly_substract_coeff:
  assumes "ring F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "y \<in> carrier (poly_ring F)"
  shows "ring.coeff F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) k = ring.coeff F x k \<ominus>\<^bsub>F\<^esub> ring.coeff F y k"
  sorry

lemma poly_substract_eval:
  assumes "ring F"
  assumes "i \<in> carrier F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "y \<in> carrier (poly_ring F)"
  shows "ring.eval F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) i = ring.eval F x i \<ominus>\<^bsub>F\<^esub> ring.eval F y i"
  sorry

lemma poly_degree_bound_from_coeff:
  assumes "ring F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "\<And>k. k \<ge> n \<Longrightarrow> ring.coeff F x k = \<zero>\<^bsub>F\<^esub>"
  shows "degree x < n \<or> x = \<zero>\<^bsub>poly_ring F\<^esub>"
proof (rule ccontr)
  assume a:"\<not>(degree x < n \<or> x = \<zero>\<^bsub>poly_ring F\<^esub>)"
  hence b:"lead_coeff x \<noteq> \<zero>\<^bsub>F\<^esub>" 
    by (metis assms(2) polynomial_def univ_poly_carrier univ_poly_zero)
  hence "ring.coeff F x (degree x) \<noteq> \<zero>\<^bsub>F\<^esub>" 
    by (metis a assms(1) ring.lead_coeff_simp univ_poly_zero)
  moreover have "degree x \<ge> n" by (meson a not_le)
  ultimately show "False" using assms(3) by blast
qed

lemma max_roots:
  assumes "field R"
  assumes "p \<in> carrier (poly_ring R)"
  assumes "K \<subseteq> carrier R"
  assumes "finite K"
  assumes "degree p < card K"
  assumes "\<And>x. x \<in> K \<Longrightarrow> ring.eval R p x = \<zero>\<^bsub>R\<^esub>"
  shows "p = \<zero>\<^bsub>poly_ring R\<^esub>"
proof (rule ccontr)
  assume "p \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>"
  hence a:"p \<noteq> []" by (simp add: univ_poly_zero)
  have "\<And>x. count (mset_set K) x \<le> count (ring.roots R p) x"
  proof -
    fix x
    show "count (mset_set K) x \<le> count (ring.roots R p) x"
    proof (cases "x \<in> K")
      case True
      hence "ring.is_root R p x" using assms(3) assms(6) 
        by (meson a assms(1) field.is_ring ring.is_root_def subsetD)
      hence "x \<in> set_mset (ring.roots R p)"
        using assms(2) assms(1) domain.roots_mem_iff_is_root field_def by force
      hence "1 \<le> count (ring.roots R p) x" by simp
      moreover have "count (mset_set K) x = 1" using True assms(4) by simp
      ultimately show ?thesis by presburger
    next
      case False
      hence "count (mset_set K) x = 0" by simp
      then show ?thesis by presburger
    qed
  qed
  hence "mset_set K \<subseteq># ring.roots R p"
    by (simp add: subseteq_mset_def)
  hence "card K \<le> size (ring.roots R p)" 
    by (metis size_mset_mono size_mset_set)
  moreover have "size (ring.roots R p) \<le> degree p"
    using a field.size_roots_le_degree assms by auto
  ultimately show "False" using assms(5) 
    by (meson leD less_le_trans)
qed

lemma split_poly_inj:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  shows "inj_on (split_poly F K) (carrier (poly_ring F))"
proof
  have ring_F: "ring F" using assms(1) field.is_ring by blast
  fix x
  fix y
  assume a1:"x \<in> carrier (poly_ring F)"
  assume a2:"y \<in> carrier (poly_ring F)"
  assume a3:"split_poly F K x = split_poly F K y"

  have x_y_carrier: "x \<ominus>\<^bsub>poly_ring F\<^esub> y \<in> carrier (poly_ring F)" using a1 a2
    by (simp add: assms(1) domain.univ_poly_is_ring field.axioms(1) ring.carrier_is_subring ring.ring_simprules(4) ring_F)
  have "\<And>k. ring.coeff F x (k+card K) = ring.coeff F y (k+card K)"
    using a3 apply (simp add:split_poly_def) by meson
  hence "\<And>k. ring.coeff F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) (k+card K) = \<zero>\<^bsub>F\<^esub>"
    apply (simp add:ring_F a1 a2 poly_substract_coeff)
    by (meson a2 ring.carrier_is_subring ring.coeff_in_carrier 
       ring.polynomial_in_carrier ring.r_right_minus_eq ring_F univ_poly_carrier)
  hence "degree (x \<ominus>\<^bsub>poly_ring F\<^esub> y) < card K \<or> (x \<ominus>\<^bsub>poly_ring F\<^esub> y) = \<zero>\<^bsub>poly_ring F\<^esub>"
    by (metis add.commute le_Suc_ex poly_degree_bound_from_coeff x_y_carrier ring_F)
  moreover have "\<And>k. k \<in> K \<Longrightarrow> ring.eval F x k = ring.eval F y k"
    using a3 apply (simp add:split_poly_def) by (meson option.inject)
  hence "\<And>k. k \<in> K \<Longrightarrow> ring.eval F x k \<ominus>\<^bsub>F\<^esub> ring.eval F y k = \<zero>\<^bsub>F\<^esub>"
    by (metis (no_types, hide_lams) a2 assms(3) ring.eval_in_carrier ring.polynomial_incl ring.r_right_minus_eq ring_F subsetD univ_poly_carrier)
  hence "\<And>k. k \<in> K \<Longrightarrow> ring.eval F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) k =  \<zero>\<^bsub>F\<^esub>"
    using  ring_F a1 a2 assms(3) poly_substract_eval by (metis (no_types, hide_lams) subsetD)
  moreover have "finite K" using assms(2) assms(3) finite_subset by blast
  ultimately have "x \<ominus>\<^bsub>poly_ring F\<^esub> y = \<zero>\<^bsub>poly_ring F\<^esub>"
    using max_roots assms(1) x_y_carrier assms(3) by blast
  then show "x = y"
    by (meson assms(1) a1 a2 domain.univ_poly_is_ring field_def ring.carrier_is_subring ring.r_right_minus_eq ring_F)
qed

lemma split_poly_surj:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  shows "split_poly F K ` bounded_len_polynomials F (card K + n) =
        {f. dom f = K \<and> ran f \<subseteq> carrier F} \<times> {f. range f \<subseteq> carrier F \<and> (\<forall>k. k \<ge> n \<longrightarrow> f k = \<zero>\<^bsub>F\<^esub>)}" 
proof -
  have "finite K" using assms(2) assms(3) finite_subset by blast
  hence "card {f. dom f = K \<and> ran f \<subseteq> carrier F} = card (carrier F)^(card K)"
    using assms(2) sorry
  show ?thesis sorry
qed

end