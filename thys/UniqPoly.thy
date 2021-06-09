theory UniqPoly
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials"
  "HOL-Algebra.IntRing"
begin

lemma max_roots:
  assumes "field R"
  assumes "p \<in> carrier (poly_ring R)"
  assumes "set s \<subseteq> carrier R"
  assumes "distinct s"
  assumes "degree p < length s"
  assumes "\<And>x. x \<in> set s \<Longrightarrow> ring.eval R p x = \<zero>\<^bsub>R\<^esub>"
  shows "p = []" 
proof (rule ccontr)
  assume a:"p \<noteq> []" 
  have "\<And>x. count (mset s) x \<le> count (ring.roots R p) x"
  proof -
    fix x
    show "count (mset s) x \<le> count (ring.roots R p) x"
    proof (cases "x \<in> set s")
      case True
      hence "ring.is_root R p x" using assms(3) assms(6) 
        by (meson a assms(1) field.is_ring ring.is_root_def subsetD)
      hence "x \<in> set_mset (ring.roots R p)"
        using assms(2) assms(1) domain.roots_mem_iff_is_root field_def by force
      hence "1 \<le> count (ring.roots R p) x" by simp
      moreover have "count (mset s) x = 1" using True assms(4) 
        by (metis distinct_count_atmost_1)
      ultimately show ?thesis by presburger
    next
      case False
      hence "count (mset s) x = 0" by simp
      then show ?thesis by presburger
    qed
  qed
  hence "mset s \<subseteq># ring.roots R p"
    by (simp add: subseteq_mset_def)
  hence "length s \<le> size (ring.roots R p)"
    by (metis size_mset size_mset_mono)
  moreover have "size (ring.roots R p) \<le> degree p"
    using a field.size_roots_le_degree assms by auto
  ultimately show "False" using assms(5) 
    by (meson leD less_le_trans)
qed

lemma (in domain) neg_hom:
  assumes "x \<in> carrier R" 
  assumes "p \<in> carrier (poly_ring R)"
  shows "eval (\<ominus>\<^bsub>poly_ring R\<^esub> p) x = \<ominus>(eval p x)"
proof -
  have "polynomial (carrier R) p" using assms(2) by (simp add: univ_poly_carrier)
  hence "set p \<subseteq> carrier R" using assms(2) by (meson polynomial_incl)
  have "eval (p \<oplus>\<^bsub>poly_ring R\<^esub> (\<ominus>\<^bsub>poly_ring R\<^esub> p)) x = eval p x \<oplus> (eval (\<ominus>\<^bsub>poly_ring R\<^esub> p) x)"
    by (metis (no_types, lifting) assms carrier_is_subring domain.eval_cring_hom domain.univ_poly_is_ring domain_axioms eval.simps(1) eval_is_hom local.ring_axioms ring.ring_simprules(16) ring_hom_closed ring_hom_cring.hom_a_inv univ_poly_zero)
  moreover 
  have a:"ring (poly_ring R)" 
    by (simp add: carrier_is_subring univ_poly_is_ring)
  hence "p \<oplus>\<^bsub>poly_ring R\<^esub> (\<ominus>\<^bsub>poly_ring R\<^esub> p) = \<zero>\<^bsub>poly_ring R\<^esub>"
    by (simp add: assms(2) ring.ring_simprules(16))
  ultimately have "\<zero> = eval p x \<oplus> (eval (\<ominus>\<^bsub>poly_ring R\<^esub> p) x)"
    by (simp add: univ_poly_zero)
  thus ?thesis 
    by (metis (no_types, hide_lams) a add.inv_comm assms(1) assms(2) eval_in_carrier minus_equality polynomial_incl ring.ring_simprules(3) univ_poly_carrier)
qed

lemma unique_poly:
  assumes "field R"
  assumes "p \<in> carrier (poly_ring R)"
  assumes "q \<in> carrier (poly_ring R)"
  assumes "set s \<subseteq> carrier R"
  assumes "distinct s"
  assumes "degree p < length s"
  assumes "degree q < length s"
  assumes "\<forall>x \<in> set s. ring.eval R p x = ring.eval R q x"
  shows "p = q"
proof -
  have f5: "ring R" using assms(1) cring_def domain.axioms(1) field_def by blast
  define h where "h = p \<ominus>\<^bsub>poly_ring R\<^esub> q" 
  have f0: "h \<in> carrier (poly_ring R)" using h_def assms field_def
    by (metis cring_def domain.univ_poly_is_domain domain_def ring.carrier_is_subring ring.ring_simprules(4))
  have f6: "\<And>x. x \<in> set s \<Longrightarrow> ring.eval R h x = \<zero>\<^bsub>R\<^esub>"
  proof -
    fix x
    assume f1: "x \<in> set s"
    have f4: "x \<in> carrier R" using assms(4) f1 by blast
    have f2: "set p \<subseteq> carrier R" by (meson assms(2) f5 ring.polynomial_incl univ_poly_carrier)
    have f3: "set q \<subseteq> carrier R" using assms(3) f5 ring.polynomial_incl univ_poly_carrier by blast
    hence "ring.eval R h x = ring.eval R p x \<ominus>\<^bsub>R\<^esub> ring.eval R q x" using f2 f3
      f4 f5 assms(1) domain.neg_hom field_def
      by (metis a_minus_def assms(3) domain.univ_poly_is_ring h_def mem_Collect_eq partial_object.select_convs(1) ring.carrier_is_subring ring.eval_poly_add ring.polynomial_incl ring.ring_simprules(3) univ_poly_add univ_poly_def)
    thus "ring.eval R h x = \<zero>\<^bsub>R\<^esub>" 
    using assms(8) h_def 
    by (metis f1 f2 f4 f5 ring.eval_in_carrier ring.r_right_minus_eq)
  qed
  have "degree (\<ominus>\<^bsub>poly_ring R\<^esub> q) = degree q" 
    using assms(1) assms(3) domain.univ_poly_a_inv_degree f5 ring.carrier_is_subring field_def by blast
  hence "degree h \<le> max (degree p) (degree q)" using h_def ring.poly_add_degree f5 
    by (metis a_minus_def univ_poly_add)
  hence "degree h < length s" using assms(6) assms(7) by fastforce
  hence "h = []" using max_roots assms(1) f0 assms(4) assms(5) f6 field_def by blast
  thus "p = q" using h_def 
    by (metis assms(1) assms(2) assms(3) domain.univ_poly_is_ring f5 field_def ring.carrier_is_subring ring.r_right_minus_eq univ_poly_zero)
qed

end