theory UniqPoly
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials"
  "HOL-Algebra.IntRing"
begin

lemma (in domain) max_roots_aux:
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "x \<oplus> (\<ominus> y) = \<zero>"
  shows "x = y"
proof -
  have "(x \<oplus> (\<ominus> y)) \<oplus> y = y" using assms(3) apply simp using assms(2) l_zero by blast
  thus "x = y" 
    using assms(1) assms(2) minus_eq r_right_minus_eq by auto
qed

(* A polynomial of degree less than n, that vanishes at n points must be zero. *)
lemma (in domain) max_roots:
  "polynomial (carrier R) p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> set s \<subseteq> (carrier R) \<Longrightarrow> distinct s \<Longrightarrow> length p \<le> length s \<Longrightarrow> (\<forall>x \<in> set s. eval p x = \<zero>) \<Longrightarrow> False"
proof (induction s arbitrary: p)
  case Nil
  hence "p = []" by simp
  then show "False" using Nil by auto
next
  case (Cons a s)
  have a:"p \<in> carrier (poly_ring R)"
    using Cons univ_poly_carrier by blast
  have a2: "a \<in> carrier R" using Cons by simp
  have a1: "set [\<one>, \<ominus> a] \<subseteq> carrier R" using Cons
    by (metis add.inv_closed insert_subset list.simps(15) one_closed polynomial_incl zero_is_polynomial)
  moreover have "lead_coeff  [\<one>, \<ominus> a] \<noteq> \<zero>" by simp
  ultimately have b: "[\<one>, \<ominus> a] \<in> carrier (poly_ring R)" using univ_poly_carrier by blast
  have c: "degree [\<one>, \<ominus> a] = 1" by simp
  have "is_root p a"
    using Cons by (simp add:is_root_def)
  hence "[\<one>, \<ominus> a] pdivides p" using is_root_imp_pdivides a by fastforce
  hence "[\<one>, \<ominus> a] divides\<^bsub>poly_ring R\<^esub> p" by (simp add: pdivides_def)
  then obtain q where q_def: "q \<in> carrier (poly_ring R)" and q_def_2: "p = [\<one>, \<ominus> a] \<otimes>\<^bsub>poly_ring R\<^esub> q"
    using factor_def by blast
  moreover have "subring (carrier R) R" by (simp add: carrier_is_subring)
  moreover have f:"polynomial (carrier R) q" using q_def by (simp add: univ_poly_carrier)
  moreover have "polynomial (carrier R) [\<one>,  \<ominus> a]" using b by (simp add: univ_poly_carrier)
  ultimately have d:"degree p = 1 + degree q" apply (simp only:q_def)
    by (metis Cons.prems(2) b c domain.integral_iff poly_mult_degree_eq q_def univ_poly_is_domain univ_poly_mult univ_poly_zero)
  have e: "q \<noteq> []" using q_def Cons 
    by (metis q_def_2 a1  poly_mult_zero(2) univ_poly_mult)
  have "length q < length p" using d e by linarith 
  hence i: "length q \<le> length s" using Cons by simp
  have g: "distinct s" using Cons by auto
  have h: "set s \<subseteq> carrier R" using Cons by (metis insert_subset list.simps(15))
  have "\<forall>x \<in> set s. eval q x = \<zero>"
  proof
    fix x
    assume j1: "x \<in> set s"
    hence j4: "eval p x = eval [\<one>, \<ominus> a] x \<otimes> eval q x" using q_def_2 eval_poly_mult 
      by (metis a1 f h polynomial_incl subset_code(1) univ_poly_mult) 
    have j3: "x \<in> carrier R" using j1 Cons(4) apply simp by blast
    have "x \<noteq> a" using Cons(5) j1 by auto
    hence j5: "eval [\<one>, \<ominus> a] x \<noteq> \<zero>" using j3 a2 max_roots_aux by auto
    have "eval p x = \<zero>" using Cons j1 by simp
    then show "eval q x = \<zero>" using j5 j4 
      by (metis a1 eval_in_carrier f j3 local.integral polynomial_incl)
  qed
  then show "False" using Cons g h f i e by blast
qed

lemma max_roots:
  assumes "domain R"
  assumes "p \<in> carrier (poly_ring R)"
  assumes "set s \<subseteq> carrier R"
  assumes "distinct s"
  assumes "degree p < length s"
  assumes "\<forall>x \<in> set s. ring.eval R p x = \<zero>\<^bsub>R\<^esub>"
  shows "p = []" 
proof (rule ccontr)
  assume a:"p \<noteq> []" 
  have "length p \<le> length s" using assms(5) by linarith
  thus "False" using domain.max_roots assms a  univ_poly_carrier by blast
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
  assumes "domain R"
  assumes "p \<in> carrier (poly_ring R)"
  assumes "q \<in> carrier (poly_ring R)"
  assumes "set s \<subseteq> carrier R"
  assumes "distinct s"
  assumes "degree p < length s"
  assumes "degree q < length s"
  assumes "\<forall>x \<in> set s. ring.eval R p x = ring.eval R q x"
  shows "p = q"
proof -
  have f5: "ring R" using assms(1) 
    using cring_def domain.axioms(1) by blast
  define h where "h = p \<ominus>\<^bsub>poly_ring R\<^esub> q" 
  have f0: "h \<in> carrier (poly_ring R)" using h_def assms 
    by (simp add: abelian_group.minus_closed domain.univ_poly_is_abelian_group f5 ring.carrier_is_subring)
  have f6: "\<forall>x \<in> set s. ring.eval R h x = \<zero>\<^bsub>R\<^esub>"
  proof 
    fix x
    assume f1: "x \<in> set s"
    have f4: "x \<in> carrier R" using assms(4) f1 by blast
    have f2: "set p \<subseteq> carrier R" by (meson assms(2) f5 ring.polynomial_incl univ_poly_carrier)
    have f3: "set q \<subseteq> carrier R" using assms(3) f5 ring.polynomial_incl univ_poly_carrier by blast
    hence "ring.eval R h x = ring.eval R p x \<ominus>\<^bsub>R\<^esub> ring.eval R q x" using f2 f3
      f4 f5 assms(1) domain.neg_hom 
      by (metis a_minus_def assms(3) domain.univ_poly_is_ring h_def mem_Collect_eq partial_object.select_convs(1) ring.carrier_is_subring ring.eval_poly_add ring.polynomial_incl ring.ring_simprules(3) univ_poly_add univ_poly_def)
    thus "ring.eval R h x = \<zero>\<^bsub>R\<^esub>" 
    using assms(8) h_def 
    by (metis f1 f2 f4 f5 ring.eval_in_carrier ring.r_right_minus_eq)
  qed
  have "degree (\<ominus>\<^bsub>poly_ring R\<^esub> q) = degree q" 
    using assms(1) assms(3) domain.univ_poly_a_inv_degree f5 ring.carrier_is_subring by blast
  hence "degree h \<le> max (degree p) (degree q)" using h_def ring.poly_add_degree f5 
    by (metis a_minus_def univ_poly_add)
  hence "degree h < length s" using assms(6) assms(7) by fastforce
  hence "h = []" using max_roots assms(1) f0 assms(4) assms(5) f6 by auto
  thus "p = q" using h_def 
    by (metis assms(1) assms(2) assms(3) domain.univ_poly_is_ring f5 ring.carrier_is_subring ring.r_right_minus_eq univ_poly_zero)
qed
end