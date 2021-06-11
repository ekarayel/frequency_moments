theory LagrangeInterpolation
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials"
begin

lemma eval_simp:
  assumes "domain F"
  assumes "x \<in> carrier F"
  assumes "p \<in> carrier (poly_ring F) \<and> ring.eval F p x = u"
  assumes "q \<in> carrier (poly_ring F) \<and> ring.eval F q x = v"
  shows "p \<oplus>\<^bsub>poly_ring F\<^esub> q \<in> carrier (poly_ring F) \<and> ring.eval F (p \<oplus>\<^bsub>poly_ring F\<^esub> q) x = u \<oplus>\<^bsub>F\<^esub> v" 
proof -
  have "subring (carrier F) F" 
    using assms(1) cring_def domain_def ring.carrier_is_subring by blast
  hence "ring_hom_ring (poly_ring F) F (\<lambda>p. (ring.eval F p) x)" 
    by (simp add: assms(1) assms(2) domain.eval_ring_hom)
  then show ?thesis using assms by (simp add: ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def ring.ring_simprules)
qed

lemma lagrange_poly_eval_aux:
  assumes "domain F"
  assumes "x \<in> carrier F"
  assumes "p \<in> carrier (poly_ring F)"
  assumes "q \<in> carrier (poly_ring F)"
  shows "ring.eval F (p \<otimes>\<^bsub>poly_ring F\<^esub> q) x = ring.eval F p x \<otimes>\<^bsub>F\<^esub> ring.eval F q x" 
proof -
  have "subring (carrier F) F" 
    using assms(1) cring_def domain_def ring.carrier_is_subring by blast
  hence "ring_hom_ring (poly_ring F) F (\<lambda>p. (ring.eval F p) x)" 
    by (simp add: assms(1) assms(2) domain.eval_ring_hom)
  then show ?thesis apply (simp add: ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def) using assms by blast
qed

fun lagrange_poly where
  "lagrange_poly F [] x f = ring.normalize F [f]" |
  "lagrange_poly F (s#ss) x f 
    = [\<one>\<^bsub>F\<^esub>, \<ominus>\<^bsub>F\<^esub> s] \<otimes>\<^bsub>poly_ring F\<^esub> (lagrange_poly F ss x (f \<otimes>\<^bsub>F\<^esub> inv\<^bsub>F\<^esub> (x \<ominus>\<^bsub>F\<^esub> s)))"

lemma gr_assoc:
  assumes "ring F"
  assumes "x \<in> carrier F"
  assumes "y \<in> carrier F"
  assumes "z \<in> carrier F"
  shows "x \<otimes>\<^bsub>F\<^esub> (y \<otimes>\<^bsub>F\<^esub> z) = (x  \<otimes>\<^bsub>F\<^esub> y)  \<otimes>\<^bsub>F\<^esub> z"
  by (simp add: assms(1) assms(2) assms(3) assms(4) ring.ring_simprules(11))

lemma poly_mult_degree_le:
  assumes "domain F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "y \<in> carrier (poly_ring F)"
  assumes "degree x \<le> n"
  assumes "degree y \<le> m"
  shows "degree (x \<otimes>\<^bsub>poly_ring F\<^esub> y) \<le> n + m"
proof -
  have a: "polynomial\<^bsub>F\<^esub> (carrier F) x" using assms 
    by (meson univ_poly_carrier)
  have b: "polynomial\<^bsub>F\<^esub> (carrier F) y" using assms 
    by (meson univ_poly_carrier)
  have c: "subring (carrier F) F" 
    using assms(1) cring_def domain_def ring.carrier_is_subring by blast
  have "degree (ring.poly_mult F x y) = (if x = [] \<or> y = [] then 0 else degree x + degree y)"
    using a b c domain.poly_mult_degree_eq assms(1) by blast
  hence "degree (x \<otimes>\<^bsub>poly_ring F\<^esub> y) = (if x = [] \<or> y = [] then 0 else degree x + degree y)"
    by (simp add: univ_poly_mult)
  thus ?thesis using assms 
    by (metis add_mono_thms_linordered_semiring(1) zero_le)   
qed

lemma gr_inv_elim:
  assumes "field F"
  assumes "x \<in> (carrier F) - {\<zero>\<^bsub>F\<^esub>}"
  shows "x \<otimes>\<^bsub>F\<^esub> inv\<^bsub>F\<^esub> x  = \<one>\<^bsub>F\<^esub>"
  by (metis Multiplicative_Group.carrier_mult_of Multiplicative_Group.mult_mult_of Multiplicative_Group.one_mult_of assms(1) assms(2) field.field_mult_group field.m_inv_mult_of group.r_inv)

lemma lagrange_poly_mem:
  fixes x
  assumes "field F"
  assumes "domain F"
  assumes "ring F"
  assumes "x \<in> carrier F"
  shows "set s \<subseteq> carrier F \<Longrightarrow> y \<in> carrier F \<Longrightarrow> x \<notin> (set s) \<Longrightarrow> 
    lagrange_poly F s x y \<in> carrier (poly_ring F) \<and>
    ring.eval F (lagrange_poly F s x y) x = y \<and>
    (\<forall>x' \<in> set s. ring.eval F (lagrange_poly F s x y) x' = \<zero>\<^bsub>F\<^esub>) \<and>
    degree (lagrange_poly F s x y) \<le> length s"
proof (induction s arbitrary: y)
  case Nil
  then have a:"polynomial\<^bsub>F\<^esub> (carrier F) (lagrange_poly F [] x y)" using assms
    apply (cases "y = \<zero>\<^bsub>F\<^esub>")
    by (simp add:ring.normalize.simps ring.eval.simps polynomial_def)+
  hence b:"ring.eval F (lagrange_poly F [] x y) x = y" using assms 
    apply (cases "y = \<zero>\<^bsub>F\<^esub>")
    by (simp add:ring.normalize.simps ring.eval.simps polynomial_def ring.ring_simprules ring_def)+
  have c: "degree (lagrange_poly F [] x y) = 0" using assms
    apply (cases "y = \<zero>\<^bsub>F\<^esub>")
    by (simp add:ring.normalize.simps ring.eval.simps polynomial_def ring.ring_simprules ring_def)+
  show ?case using a b c 
    by (metis empty_iff empty_set univ_poly_carrier zero_le)
next
  case (Cons s ss)
  have d6: "ring (poly_ring F)" using assms 
    using domain.univ_poly_is_ring ring.carrier_is_subring by blast
  define z where "z = y \<otimes>\<^bsub>F\<^esub> inv\<^bsub>F\<^esub> (x \<ominus>\<^bsub>F\<^esub> s)"
  have "polynomial\<^bsub>F\<^esub> (carrier F) [\<one>\<^bsub>F\<^esub>, \<ominus>\<^bsub>F\<^esub> s]" 
    by (metis Cons.prems(1) assms(2) assms(3) domain.one_not_zero insert_subset list.sel(1) list.set(2) polynomial_def ring.polynomial_incl ring.ring_simprules(3) ring.ring_simprules(6))
  hence d2: "[\<one>\<^bsub>F\<^esub>, \<ominus>\<^bsub>F\<^esub> s] \<in> carrier (poly_ring F)" by (simp add: univ_poly_carrier)
  have d3: "set ss \<subseteq> carrier F" 
    using Cons.prems(1) by auto
  have d4: "x \<notin> set ss" 
    by (meson Cons.prems(3) list.set_intros(2))
  have d7: "ring.eval F [\<one>\<^bsub>F\<^esub>, \<ominus>\<^bsub>F\<^esub> s] x = x \<ominus>\<^bsub>F\<^esub> s" using assms apply (simp add:ring.eval.simps)
    by (metis Cons.prems(1) insert_subset list.set(2) monoid.r_one ring.ring_simprules(12) ring.ring_simprules(14) ring.ring_simprules(15) ring.ring_simprules(3) ring_def)
  have d13: "y \<in> carrier F" 
    by (simp add: Cons.prems(2))
  have d14: "(x \<ominus>\<^bsub>F\<^esub> s) \<in> carrier F" 
    by (metis Cons.prems(1) assms(3) assms(4) insert_subset list.simps(15) ring.ring_simprules(4))
  have d16:"(x \<ominus>\<^bsub>F\<^esub> s) \<in> carrier F - {\<zero>\<^bsub>F\<^esub>}" 
    by (metis Cons.prems(1) Cons.prems(3) Diff_iff assms(1) assms(3) assms(4) cring.cring_simprules(4) empty_iff fieldE(1) insert_iff insert_subset list.simps(15) ring.r_right_minus_eq)
  hence d15: "inv\<^bsub>F\<^esub> (x \<ominus>\<^bsub>F\<^esub> s) \<in> carrier F" 
    by (metis Diff_iff Multiplicative_Group.carrier_mult_of assms(1) field.field_mult_group field.m_inv_mult_of group.inv_closed) 
  have d12: "y \<otimes>\<^bsub>F\<^esub> inv\<^bsub>F\<^esub> (x \<ominus>\<^bsub>F\<^esub> s) = inv\<^bsub>F\<^esub> (x \<ominus>\<^bsub>F\<^esub> s) \<otimes>\<^bsub>F\<^esub> y" using d13 d15 assms(3) 
    by (simp add: assms(1) cring.cring_simprules(14) fieldE(1))
  have d9: "(x \<ominus>\<^bsub>F\<^esub> s) \<otimes>\<^bsub>F\<^esub> (y \<otimes>\<^bsub>F\<^esub> inv\<^bsub>F\<^esub> (x \<ominus>\<^bsub>F\<^esub> s)) = y" using assms d13 d14 d15 d16 apply (simp add:d12 gr_assoc gr_inv_elim)
    by (simp add: Cons.prems(2) ring.ring_simprules(12))
  have d1:"z \<in> carrier F" 
    by (simp add: assms(3) d13 d15 ring.ring_simprules(5) z_def)
  have d5: "lagrange_poly F ss x z \<in> carrier (poly_ring F)"
    using Cons(1) d4 d1 d3 by blast
  have a: "lagrange_poly F (s#ss) x y \<in> carrier (poly_ring F)"
    apply (simp add:z_def[symmetric])
    using d2 d5 d6
    by (simp add: ring.ring_simprules(5))
  have d8: "ring.eval F (lagrange_poly F ss x z) x = z" 
    using Cons.IH d1 d3 d4 by blast
  have b:"ring.eval F (lagrange_poly F (s#ss) x y) x = y"
    using lagrange_poly_eval_aux assms d2 d5 z_def d7 d8 d9
    by (simp add:lagrange_poly_eval_aux)
  have c:"\<forall>x' \<in> set (s#ss). ring.eval F (lagrange_poly F (s#ss) x y) x' = \<zero>\<^bsub>F\<^esub>"
  proof 
    fix x'
    assume d10: "x' \<in> set (s#ss)"
    have d11: "x' \<in> carrier F" 
      using Cons.prems(1) d10 by blast
    consider (c1) "x' = s" | (c2) "x' \<in> set ss" using d10 
      by fastforce
    then show "ring.eval F (lagrange_poly F (s # ss) x y) x' = \<zero>\<^bsub>F\<^esub>" 
    proof cases
      case c1
      have "ring.eval F [\<one>\<^bsub>F\<^esub>, \<ominus>\<^bsub>F\<^esub> s] s = \<zero>\<^bsub>F\<^esub>" 
        by (metis assms(3) c1 d11 ring.is_root_def ring.monic_degree_one_root_condition)
      then show ?thesis 
        using c1 d2 d5 d11 z_def assms   apply (simp add:d7 lagrange_poly_eval_aux)
        by (metis empty_iff empty_set polynomial_def ring.eval_in_carrier ring.ring_simprules(24) subsetI univ_poly_carrier)
    next
      case c2
      have "ring.eval F (lagrange_poly F ss x z) x' =  \<zero>\<^bsub>F\<^esub>" 
        by (simp add: Cons.IH c2 d1 d3 d4)
      then show ?thesis
        using c2 d2 d5 d11 z_def assms   apply (simp add:d7 lagrange_poly_eval_aux)
        by (metis empty_iff empty_set polynomial_def ring.eval_in_carrier ring.ring_simprules(25) subsetI univ_poly_carrier)
    qed
  qed
  have "degree (lagrange_poly F ss x z) \<le> length ss" 
    using Cons.IH d1 d3 d4 by blast
  moreover have "degree [\<one>\<^bsub>F\<^esub>, \<ominus>\<^bsub>F\<^esub> s] \<le> 1" by simp
  ultimately have d: "degree (lagrange_poly F (s#ss) x y) \<le> 1 + length (ss)"
    using poly_mult_degree_le d2 d5
    apply (simp only:lagrange_poly.simps z_def) 
    using assms by blast
  show ?case using a b c d
    by (metis One_nat_def add.commute list.size(4))
qed

lemma langrange_poly_elim:
  assumes "field F"
  assumes "x \<in> carrier F"
  assumes "set s \<subseteq> carrier F"
  assumes "y \<in> carrier F"
  assumes "x \<notin> set s"
  shows "lagrange_poly F s x y \<in> carrier (poly_ring F) \<and>
    ring.eval F (lagrange_poly F s x y) x = y \<and>
    (\<forall>x' \<in> set s. ring.eval F (lagrange_poly F s x y) x' = \<zero>\<^bsub>F\<^esub>) \<and>
    degree (lagrange_poly F s x y) \<le> length s"
proof -
  have "domain F" using assms(1) using field_def by blast
  thus ?thesis
    by (meson assms(1) assms(2) assms(3) assms(4) assms(5) field.is_ring lagrange_poly_mem)
qed

lemma poly_sum_degree_le:
  assumes "domain F"
  assumes "x \<in> carrier (poly_ring F) \<and> degree x < n"
  assumes "y \<in> carrier (poly_ring F) \<and> degree y < n"
  shows "x \<oplus>\<^bsub>poly_ring F\<^esub> y \<in> carrier (poly_ring F) \<and> degree (x \<oplus>\<^bsub>poly_ring F\<^esub> y) < n"
proof -
  have a:"ring F" using assms 
    using cring_def domain_def by blast
  then 
  have b: "n \<ge> 1" using assms by auto
  have c:"degree x \<le> n - 1" using assms a by auto
  have d:"degree y \<le> n - 1" using assms a by auto
  hence "degree (x \<oplus>\<^bsub>poly_ring F\<^esub> y) \<le> n-1" using assms ring.poly_add_degree a b c 
    by (metis dual_order.trans max.bounded_iff univ_poly_add)
  then show ?thesis using assms  
    by (metis (no_types, lifting) One_nat_def a b diff_less domain.univ_poly_is_ring dual_order.strict_trans2 lessI not_le ring.carrier_is_subring ring.ring_simprules(1))
qed

fun sum_ring where
  "sum_ring R (p#ps) = p \<oplus>\<^bsub>R\<^esub> (sum_ring R ps)" |
  "sum_ring R [] =  \<zero>\<^bsub>R\<^esub>"

lemma sum_ring_elem:
  assumes "ring R"
  assumes "set x \<subseteq> carrier R"
  shows "sum_ring R x \<in> carrier R"
  using assms by (induction x, (simp add: ring.ring_simprules)+)

lemma sum_ring_degree:
  assumes "domain F"
  assumes "n \<ge> 1"
  assumes "\<And>y. y \<in> set x \<Longrightarrow> y \<in> carrier (poly_ring F) \<and> degree y < n"
  shows "sum_ring (poly_ring F) x \<in> carrier (poly_ring F) \<and> degree (sum_ring (poly_ring F) x) < n"
  using assms apply (induction x)
   apply (simp add: univ_poly_zero univ_poly_zero_closed)
  apply (simp only:sum_ring.simps) apply (rule poly_sum_degree_le) 
  by (blast, (meson list.set_intros)+)

lemma sum_ring_degree_1:
  assumes "domain F"
  assumes "n \<ge> 1"
  assumes "\<And>y. y \<in> set x \<Longrightarrow> y \<in> carrier (poly_ring F) \<and> degree y < n"
  shows "degree (sum_ring (poly_ring F) x) < n"
  using sum_ring_degree assms by blast

lemma sum_ring_comm:
  assumes "domain F"
  assumes "x \<in> carrier F"
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> p \<in> carrier (poly_ring F)"
  shows "sum_ring (poly_ring F) ps \<in> carrier (poly_ring F) \<and> 
         ring.eval F (sum_ring (poly_ring F) ps) x = sum_ring F (map (\<lambda>q. ring.eval F q x) ps)"
  using assms apply (induction ps)
   apply (simp add: univ_poly_zero univ_poly_zero_closed ring.eval.simps cring_def domain_def)
  by (simp add:eval_simp)

lemma sum_ring_comm_1:
  assumes "domain F"
  assumes "x \<in> carrier F"
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> p \<in> carrier (poly_ring F)"
  shows "ring.eval F (sum_ring (poly_ring F) ps) x = sum_ring F (map (\<lambda>q. ring.eval F q x) ps)"
  using sum_ring_comm assms by force

fun interpolate where
  "interpolate F f s = sum_ring (poly_ring F) (map (\<lambda>t. lagrange_poly F (removeAll t s) t (f t)) s)"

lemma interpolate_l:
  assumes "field F"
  assumes "distinct s"
  assumes "length s \<ge> 1"
  assumes "set s \<subseteq> carrier F"
  assumes "\<And>x. x \<in> set s \<Longrightarrow> f x \<in> carrier F"
  shows "interpolate F f s \<in> carrier (poly_ring F) \<and>
         degree (interpolate F f s) < length s \<and>
    (\<forall>x' \<in> set s. ring.eval F (interpolate F f s) x' = f x')"
proof -
  have a: "domain F" using assms(1) using field_def by blast

  have b: "\<And>t. t \<in> set s \<Longrightarrow> lagrange_poly F (removeAll t s) t (f t) \<in> carrier (poly_ring F)" 
    by (metis (no_types, hide_lams) assms(1) assms(4) assms(5) langrange_poly_elim member_remove remove_code(1) subset_iff)
  have e1: "\<forall>x' \<in> set s. ring.eval F (interpolate F f s) x' = f x'"
  proof
    fix x'
    assume d:"x' \<in> set s"
    hence c:"x' \<in> carrier F" 
      using assms(4) by blast
    have "ring.eval F (interpolate F f s) x' = sum_ring F (map (\<lambda>t. ring.eval F t x') (map (\<lambda>t. (lagrange_poly F (removeAll t s) t (f t))) s))"
      apply (simp only:interpolate.simps)
      apply (rule sum_ring_comm_1)
        apply (simp add: a c)+
      using b by blast
    hence d2:"ring.eval F (interpolate F f s) x' = sum_ring F (map (\<lambda>t. ring.eval F (lagrange_poly F (removeAll t s) t (f t)) x') s)"
      by (simp, meson comp_apply)
    have "\<And>t. t \<in> set s \<Longrightarrow> ring.eval F (lagrange_poly F (removeAll t s) t (f t)) x' = (if t = x' then f t else \<zero>\<^bsub>F\<^esub>)"
      by (metis (no_types, lifting) assms(1) assms(4) assms(5) d langrange_poly_elim member_remove remove_code(1) subset_iff)
    hence d1:"map (\<lambda>t. ring.eval F (lagrange_poly F (removeAll t s) t (f t)) x') s = map (\<lambda>t. if t = x' then f t else \<zero>\<^bsub>F\<^esub>) s"
      by simp
    have "sum_ring F (map (\<lambda>t. if t = x' then f t else \<zero>\<^bsub>F\<^esub>) s) = (if x' \<in> set s then f x' else \<zero>\<^bsub>F\<^esub>)"
      using assms a apply (induction s, simp, simp) 
      using field.is_ring ring.ring_simprules(15) ring.ring_simprules(2) ring.ring_simprules(8) not_less_eq_eq by fastforce
    thus "ring.eval F (interpolate F f s) x' = f x'" using d1 d2 d by presburger
  qed
  have e3: "interpolate F f s \<in> carrier (poly_ring F)" apply simp using b sum_ring_elem 
    by (metis (no_types, lifting) a assms(1) domain.univ_poly_is_ring field.is_ring imageE ring.carrier_is_subring set_map subsetI)
  have "\<And>t. t \<in> set s \<Longrightarrow> degree (lagrange_poly F (removeAll t s) t (f t)) < length s"
    by (metis (no_types, hide_lams) assms(1) assms(4) assms(5) dual_order.strict_trans2 langrange_poly_elim length_removeAll_less member_remove remove_code(1) subset_iff)
  hence e2: "degree (interpolate F f s) < length s" apply (simp only:interpolate.simps)
    apply (rule sum_ring_degree_1)
    using a apply blast
    using assms apply blast
    using b by auto
  thus ?thesis using b e1 e2 e3 by blast
qed

end