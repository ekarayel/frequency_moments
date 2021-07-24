section \<open>Counting Interpolation Polynomials\<close>

theory PolynomialCounting
  imports Main CountMaps "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials"
  PolyCard
begin

text \<open>It is well known that over any field there is exactly one polynomial with degree at most
@{term "k-(1::nat)"} interpolating  @{term "k"} points. That there is never more that one such
polynomial follow from the fact that a polynomial of degree @{term "k-(1::nat)"} cannot have more
than @{term "k-(1::nat)"} roots. This is already shown in HOL-Algebra in
@{thm [source] field.size_roots_le_degree}. Existence is usually shown using Lagrange interpolation.

In the case of finite fields it is actually only necessary to show either that there is at most one
such polynomial or at least one - because a function whose domain and co-domain has the same finite
cardinality is injective if and only if it is surjective.

Here we are interested in a more generic result (over finite fields). We also want to count the 
number of polynomials of degree @{term "k+n-(1::nat)"} interpolating @{term "k"} points for
non-negative @{term "n"}. As it turns out there are @{term "card (carrier F)^n"} such polynomials.
The trick is to observe that, for a given fix on the coefficients of order @{term "k"} to 
@{term "k+n-(1::nat)"} and the values at @{term "k"} points we have at most one fitting polynomial.

An alternative way of stating the above result is that there is bijection between the polynomials
of degree @{term "n+k-(1::nat)"} and the product space $F^k \times F^n$ where the first component is
the evaluation of the polynomials at @{term "k"} distinct points and the second component are the
coefficients of order at least @{term "k"}.\<close>

definition split_poly where "split_poly F K p = 
  (\<lambda>k. if k \<in> K then Some (ring.eval F p k) else None, \<lambda>k. ring.coeff F p (k+card K))"

text \<open>We call the bijection @{term "split_poly"} it returns the evaluation of the polynomial
at the points in @{term "K"} and the coefficients of order at least @{term "card K"}.

We first show that its image is a subset of the product space mentioned above, after that we will
show that  @{term "split_poly"} is injective and finally we will be able to show that its image
is exactly that product space using cardinalities.\<close>

lemma split_poly_image:
  assumes "field F"
  assumes "K \<subseteq> carrier F"
  shows "split_poly F K ` bounded_degree_polynomials F (card K + n) \<subseteq>
        {f. dom f = K \<and> ran f \<subseteq> carrier F} \<times> {f. range f \<subseteq> carrier F \<and> (\<forall>k \<ge> n. f k = \<zero>\<^bsub>F\<^esub>)}" 
  apply (rule image_subsetI)
  apply (simp add:split_poly_def dom_def ran_def bounded_degree_polynomials_length)
  apply (rule conjI, rule subsetI, simp)
   apply (metis assms(1) assms(2) field.is_ring mem_Collect_eq partial_object.select_convs(1) 
          ring.carrier_is_subring ring.eval_in_carrier ring.polynomial_in_carrier subset_iff 
          univ_poly_def) 
  apply (rule conjI, rule subsetI) 
   apply (metis (no_types, lifting) assms(1) field.is_ring imageE mem_Collect_eq 
        partial_object.select_convs(1) ring.carrier_is_subring ring.coeff_in_carrier
        ring.polynomial_in_carrier univ_poly_def)
  by (simp add: assms(1) field.is_ring ring.coeff_length)

lemma poly_neg_coeff:
  assumes "domain F"
  assumes "x \<in> carrier (poly_ring F)"
  shows "ring.coeff F (\<ominus>\<^bsub>poly_ring F\<^esub> x) k = \<ominus>\<^bsub>F\<^esub> ring.coeff F x k"
proof -
  interpret ring "poly_ring F"
    using assms cring_def domain.univ_poly_is_ring domain_def ring.carrier_is_subring by blast
  have "\<zero>\<^bsub>poly_ring F\<^esub> = x \<ominus>\<^bsub>poly_ring F\<^esub> x" by (metis assms(2) r_right_minus_eq)
  hence "ring.coeff F (\<zero>\<^bsub>poly_ring F\<^esub>) k = ring.coeff F x k \<oplus>\<^bsub>F\<^esub> ring.coeff F (\<ominus>\<^bsub>poly_ring F\<^esub> x) k"
    by (metis assms cring_def domain.univ_poly_a_inv_length domain_def dual_order.refl minus_eq 
        ring.carrier_is_subring ring.poly_add_coeff_aux univ_poly_add)
  thus ?thesis 
    by (metis abelian_group.minus_equality add.l_inv_ex assms(1) assms(2) cring_def 
        domain.axioms(1) is_abelian_group mem_Collect_eq partial_object.select_convs(1) 
        ring.carrier_is_subring ring.coeff.simps(1) ring.coeff_in_carrier ring.polynomial_in_carrier
        ring.ring_simprules(20) ring_def univ_poly_def univ_poly_zero)
qed

lemma poly_substract_coeff:
  assumes "domain F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "y \<in> carrier (poly_ring F)"
  shows "ring.coeff F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) k = ring.coeff F x k \<ominus>\<^bsub>F\<^esub> ring.coeff F y k"
  apply (simp add:a_minus_def poly_neg_coeff[symmetric])
  using assms ring.poly_add_coeff 
  by (metis abelian_group.a_inv_closed cring_def domain.univ_poly_is_abelian_group domain_def 
      poly_neg_coeff ring.carrier_is_subring ring.polynomial_incl univ_poly_add univ_poly_carrier)

lemma poly_substract_eval:
  assumes "domain F"
  assumes "i \<in> carrier F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "y \<in> carrier (poly_ring F)"
  shows "ring.eval F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) i = ring.eval F x i \<ominus>\<^bsub>F\<^esub> ring.eval F y i"
proof -
  have "subring (carrier F) F" 
    using assms(1) cring_def domain_def ring.carrier_is_subring by blast
  hence "ring_hom_cring (poly_ring F) F (\<lambda>p. (ring.eval F p) i)"
    by (simp add: assms(1) assms(2) domain.eval_cring_hom)
  then show ?thesis by (meson  ring_hom_cring.hom_sub assms(3) assms(4))
qed

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
  assumes "finite K"
  assumes "K \<subseteq> carrier F"
  shows "inj_on (split_poly F K) (carrier (poly_ring F))"
proof
  have ring_F: "ring F" using assms(1) field.is_ring by blast
  have domain_F: "domain F" using assms(1) field_def by blast
  fix x
  fix y
  assume a1:"x \<in> carrier (poly_ring F)"
  assume a2:"y \<in> carrier (poly_ring F)"
  assume a3:"split_poly F K x = split_poly F K y"

  have x_y_carrier: "x \<ominus>\<^bsub>poly_ring F\<^esub> y \<in> carrier (poly_ring F)" using a1 a2
    by (simp add: assms(1) domain.univ_poly_is_ring field.axioms(1) ring.carrier_is_subring 
        ring.ring_simprules(4) ring_F)
  have "\<And>k. ring.coeff F x (k+card K) = ring.coeff F y (k+card K)"
    using a3 apply (simp add:split_poly_def) by meson
  hence "\<And>k. ring.coeff F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) (k+card K) = \<zero>\<^bsub>F\<^esub>"
    apply (simp add:domain_F a1 a2 poly_substract_coeff)
    by (meson a2 ring.carrier_is_subring ring.coeff_in_carrier 
       ring.polynomial_in_carrier ring.r_right_minus_eq ring_F univ_poly_carrier)
  hence "degree (x \<ominus>\<^bsub>poly_ring F\<^esub> y) < card K \<or> (x \<ominus>\<^bsub>poly_ring F\<^esub> y) = \<zero>\<^bsub>poly_ring F\<^esub>"
    by (metis add.commute le_Suc_ex poly_degree_bound_from_coeff x_y_carrier ring_F)
  moreover have "\<And>k. k \<in> K \<Longrightarrow> ring.eval F x k = ring.eval F y k"
    using a3 apply (simp add:split_poly_def) by (meson option.inject)
  hence "\<And>k. k \<in> K \<Longrightarrow> ring.eval F x k \<ominus>\<^bsub>F\<^esub> ring.eval F y k = \<zero>\<^bsub>F\<^esub>"
    by (metis (no_types, hide_lams) a2 assms(3) ring.eval_in_carrier ring.polynomial_incl 
        ring.r_right_minus_eq ring_F subsetD univ_poly_carrier)
  hence "\<And>k. k \<in> K \<Longrightarrow> ring.eval F (x \<ominus>\<^bsub>poly_ring F\<^esub> y) k =  \<zero>\<^bsub>F\<^esub>"
    using domain_F a1 a2 assms(3) poly_substract_eval by (metis (no_types, hide_lams) subsetD)
  ultimately have "x \<ominus>\<^bsub>poly_ring F\<^esub> y = \<zero>\<^bsub>poly_ring F\<^esub>"
    using max_roots x_y_carrier assms by blast
  then show "x = y"
    by (meson assms(1) a1 a2 domain.univ_poly_is_ring field_def ring.carrier_is_subring 
        ring.r_right_minus_eq ring_F)
qed

lemma
  assumes "field F"
  assumes "finite (carrier F)"
  shows 
    poly_count:"card (bounded_degree_polynomials F n) = card (carrier F)^n" (is ?A) and
    finite_poly_count: "finite (bounded_degree_polynomials F n)" (is ?B)
proof -
  have a:"ring F" using assms(1) by (simp add: field.is_ring)
  show ?A using a bounded_degree_polynomials_count assms(2) by blast
  show ?B using a fin_degree_bounded assms(2) by blast
qed

lemma split_poly_surj:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  shows "split_poly F K ` bounded_degree_polynomials F (card K + n) =
        {f. dom f = K \<and> ran f \<subseteq> carrier F} \<times> {f. range f \<subseteq> carrier F \<and> (\<forall>k \<ge> n. f k = \<zero>\<^bsub>F\<^esub>)}" 
      (is "split_poly F K ` ?A = ?B")
proof -
  define M where "M = split_poly F K ` ?A"
  have a:"\<zero>\<^bsub>F\<^esub> \<in> carrier F" using assms(1) 
    by (simp add: field.is_ring ring.ring_simprules(2))
  have b:"finite K" using assms(2) assms(3) finite_subset by blast
  moreover have "?A \<subseteq> carrier (poly_ring F)"
    by (simp add: Collect_mono_iff bounded_degree_polynomials_def)
  ultimately have "inj_on (split_poly F K) ?A" 
    by (meson split_poly_inj assms(1) assms(3) inj_on_subset)
  moreover have "finite ?A" using finite_poly_count assms(2) assms(1) by blast
  ultimately have "card ?A = card M" by (simp add: M_def card_image)
  hence "card M = card (carrier F)^(card K + n)"
    using poly_count assms(2) assms(1) by metis
  moreover have "M \<subseteq> ?B" using split_poly_image M_def assms by blast
  moreover have "card ?B = card (carrier F)^(card K + n)" 
    by (simp add: a assms b card_mostly_constant_maps count_maps power_add card_cartesian_product) 
  moreover have "finite ?B" using assms(2) a b
    by (simp add: finite_mostly_constant_maps finite_set_of_finite_maps)
  ultimately have "M = ?B" by (simp add: card_seteq)
  thus ?thesis using M_def by auto
qed


text \<open>This is like @{thm [source] card_vimage_inj} but supports @{term "inj_on"} instead.\<close>
lemma card_vimage_inj_on:
  assumes "inj_on f B"
  assumes "A \<subseteq> f ` B"
  shows "card (f -` A \<inter> B) = card A"
proof -
  have "A = f ` (f -` A \<inter> B)" using assms(2) by auto
  thus ?thesis using assms card_image 
    by (metis inf_le2 inj_on_subset)
qed

lemma inv_subsetI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B \<Longrightarrow> x \<in> C"
  shows "f -` B \<inter> A \<subseteq> C"
  using assms by force

lemma interpolating_polynomials_count:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  assumes "f ` K \<subseteq> carrier F"
  shows "card {\<omega> \<in> bounded_degree_polynomials F (card K + n). (\<forall>k \<in> K. ring.eval F \<omega> k = f k)} = 
    card (carrier F)^n" 
    (is "card ?A = ?B")
proof -
  define z where "z = (\<lambda>k. if k \<in> K then Some (f k) else None)"
  define M where "M = {f. range f \<subseteq> carrier F \<and> (\<forall>k \<ge> n. f k = \<zero>\<^bsub>F\<^esub>)}"

  have a:"\<zero>\<^bsub>F\<^esub> \<in> carrier F" using assms(1)
    by (simp add: field.is_ring ring.ring_simprules(2))

  have "finite K" using assms(2) assms(3) finite_subset by blast
  hence inj_on_bounded: "inj_on (split_poly F K) (bounded_degree_polynomials F (card K + n))"
    using split_poly_inj assms(1) assms(3) inj_on_subset bounded_degree_polynomials_length 
    by (metis (mono_tags) Collect_subset)
  moreover have "z \<in> {f. dom f = K \<and> ran f \<subseteq> carrier F}" apply (simp add: z_def dom_def ran_def)
    using assms by blast
  hence "{z} \<times> M \<subseteq> split_poly F K ` (bounded_degree_polynomials F (card K + n))"
    apply (simp add: split_poly_surj assms M_def z_def) 
    by fastforce
  ultimately have "card ((split_poly F K -` ({z} \<times> M)) \<inter> bounded_degree_polynomials F (card K + n))
    = card ({z} \<times> M)" by (meson card_vimage_inj_on)
  moreover have "(split_poly F K -` ({z} \<times> M)) \<inter> bounded_degree_polynomials F (card K + n) \<subseteq> ?A"
    apply (rule inv_subsetI)
    apply (simp add:split_poly_def z_def) 
    by (meson option.inject)
  moreover have "finite ?A" by (simp add: finite_poly_count assms)
  ultimately have card_ineq_1: "card ({z} \<times> M) \<le> card ?A" 
    by (metis (mono_tags, lifting) card_mono)

  have "split_poly F K ` ?A \<subseteq> {z} \<times> M"
    apply (rule image_subsetI)
    apply (simp add:split_poly_def z_def M_def)
    apply (rule conjI, fastforce)
    apply (simp add:bounded_degree_polynomials_length)
    apply (rule conjI) 
     apply (meson assms(1) field.is_ring image_subsetI ring.coeff_in_carrier ring.polynomial_incl 
            univ_poly_carrier)
    by (simp add: assms(1) field.is_ring ring.coeff_length)
  moreover have "inj_on (split_poly F K) ?A" using inj_on_subset inj_on_bounded by fastforce
  moreover have "finite ({z} \<times> M)" by (simp add:M_def finite_mostly_constant_maps assms(2) a)
  ultimately have card_ineq_2:"card ?A \<le> card ({z} \<times> M)" by (meson card_inj_on_le)

  have "card ?A = card ({z} \<times> M)" using card_ineq_1 card_ineq_2 by auto
  moreover have "card ({z} \<times> M) =  card (carrier F)^n"
    by (simp add:card_cartesian_product M_def a card_mostly_constant_maps assms(2) )
  ultimately show ?thesis by presburger
qed

end