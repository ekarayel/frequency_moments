theory PolyBijection
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials" LagrangeInterpolation
  PolyCard
begin

lemma bounded_degree_polynomials_def_alt:
  "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> (length x \<le> n )}"
  apply (simp add:bounded_degree_polynomials_def)
  apply (rule order_antisym, rule subsetI, simp) 
  apply (metis Suc_leI Suc_pred length_greater_0_conv list.size(3) zero_le)
  apply (rule subsetI, simp) 
  by (metis diff_Suc_less le_neq_implies_less length_greater_0_conv less_imp_diff_less)

text \<open>
  If a function from A to B is surjective and card A = card B 
  then the function must also be injective. 

  We can extend that principle, i.e., if there are at least n distinct elements of A
  mapping to each element in B. And card B = n * card A. Then, it must be that
  there are always exactly n elements mapping to each element.
\<close>

lemma sum_tight:
  assumes "finite B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> n \<le> (f x::nat)"
  assumes "sum f B \<le> n * card B"
  shows "\<And>x. x \<in> B \<Longrightarrow> f x = n"
proof (rule ccontr)
  fix x
  assume a:"x \<in> B"
  assume "f x \<noteq> n"
  hence d:"f x > n" using assms(2) a le_neq_implies_less by blast
  define B' where "B' = B - {x}"
  hence b:"B = insert x B'" using a B'_def by auto
  have c:"x \<notin> B'" using B'_def by auto
  moreover have "finite B'" using assms(1) B'_def by auto
  ultimately have "sum f B = sum f B' + f x" by (simp add:b)
  moreover have "B' \<subseteq> B" using B'_def by auto
  hence "sum f B' \<ge> n * card B'" using assms(2) 
    by (metis (no_types, hide_lams) id_apply mult.commute of_nat_eq_id subset_iff sum_bounded_below)
  moreover have "card B = Suc (card B')" using b c  assms(1) by auto
  ultimately have "n * (Suc (card B')) \<ge> n * card B' + f x" using assms(3) by auto
  thus "False" using d by auto
qed

lemma generalized_inj_if_surj:
  assumes "finite B"
  assumes "finite A"
  assumes "\<And> y. y \<in> B \<Longrightarrow> card (f -` {y} \<inter> A) \<ge> n"
  assumes "card A = n * card B"
  shows "\<And>y. y \<in> B \<Longrightarrow> card (f -` {y} \<inter> A) = n"
proof -
  have "(\<Union> y\<in> B. (f -` {y} \<inter> A)) \<subseteq> A" by blast
  moreover have "sum (\<lambda>y. card (f -` {y} \<inter> A)) B = card (\<Union> y\<in> B. (f -` {y} \<inter> A))"
    apply (rule card_UN_disjoint[symmetric])
    by ((simp add:assms)+, fastforce)
  ultimately have "sum (\<lambda>y. card (f -` {y} \<inter> A)) B \<le>  n * card B"
    by (simp add: assms(2) card_mono assms(4)[symmetric])
  thus "\<And>y. y \<in> B \<Longrightarrow> (\<lambda>y. card (f -` {y} \<inter> A)) y = n"
    using sum_tight[where f ="(\<lambda>y. card (f -` {y} \<inter> A))"] assms(3) assms(1) by auto
qed

lemma min_count_interpolating_polynomials:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  shows "f ` K \<subseteq> carrier F \<Longrightarrow> card (carrier F)^n \<le> card {\<omega> \<in> bounded_degree_polynomials F (card K+n). \<forall>x \<in> K. ring.eval F \<omega> x = f x}" (is "_ \<Longrightarrow> ?A n \<le> card (?B f n)")
proof (induction n arbitrary: f)
  case 0
  have a:"ring F" using assms(1) by (simp add:field_def domain_def cring_def)
  have "finite K" using assms(2) assms(3) finite_subset by auto
  then obtain xs where xs_def:"set xs = K" and xs_distinct:"distinct xs" using finite_distinct_list by blast
  have "set xs \<subseteq> carrier F" using xs_def assms(3) by auto
  moreover have "\<And>x. x \<in> set xs \<Longrightarrow> f x \<in> carrier F" using xs_def "0.prems" by blast
  ultimately have "interpolate F f xs \<in> {\<omega> \<in> bounded_degree_polynomials F (length xs). \<forall>x \<in> K. ring.eval F \<omega> x = f x}" 
    apply (simp add:bounded_degree_polynomials_def_alt del:interpolate.simps)
    using interpolate_len assms(1) 0 xs_distinct by (metis xs_def)
  moreover have "finite  {\<omega> \<in> bounded_degree_polynomials F (length xs). \<forall>x \<in> K. ring.eval F \<omega> x = f x}"
    by (simp add:a fin_degree_bounded assms(2))
  ultimately have "1 \<le> card {\<omega> \<in> bounded_degree_polynomials F (length xs). \<forall>x \<in> K. ring.eval F \<omega> x = f x}"
    by (metis (no_types, lifting) One_nat_def Suc_leI card_eq_0_iff empty_iff neq0_conv)
  moreover have "length xs = card K"
    using xs_def xs_distinct by (metis distinct_card)
  moreover have "(card (carrier F))^0 = 1" by simp
  ultimately show ?case by force
next
  case (Suc n)
  have j:"ring F" using assms(1) by (simp add:field_def domain_def cring_def)

  interpret field F using assms(1) by blast
  interpret UP: ring "poly_ring F" 
    using carrier_is_subring univ_poly_is_ring by auto
  define group where 
    "group = (\<lambda>l. {\<omega> \<in> bounded_degree_polynomials F (card K+Suc n). (\<forall>x \<in> K. eval \<omega> x = f x) \<and> coeff \<omega> (card K + n) = l})"
  have "\<And>x. x \<in> carrier (poly_ring F) \<Longrightarrow> set x \<subseteq> carrier F" 
    by (meson field.is_ring local.field_axioms ring.carrier_is_subring ring.polynomial_in_carrier univ_poly_carrier)
  hence coeff_hom: "\<And>x y n. x \<in> carrier (poly_ring F) \<Longrightarrow> y \<in> carrier (poly_ring F) \<Longrightarrow> coeff (x \<oplus>\<^bsub>poly_ring F\<^esub> y) n = coeff x n \<oplus>\<^bsub>F\<^esub> coeff y n"
    by (metis  poly_add_coeff  univ_poly_add)
  have eval_hom: "\<And>x y n. n \<in> K \<Longrightarrow> x \<in> carrier (poly_ring F) \<Longrightarrow> y \<in> carrier (poly_ring F) \<Longrightarrow> eval (x \<oplus>\<^bsub>poly_ring F\<^esub> y) n = eval x n \<oplus>\<^bsub>F\<^esub> eval y n"
    by (meson assms(3) eval_simp domain_axioms subset_iff)

  have "\<And>l. l \<in> carrier F \<Longrightarrow> card (group l) \<ge> (card (carrier F))^n"
  proof -
    fix l
    assume f:"l \<in> carrier F"
    define lp where "lp = normalize (monom l (card K + n))"
    define f' where "f' = (\<lambda>x. f x \<ominus>\<^bsub>F\<^esub> l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n))"
    define S where "S = {\<omega> \<in> bounded_degree_polynomials F (card K+n). (\<forall>x \<in> K. eval \<omega> x = f' x)}"

    define m where "m = (\<lambda>\<omega>. \<omega> \<oplus>\<^bsub>poly_ring F\<^esub> lp)"
    have a:"lp \<in> carrier (poly_ring F)" using f apply (simp add:lp_def) 
      by (meson field.is_ring local.field_axioms ring.monom_in_carrier ring.normalize_gives_polynomial univ_poly_carrier)
    have b:"degree (lp) < Suc (card K + n)" apply (simp add:lp_def monom_def) 
      by (metis le_imp_less_Suc length_replicate less_imp_diff_less normalize_length_le) 
    have c:"coeff (lp) (card K + n) = l" apply (simp add:lp_def)
      using monom_coeff normalize_coeff by presburger
    have d:"\<And>x. x \<in> carrier (poly_ring F) \<Longrightarrow> degree x < card K + n \<Longrightarrow> coeff x (card K + n) = \<zero>\<^bsub>F\<^esub>"
      using coeff_degree by blast
    have e:"\<And>x. x \<in> K \<Longrightarrow> eval lp x = l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n)"
      apply (simp add:lp_def) using assms(3) eval_monom f subsetD eval_normalize monom_in_carrier by auto
    have i:"\<And>x. x \<in> K \<Longrightarrow> l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n) \<in> carrier F" using f assms(3) 
      by (meson m_closed nat_pow_closed subset_iff)
    moreover have "\<And>x y z. x \<in> carrier F \<Longrightarrow> y \<in> carrier F \<Longrightarrow> x  \<ominus>\<^bsub>F\<^esub> y  \<oplus>\<^bsub>F\<^esub> y = x"
      by (metis a_minus_def add.inv_solve_right minus_closed)
    ultimately have g:"\<And>x. x \<in> K \<Longrightarrow> f x = f' x \<oplus>\<^bsub>F\<^esub> l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n)"
      using Suc(2) apply (simp add:f'_def) by (metis image_eqI subset_iff)
    have h:"m ` S \<subseteq> group l"
      apply (rule image_subsetI, simp add:m_def S_def degree_def' group_def bounded_degree_polynomials_def)
      apply (rule conjI, meson a UP.add.m_closed)
      apply (rule conjI) using a b One_nat_def field_def less_Suc_eq local.field_axioms poly_sum_degree_le 
      apply (metis length_0_conv zero_diff zero_less_Suc)
      apply (rule conjI) using a apply (simp add:eval_hom g e)
      using a f assms(3) coeff_hom c d e 
      by (metis One_nat_def coeff.simps(1) l_zero) 
    have "f' ` K \<subseteq> carrier F" apply (rule subsetI, simp add:f'_def) 
      using Suc.prems i by blast
    hence "card (carrier F)^n \<le> card S" using Suc(1) S_def by blast
    moreover have "finite (group l)" 
      by (simp add: fin_degree_bounded assms(2) j group_def)
    hence "card (m ` S) \<le> card (group l)" using h card_mono by blast
    moreover have "inj_on m S"
      by (simp add:m_def S_def a inj_on_def bounded_degree_polynomials_def)
    hence  "card S = card (m ` S)" by (simp add: card_image)
    ultimately show "card (carrier F)^n \<le> card (group l)" by linarith
  qed
  hence "sum (\<lambda>l. (card (group l))) (carrier F) \<ge> card (carrier F) * (card (carrier F))^n"
    by (metis sum_bounded_below id_apply of_nat_eq_id) 
  hence "sum (\<lambda>l. (card (group l))) (carrier F) \<ge> (card (carrier F))^(Suc n)"
    by simp
  moreover have "sum (\<lambda>l. card (group l)) (carrier F) = card (\<Union>l \<in> carrier F. group l)"
    apply (rule card_UN_disjoint[symmetric])
      apply (simp add:assms(2))
    apply (simp add:fin_degree_bounded j group_def assms)
    by (simp add:group_def, fastforce)
  ultimately have "card (\<Union>l \<in> carrier F. group l) \<ge> (card (carrier F))^(Suc n)"
    by presburger
  moreover have "?B f (Suc n) = (\<Union>l \<in> carrier F. group l)"
    apply (rule order_antisym)
     apply (rule subsetI, simp add:bounded_degree_polynomials_def group_def)
    apply (metis coeff_in_carrier field.is_ring local.field_axioms ring.carrier_is_subring ring.polynomial_in_carrier univ_poly_carrier)
    by (rule subsetI, simp add:bounded_degree_polynomials_def group_def)
  ultimately show ?case by presburger
qed

lemma poly_minus_len:
  assumes "domain F"
  assumes "x \<in> carrier (poly_ring F)"
  assumes "length x \<le> n"
  assumes "y \<in> carrier (poly_ring F)"
  assumes "length y \<le> n"
  shows "length (x \<ominus>\<^bsub>poly_ring F\<^esub> y) \<le> n"
  sorry

lemma count_interpolating_polynomials:
  assumes "field F"
  assumes "finite (carrier F)"
  assumes "K \<subseteq> carrier F"
  shows "f ` K \<subseteq> carrier F \<Longrightarrow> card (carrier F)^n = card {\<omega> \<in> bounded_degree_polynomials F (card K+n). \<forall>x \<in> K. ring.eval F \<omega> x = f x}" (is "_ \<Longrightarrow> ?A n = card (?B f n)")
proof (induction n arbitrary: f)
  case 0
  have a:"ring F" using assms(1) by (simp add:field_def domain_def cring_def)
  have "finite K" using assms(2) assms(3) finite_subset by auto
  then obtain xs where xs_def:"set xs = K" and xs_distinct:"distinct xs" using finite_distinct_list by blast
  have "set xs \<subseteq> carrier F" using xs_def assms(3) by auto
  moreover have "\<And>x. x \<in> set xs \<Longrightarrow> f x \<in> carrier F" using xs_def "0.prems" by blast
  ultimately have "{interpolate F f xs} = {\<omega> \<in> bounded_degree_polynomials F (length xs). \<forall>x \<in> K. ring.eval F \<omega> x = f x}" 
    sorry
  moreover have "finite  {\<omega> \<in> bounded_degree_polynomials F (length xs). \<forall>x \<in> K. ring.eval F \<omega> x = f x}"
    by (simp add:a fin_degree_bounded assms(2))
  ultimately have "1 = card {\<omega> \<in> bounded_degree_polynomials F (length xs). \<forall>x \<in> K. ring.eval F \<omega> x = f x}"
    by (metis One_nat_def card_1_singleton_iff)
  moreover have "length xs = card K"
    using xs_def xs_distinct by (metis distinct_card)
  moreover have "(card (carrier F))^0 = 1" by simp
  ultimately show ?case by force
next
  case (Suc n)
  have j:"ring F" using assms(1) by (simp add:field_def domain_def cring_def)

  interpret field F using assms(1) by blast
  interpret UP: ring "poly_ring F" 
    using carrier_is_subring univ_poly_is_ring by auto
  define group where 
    "group = (\<lambda>l. {\<omega> \<in> bounded_degree_polynomials F (card K+Suc n). (\<forall>x \<in> K. eval \<omega> x = f x) \<and> coeff \<omega> (card K + n) = l})"
  have "\<And>x. x \<in> carrier (poly_ring F) \<Longrightarrow> set x \<subseteq> carrier F" 
    by (meson field.is_ring local.field_axioms ring.carrier_is_subring ring.polynomial_in_carrier univ_poly_carrier)
  hence coeff_hom: "\<And>x y n. x \<in> carrier (poly_ring F) \<Longrightarrow> y \<in> carrier (poly_ring F) \<Longrightarrow> coeff (x \<oplus>\<^bsub>poly_ring F\<^esub> y) n = coeff x n \<oplus>\<^bsub>F\<^esub> coeff y n"
    by (metis  poly_add_coeff  univ_poly_add)
  have eval_hom: "\<And>x y n. n \<in> K \<Longrightarrow> x \<in> carrier (poly_ring F) \<Longrightarrow> y \<in> carrier (poly_ring F) \<Longrightarrow> eval (x \<oplus>\<^bsub>poly_ring F\<^esub> y) n = eval x n \<oplus>\<^bsub>F\<^esub> eval y n"
    by (meson assms(3) eval_simp domain_axioms subset_iff)

  have "\<And>l. l \<in> carrier F \<Longrightarrow> card (group l) \<ge> (card (carrier F))^n"
  proof -
    fix l
    assume f:"l \<in> carrier F"
    define lp where "lp = normalize (monom l (card K + n))"
    define f' where "f' = (\<lambda>x. f x \<ominus>\<^bsub>F\<^esub> l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n))"
    define S where "S = {\<omega> \<in> bounded_degree_polynomials F (card K+n). (\<forall>x \<in> K. eval \<omega> x = f' x)}"

    define m where "m = (\<lambda>\<omega>. \<omega> \<oplus>\<^bsub>poly_ring F\<^esub> lp)"

    have a:"lp \<in> carrier (poly_ring F)" using f apply (simp add:lp_def)
      by (meson field.is_ring local.field_axioms ring.monom_in_carrier ring.normalize_gives_polynomial univ_poly_carrier)
    have b:"degree (lp) < Suc (card K + n)" apply (simp add:lp_def monom_def) 
      by (metis le_imp_less_Suc length_replicate less_imp_diff_less normalize_length_le) 
    have c:"coeff (lp) (card K + n) = l" apply (simp add:lp_def)
      using monom_coeff normalize_coeff by presburger
    have d:"\<And>x. x \<in> carrier (poly_ring F) \<Longrightarrow> degree x < card K + n \<Longrightarrow> coeff x (card K + n) = \<zero>\<^bsub>F\<^esub>"
      using coeff_degree by blast
    have e:"\<And>x. x \<in> K \<Longrightarrow> eval lp x = l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n)"
      apply (simp add:lp_def) using assms(3) eval_monom f subsetD eval_normalize monom_in_carrier by auto
    have i:"\<And>x. x \<in> K \<Longrightarrow> l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n) \<in> carrier F" using f assms(3) 
      by (meson m_closed nat_pow_closed subset_iff)
    moreover have "\<And>x y z. x \<in> carrier F \<Longrightarrow> y \<in> carrier F \<Longrightarrow> x \<ominus>\<^bsub>F\<^esub> y \<oplus>\<^bsub>F\<^esub> y = x"
      by (metis a_minus_def add.inv_solve_right minus_closed)
    ultimately have g:"\<And>x. x \<in> K \<Longrightarrow> f x = f' x \<oplus>\<^bsub>F\<^esub> l \<otimes>\<^bsub>F\<^esub> x [^]\<^bsub>F\<^esub> (card K + n)"
      using Suc(2) apply (simp add:f'_def) by (metis image_eqI subset_iff)
    have h:"m ` S \<subseteq> group l"
      apply (rule image_subsetI, simp add:m_def S_def degree_def' group_def bounded_degree_polynomials_def)
      apply (rule conjI, meson a UP.add.m_closed)
      apply (rule conjI) using a b One_nat_def field_def less_Suc_eq local.field_axioms poly_sum_degree_le 
      apply (metis length_0_conv zero_diff zero_less_Suc)
      apply (rule conjI) using a apply (simp add:eval_hom g e)
      using a f assms(3) coeff_hom c d e 
      by (metis One_nat_def coeff.simps(1) l_zero) 
    have "f' ` K \<subseteq> carrier F" apply (rule subsetI, simp add:f'_def)
      using Suc.prems i by blast
    hence "card (carrier F)^n \<le> card S" using Suc(1) S_def by blast
    moreover have "finite (group l)" 
      by (simp add: fin_degree_bounded assms(2) j group_def)
    hence "card (m ` S) \<le> card (group l)" using h card_mono by blast
    moreover have "inj_on m S"
      by (simp add:m_def S_def a inj_on_def bounded_degree_polynomials_def)
    hence  "card S = card (m ` S)" by (simp add: card_image)
    ultimately show "card (carrier F)^n \<le> card (group l)" by linarith
  qed
  hence "sum (\<lambda>l. (card (group l))) (carrier F) \<ge> card (carrier F) * (card (carrier F))^n"
    by (metis sum_bounded_below id_apply of_nat_eq_id) 
  hence "sum (\<lambda>l. (card (group l))) (carrier F) \<ge> (card (carrier F))^(Suc n)"
    by simp
  moreover have "sum (\<lambda>l. card (group l)) (carrier F) = card (\<Union>l \<in> carrier F. group l)"
    apply (rule card_UN_disjoint[symmetric])
      apply (simp add:assms(2))
    apply (simp add:fin_degree_bounded j group_def assms)
    by (simp add:group_def, fastforce)
  ultimately have "card (\<Union>l \<in> carrier F. group l) \<ge> (card (carrier F))^(Suc n)"
    by presburger
  moreover have "?B f (Suc n) = (\<Union>l \<in> carrier F. group l)"
    apply (rule order_antisym)
     apply (rule subsetI, simp add:bounded_degree_polynomials_def group_def)
    apply (metis coeff_in_carrier field.is_ring local.field_axioms ring.carrier_is_subring ring.polynomial_in_carrier univ_poly_carrier)
    by (rule subsetI, simp add:bounded_degree_polynomials_def group_def)
  ultimately show ?case by presburger
qed

end