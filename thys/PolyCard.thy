theory PolyCard
  imports Main "HOL-Algebra.Polynomials" "HOL-Algebra.Polynomial_Divisibility"
begin

(* Set of polynomials with a maximal degree *)
definition bounded_degree_polynomials where "bounded_degree_polynomials F n = {x. x \<in> carrier (poly_ring F) \<and> degree x < n}"

lemma fin_degree_bounded:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "finite (bounded_degree_polynomials F n)"
proof -
  have b: "bounded_degree_polynomials F n = {p. polynomial \<^bsub>F\<^esub> (carrier F) p \<and> degree p < n}"
    apply(rule order_antisym, rule subsetI)
    using assms(1) by (simp add: bounded_degree_polynomials_def univ_poly_carrier)+
  have c: "bounded_degree_polynomials F n \<subseteq> {[]} \<union> {p. set p \<subseteq> carrier F \<and> length p -1 < n}"
    apply (simp add: b polynomial_def subset_eq)
    by meson
  have d: "bounded_degree_polynomials F n \<subseteq> {[]} \<union> {p. set p \<subseteq> carrier F \<and> length p \<le> n}"
    using c  Suc_diff_Suc by auto
  thus "finite (bounded_degree_polynomials F n)" apply (rule finite_subset)
    apply (rule finite_UnI)
    using assms(2) finite_lists_length_le by auto
qed

lemma fin_fixed_degree:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "finite {p. p \<in> carrier (poly_ring F) \<and> degree p = n}"
proof -
  have "{p. p \<in> carrier (poly_ring F) \<and> degree p = n} \<subseteq> bounded_degree_polynomials F (Suc n)"
    by (rule subsetI, simp add:bounded_degree_polynomials_def)
  then show ?thesis
  using fin_degree_bounded assms rev_finite_subset by blast
qed

lemma zero_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card {p. p \<in> carrier (poly_ring F) \<and> degree p = 0} = card (carrier F)"
proof -
  define A where "A = {p. p \<in> (carrier (poly_ring F)) \<and> degree p = 0}"
  have b:"A = {p. polynomial\<^bsub>F\<^esub> (carrier F) p \<and> degree p = 0}"
    apply(rule order_antisym, rule subsetI)
    using A_def assms(1) by (simp add: univ_poly_carrier)+
  have c:"A = {[]} \<union> {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = 1}"
    apply(rule order_antisym, rule subsetI)
    apply(simp add:b polynomial_def)
    apply (meson bot_nat_0.extremum_uniqueI le_SucE length_0_conv)
    apply (rule subsetI)
    apply (simp add:b polynomial_def)
    by fastforce
  have "finite {[]}" by simp
  moreover 
  have "finite {p. set p \<subseteq> carrier F \<and> length p = 1}" using assms(2) finite_lists_length_eq by auto
  hence "finite {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = 1}"
    by (simp add: Collect_mono rev_finite_subset)
  ultimately have d:"card A = card {[]} + card {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = 1}"
    by (simp add:c card_Un_disjoint) 
  have "{p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = 1} = (\<lambda>x. x#[]) ` (carrier F -{ \<zero>\<^bsub>F\<^esub>})"
    apply (rule order_antisym, rule subsetI, simp add:length_Suc_conv, force)
    by (rule subsetI,simp add:length_Suc_conv, force) 
  moreover have "inj_on (\<lambda>x. x#[]) (carrier F -{ \<zero>\<^bsub>F\<^esub>})"
    using inj_on_def by blast
  ultimately have 
    e:"card {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = 1} = card (carrier F -{ \<zero>\<^bsub>F\<^esub>})"
    by (simp add: card_image)
  hence "card A = card {[]} + card (carrier F -{ \<zero>\<^bsub>F\<^esub>})"
    using d e by auto
  hence "card A = card (carrier F)" 
    using  card_Suc_Diff1 ring.ring_simprules(2) assms(1) assms(2) by fastforce
  thus ?thesis by (simp add: A_def) 
qed

lemma fixed_degree_polynomials_count_gr_0:
  assumes "ring F"
  assumes "n \<ge> 1"
  assumes "finite (carrier F)"
  shows "card ({p. p \<in> carrier (poly_ring F) \<and> degree p = n}) = (card (carrier F) - 1) * (card (carrier F) ^ n)"
proof -
  define A where "A = {p. p \<in> (carrier (poly_ring F)) \<and> degree p = n}"
  have b:"A = {p. polynomial\<^bsub>F\<^esub> (carrier F) p \<and> degree p = n}"
    apply(rule order_antisym, rule subsetI)
    using A_def assms(1) by (simp add: univ_poly_carrier)+
  have c:"A = {p. set p \<subseteq> carrier F \<and> hd p \<noteq> \<zero>\<^bsub>F\<^esub> \<and> length p = Suc n}"
    apply(rule order_antisym, rule subsetI)
    apply(simp add:b polynomial_def)
     apply (metis assms(2) One_nat_def Suc_pred diff_is_0_eq' length_greater_0_conv list.size(3) not_one_le_zero zero_le_one)
    apply (rule subsetI)
    by (simp add:b polynomial_def)
  have d:"A = {p. \<exists>u v. p=u#v \<and> set v \<subseteq> carrier F \<and> u \<in> carrier F - {\<zero>\<^bsub>F\<^esub>} \<and> length v = n}"
    apply(rule order_antisym, rule subsetI)
    apply (simp add:c)
    apply (metis Suc_length_conv list.sel(1) list.set_intros(1) set_subset_Cons subset_code(1))
    apply (rule subsetI, simp add:c)
    by force
  define B where "B = {p. set p \<subseteq> carrier F \<and> length p = n}"
  have "A = (\<lambda>(u,v). u # v) ` ((carrier F -  {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    using d B_def by auto
  moreover have "inj_on (\<lambda>(u,v). u # v) ((carrier F -  {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    by (auto intro!: inj_onI) 
  ultimately have "card A = card ((carrier F - {\<zero>\<^bsub>F\<^esub>}) \<times> B)"
    using card_image by meson
  moreover have "card B = (card (carrier F) ^ n)" using B_def
    using card_lists_length_eq assms(3) by blast
  ultimately have "card A = card (carrier F - {\<zero>\<^bsub>F\<^esub>}) * (card (carrier F) ^ n)"
    by (simp add: card_cartesian_product)
  moreover have "card (carrier F - {\<zero>\<^bsub>F\<^esub>}) = card (carrier F) - 1" 
    by (meson assms(1) assms(3) card_Diff_singleton ring.ring_simprules(2))
  ultimately show "card ({p. p \<in> carrier (poly_ring F) \<and> degree p = n}) = (card (carrier F) - 1) * (card (carrier F) ^ n)" using A_def by simp
qed

lemma fixed_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card ({p. p \<in> carrier (poly_ring F) \<and> degree p = n}) = (
    if n \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ n) else card (carrier F))"
proof -
  have a:"\<not> 1 \<le> n \<Longrightarrow> n = 0" by linarith
  show ?thesis 
    apply (cases "n\<ge>1")
    using fixed_degree_polynomials_count_gr_0 assms apply auto[1]
    using zero_degree_polynomials_count assms a by fastforce
qed

lemma bounded_degree_polynomials_count:
  assumes "ring F"
  assumes "finite (carrier F)"
  shows "card (bounded_degree_polynomials F (Suc n)) = card (carrier F) ^ (Suc n)"
proof -
  have a: "bounded_degree_polynomials F (Suc n) = (\<Union> m < (Suc n). {p.  p \<in> carrier (poly_ring F) \<and> degree p = m})"
    apply (simp only: bounded_degree_polynomials_def) by blast
  have "card (bounded_degree_polynomials F (Suc n)) = (\<Sum> m < (Suc n). card {p.  p \<in> carrier (poly_ring F) \<and> degree p = m})"
    apply (simp only:a)
    apply(rule card_UN_disjoint)
      apply blast
    using fin_fixed_degree assms apply blast
    by blast
  hence "card (bounded_degree_polynomials F (Suc n)) = (\<Sum> m < (Suc n). if m \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ m) else card (carrier F))"
    using fixed_degree_polynomials_count assms by fastforce
  moreover have "(\<Sum> m < (Suc n). if m \<ge> 1 then (card (carrier F) - 1) * (card (carrier F) ^ m) else card (carrier F)) = (card (carrier F) ^ (Suc n))"
    by (induction n, simp, simp add:mult_eq_if) 
  ultimately show ?thesis by auto
qed

lemma bounded_degree_polynomials_count_1:
  assumes "ring F"
  assumes "finite (carrier F)"
  assumes "n > 0"
  shows "card (bounded_degree_polynomials F n) = card (carrier F) ^ n"
  sorryc
end