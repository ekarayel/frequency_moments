theory Field
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials"
  "HOL-Algebra.IntRing"
begin

text \<open>In the following, we show that the factor ring @{term "ZFact p"} for @{term "prime p"} is
a field. Note the bulk of the work has already been done in HOL-Algebra, in particular it is
established that @{term "ZFact p"} is a domain.

However, any domain with a finite carrier is actually already a field. This can be seen by, e.g.,
establishing that multiplication by a non-zero element is an injective map between the elements of
the carrier of the domain. But an injective map between sets of the same non-finite cardinality is
also surjective. Hence we can find the unit element in the image of such a map.

There is also another route to establish this, i.e., by showing that the ideal formed by a prime
is maximal. We choose this route, because we also need the fact that @{term "ZFact p"} is finite
for a further reason: We are planning to show bounds on the space complexity of the data stream
algorithms, for that we need to know how many bits are needed to represent an element of the
factorial ring.\<close>

lemma coset_elim:
  assumes "x \<in> a_rcosets\<^bsub>R\<^esub> I"
  shows "\<exists>y. x = I +>\<^bsub>R\<^esub> y"
  using assms apply (simp add:FactRing_simps) by blast

lemma zfact_find_any_repr:
  assumes "(p :: int) > 1"
  assumes "x \<in> carrier (ZFact p)"
  shows "\<exists>y :: int. x = Idl\<^bsub>\<Z>\<^esub> {p} +>\<^bsub>\<Z>\<^esub> y"
  using assms  apply (simp add:carrier_def ZFact_def FactRing_def) 
  by (metis ZFact_defs(1) ZFact_defs(2) assms(2) coset_elim partial_object.select_convs(1))

lemma zfact_find_canonical_repr:
  assumes "(p :: int) > 1"
  assumes "x \<in> carrier (ZFact p)"
  shows "\<exists>y :: nat. x = Idl\<^bsub>\<Z>\<^esub> {p} +>\<^bsub>\<Z>\<^esub> y \<and> y < p"
proof -
  define I where "I = Idl\<^bsub>\<Z>\<^esub> {p}"
  obtain z where a2: "x = Idl\<^bsub>\<Z>\<^esub> {p} +>\<^bsub>\<Z>\<^esub> z" using zfact_find_any_repr assms by presburger
  define y where "y = z mod p -z"
  hence "y mod p = 0" by (simp add: mod_diff_left_eq)
  hence y_1:"y \<in> I" using I_def 
    by (metis Idl_subset_eq_dvd int_Idl_subset_ideal mod_0_imp_dvd)
  have y_3:"y + z < p \<and> y + z \<ge> 0" 
    using y_def assms(1) by auto
  hence y_2:"(y \<oplus>\<^bsub>\<Z>\<^esub> z) < p \<and> (y \<oplus>\<^bsub>\<Z>\<^esub> z) \<ge> 0" using int_add_eq by presburger
  then have a3: "I +>\<^bsub>\<Z>\<^esub> (z::int) = I +>\<^bsub>\<Z>\<^esub> (y \<oplus>\<^bsub>\<Z>\<^esub> z)" using I_def 
    by (metis (no_types, lifting) y_1 UNIV_I abelian_group.a_coset_add_assoc int.Idl_subset_ideal' int.a_rcos_zero int.abelian_group_axioms int.cgenideal_eq_genideal int.cgenideal_ideal int.genideal_one int_carrier_eq)
  obtain w::nat  where "int w =  (y \<oplus>\<^bsub>\<Z>\<^esub> z)" 
    using y_2 nonneg_int_cases by metis
  thus ?thesis by (metis I_def a2 a3 y_2)
qed

lemma zfact_card:
  assumes "(p :: nat) > 1"
  shows "card (carrier (ZFact (int p))) = p"
proof -
  define car where "car \<equiv> (\<lambda>(k::nat). (Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> (int k)))"
  define A where "A = car ` {y :: nat. y < p}"
  have a:"carrier (ZFact (int p)) \<subseteq> A" 
  proof
    fix x
    assume "x \<in> carrier (ZFact (int p))"
    then obtain y :: nat where y_def: "x = Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> y \<and> y < p" 
      using zfact_find_canonical_repr by (metis assms of_nat_1 of_nat_less_iff)
    hence "x = car y" using car_def by presburger
    thus "x \<in> A" using A_def y_def by blast
  qed
  have b:"A \<subseteq> carrier (ZFact (int p))" apply (simp add:A_def car_def) 
    by (metis (no_types, lifting) UNIV_I ZFact_def ZFact_defs(2) imageE int.a_rcosetsI partial_object.select_convs(1) subsetI)
  have c:"inj_on car {y::nat. y < p}"
  proof
    fix x
    fix y
    assume d1:"x \<in> {y. y < p}"
    assume d2:"y \<in> {y. y < p}"
    assume "car x = car y"
    hence "Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> (int x) = Idl\<^bsub>\<Z>\<^esub> {int p} +>\<^bsub>\<Z>\<^esub> (int y)"
      by (simp add:car_def)
    hence "(int x) \<ominus>\<^bsub>\<Z>\<^esub> (int y) \<in> Idl\<^bsub>\<Z>\<^esub> {int p}"
      using ring.quotient_eq_iff_same_a_r_cos 
      by (metis UNIV_I int.cgenideal_eq_genideal int.cgenideal_ideal int.ring_axioms int_carrier_eq)
    hence "p dvd ((int x) - (int y))" apply (simp add:int_Idl) 
      using int_a_minus_eq by force
    thus "x = y" using d1 d2 
      by (metis diffs0_imp_equal dvd_0_right dvd_diff_commute gr_implies_not_zero int_ops(6) less_imp_diff_less mem_Collect_eq nat_dvd_not_less nat_neq_iff of_nat_dvd_iff) 
  qed
  hence "card A = p" using A_def 
    by (simp add: card_image)
  moreover have "A = carrier (ZFact (int p))" using b a by auto
  ultimately show ?thesis by auto
qed    

lemma zfact_finite:
  assumes "(p :: nat) > 1"
  shows "finite (carrier (ZFact (int p)))"
  using zfact_card 
  by (metis One_nat_def Suc_lessD assms card_ge_0_finite)

lemma finite_domains_are_fields:
  fixes R
  assumes "domain R"
  assumes "finite (carrier R)"
  shows "field R"
proof -
  have a3:"ring R" using assms
    using cring.axioms(1) domain_def by blast
  have "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>}"
  proof 
    have "Units R \<subseteq> carrier R" by (simp add:Units_def) 
    moreover have "\<zero>\<^bsub>R\<^esub> \<notin> Units R"
      by (meson assms(1) domain.zero_is_prime(1) primeE)
    ultimately show "Units R \<subseteq> carrier R - {\<zero>\<^bsub>R\<^esub>}" by blast
  next
    show "carrier R - {\<zero>\<^bsub>R\<^esub>} \<subseteq> Units R"
    proof
      fix x
      assume a:"x \<in> carrier R - {\<zero>\<^bsub>R\<^esub>}"
      define f where "f = (\<lambda>y. y \<otimes>\<^bsub>R\<^esub> x)"
      have "inj_on f  (carrier R)" apply (simp add:inj_on_def f_def)
        by (metis DiffD1 DiffD2 a assms(1) domain.m_rcancel insertI1)
      hence "card (carrier R) = card (f ` carrier R)"
        by (metis card_image)
      moreover have "f ` (carrier R) \<subseteq> carrier R"
        apply (rule image_subsetI) apply (simp add:f_def) using a a3
        by (simp add: ring.ring_simprules(5))
      ultimately have "f ` (carrier R) = carrier R" using card_subset_eq assms(2) by metis
      moreover have "\<one>\<^bsub>R\<^esub> \<in> carrier R" 
        by (simp add: a3 ring.ring_simprules(6))
      ultimately have "\<exists>y \<in> carrier R. f y = \<one>\<^bsub>R\<^esub>" 
        by (metis image_iff)
      then obtain y where y_1: "y \<in> carrier R" and y_2: "y \<otimes>\<^bsub>R\<^esub> x = \<one>\<^bsub>R\<^esub>" 
        using f_def by blast
      hence  y_3: "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>" using assms(1) a 
        by (metis DiffD1 a cring.cring_simprules(14) domain.axioms(1))
      show "x \<in> Units R" using y_1 y_2 y_3
        by (metis DiffD1 a assms(1) cring.divides_one domain.axioms(1) factor_def)
    qed
  qed
  then show "field R" 
    by (simp add: assms(1) field.intro field_axioms.intro)
qed

lemma zfact_is_field:
  assumes "prime (p :: nat)" 
  shows "field (ZFact (int p))"
proof -
  define q where "q = int p"
  have "finite (carrier (ZFact q))" using zfact_finite assms q_def prime_gt_1_nat by blast
  moreover have "domain (ZFact q)" using ZFact_prime_is_domain assms q_def by auto
  ultimately show ?thesis using finite_domains_are_fields q_def by blast
qed

end