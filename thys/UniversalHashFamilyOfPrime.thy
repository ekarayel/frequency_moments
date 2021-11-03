section \<open>Universal Hash Family for $\{0..<p\}$\<close>

text \<open>Specialization of universal hash families from arbitrary finite 
  fields to $\{0..<p\}$.\<close>


theory UniversalHashFamilyOfPrime
  imports Field UniversalHashFamily Probability_Ext Encoding
begin

lemma fin_bounded_degree_polynomials:
  assumes "p > 0"
  shows "finite (bounded_degree_polynomials (ZFact (int p)) n)"
  apply (rule fin_degree_bounded)
   apply (metis ZFact_is_cring cring_def)
  by (rule zfact_finite[OF assms])

lemma ne_bounded_degree_polynomials:
  shows "bounded_degree_polynomials (ZFact (int p)) n \<noteq> {}"
  apply (rule non_empty_bounded_degree_polynomials)
  by (metis ZFact_is_cring cring_def)

lemma card_bounded_degree_polynomials:
  assumes "p > 0"
  shows "card (bounded_degree_polynomials (ZFact (int p)) n) = p^n"
  apply (subst bounded_degree_polynomials_count)
    apply (metis ZFact_is_cring cring_def)
   apply (rule zfact_finite[OF assms])
  by (subst zfact_card, metis assms, simp)

fun hash :: "nat \<Rightarrow> nat \<Rightarrow> int set list \<Rightarrow> nat"
  where "hash p x f = the_inv_into {0..<p} (zfact_embed p) (UniversalHashFamily.hash (ZFact p) (zfact_embed p x) f)"

declare hash.simps [simp del]

lemma hash_range:
  assumes "p > 0"
  assumes "\<omega> \<in> bounded_degree_polynomials (ZFact (int p)) n"
  assumes "x < p"
  shows "hash p x \<omega> < p"
proof -
  have "UniversalHashFamily.hash (ZFact (int p)) (zfact_embed p x) \<omega> \<in> carrier (ZFact (int p))"
    apply (rule UniversalHashFamily.hash_range[OF _ assms(2)])
     apply (metis ZFact_is_cring cring_def)
    by (metis zfact_embed_ran[OF assms(1)] assms(3) atLeast0LessThan image_eqI lessThan_iff)
  thus ?thesis
    using the_inv_into_into[OF zfact_embed_inj[OF assms(1)], where B="{0..<p}"]
      zfact_embed_ran[OF assms(1)]
    by (simp add:hash.simps)
qed

(* TODO: We can show this for arbitrary fields and lift the result. *)
lemma hash_inj_if_degree_1:
  assumes "prime p"
  assumes "\<omega> \<in> bounded_degree_polynomials (ZFact (int p)) n"
  assumes "degree \<omega> = 1"
  shows "inj_on (\<lambda>x. hash p x \<omega>) {0..<p}"
proof (rule inj_onI)
  interpret field "ZFact (int p)"
    using zfact_prime_is_field[OF assms(1)] by blast
  have p_ge_0: "p > 0" using assms(1)  
    by (simp add: prime_gt_0_nat)

  fix x y
  assume a1: "x \<in> {0..<p}"
  assume a2: "y \<in> {0..<p}"
  define x' where "x' = zfact_embed p x"
  define y' where "y' = zfact_embed p y"
  assume a3: "hash p x \<omega> = hash p y \<omega>"

  have x'_carr: "x' \<in> carrier (ZFact (int p))" 
    using zfact_embed_ran[OF p_ge_0] a1 x'_def by blast
  have y'_carr: "y' \<in> carrier (ZFact (int p))" 
    using zfact_embed_ran[OF p_ge_0] a2 y'_def by blast
  have \<omega>_carr: "set \<omega> \<subseteq> carrier (ZFact (int p))" 
    using assms(2) apply (simp add:bounded_degree_polynomials_def) 
    by (metis carrier_is_subring polynomial_in_carrier univ_poly_carrier)

  have eval_eq: "ring.eval (ZFact (int p)) \<omega> x' = ring.eval (ZFact (int p)) \<omega> y'" 
    using a3 inj_on_the_inv_into[OF zfact_embed_inj[OF p_ge_0]]
      eval_in_carrier[OF \<omega>_carr]
      zfact_embed_ran[OF p_ge_0] x'_carr y'_carr
    apply (simp add:hash.simps UniversalHashFamily.hash_def x'_def[symmetric] y'_def[symmetric])
    by (meson inj_on_eq_iff)


  obtain u v where \<omega>_def: "\<omega> = [u,v]" using assms(3)
    apply (cases \<omega>, simp)
    by (cases "(tl \<omega>)", simp, simp)

  have u_carr: "u \<in> carrier (ZFact (int p)) - {\<zero>\<^bsub>ZFact p\<^esub>}"
    using \<omega>_def assms(2) apply (simp add:bounded_degree_polynomials_def)
    using assms(3) by blast
  have v_carr: "v \<in> carrier (ZFact (int p))" 
    using \<omega>_def assms(2) apply (simp add:bounded_degree_polynomials_def)
    using assms(3) by blast

  have "\<And>x. x \<in> carrier (ZFact (int p)) \<Longrightarrow> ring.eval (ZFact (int p)) \<omega> x = u \<otimes>\<^bsub>ZFact p\<^esub> x  \<oplus>\<^bsub>ZFact p\<^esub> v"
    using u_carr v_carr by (simp add:\<omega>_def) 

  hence "u \<otimes>\<^bsub>ZFact p\<^esub> x'  \<oplus>\<^bsub>ZFact p\<^esub> v =  u \<otimes>\<^bsub>ZFact p\<^esub> y'  \<oplus>\<^bsub>ZFact p\<^esub> v"
    using x'_carr y'_carr eval_eq by simp

  hence "x' = y'"
    using u_carr x'_carr y'_carr v_carr
    by (simp add: local.field_Units)

  thus "x = y" 
    by (metis  zfact_embed_inj[OF p_ge_0] a1 a2  inj_onD x'_def y'_def)
qed

lemma hash_prob:
  assumes "prime p"
  assumes "K \<subseteq> {0..<p}"
  assumes "y ` K \<subseteq> {0..<p}"
  assumes "card K \<le> n"
  shows "\<P>(\<omega> in measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)).
    (\<forall>x \<in> K. hash p x \<omega> = (y x))) = 1 / real p^card K"
proof -
  define y' where "y' = zfact_embed p \<circ> y \<circ> (the_inv_into K (zfact_embed p))"
  define \<Omega> where "\<Omega> = pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)"

  have p_ge_0: "p > 0" using prime_gt_0_nat[OF assms(1)] by simp

  have "\<And>x. x \<in> zfact_embed p ` K \<Longrightarrow> the_inv_into K (zfact_embed p) x \<in> K"
    apply (rule the_inv_into_into)
      apply (metis zfact_embed_inj[OF p_ge_0] assms(2) inj_on_subset)
    by auto

  hence ran_y: "\<And>x. x \<in> zfact_embed p ` K \<Longrightarrow> y (the_inv_into K (zfact_embed p) x) \<in> {0..<p}"
    using assms(3) by blast

  have ran_y': "y' ` (zfact_embed p ` K) \<subseteq> carrier (ZFact (int p))"
    apply (rule image_subsetI)
    apply (simp add:y'_def)
    by (metis zfact_embed_ran[OF p_ge_0] imageI ran_y)

  have K_embed: "zfact_embed p ` K \<subseteq> carrier (ZFact (int p))"
    using zfact_embed_ran[OF p_ge_0] assms(2) by auto

  have ring_zfact: "ring (ZFact (int p))" 
    using ZFact_is_cring cring_def by blast

  have "\<P>(\<omega> in measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)). 
    (\<forall>x \<in> K. hash p x \<omega> = (y x))) = \<P>(\<omega> in measure_pmf \<Omega>. (\<forall>x \<in> K. hash p x \<omega> = (y x)))"
    by (simp add: \<Omega>_def)
  also have "... =
    \<P>(\<omega> in measure_pmf \<Omega>. (\<forall>x \<in> zfact_embed p ` K. UniversalHashFamily.hash (ZFact (int p)) x \<omega> = y' x))"
    apply (rule pmf_eq)
    apply (simp add:y'_def hash.simps \<Omega>_def)
    apply (subst (asm) set_pmf_of_set, metis ne_bounded_degree_polynomials, 
            metis fin_bounded_degree_polynomials[OF p_ge_0])
    apply (rule ball_cong, simp)
    apply (subst the_inv_into_f_f)
      apply (metis zfact_embed_inj[OF p_ge_0] assms(2) inj_on_subset)
     apply (simp)
    apply (subst eq_commute)
    apply (rule order_antisym)
     apply (simp, rule impI)
     apply (subst f_the_inv_into_f[OF zfact_embed_inj[OF p_ge_0]])
      apply (subst zfact_embed_ran[OF p_ge_0])
      apply (rule UniversalHashFamily.hash_range[OF ring_zfact, where n="n"], simp)
      apply (meson K_embed image_subset_iff)
     apply simp
    apply (simp, rule impI)
    apply (subst the_inv_into_f_f[OF zfact_embed_inj[OF p_ge_0]])
     apply (metis assms(3) image_subset_iff) 
    by simp
  also have "... =
    1 / real (card (carrier (ZFact (int p))))^(card (zfact_embed p ` K))"
    apply (simp only: \<Omega>_def)
    apply (rule UniversalHashFamily.hash_prob[where K="zfact_embed p ` K" and F="ZFact (int p)" and n="n" and y="y'"])
        apply (rule zfact_prime_is_field[OF assms(1)])
       apply (rule zfact_finite[OF p_ge_0])
      apply (metis zfact_embed_ran[OF p_ge_0] assms(2) image_mono)
     apply (rule order_trans[OF card_image_le], rule finite_subset[OF assms(2)], simp, metis assms(4))
    using K_embed ran_y' by blast
  also have "... = 1/real p^(card K)" 
    apply (subst card_image, meson inj_on_subset zfact_embed_inj[OF p_ge_0] assms(2))
    apply (subst zfact_card[OF p_ge_0])
    by simp
  finally show ?thesis by simp
qed

lemma hash_prob_2:
  assumes "prime p"
  assumes "inj_on x K"
  assumes "x ` K \<subseteq> {0..<p}"
  assumes "y ` K \<subseteq> {0..<p}"
  assumes "card K \<le> n"
  shows "\<P>(\<omega> in measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)).
    (\<forall>k \<in> K. hash p (x k) \<omega> = (y k))) = 1 / real p^card K" (is "?lhs = ?rhs")
proof -
  define y' where "y' = y \<circ> (the_inv_into K x)"
  have "?lhs = \<P>(\<omega> in measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)).
    (\<forall>k \<in> x ` K. hash p k \<omega> = y' k))"
    apply (rule pmf_eq)
    apply (simp add:y'_def)
    apply (rule ball_cong, simp)
    by (subst the_inv_into_f_f[OF assms(2)], simp, simp)
  also have "... = 1 / real p ^ card (x ` K)" 
    apply (rule hash_prob[OF assms(1) assms(3)]) 
     using assms apply (simp add: y'_def subset_eq the_inv_into_f_f)
     by (metis card_image assms(2) assms(5))
  also have "... = ?rhs"
     by (subst card_image[OF assms(2)], simp)
   finally show ?thesis by simp
qed

lemma hash_prob_range:
  assumes "prime p"
  assumes "x < p"
  assumes "n > 0"
  shows "\<P>(\<omega> in measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)).
    hash p x \<omega> \<in> A) = card (A \<inter> {0..<p}) / p"
proof -
  define \<Omega> where "\<Omega> = measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n))"
  have p_ge_0: "p > 0" using assms(1) by (simp add: prime_gt_0_nat)

  have "\<P>(\<omega> in \<Omega>. hash p x \<omega> \<in> A) = measure \<Omega> (\<Union> k \<in> A \<inter> {0..<p}. {\<omega>. hash p x \<omega> = k})"
    apply (simp only:\<Omega>_def)
    apply (rule pmf_eq, simp)
    apply (subst (asm) set_pmf_of_set[OF ne_bounded_degree_polynomials fin_bounded_degree_polynomials[OF p_ge_0]])
    using hash_range[OF p_ge_0 _ assms(2)] by simp
  also have "... = (\<Sum> k \<in> (A \<inter> {0..<p}). measure \<Omega> {\<omega>. hash p x \<omega> = k})"
    apply (rule measure_finite_Union, simp, simp add:\<Omega>_def)
     apply (simp add:disjoint_family_on_def, fastforce) 
    by (simp add:\<Omega>_def)
  also have "... = (\<Sum> k \<in> (A \<inter> {0..<p}). \<P>(\<omega> in \<Omega>. \<forall>x' \<in> {x}. hash p x' \<omega> = k ))"
    by (simp add:\<Omega>_def)
  also have "... = (\<Sum> k \<in> (A \<inter> {0..<p}). 1/ real p ^ card {x})"
    apply (rule sum.cong, simp)
    apply (simp only:\<Omega>_def)
    apply (rule hash_prob[OF assms(1)], simp add:assms, simp)
    using assms(3) by simp
  also have "... = card (A \<inter> {0..<p}) / real p"
    by simp
  finally show ?thesis
    by (simp only:\<Omega>_def)
qed

lemma hash_k_wise_indep:
  assumes "prime p"
  assumes "1 \<le> n"
  shows "prob_space.k_wise_indep_vars (measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)))
   n (\<lambda>_. pmf_of_set {0..<p}) (hash p) {0..<p}"
proof -
  have p_ge_0: "p > 0"
    using assms(1) by (simp add: prime_gt_0_nat)

  have a:"\<And>J. J \<subseteq> {0..<p} \<Longrightarrow> card J \<le> n \<Longrightarrow> finite J \<Longrightarrow>
    prob_space.indep_vars (measure_pmf (pmf_of_set (bounded_degree_polynomials (ZFact (int p)) n)))
        ((\<lambda>x. measure_pmf (pmf_of_set {0..<p})) \<circ> zfact_embed p) (\<lambda>i \<omega>. hash p i \<omega>) J"
    apply (subst hash.simps)
    apply (rule prob_space.indep_vars_reindex[OF prob_space_measure_pmf])
     apply (rule inj_on_subset[OF zfact_embed_inj[OF p_ge_0]], simp)
    apply (rule prob_space.indep_vars_compose2[where Y="\<lambda>_. the_inv_into {0..<p} (zfact_embed p)" and M'="\<lambda>_. measure_pmf (pmf_of_set (carrier (ZFact p)))"])
      apply (rule prob_space_measure_pmf)
     apply (rule hash_indep_pmf[OF zfact_prime_is_field[OF assms(1)] zfact_finite[OF p_ge_0]])
        using  zfact_embed_ran[OF p_ge_0] apply blast
       apply simp
      apply (subst card_image, metis zfact_embed_inj[OF p_ge_0] inj_on_subset, simp)
     apply (metis assms(2))
    by simp

  show ?thesis
    using a by (simp add:measure_pmf.k_wise_indep_vars_def comp_def)
qed

subsection \<open>Encoding\<close>

fun zfact\<^sub>S where "zfact\<^sub>S p x = (
    if x \<in> zfact_embed p ` {0..<p} then
      N\<^sub>S (the_inv_into {0..<p} (zfact_embed p) x)
    else
     None
  )"

lemma zfact_encoding : 
  "is_encoding (zfact\<^sub>S p)"
proof -
  have "p > 0 \<Longrightarrow> is_encoding (\<lambda>x. zfact\<^sub>S p x)"
    apply simp 
    apply (rule encoding_compose[where f="N\<^sub>S"])
     apply (metis nat_encoding, simp)
    by (metis inj_on_the_inv_into zfact_embed_inj)
  moreover have "is_encoding (zfact\<^sub>S 0)"
    by (simp add:is_encoding_def)
  ultimately show ?thesis by blast
qed

lemma bounded_degree_polynomial_bit_count:
  assumes "p > 0"
  assumes "x \<in> bounded_degree_polynomials (ZFact p) n"
  shows "bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le> ereal (real n * (2 * log 2 p + 2) + 1)"
proof -
  have b:"real (length x) \<le> real n"
    using assms(2) 
    apply (simp add:bounded_degree_polynomials_def)
    apply (cases "x=[]", simp, simp)
    by linarith

  have a:"\<And>y. y \<in> set x \<Longrightarrow> y \<in> zfact_embed p ` {0..<p}" 
    using assms(2) 
    apply (simp add:bounded_degree_polynomials_def)
    by (metis length_greater_0_conv length_pos_if_in_set polynomial_def subsetD univ_poly_carrier zfact_embed_ran[OF assms(1)])

  have "bit_count (list\<^sub>S (zfact\<^sub>S p) x) \<le> ereal (real (length x)) * ( ereal (2 * log 2 (1 + real (p-1)) + 1) + 1) + 1"
    apply (rule list_bit_count_est)
    apply (simp add:a del:N\<^sub>S.simps)
    apply (rule nat_bit_count_est)
    by (metis a the_inv_into_into[OF zfact_embed_inj[OF assms(1)], where B="{0..<p}", simplified]
        Suc_pred assms(1) less_Suc_eq_le)
  also have "... \<le> ereal (real n) * (2 + ereal (2 * log 2 p) ) + 1"
    apply simp
    apply (rule mult_mono, metis b)
      apply (rule add_mono)
    using assms(1) by simp+
  also have "... = ereal (real n * (2 * log 2 p + 2) + 1)"
    by simp
  finally show ?thesis by simp
qed

end
