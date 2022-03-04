section \<open>Landau Symbols\<close>

theory Landau_Ext
  imports "HOL-Library.Landau_Symbols" "HOL.Topological_Spaces"
begin

text \<open>This section contains results about Landau Symbols in addition to "HOL-Library.Landau".\<close>

text \<open>The following lemma is an intentional copy of @{thm [source] sum_in_bigo} with order of assumptions reversed *)\<close>

lemma sum_in_bigo_r: 
  assumes "f2 \<in> O[F'](g)"
  assumes "f1 \<in> O[F'](g)"
  shows "(\<lambda>x. f1 x + f2 x) \<in> O[F'](g)"
  by (rule sum_in_bigo[OF assms(2) assms(1)]) 

lemma landau_sum:
  assumes "eventually (\<lambda>x. g1 x \<ge> (0::real)) F'" 
  assumes "eventually (\<lambda>x. g2 x \<ge> 0) F'" 
  assumes "f1 \<in> O[F'](g1)"
  assumes "f2 \<in> O[F'](g2)"
  shows "(\<lambda>x. f1 x + f2 x) \<in> O[F'](\<lambda>x. g1 x + g2 x)"
proof -
  obtain c1 where a1: "c1 > 0" and b1: "eventually (\<lambda>x. abs (f1 x) \<le> c1 * abs (g1 x)) F'"
    using assms(3) by (simp add:bigo_def, blast)
  obtain c2 where a2: "c2 > 0" and b2: "eventually (\<lambda>x. abs (f2 x) \<le> c2 * abs (g2 x)) F'"
    using assms(4) by (simp add:bigo_def, blast)
  have "eventually (\<lambda>x. abs (f1 x + f2 x) \<le> (max c1 c2) * abs (g1 x + g2 x)) F'"
  proof (rule eventually_mono[OF eventually_conj[OF b1 eventually_conj[OF b2 eventually_conj[OF assms(1) assms(2)]]]])
    fix x
    assume a: "\<bar>f1 x\<bar> \<le> c1 * \<bar>g1 x\<bar> \<and> \<bar>f2 x\<bar> \<le> c2 * \<bar>g2 x\<bar> \<and> 0 \<le> g1 x \<and> 0 \<le> g2 x"
    have "\<bar>f1 x + f2 x\<bar> \<le> \<bar>f1 x \<bar> + \<bar>f2 x\<bar>" using abs_triangle_ineq by blast
    also have "... \<le> c1 *  \<bar>g1 x\<bar> + c2 * \<bar>g2 x\<bar>" using a add_mono by blast
    also have "... \<le> max c1 c2 * \<bar>g1 x\<bar> + max c1 c2 * \<bar>g2 x\<bar>" 
      apply (rule add_mono)
       apply (rule mult_right_mono, simp)
       apply (metis a a1 abs_le_zero_iff abs_zero linorder_not_less order_trans semiring_norm(63) zero_le_mult_iff)
      apply (rule mult_right_mono, simp)
      by (metis a a2 abs_le_zero_iff abs_zero linorder_not_less order_trans semiring_norm(63) zero_le_mult_iff)
    also have "... \<le> max c1 c2 * (\<bar>g1 x + g2 x\<bar>)"
      apply (subst distrib_left[symmetric])
      apply (rule mult_left_mono)
      using a a1 a2 by auto
    finally show "\<bar>f1 x + f2 x\<bar> \<le> max c1 c2 * \<bar>g1 x + g2 x\<bar>" by (simp add:algebra_simps)
  qed
  thus ?thesis
    apply (simp add:bigo_def)
    apply (rule exI[where x= "max c1 c2"])
    using a1 a2 by linarith
qed

lemma landau_sum_1:
  assumes "eventually (\<lambda>x. g1 x \<ge> (0::real)) F'" 
  assumes "eventually (\<lambda>x. g2 x \<ge> 0) F'" 
  assumes "f \<in> O[F'](g1)"
  shows "f \<in> O[F'](\<lambda>x. g1 x + g2 x)"
proof -
  have "f = (\<lambda>x. f x + 0)"
    by simp
  also have "... \<in> O[F'](\<lambda>x. g1 x + g2 x)"
    by (rule landau_sum[OF assms(1) assms(2) assms(3) zero_in_bigo])
  finally show ?thesis by simp
qed

lemma landau_sum_2:
  assumes "eventually (\<lambda>x. g1 x \<ge> (0::real)) F'" 
  assumes "eventually (\<lambda>x. g2 x \<ge> 0) F'" 
  assumes "f \<in> O[F'](g2)"
  shows "f \<in> O[F'](\<lambda>x. g1 x + g2 x)"
proof -
  have "f = (\<lambda>x. 0 + f x)"
    by simp
  also have "... \<in> O[F'](\<lambda>x. g1 x + g2 x)"
    by (rule landau_sum[OF assms(1) assms(2) zero_in_bigo assms(3)])
  finally show ?thesis by simp
qed

lemma landau_ln_3:
  assumes "eventually (\<lambda>x. (1::real) \<le> f x) F'" 
  assumes "f \<in> O[F'](g)" 
  shows "(\<lambda>x. ln (f x)) \<in> O[F'](g)" 
proof -
  have a:"(\<lambda>x. ln (f x)) \<in> O[F'](f)"
    apply (rule landau_o.big_mono, simp)
    apply (rule eventually_mono[OF assms(1)])
    apply (subst abs_of_nonneg, subst ln_ge_zero_iff, simp, simp, simp)
    using ln_less_self 
    by (meson ln_bound order.strict_trans2 zero_less_one)
  show ?thesis
    by (rule landau_o.big_trans[OF a assms(2)])
qed

lemma landau_ln_2:
  assumes "a > (1::real)"
  assumes "eventually (\<lambda>x. 1 \<le> f x) F'" 
  assumes "eventually (\<lambda>x. a \<le> g x) F'" 
  assumes "f \<in> O[F'](g)" 
  shows "(\<lambda>x. ln (f x)) \<in> O[F'](\<lambda>x. ln (g x))" 
proof -
  obtain c where a: "c > 0" and b: "eventually (\<lambda>x. abs (f x) \<le> c * abs (g x)) F'"
    using assms(4) by (simp add:bigo_def, blast)
  define d where "d = 1 + (max 0 (ln c)) / ln a"
  have d:"eventually (\<lambda>x. abs (ln (f x)) \<le> d * abs (ln (g x))) F'"
  proof (rule eventually_mono[OF eventually_conj[OF b eventually_conj[OF assms(3) assms(2)]]])
    fix x
    assume c:"\<bar>f x\<bar> \<le> c * \<bar>g x\<bar> \<and> a \<le> g x \<and> 1 \<le> f x" 
    have "abs (ln (f x)) = ln (f x)"
      by (subst abs_of_nonneg, rule ln_ge_zero, metis c, simp)
    also have "... \<le> ln (c * abs (g x))"
      apply (subst ln_le_cancel_iff) using c apply simp
       apply (rule mult_pos_pos[OF a]) using c assms(1) apply simp
      using c by linarith
    also have "... \<le> ln c + ln (abs (g x))"
      apply (subst ln_mult[OF a])
      using c assms(1) by simp+
    also have "... \<le> (d-1)*ln a + ln (g x)"
      apply (rule add_mono)
      using assms(1) apply (simp add:d_def)
      apply (subst abs_of_nonneg)
      using c assms(1) by simp+
    also have "... \<le> (d-1)* ln (g x) + ln (g x)"
      apply (rule add_mono)
       apply (rule mult_left_mono)
        apply (subst ln_le_cancel_iff)
      using assms(1) apply simp
      using c assms(1) apply simp
      using c assms(1) apply simp
       apply (simp add:d_def)
       apply (rule divide_nonneg_nonneg, simp, rule ln_ge_zero) using assms(1) apply simp
      by simp
    also have "... = d * ln (g x)" by (simp add:algebra_simps)
    also have "... = d * abs (ln (g x))"
      apply (subst abs_of_nonneg)
       apply (rule ln_ge_zero) using c assms(1) by simp+
    finally show "abs (ln (f x)) \<le> d * abs (ln (g x))" by simp
  qed
  show ?thesis
    apply (simp add:bigo_def)
    apply (rule exI[where x="d"])
    apply (rule conjI, simp add:d_def)
     apply (meson add_pos_nonneg assms(1) less_le_not_le less_numeral_extra(1) ln_ge_zero max.cobounded1 zero_le_divide_iff)
    by (metis d)
qed

lemma landau_real_nat:
  fixes f :: "'a \<Rightarrow> int"
  assumes "(\<lambda>x. of_int (f x)) \<in> O[F'](g)"
  shows "(\<lambda>x. real (nat (f x))) \<in> O[F'](g)"
proof -
  obtain c where a: "c > 0" and b: "eventually (\<lambda>x. abs (of_int (f x)) \<le> c * abs (g x)) F'"
    using assms(1) by (simp add:bigo_def, blast)

  show ?thesis
    apply (simp add:bigo_def)
    apply (rule exI[where x="c"])
    apply (rule conjI[OF a])
    apply (rule eventually_mono[OF b])
    by simp
qed

lemma landau_ceil:
  assumes "(\<lambda>_. 1) \<in> O[F'](g)"
  assumes "f \<in> O[F'](g)"
  shows "(\<lambda>x. real_of_int \<lceil>f x\<rceil>) \<in> O[F'](g)"
  apply (rule landau_o.big_trans[where g="\<lambda>x. 1 + abs (f x)"])
   apply (rule landau_o.big_mono)
   apply (rule always_eventually, rule allI, simp, linarith)
  by (rule sum_in_bigo[OF assms(1)], simp add:assms)

lemma landau_rat_ceil:
  assumes "(\<lambda>_. 1) \<in> O[F'](g)"
  assumes "(\<lambda>x. real_of_rat (f x)) \<in> O[F'](g)"
  shows "(\<lambda>x. real_of_int \<lceil>f x\<rceil>) \<in> O[F'](g)"
  apply (rule landau_o.big_trans[where g="\<lambda>x. 1 + abs (real_of_rat (f x))"])
   apply (rule landau_o.big_mono)
   apply (rule always_eventually, rule allI, simp) 
  apply (smt (verit) abs_ge_self abs_of_nonpos abs_of_rat le_of_int_ceiling of_int_ceiling_le_add_one of_rat_ceiling)
  apply (rule sum_in_bigo[OF assms(1)])
  using assms(2) 
  by (metis landau_o.big.abs_in_iff)

lemma landau_nat_ceil:
  assumes "(\<lambda>_. 1) \<in> O[F'](g)"
  assumes "f \<in> O[F'](g)"
  shows "(\<lambda>x. real (nat \<lceil>f x\<rceil>)) \<in> O[F'](g)"
  apply (rule landau_real_nat)
  by (rule landau_ceil[OF assms(1) assms(2)])

lemma landau_const_inv:
  assumes "c > (0::real)"
  assumes "(\<lambda>x. 1 / f x) \<in> O[F'](g)"
  shows "(\<lambda>x. c / f x) \<in> O[F'](g)"
proof -
  obtain d where a: "d > 0" and b: "eventually (\<lambda>x. abs (1 / f x) \<le> d * abs (g x)) F'"
    using assms(2) by (simp add:bigo_def, blast)
  have c:"eventually (\<lambda>x. \<bar>c\<bar> / \<bar>f x\<bar> \<le> (c)*d * abs (g x)) F'"
    apply (rule eventually_mono[OF b])
    using assms(1)
    apply simp 
    by (metis Groups.mult_ac(2) Groups.mult_ac(3) divide_inverse inverse_eq_divide less_imp_le mult_le_cancel_left not_less)
  show ?thesis
    apply (simp add:bigo_def)
    apply (rule exI[where x="c*d"])
    apply (rule conjI, rule mult_pos_pos[OF assms(1) a])
    by (rule c)
qed

lemma eventually_nonneg_div:
  assumes "eventually (\<lambda>x. (0::real) \<le> f x) F'"
  assumes "eventually (\<lambda>x. 0 < g x) F'"
  shows "eventually (\<lambda>x. 0 \<le> f x / g x) F'"
  apply (rule eventually_mono[OF eventually_conj[OF assms(1) assms(2)]])
  by simp

lemma eventually_nonneg_add:
  assumes "eventually (\<lambda>x. (0::real) \<le> f x) F'"
  assumes "eventually (\<lambda>x. 0 \<le> g x) F'"
  shows "eventually (\<lambda>x. 0 \<le> f x + g x) F'"
  apply (rule eventually_mono[OF eventually_conj[OF assms(1) assms(2)]])
  by simp

lemma eventually_ln_ge_iff:
  assumes "eventually (\<lambda>x. (exp (c::real)) \<le> f x) F'"
  shows "eventually (\<lambda>x. c \<le> ln (f x)) F'"
  apply (rule eventually_mono[OF assms(1)])
  by (meson ln_ge_iff  exp_gt_zero order_less_le_trans)

lemma div_commute: "(a::real) / b = (1/b) * a" by simp

lemma eventually_prod1':
  assumes "B \<noteq> bot"
  shows "(\<forall>\<^sub>F x in A \<times>\<^sub>F B. P (fst x)) \<longleftrightarrow> (\<forall>\<^sub>F x in A. P x)"
  apply (subst (2) eventually_prod1[OF assms(1), symmetric])
  apply (rule arg_cong2[where f="eventually"])
  by (rule ext, simp add:case_prod_beta, simp)

lemma eventually_prod2':
  assumes "A \<noteq> bot"
  shows "(\<forall>\<^sub>F x in A \<times>\<^sub>F B. P (snd x)) \<longleftrightarrow> (\<forall>\<^sub>F x in B. P x)"
  apply (subst (2) eventually_prod2[OF assms(1), symmetric])
  apply (rule arg_cong2[where f="eventually"])
  by (rule ext, simp add:case_prod_beta, simp)

instantiation rat :: linorder_topology
begin

definition open_rat :: "rat set \<Rightarrow> bool"
  where "open_rat = generate_topology (range (\<lambda>a. {..< a}) \<union> range (\<lambda>a. {a <..}))"

instance
  by standard (rule open_rat_def)
end

lemma inv_at_right_0_inf:
  "\<forall>\<^sub>F x in at_right 0. c \<le> 1 / real_of_rat x"
  apply (rule eventually_at_rightI[where b="1/rat_of_int (max \<lceil>c\<rceil> 1)"])
   apply (rule order_trans[where y="real_of_int (max \<lceil>c\<rceil> 1)"], linarith)
   apply (subst pos_le_divide_eq, simp)
   apply simp
   apply (subst (asm) pos_less_divide_eq, simp)
   apply (metis less_eq_real_def mult.commute of_rat_less_1_iff of_rat_mult of_rat_of_int_eq)
  by simp

end