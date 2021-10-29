theory Float_Ext
  imports "HOL-Library.Float"
begin

lemma mantissa_bound:
  fixes e :: int
  shows "abs (mantissa (float_of (m * 2 powr e))) \<le> abs m"
proof (cases "Float m e \<noteq> 0")
  case True
  obtain i where m_def: "m = mantissa (Float m e) * 2 ^ i"
    using True denormalize_shift by metis
  have "abs (mantissa (Float m e)) * 1 \<le> abs m"
    apply (subst (2) m_def)
    apply (subst abs_mult)
    by (rule mult_left_mono, simp, simp)
  moreover have "float_of (m * 2 powr e) = Float m e"
    by (simp add: Float.abs_eq)
  ultimately show ?thesis by presburger
next
  case False
  moreover have "float_of (m * 2 powr e) = Float m e"
    by (simp add: Float.abs_eq)
  ultimately show ?thesis by simp
qed


lemma round_down_ge:
  "x \<le> round_down prec x + 2 powr (-prec)"
  using round_down_correct by (simp, meson diff_diff_eq diff_eq_diff_less_eq)

lemma truncate_down_ge:
  "x \<le> truncate_down prec x + abs x * 2 powr (-prec)"
proof (cases "abs x > 0")
  case True
  have "x \<le> round_down (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) x + 2 powr (-real_of_int(int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>))"
    by (rule round_down_ge)
  also have "... \<le> truncate_down prec x + abs x * 2 powr (-prec)"
    apply (rule add_mono)
     apply (simp add:truncate_down_def)
    apply (subst of_int_diff, simp)
    apply (subst powr_diff)
    apply (subst pos_divide_le_eq, simp)
    apply (subst mult.assoc)
    apply (subst powr_add[symmetric], simp)
    apply (subst le_log_iff[symmetric], simp, metis True)
    by auto
  finally show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

lemma truncate_down_pos:
  assumes "x \<ge> 0"
  shows "x * (1 - 2 powr (-prec)) \<le> truncate_down prec x"
  apply (simp add:right_diff_distrib diff_le_eq)
  by (metis truncate_down_ge assms  abs_of_nonneg)

lemma truncate_down_eq:
  assumes "truncate_down r x = truncate_down r y"
  shows "abs (x-y) \<le> max (abs x) (abs y) * 2 powr (-real r)"
proof - 
  have "x - y \<le> truncate_down r x + abs x * 2 powr (-real r) - y"
    by (rule diff_right_mono, rule truncate_down_ge)
  also have "... \<le> y + abs x * 2 powr (-real r) - y"
    apply (rule diff_right_mono, rule add_mono)
     apply (subst assms(1), rule truncate_down_le, simp)
    by simp
  also have "... \<le> abs x * 2 powr (-real r)" by simp
  also have "... \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp
  finally have a:"x - y \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp

  have "y - x \<le> truncate_down r y + abs y * 2 powr (-real r) - x"
    by (rule diff_right_mono, rule truncate_down_ge)
  also have "... \<le> x + abs y * 2 powr (-real r) - x"
    apply (rule diff_right_mono, rule add_mono)
     apply (subst assms(1)[symmetric], rule truncate_down_le, simp)
    by simp
  also have "... \<le> abs y * 2 powr (-real r)" by simp
  also have "... \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp
  finally have b:"y - x \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp

  show ?thesis
    using abs_le_iff a b by linarith
qed


lemma truncate_down_rule:
  assumes "x \<ge> 0"
  assumes "prec > 0"
  assumes "truncate_down prec x \<le> y"
  shows "x \<le> y / (1-2 powr (-real prec))"
proof -
  have a: "2 powr - real prec < 2 powr 0"
    by (rule powr_less_mono, simp add:assms, simp)
  also have "...  = 1" by simp
  finally have a:"2 powr - real prec < 1" by simp
  have "x \<le> truncate_down prec x / (1-2 powr (-real prec))"
    apply (subst pos_le_divide_eq)
     apply (simp add:a)
    by (rule truncate_down_pos[OF assms(1)])
  also have "... \<le> y / (1-2 powr (-real prec))"
    apply (rule divide_right_mono, simp add:assms)
    using a by fastforce
  finally show ?thesis by simp
qed

definition rat_of_float :: "float \<Rightarrow> rat" where "rat_of_float f = of_int (mantissa f) * (
  if exponent f \<ge> 0 then 2 ^ (nat (exponent f)) else 1 / 2 ^ (nat (-exponent f)))" 

lemma real_of_rat_of_float: "real_of_rat (rat_of_float x) = real_of_float x"
  apply (cases x)
  apply (simp add:rat_of_float_def)
  apply (rule conjI)
   apply (metis (mono_tags, opaque_lifting) Float.rep_eq compute_real_of_float mantissa_exponent of_int_mult of_int_numeral of_int_power of_rat_of_int_eq)
  by (metis Float.rep_eq Float_mantissa_exponent compute_real_of_float of_int_numeral of_int_power of_rat_divide of_rat_of_int_eq)

end