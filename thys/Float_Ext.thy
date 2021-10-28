theory Float_Ext
  imports "HOL-Library.Float"
begin

definition round_nearest :: "int \<Rightarrow> real \<Rightarrow> real"
  where "round_nearest prec x = (\<lceil>x * 2 powr prec - 1/2\<rceil> * 2 powr (-prec))"

definition truncate_nearest :: "nat \<Rightarrow> real \<Rightarrow> real"
  where "truncate_nearest prec x = round_nearest (prec - \<lfloor>log 2 (abs x)\<rfloor>) x"

lemma truncate_nearest_float: "truncate_nearest p x \<in> float"
  apply (simp add:truncate_nearest_def round_nearest_def)
  apply (rule times_float) 
  using real_of_int_float apply blast
  by (metis of_int_diff of_int_of_nat_eq two_powr_int_float)

lemma truncate_nearest_mono: "mono (truncate_nearest prec)"
  apply (rule monoI)
  apply (simp add:truncate_nearest_def round_nearest_def)
  sorry

(*
  if floor (log 2 |x| ) = floor (log 2 |y|)
  then mono should follow from mono of round_nearest

  let's assume fl (log 2 |x|) < fl (log 2 |y | )

  Four cases:
   |x| < 2^m \<le> |y|
  If the signs are different we have no issue
  Case 1:
    x pos y pos


  truncate r x = round_nearest (r-m+1) x = cl (x * 2^[r-m+1] - 1/2) \<le> cl (2^m * 2^[r-m+1] - 1/2) * 2^[-r+m-1]
    = cl (2^[r+1] - 1/2) * 2^[r-m+1] = 2^[r+1] & 2^[-r+m-1] = 2^m

  truncate r y = round_neatest (r-m) y = cl( y * 2^[r-m] - 1/2) \<ge> cl (2^m * 2^[r-m] - 1/2) * 2^[-r+m] =
    cl (2^r - 1/2) * 2^[-r+m] = 2^m

  okey

    x neg y neg

  


  |x| 

  truncate_nearest 


 0.5 \<rightarrow> 0 , 0.51 \<rightarrow> 1  *)
(* fl (x+1/2) 0.5 \<rightarrow> 1, 0.49 \<rightarrow> 0   *)

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

lemma round_nearest_mantissa_bound:
  fixes e :: int
  shows "abs (mantissa (float_of (round_nearest prec x))) \<le> abs \<lceil>x * 2 powr prec - 1/2\<rceil>"
  apply (simp add:round_nearest_def)
  by (metis mantissa_bound of_int_minus)

lemma truncate_nearest_mantissa_bound:
  shows "abs (mantissa (float_of (truncate_nearest prec x))) \<le> 2 ^ (prec+1)"
proof -
  have c: "abs x \<le> 2 powr (1+real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
    apply (cases "x=0", simp)
    apply (subst le_powr_iff, simp, simp)
    by (metis add.commute real_of_int_floor_add_one_ge)
  also have "... = 2 * 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>"
    by (simp add:powr_add)
  finally have c: "abs x \<le> 2 * 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>" by blast
  have "x * 2 ^ prec / 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1 / 2 \<le> x / 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> * 2 ^ prec"
    by simp
  also have "... \<le>  2 * 2 ^ prec" 
    apply (rule mult_right_mono)
     apply (subst pos_divide_le_eq, simp)
    using c abs_le_iff apply blast
    by simp
  finally have a: "x * 2 ^ prec / 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1 / 2 \<le> 2 * 2 ^ prec"
    by blast
                                                          
  have "- (2 * 2 ^ prec) - (1::int) < - (2 * 2 ^ prec) - 1/2"
    by simp
  also have "... \<le> x / 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> * 2 ^ prec - 1 / 2" 
    apply (rule diff_mono)
     apply (subst minus_mult_left)
     apply (rule mult_right_mono)
      apply (subst pos_le_divide_eq, simp)
    using c abs_le_iff apply linarith
    by simp+
  finally have b: "- (2 * 2 ^ prec) - 1 < x * 2 ^ prec / 2 powr real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - 1 / 2"
    by simp

  have "\<bar>mantissa (float_of (round_nearest (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) x))\<bar> \<le> abs \<lceil>x * 2 powr (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) - 1/2\<rceil>"
    using round_nearest_mantissa_bound by metis
  also have "... \<le> 2 ^ (prec+1)"
    apply (simp add:powr_diff)
    apply (subst powr_realpow, simp)
    apply (subst abs_le_iff)
    apply (rule conjI, subst ceiling_le_iff, simp add:a)
    apply (subst minus_le_iff)
    apply (subst le_ceiling_iff)
    by (simp add:b)
  finally show ?thesis
    by (simp add:truncate_nearest_def)
qed

lemma round_nearest_le:
  "x - 2 powr (-prec-1) \<le> round_nearest prec x"
proof -
  have "x - 2 powr (-prec-1) = (x * 2 powr prec - 1/2) * 2 powr (-prec)"
    apply (subst left_diff_distrib)
    apply (rule arg_cong2[where f="(-)"])
    apply (subst mult.assoc)
     apply (subst powr_add[symmetric], simp)
    by (simp add:algebra_simps powr_diff powr_add)
  also have "... \<le>   \<lceil>x * 2 powr prec - 1/2\<rceil> * 2 powr (-prec)"
    apply (rule mult_right_mono)
     apply (meson ceiling_correct)
    by simp
  finally show ?thesis by (simp add:round_nearest_def)
qed

lemma round_nearest_ge:
  "round_nearest prec x \<le> x + 2 powr (-prec-1)"
proof -
  have "x + 2 powr (-prec-1) = (x * 2 powr prec + 1/2) * 2 powr (-prec)"
    apply (subst distrib_right)
    apply (rule arg_cong2[where f="(+)"])
    apply (subst mult.assoc)
     apply (subst powr_add[symmetric], simp)
    by (simp add:algebra_simps powr_diff powr_add)
  also have "... = (x * 2 powr prec - 1/2 + 1) * 2 powr (-prec)"
    by simp
  also have "... \<ge>  \<lceil>x * 2 powr prec - 1/2\<rceil> * 2 powr (-prec)"
    apply (rule mult_right_mono)
    apply (meson of_int_ceiling_le_add_one)
    by simp
  finally show ?thesis by (simp add:round_nearest_def)
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

lemma truncate_nearest_le:
  "x - abs x * (2 powr (-prec-1)) \<le> truncate_nearest prec x"
proof (cases "abs x > 0")
  case True
  have " x - abs x * (2 powr (- real prec - 1)) \<le> x - 2 powr ((-int prec-1)  + \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
    apply (rule diff_mono, simp)
    apply (subst mult.commute)
    apply (subst of_int_add)
    apply (subst powr_add)
    apply (rule mult_mono, simp)
      apply (subst le_log_iff[symmetric], simp, metis True)
     apply (meson of_int_floor_le)
    by simp+
  also have "... =  x - 2 powr (-real_of_int (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)-1)"
    by (simp add:algebra_simps)
  also have "... \<le>  truncate_nearest prec x"
    apply (subst truncate_nearest_def)
    by (rule round_nearest_le)
  finally show ?thesis by blast
next
  case False
  hence "x = 0" by fastforce
  thus ?thesis
    by (simp add:truncate_nearest_def round_nearest_def ceiling_def)
qed

lemma truncate_nearest_le_pos:
  assumes "x \<ge> 0"
  shows "x * (1 - 2 powr (-prec-1)) \<le> truncate_nearest prec x"
  apply (subst right_diff_distrib)
  by (metis truncate_nearest_le abs_of_nonneg assms mult.right_neutral)

lemma truncate_nearest_ge:
  "truncate_nearest prec x \<le> x + abs x * (2 powr (-prec-1))"
proof (cases "abs x > 0")
  case True
  have "truncate_nearest prec x \<le> x + 2 powr (-real_of_int (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)-1)"
    apply (subst truncate_nearest_def)
    by (rule round_nearest_ge)
  also have "... = x + 2 powr ((-int prec-1)  + \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
    apply (rule arg_cong2[where f="(+)"], simp)
    by (simp add:algebra_simps)
  also have "... \<le> x + abs x * (2 powr (- real prec - 1))"
    apply (rule add_mono, simp)
    apply (subst mult.commute)
    apply (subst of_int_add)
    apply (subst powr_add)
    apply (rule mult_mono, simp)
      apply (subst le_log_iff[symmetric], simp, metis True)
     apply (meson of_int_floor_le)
    by simp+
  finally show ?thesis by simp
next
  case False
  hence "x = 0" by fastforce
  thus ?thesis
    by (simp add:truncate_nearest_def round_nearest_def ceiling_def)
qed

lemma truncate_nearest_ge_pos:
  assumes "x \<ge> 0"
  shows " truncate_nearest prec x \<le> x * (1 + 2 powr (-prec-1))"
  apply (subst distrib_left)
  by (metis truncate_nearest_ge abs_of_nonneg assms mult.right_neutral)

lemma truncate_nearest:
  "abs (x - truncate_nearest prec x) \<le> abs x * (2 powr (-prec-1))"
  apply (subst abs_le_iff)
  apply (rule conjI)
  using truncate_nearest_ge truncate_nearest_le 
  by (smt (verit, ccfv_SIG))+

lemma truncate_nearest_eq_bound:
  assumes "truncate_nearest r x = truncate_nearest r y"
  shows "abs (x - y) \<le> (abs x + abs y) * 2 powr (-real r-1)"
proof -
  have "abs (x - y) \<le> abs (x - truncate_nearest r x) + abs (y - truncate_nearest r x)"
    by linarith
  also have "... \<le> abs x * (2 powr (-real r-1)) + abs y * (2 powr (-real r -1))"
    by (rule add_mono, rule truncate_nearest, subst assms, rule truncate_nearest)
  also have "... = (abs x + abs y) * (2 powr (-real r-1))"
    by (simp add:distrib_right)
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