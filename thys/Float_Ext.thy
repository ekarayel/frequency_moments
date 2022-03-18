section \<open>Float\<close>

text \<open>This section contains results about floating point numbers in addition to "HOL-Library.Float"\<close>

theory Float_Ext
  imports "HOL-Library.Float" Encoding
begin

lemma round_down_ge:
  "x \<le> round_down prec x + 2 powr (-prec)"
  using round_down_correct by (simp, meson diff_diff_eq diff_eq_diff_less_eq)

lemma truncate_down_ge:
  "x \<le> truncate_down prec x + abs x * 2 powr (-prec)"
proof (cases "abs x > 0")
  case True
  have "x \<le> round_down (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) x + 2 powr (-real_of_int(int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>))"
    by (rule round_down_ge)
  also have "... \<le> truncate_down prec x + 2 powr ( \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) * 2 powr (-real prec)"
    by (rule add_mono, simp_all add:powr_add[symmetric] truncate_down_def)
  also have "... \<le> truncate_down prec x + \<bar>x\<bar> * 2 powr (-real prec)"
    using True
    by (intro add_mono mult_right_mono, simp_all add:le_log_iff[symmetric])
  finally show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

lemma truncate_down_pos:
  assumes "x \<ge> 0"
  shows "x * (1 - 2 powr (-prec)) \<le> truncate_down prec x"
  by (simp add:right_diff_distrib diff_le_eq)
   (metis truncate_down_ge assms  abs_of_nonneg)

lemma truncate_down_eq:
  assumes "truncate_down r x = truncate_down r y"
  shows "abs (x-y) \<le> max (abs x) (abs y) * 2 powr (-real r)"
proof - 
  have "x - y \<le> truncate_down r x + abs x * 2 powr (-real r) - y"
    by (rule diff_right_mono, rule truncate_down_ge)
  also have "... \<le> y + abs x * 2 powr (-real r) - y"
    using truncate_down_le
    by (intro diff_right_mono add_mono, subst assms(1), simp_all)
  also have "... \<le> abs x * 2 powr (-real r)" by simp
  also have "... \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp
  finally have a:"x - y \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp

  have "y - x \<le> truncate_down r y + abs y * 2 powr (-real r) - x"
    by (rule diff_right_mono, rule truncate_down_ge)
  also have "... \<le> x + abs y * 2 powr (-real r) - x"
    using truncate_down_le
    by (intro diff_right_mono add_mono, subst assms(1)[symmetric], auto)
  also have "... \<le> abs y * 2 powr (-real r)" by simp
  also have "... \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp
  finally have b:"y - x \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp

  show ?thesis
    using abs_le_iff a b by linarith
qed

definition rat_of_float :: "float \<Rightarrow> rat" where 
  "rat_of_float f = of_int (mantissa f) * 
    (if exponent f \<ge> 0 then 2 ^ (nat (exponent f)) else 1 / 2 ^ (nat (-exponent f)))" 

lemma real_of_rat_of_float: "real_of_rat (rat_of_float x) = real_of_float x"
proof -
  have "real_of_rat (rat_of_float x) = mantissa x * (2 powr (exponent x))"
    by (simp add:rat_of_float_def of_rat_mult of_rat_divide of_rat_power powr_realpow[symmetric] powr_minus_divide)
  also have "... = real_of_float x"
    using mantissa_exponent by simp
  finally show ?thesis by simp 
qed

text \<open>Definition of an encoding for floating point numbers.\<close>

definition F\<^sub>S where "F\<^sub>S f = (I\<^sub>S \<times>\<^sub>S I\<^sub>S) (mantissa f,exponent f)"

lemma encode_float:
  "is_encoding F\<^sub>S"
proof -
  have a : "inj (\<lambda>x. (mantissa x, exponent x))"
  proof (rule injI)
    fix x y
    assume "(mantissa x, exponent x) = (mantissa y, exponent y)"
    hence "real_of_float x = real_of_float y"
      by (simp add:mantissa_exponent)
    thus "x = y"
      by (metis real_of_float_inverse)
  qed
  have "is_encoding (\<lambda>f. if True then ((I\<^sub>S \<times>\<^sub>S I\<^sub>S) (mantissa f,exponent f)) else None)"
    using a
    by (intro encoding_compose[where f="(I\<^sub>S \<times>\<^sub>S I\<^sub>S)"]  dependent_encoding int_encoding, simp)
  moreover have "F\<^sub>S = (\<lambda>f. if f \<in> UNIV then ((I\<^sub>S \<times>\<^sub>S I\<^sub>S) (mantissa f,exponent f)) else None)"
    by (rule ext, simp add:F\<^sub>S_def)
  ultimately show "is_encoding F\<^sub>S"
    by simp
qed

lemma truncate_mantissa_bound:
  "abs (\<lfloor>x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor>) \<le> 2 ^ (r+1)" (is "?lhs \<le> _")
proof -
  define q where "q = \<lfloor>x * 2 powr (real r - real_of_int (\<lfloor>log 2 \<bar>x\<bar>\<rfloor>))\<rfloor>"

  have "abs q \<le> 2 ^ (r + 1)" if a:"x > 0"
  proof -
    have "abs q = q"
      using a by (intro abs_of_nonneg, simp add:q_def)
    also have "... \<le> x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
      unfolding q_def using of_int_floor_le by blast
    also have "... = x * 2 powr real_of_int (int r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
      by auto
    also have "... = 2 powr (log 2 x + real_of_int (int r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>))"
      using a by (simp add:powr_add)
    also have "... \<le> 2 powr (real r + 1)"
      using a by (intro powr_mono, linarith+) 
    also have "... = 2 ^ (r+1)"
      by (subst powr_realpow[symmetric], simp_all add:add.commute)
    finally show "abs q \<le> 2 ^ (r+1)" 
      by (metis of_int_le_iff of_int_numeral of_int_power)
  qed
    
  moreover have "abs q \<le> (2 ^ (r + 1))" if a: "x < 0"
  proof -
    have "-(2 ^ (r+1) + 1) = -(2 powr (real r + 1)+1)"
      by (subst powr_realpow[symmetric], simp_all add: add.commute)
    also have  "... < -(2 powr (log 2 (- x) + (r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)) + 1)"
      using a by (simp, linarith)
    also have "... = x * 2 powr (r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) - 1"
      using a by (simp add:powr_add)
    also have "... \<le> q"
      by (simp add:q_def)
    also have "... = - abs q"
      using a
      by (subst abs_of_neg, simp_all add: mult_pos_neg2 q_def)
    finally have "-(2 ^ (r+1)+1) < - abs q" using of_int_less_iff by fastforce
    hence "-(2 ^ (r+1)) \<le> - abs q" by linarith
    thus "abs q \<le> 2^(r+1)" by linarith
  qed

  moreover have "x = 0 \<Longrightarrow> abs q \<le> 2^(r+1)"
    by (simp add:q_def)
  ultimately have "abs q \<le> 2^(r+1)"
    by fastforce
  thus ?thesis using q_def by blast
qed

lemma suc_n_le_2_pow_n:
  fixes n :: nat
  shows "n + 1 \<le> 2 ^ n"
  by (induction n, simp, simp)

lemma float_bit_count:
  fixes m :: int
  fixes e :: int
  defines "f \<equiv> float_of (m * 2 powr e)"
  shows "bit_count (F\<^sub>S f) \<le> 4 + 2 * (log 2 (\<bar>m\<bar> + 2) + log 2 (\<bar>e\<bar> + 1))"
proof (cases "m \<noteq> 0")
  case True
  have "f = Float m e" 
    by (simp add: f_def Float.abs_eq)
  moreover have f_ne_0: "f \<noteq> 0" using True apply (simp add:f_def) 
    by (metis Float.compute_is_float_zero Float.rep_eq is_float_zero.rep_eq real_of_float_inverse zero_float.rep_eq)
  ultimately obtain i :: nat where m_def: "m = mantissa f * 2 ^ i" and e_def: "e = exponent f - i"
    using  denormalize_shift by blast

  have b:"abs (real_of_int (mantissa f)) \<ge> 1" 
    by (meson dual_order.refl f_ne_0 mantissa_noteq_0 of_int_leD)

  have c: "2*i \<le> 2^i"
    apply (cases "i > 0")
      using suc_n_le_2_pow_n[where n="i-1"] apply simp
     apply (metis One_nat_def nat_mult_le_cancel_disj power_commutes power_minus_mult)
    by simp

  have a:"\<bar>real_of_int (mantissa f)\<bar> * (real i + 1) + real i \<le> \<bar>real_of_int (mantissa f)\<bar> * 2 ^ i + 1" 
  proof (cases "i \<ge> 1")
    case True
    have "\<bar>real_of_int (mantissa f)\<bar> * (real i + 1) + real i = \<bar>real_of_int (mantissa f)\<bar> * (real i + 1) + (real i - 1) + 1"
      by simp
    also have "...  \<le> \<bar>real_of_int (mantissa f)\<bar> * ((real i + 1) + (real i - 1)) + 1"
      apply (subst (2) distrib_left)
      apply (rule add_mono)
       apply (rule add_mono, simp)
       apply (rule order_trans[where y="1* (real i - 1)"], simp)
       apply (rule mult_right_mono, metis b)
       using True apply simp
      by simp
    also have "... = \<bar>real_of_int (mantissa f)\<bar> * (2 * real i) + 1"
      by simp
    also have "... \<le> \<bar>real_of_int (mantissa f)\<bar> * 2 ^ i + 1"
      apply (rule add_mono)
       apply (rule mult_left_mono) 
       using c of_nat_mono apply fastforce
      by simp+
    finally show ?thesis by simp
  next
    case False
    hence "i = 0" by simp
    then show ?thesis by simp
  qed 

  have "bit_count (F\<^sub>S f) = bit_count (I\<^sub>S (mantissa f)) + bit_count (I\<^sub>S (exponent f))"
    by (simp add: F\<^sub>S_def dependent_bit_count)
  also have "... \<le> 
      ereal (2 * (log 2 (real_of_int (abs (mantissa f) + 1)))+ 2) + 
      ereal (2 * (log 2 (real_of_int (abs (exponent f) + 1)))+ 2)"
    by (rule add_mono, rule int_bit_count, rule int_bit_count)
  also have "... = ereal (4 + 2 * (log 2 (real_of_int (abs (mantissa f)) + 1) + 
                                   log 2 (real_of_int (abs (e + i)) + 1)))"
    by (simp add:algebra_simps e_def)
  also have "... \<le> ereal (4 + 2 * (log 2 (real_of_int (abs (mantissa f)) + 1) +
                                    log 2 (real i+1) +
                                    log 2 (abs e + 1)))"
    apply (simp)
    apply (subst distrib_left[symmetric])
    apply (rule mult_left_mono)
     apply (subst log_mult[symmetric], simp, simp, simp, simp)
     apply (subst log_le_cancel_iff, simp, simp, simp)
    apply (rule order_trans[where y=" abs e + real i + 1"], simp)
    by (simp add:algebra_simps, simp)
  also have "... \<le> ereal (4 + 2 * (log 2 (real_of_int (abs (mantissa f * 2 ^ i)) + 2) +
    log 2 (abs e + 1)))"
    apply (simp)
    apply (subst distrib_left[symmetric])
    apply (rule mult_left_mono)
     apply (subst log_mult[symmetric], simp, simp, simp, simp)
     apply (subst log_le_cancel_iff, simp, simp, simp)
     apply (subst abs_mult)
     using a apply (simp add: distrib_right)
    by simp
  also have "... = ereal (4 + 2 * (log 2 (real_of_int (abs m) + 2) + log 2 (abs e + 1)))"
    by (simp add:m_def)
  finally show ?thesis by (simp add:f_def[symmetric] bit_count_append del:I\<^sub>S.simps)
next
  case False
  hence "float_of (m * 2 powr e) = Float 0 0"
    apply simp 
    using zero_float.abs_eq by linarith
  then show ?thesis by (simp add: f_def F\<^sub>S_def N\<^sub>S_def dependent_bit_count)
qed

lemma float_bit_count_zero:
  "bit_count (F\<^sub>S (float_of 0)) = 4"
  by (simp add:F\<^sub>S_def N\<^sub>S_def dependent_bit_count  zero_float.abs_eq[symmetric])

lemma log_est: "log 2 (real n + 1) \<le> n"
proof -
  have "1 + real n = real (n + 1)"
    by simp
  also have "... \<le> real (2 ^ n)"
    by (intro of_nat_mono suc_n_le_2_pow_n)
  also have "... = 2 powr (real n)"
    by (simp add:powr_realpow)
  finally have "1 + real n \<le> 2 powr (real n)"
    by simp
  thus ?thesis
    by (simp add: Transcendental.log_le_iff)
qed

lemma truncate_float_bit_count:
  "bit_count (F\<^sub>S (float_of (truncate_down r x))) \<le> 8 + 4 * real r + 2*log 2 (2 + abs (log 2 (abs x)))" 
  (is "?lhs \<le> ?rhs")
proof -
  define m where "m = \<lfloor>x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor>"
  define e where "e = \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - int r"

  have a: "real r = real_of_int (int r)" by simp
  have "abs m + 2 \<le> 2 ^ (r + 1) + 2^1"
    apply (rule add_mono)
     using truncate_mantissa_bound apply (simp add:m_def)
    by simp
  also have "... \<le> 2 ^ (r+2)"
    by simp
  finally have b:"abs m + 2 \<le> 2 ^ (r+2)" by simp
  have c:"log 2 (real_of_int (\<bar>m\<bar> + 2)) \<le> r+2"
    apply (subst Transcendental.log_le_iff, simp, simp)
    apply (subst powr_realpow, simp)
    by (metis of_int_le_iff of_int_numeral of_int_power b)

  have "real_of_int (abs e + 1) \<le> real_of_int \<bar>\<lfloor>log 2 \<bar>x\<bar>\<rfloor>\<bar> +  real_of_int r + 1"
    by (simp add:e_def)
  also have "... \<le> 1 + abs (log 2 (abs x)) + real_of_int r + 1"
    apply (simp)
    apply (subst abs_le_iff)
    by (rule conjI, linarith, linarith)
  also have "... \<le> (real_of_int r+ 1) * (2 + abs (log 2 (abs x)))"
    by (simp add:distrib_left distrib_right)
  finally have d:"real_of_int (abs e + 1) \<le> (real_of_int r+ 1) * (2 + abs (log 2 (abs x)))" by simp

  have "log 2 (real_of_int (abs e + 1)) \<le> log 2 (real_of_int r + 1) + log 2 (2 + abs (log 2 (abs x)))"
    apply (subst log_mult[symmetric], simp, simp, simp, simp)
    using d by simp
  also have "... \<le> r + log 2 (2 + abs (log 2 (abs x)))"
    apply (rule add_mono)
    using log_est apply (simp add:add.commute)
    by simp
  finally have e: "log 2 (real_of_int (abs e + 1)) \<le> r + log 2 (2 + abs (log 2 (abs x)))" by simp

  have "?lhs \<le> ereal (4 + (2 * log 2 (real_of_int (\<bar>m\<bar> + 2)) + 2 * log 2 (real_of_int (\<bar>e\<bar> + 1))))"
    apply (simp add:truncate_down_def round_down_def m_def[symmetric])
    apply (subst a, subst of_int_diff[symmetric], subst e_def[symmetric])
    using float_bit_count by simp
  also have "... \<le> ereal (4 + (2 * real (r+2) + 2 * (r + log 2 (2 + abs (log 2 (abs x))))))"
    apply (subst ereal_less_eq)
    apply (rule add_mono, simp)
    apply (rule add_mono, rule mult_left_mono, metis c, simp)
    by (rule mult_left_mono, metis e, simp)
  also have "... = ?rhs"  by simp
  finally show ?thesis by simp
qed

end
