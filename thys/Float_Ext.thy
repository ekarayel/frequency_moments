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

lemma float_bit_count_1:
  "bit_count (F\<^sub>S f) \<le> 6 + 2 * (log 2 (\<bar>mantissa f\<bar> + 1) + log 2 (\<bar>exponent f\<bar> + 1))" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs = bit_count (I\<^sub>S (mantissa f)) + bit_count (I\<^sub>S (exponent f))"
    by (simp add:F\<^sub>S_def dependent_bit_count)
  also have "... \<le> ereal (2 * log 2 (real_of_int (\<bar>mantissa f\<bar> + 1)) + 3) + ereal (2 * log 2 (real_of_int (\<bar>exponent f\<bar> + 1)) + 3)"
    by (intro int_bit_count_est_1 add_mono) auto
  also have "... = ?rhs"
    by simp
  finally show ?thesis by simp
qed

lemma float_bit_count_2:
  fixes m :: int
  fixes e :: int
  defines "f \<equiv> float_of (m * 2 powr e)"
  shows "bit_count (F\<^sub>S f) \<le> 6 + 2 * (log 2 (\<bar>m\<bar> + 2) + log 2 (\<bar>e\<bar> + 1))"
proof -
  have b:" (r + 1) * int i \<le> r * (2 ^ i - 1) + 1" if b_assms: "r \<ge> 1" for r :: int and i :: nat
  proof (cases "i > 0")
    case True
    have "(r + 1) * int i = r * i + 2 * int ((i-1)+1) - i"
      using True by (simp add:algebra_simps)
    also have "... \<le> r * i + int (2^1) * int (2^(i-1)) - i"
      using b_assms
      by (intro add_mono diff_mono mult_mono of_nat_mono suc_n_le_2_pow_n, simp_all)
    also have "... = r * i + 2^i - i"
      using True
      by (subst of_nat_mult[symmetric], subst power_add[symmetric], simp)
    also have "... = r *i + 1 * (2 ^ i - int i - 1) + 1"  by simp
    also have "... \<le> r *i + r * (2 ^ i - int i - 1) + 1"  
      using b_assms
      by (intro add_mono mult_mono, simp_all)
    also have "... = r * (2 ^ i - 1) + 1"
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  next
    case False
    hence "i = 0" by simp
    then show ?thesis by simp
  qed

  have a:"log 2 (\<bar>mantissa f\<bar> + 1) + log 2 (\<bar>exponent f\<bar> + 1) \<le> log 2 (\<bar>m\<bar>+2) + log 2 (\<bar>e\<bar>+1)"
  proof (cases "f=0")
    case True then show ?thesis by simp
  next
    case False
    moreover have "f = Float m e" 
      by (simp add:f_def Float.abs_eq) 
    ultimately obtain i :: nat where m_def: "m = mantissa f * 2 ^ i" and e_def: "e = exponent f - i"
      using denormalize_shift by blast

    have mantissa_ge_1: "1 \<le> \<bar>mantissa f\<bar>"
      using False mantissa_noteq_0 by fastforce

    have "(\<bar>mantissa f\<bar> + 1) * (\<bar>exponent f\<bar> + 1) = (\<bar>mantissa f\<bar> + 1) * (\<bar>e+i\<bar>+1)"
      by (simp add:e_def)
    also have "...  \<le>  (\<bar>mantissa f\<bar> + 1) * ((\<bar>e\<bar>+\<bar>i\<bar>)+1)"
      by (intro mult_mono add_mono, simp_all)
    also have "... = (\<bar>mantissa f\<bar> + 1) * ((\<bar>e\<bar>+1)+i)"
      by simp
    also have "... = (\<bar>mantissa f\<bar> + 1) * (\<bar>e\<bar>+1) + (\<bar>mantissa f\<bar>+1)*i"
      by (simp add:algebra_simps)
    also have "... \<le>  (\<bar>mantissa f\<bar> + 1)*(\<bar>e\<bar>+1) + (\<bar>mantissa f\<bar>*  (2^i-1)+1)" 
      by (intro add_mono b mantissa_ge_1, simp) 
    also have "... =  (\<bar>mantissa f\<bar> + 1)*(\<bar>e\<bar>+1)+(\<bar>mantissa f\<bar>*  (2^i-1)+1)*(1)"
      by simp
    also have "... \<le>  (\<bar>mantissa f\<bar> + 1)*(\<bar>e\<bar>+1)+(\<bar>mantissa f\<bar>*  (2^i-1)+1)*(\<bar>e\<bar>+1)" 
      by (intro add_mono mult_left_mono, simp_all)
    also have "... =  ((\<bar>mantissa f\<bar> + 1)+(\<bar>mantissa f\<bar>*  (2^i-1)+1))*(\<bar>e\<bar>+1)"
      by (simp add:algebra_simps)
    also have "... =  (\<bar>mantissa f\<bar>*2^i+2)*(\<bar>e\<bar>+1)" 
      by (simp add:algebra_simps)
    also have "... =  (\<bar>m\<bar>+2)*(\<bar>e\<bar>+1)" 
      by (simp add:m_def abs_mult)
    finally have "(\<bar>mantissa f\<bar> + 1) * (\<bar>exponent f\<bar> + 1) \<le> (\<bar>m\<bar>+2)*(\<bar>e\<bar>+1)" by simp

    hence "(\<bar>real_of_int (mantissa f)\<bar> + 1) * (\<bar>of_int (exponent f)\<bar> + 1) \<le> (\<bar>of_int m\<bar>+2)*(\<bar>of_int e\<bar>+1)" 
      by (simp flip:of_int_abs)
       (metis (mono_tags, opaque_lifting) numeral_One of_int_add of_int_le_iff of_int_mult of_int_numeral)
    then show ?thesis by (simp add:log_mult[symmetric])
  qed
  have "bit_count (F\<^sub>S f) \<le> 6 + 2 * (log 2 (\<bar>mantissa f\<bar> + 1) + log 2 (\<bar>exponent f\<bar> + 1))"
    using float_bit_count_1 by simp
  also have "... \<le> 6 + 2 * (log 2 (\<bar>m\<bar> + 2) + log 2 (\<bar>e\<bar> + 1))"
    using a by simp
  finally show ?thesis by simp
qed

lemma float_bit_count_zero:
  "bit_count (F\<^sub>S (float_of 0)) = 2"
  by (simp add:F\<^sub>S_def dependent_bit_count int_bit_count zero_float.abs_eq[symmetric])

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
  "bit_count (F\<^sub>S (float_of (truncate_down r x))) \<le> 10 + 4 * real r + 2*log 2 (2 + \<bar>log 2 \<bar>x\<bar>\<bar>)" 
  (is "?lhs \<le> ?rhs")
proof -
  define m where "m = \<lfloor>x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor>"
  define e where "e = \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - int r"

  have a: "(real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - real r) = e"
    by (simp add:e_def)
  have "abs m + 2 \<le> 2 ^ (r + 1) + 2^1"
    using truncate_mantissa_bound
    by (intro add_mono, simp_all add:m_def)
  also have "... \<le> 2 ^ (r+2)"
    by simp
  finally have b:"abs m + 2 \<le> 2 ^ (r+2)" by simp
  hence "real_of_int (\<bar>m\<bar> + 2) \<le> real_of_int (4 * 2 ^ r)" 
    by (subst of_int_le_iff, simp)
  hence "\<bar>real_of_int m\<bar> + 2 \<le> 4 * 2 ^ r" 
    by simp
  hence c:"log 2 (real_of_int (\<bar>m\<bar> + 2)) \<le> r+2"
    by (simp add: Transcendental.log_le_iff powr_add powr_realpow)

  have "real_of_int (abs e + 1) \<le> real_of_int \<bar>\<lfloor>log 2 \<bar>x\<bar>\<rfloor>\<bar> +  real_of_int r + 1"
    by (simp add:e_def)
  also have "... \<le> 1 + abs (log 2 (abs x)) + real_of_int r + 1"
    by (simp add:abs_le_iff, linarith)
  also have "... \<le> (real_of_int r+ 1) * (2 + abs (log 2 (abs x)))"
    by (simp add:distrib_left distrib_right)
  finally have d:"real_of_int (abs e + 1) \<le> (real_of_int r+ 1) * (2 + abs (log 2 (abs x)))" by simp

  have "log 2 (real_of_int (abs e + 1)) \<le> log 2 (real_of_int r + 1) + log 2 (2 + abs (log 2 (abs x)))"
    using d by (simp add: log_mult[symmetric])
  also have "... \<le> r + log 2 (2 + abs (log 2 (abs x)))"
    using log_est by (intro add_mono, simp_all add:add.commute)
  finally have e: "log 2 (real_of_int (abs e + 1)) \<le> r + log 2 (2 + abs (log 2 (abs x)))" by simp

  have "?lhs =  bit_count (F\<^sub>S (float_of (real_of_int m * 2 powr real_of_int e)))"
    by (simp add:truncate_down_def round_down_def m_def[symmetric] a)
  also have "... \<le> ereal (6 + (2 * log 2 (real_of_int (\<bar>m\<bar> + 2)) + 2 * log 2 (real_of_int (\<bar>e\<bar> + 1))))"
    using float_bit_count_2 by simp
  also have "... \<le> ereal (6 + (2 * real (r+2) + 2 * (r + log 2 (2 + abs (log 2 (abs x))))))"
    using c e
    by (subst ereal_less_eq, intro add_mono mult_left_mono, linarith+) 
  also have "... = ?rhs" by simp
  finally show ?thesis by simp
qed

end
