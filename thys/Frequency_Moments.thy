section "Frequency Moments"

theory Frequency_Moments
  imports Main HOL.List HOL.Rat List_Ext Encoding     Universal_Hash_Families.Field
    Interpolation_Polynomials_HOL_Algebra.Interpolation_Polynomial_Cardinalities
begin

text \<open>This section contains a definition of the frequency moments of a stream.\<close>

definition F where
  "F k xs = (\<Sum> x \<in> set xs. (rat_of_nat (count_list xs x)^k))"

lemma F_gr_0:
  assumes "as \<noteq> []"
  shows "F k as > 0"
proof -
  have "rat_of_nat 1 \<le> rat_of_nat (card (set as))"
    apply (rule of_nat_mono)
    using assms card_0_eq[where A="set as"] 
    by (metis List.finite_set One_nat_def Suc_leI neq0_conv set_empty)
  also have "... \<le> F k as"
    apply (simp add:F_def)
    apply (rule sum_mono[where K="set as" and f="\<lambda>_.(1::rat)", simplified])
    by (metis  count_list_gr_1  of_nat_1 of_nat_power_le_of_nat_cancel_iff one_le_power)
  finally show  "F k as > 0" by simp
qed

lemma bounded_degree_polynomial_bit_count:
  assumes "p > 0"
  assumes "x \<in> bounded_degree_polynomials (Field.mod_ring p) n"
  shows "bit_count (list\<^sub>S N\<^sub>S x) \<le> ereal (real n * (2 * log 2 p + 2) + 1)" (is "_ \<le> ?rhs")
proof -
  have a:"length x \<le> n" 
    using  assms(2) by (simp add:bounded_degree_polynomials_length)
  have b:"\<And>y. y \<in> set x \<Longrightarrow> y \<le> p-1"
  proof -
    fix y
    assume "y \<in> set x"
    moreover have "x \<in> (carrier (poly_ring (Field.mod_ring p)))" 
      using bounded_degree_polynomials_def assms(2) by blast
    ultimately have "y \<in> carrier (Field.mod_ring p)"
      using univ_poly_carrier polynomial_def 
      by (metis empty_iff list.set(1) subset_code(1))
    hence "y < p"
      by (simp add:Field.mod_ring_def)
    thus "y \<le> p -1"
      using assms(1) by simp
  qed

  have "bit_count (list\<^sub>S N\<^sub>S x) \<le> ereal (length x) * (ereal (2 * log 2 (1 + real (p - 1)) + 1) + 1) + 1"
    apply (rule list_bit_count_est)
    apply (rule nat_bit_count_est[where m="p-1"])
    using b by simp
  also have "... \<le> ereal (n * ((2 * log 2 p + 1) + 1) + 1)"
    apply (simp, rule mult_mono)
    using a assms by simp+
  also have "... \<le> ?rhs"
    by (simp add:ac_simps)
  finally show ?thesis by simp
qed

end