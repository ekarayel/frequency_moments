section "Frequency Moments"

theory Frequency_Moments
  imports Main HOL.List HOL.Rat List_Ext
begin

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

end