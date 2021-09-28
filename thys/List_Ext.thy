theory List_Ext
  imports Main "HOL.List"
begin

lemma count_list_gr_1:
  "(x \<in> set xs) = (count_list xs x \<ge> 1)"
  by (induction xs, simp, simp)

lemma count_list_append: "count_list (xs@ys) v = count_list xs v + count_list ys v"
  by (induction xs, simp, simp)

end