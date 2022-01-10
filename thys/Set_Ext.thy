theory Set_Ext
imports Main
begin

text \<open>This is like @{thm [source] card_vimage_inj} but supports @{term "inj_on"} instead.\<close>
lemma card_vimage_inj_on:
  assumes "inj_on f B"
  assumes "A \<subseteq> f ` B"
  shows "card (f -` A \<inter> B) = card A"
proof -
  have "A = f ` (f -` A \<inter> B)" using assms(2) by auto
  thus ?thesis using assms card_image 
    by (metis inf_le2 inj_on_subset)
qed

lemma card_ordered_pairs:
  fixes M :: "('a ::linorder) set" 
  assumes "finite M"
  shows "2 * card {(x,y) \<in> M \<times> M. x < y} = card M * (card M - 1)"
proof -
  have "2 * card {(x,y) \<in> M \<times> M. x < y} =
    card {(x,y) \<in> M \<times> M. x < y} + card ((\<lambda>x. (snd x, fst x))`{(x,y) \<in> M \<times> M. x < y})"
    apply (subst card_image)
    apply (rule inj_onI, simp add:case_prod_beta prod_eq_iff)
    by simp
  also have "... = card {(x,y) \<in> M \<times> M. x < y} + card {(x,y) \<in> M \<times> M. y < x}"
    apply (rule arg_cong2[where f="(+)"], simp)
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym)
     apply (rule image_subsetI, simp add:case_prod_beta)
    apply (rule subsetI, simp) 
    using image_iff by fastforce 
  also have "... = card ({(x,y) \<in> M \<times> M. x < y} \<union> {(x,y) \<in> M \<times> M. y < x})"
    apply (rule card_Un_disjoint[symmetric])
    apply (rule finite_subset[where B="M \<times> M"], rule subsetI, simp add:case_prod_beta mem_Times_iff)
    using assms apply simp
    apply (rule finite_subset[where B="M \<times> M"], rule subsetI, simp add:case_prod_beta mem_Times_iff)
    using assms apply simp
    apply (rule order_antisym, rule subsetI, simp add:case_prod_beta, force) 
    by simp
  also have "... = card ((M \<times> M) - {(x,y) \<in> M \<times> M. x = y})"
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym, rule subsetI, simp add:case_prod_beta, force)
    by (rule subsetI, simp add:case_prod_beta, force)
  also have "... = card (M \<times> M) - card {(x,y) \<in> M \<times> M. x = y}"
    apply (rule card_Diff_subset)
    apply (rule finite_subset[where B="M \<times> M"], rule subsetI, simp add:case_prod_beta mem_Times_iff)
    using assms apply simp
    by (rule subsetI, simp add:case_prod_beta mem_Times_iff)
  also have "... = card M ^ 2 - card ((\<lambda>x. (x,x)) ` M)"
    apply (rule arg_cong2[where f="(-)"])
    using assms apply (simp add:power2_eq_square)
    apply (rule arg_cong[where f="card"])
    apply (rule order_antisym, rule subsetI, simp add:case_prod_beta, force)
    by (rule image_subsetI, simp)
  also have "... = card M ^ 2 - card M"
    apply (rule arg_cong2[where f="(-)"], simp)
    apply (rule card_image)
    by (rule inj_onI, simp)
  also have "... = card M * (card M - 1)"
    apply (cases "card M \<ge> 0", simp add:power2_eq_square algebra_simps)
    by simp
  finally show ?thesis by simp
qed

end