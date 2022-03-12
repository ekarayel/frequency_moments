theory Set_Ext
  imports Main
begin

lemma card_ordered_pairs:
  fixes M :: "('a ::linorder) set" 
  assumes "finite M"
  shows "2 * card {(x,y) \<in> M \<times> M. x < y} = card M * (card M - 1)"
proof -
  have a: "finite (M \<times> M)" using assms by simp

  have inj_swap: "inj (\<lambda>x. (snd x, fst x))"
    by (rule inj_onI, simp add: prod_eq_iff)

  have "2 * card {(x,y) \<in> M \<times> M. x < y} =
    card {(x,y) \<in> M \<times> M. x < y} + card ((\<lambda>x. (snd x, fst x))`{(x,y) \<in> M \<times> M. x < y})"
    by (simp add: card_image[OF inj_on_subset[OF inj_swap]])
  also have "... = card {(x,y) \<in> M \<times> M. x < y} + card {(x,y) \<in> M \<times> M. y < x}"
    by (auto intro: arg_cong[where f="card"] simp add:set_eq_iff image_iff)
  also have "... = card ({(x,y) \<in> M \<times> M. x < y} \<union> {(x,y) \<in> M \<times> M. y < x})"
    by (intro card_Un_disjoint[symmetric] a finite_subset[where B="M \<times> M"] subsetI) auto
  also have "... = card ((M \<times> M) - {(x,y) \<in> M \<times> M. x = y})"
    by (auto intro: arg_cong[where f="card"] simp add:set_eq_iff) 
  also have "... = card (M \<times> M) - card {(x,y) \<in> M \<times> M. x = y}"
    by (intro card_Diff_subset a finite_subset[where B="M \<times> M"] subsetI) auto
  also have "... = card M ^ 2 - card ((\<lambda>x. (x,x)) ` M)"
    using assms
    by (intro arg_cong2[where f="(-)"] arg_cong[where f="card"])
      (auto simp:power2_eq_square set_eq_iff image_iff)
  also have "... = card M ^ 2 - card M"
    by (intro arg_cong2[where f="(-)"] card_image inj_onI, auto)
  also have "... = card M * (card M - 1)"
    by (cases "card M \<ge> 0", auto simp:power2_eq_square algebra_simps)
  finally show ?thesis by simp
qed

end