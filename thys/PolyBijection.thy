theory PolyBijection
  imports Main "HOL-Algebra.Polynomial_Divisibility" "HOL-Algebra.Polynomials" LangrangePolynomial
begin

text \<open>
  If a function from A to B is surjective and card A = card B 
  then the function must also be injective. 

  We can extend that principle, i.e., if there are at least n distinct elements
  mapping to each element in A. And card B = n * card A. Then, it must be that
  there are always exactly n elements mapping to each element.
\<close>

lemma sum_tight:
  assumes "finite B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> n \<le> (f x::nat)"
  assumes "sum f B \<le> n * card B"
  shows "\<And>x. x \<in> B \<Longrightarrow> f x = n"
proof (rule ccontr)
  fix x
  assume a:"x \<in> B"
  assume "f x \<noteq> n"
  hence d:"f x > n" using assms(2) a le_neq_implies_less by blast
  define B' where "B' = B - {x}"
  hence b:"B = insert x B'" using a B'_def by auto
  have c:"x \<notin> B'" using B'_def by auto
  moreover have "finite B'" using assms(1) B'_def by auto
  ultimately have "sum f B = sum f B' + f x" by (simp add:b)
  moreover have "B' \<subseteq> B" using B'_def by auto
  hence "sum f B' \<ge> n * card B'" using assms(2) 
    by (metis (no_types, hide_lams) id_apply mult.commute of_nat_eq_id subset_iff sum_bounded_below)
  moreover have "card B = Suc (card B')" using b c  assms(1) by auto
  ultimately have "n * (Suc (card B')) \<ge> n * card B' + f x" using assms(3) by auto
  thus "False" using d by auto
qed

lemma generalized_inj_if_surj:
  assumes "finite B"
  assumes "finite A"
  assumes "\<And> y. y \<in> B \<Longrightarrow> card (f -` {y} \<inter> A) \<ge> n"
  assumes "card A = n * card B"
  shows "\<And>y. y \<in> B \<Longrightarrow> card (f -` {y} \<inter> A) = n"
proof -
  have "(\<Union> y\<in> B. (f -` {y} \<inter> A)) \<subseteq> A" by blast
  moreover have "sum (\<lambda>y. card (f -` {y} \<inter> A)) B = card (\<Union> y\<in> B. (f -` {y} \<inter> A))"
    apply (rule card_UN_disjoint[symmetric])
    by ((simp add:assms)+, fastforce)
  ultimately have "sum (\<lambda>y. card (f -` {y} \<inter> A)) B \<le>  n * card B"
    by (simp add: assms(2) card_mono assms(4)[symmetric])
  thus "\<And>y. y \<in> B \<Longrightarrow> (\<lambda>y. card (f -` {y} \<inter> A)) y = n"
    using sum_tight[where f ="(\<lambda>y. card (f -` {y} \<inter> A))"] assms(3) assms(1) by auto
qed

(*
definition poly_bijection where*)
(*  "poly_bijection K n p = (\<lambda>x. *)

(*
  f : poly n \<rightarrow> (F^K)

  \<Rightarrow> forall y. card(f -` {y}) \<ge> (card F)^(n-card K)

  if there were at least which was strictly more than we use up our treshold

*)


end