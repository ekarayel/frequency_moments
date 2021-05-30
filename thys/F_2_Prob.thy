theory F_2_Prob
  imports Main "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family"
begin

subsection \<open>Combinatorics\<close>

text \<open>In this section, we build combinatorial tools to be able to split powers of sums into summands
that can be evaluated using the same term structure. For example $\left(\Sigma_{i \in I} x_i\right)^2 = 
\Sigma_{i \in I} x_i^2 + \Sigma_{i,j \in I, i \neq j} x_i x_j$. In each summand the indices range
over distinct values. In the case of powers of 4 we end up with 5 distinct groups.

It seems tempting to also unify symmetric terms within the same group. For example:
\[
\Sigma_{i,j \in I, i \neq j} x_i x_j
\]
could also be written as
\[
2 \Sigma_{i,j \in I, i < j} x_i x_j
\]
The latter however would need to be undone, when we want to use the Hoelder-Inequaliy to approximate
some of the terms, hence the decision to just group by structure.\<close>

definition is_partition :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "is_partition n xs = ((sum_list xs = n) \<and> (sorted xs) \<and> (\<forall>x. x \<in> set xs \<longrightarrow> x > 0))"

lemma is_partition_max_length:
  assumes "is_partition n xs"
  shows "length xs \<le> n"
proof -
  have a:"\<forall>x. x \<in> set xs \<longrightarrow> x > 0" using assms is_partition_def by auto
  have b:"(\<forall>x. x \<in> set xs \<longrightarrow> x > 0) \<Longrightarrow> sum_list xs \<ge> length xs"
    apply (induction xs, simp, simp) 
    using add.left_commute by auto
  thus ?thesis using a b is_partition_def assms by force
qed

lemma two_partitions:
  assumes "is_partition 2 xs"
  shows "xs = [2] \<or> xs = [1,1]"
proof -
  have a:"length xs \<le> Suc (Suc 0)" using is_partition_max_length assms by force
  show "?thesis"
    apply (cases xs)
    using assms apply (simp add:is_partition_def)
     apply (cases "tl xs")
    using assms apply (simp add:is_partition_def)
     apply (cases "tl (tl xs)")
    using assms apply (simp add:is_partition_def, fastforce)
    using a by auto
qed

lemma four_partitions:
  assumes "is_partition 4 xs"
  shows "xs = [4] \<or> xs = [1,3] \<or> xs = [1,1,2] \<or> xs = [2,2] \<or> xs = [1,1,1,1]"
proof -
  have a:"length xs \<le> (Suc (Suc (Suc (Suc 0))))" using is_partition_max_length assms by force
  show "?thesis"
    apply (cases xs)
    using assms apply (simp add:is_partition_def)
     apply (cases "tl xs")
    using assms apply (simp add:is_partition_def)
     apply (cases "tl (tl xs)")
    using assms apply (simp add:is_partition_def, fastforce)
     apply (cases "tl (tl (tl xs))")
    using assms apply (simp add:is_partition_def, fastforce)
     apply (cases "tl (tl (tl (tl xs)))")
    using assms apply (simp add:is_partition_def, fastforce)
    using a by auto
qed

text \<open>Returns pairs representing the frequency and the associated element in a list, sorted in
increasing order by frequency. Two elements with the same frequency appear in original order.\<close>

definition counts :: "'a list \<Rightarrow> (nat \<times> 'a) list" where
  "counts xs = sort_key fst (map (\<lambda>x. (count_list xs x,x)) (remdups xs))"

definition select
  where "select xs k = snd ((counts xs) ! k)"

definition struct :: "'a list \<Rightarrow> nat list"
  where "struct xs = map fst (counts xs)"

fun prod_eval :: "('a \<Rightarrow> real) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real"
  where 
    "prod_eval f xs k [] = 1" |
    "prod_eval f xs k (a#as) = (f (select xs k) ^ a) * (prod_eval f xs (Suc k) as)"

lemma use_prod_eval:
  assumes "struct xs = a"
  shows "prod_list (map f xs) = prod_eval f xs 0 a"
  sorry


lemma
  assumes "struct xs = [1,1,2]"
  shows "prob_space.expectation \<Omega> (\<lambda>\<omega>. prod_list (map (\<lambda>i. real (n(i)) * h i \<omega>) xs)) = 
    \<alpha>^2 * prod_list (map (\<lambda>i. real (n(i))) xs)"
  using assms apply (simp add:use_prod_eval algebra_simps(23))
  sorry



definition lists_set
  where "lists_set n A = {x. length x = n \<and> set x \<subseteq> A}"

lemma list_set_zero: "lists_set 0 A = {[]}" by (simp add:lists_set_def, auto)
lemma list_set_suc: "lists_set (Suc n) A = (\<lambda>(u,v). u#v) ` (A \<times> lists_set n A)"
  apply (simp add:lists_set_def)
  apply (rule order_antisym)
  by (simp add:length_Suc_conv, force)+

definition lists_set_with_struct
  where "lists_set_with_struct a A = {x. struct x = a \<and> set x \<subseteq> A}"


lemma test_1:
  assumes "xs \<in> lists_set_with_struct [1,1,2] A"
  shows "prob_space.expectation \<Omega> (\<lambda>\<omega>. prod_list (map (\<lambda>i. real (n(i)) * h i \<omega>) xs)) = 
    \<alpha>^2 * prod_list (map (\<lambda>i. real (n(i))) xs)"
  using assms apply (simp add:use_prod_eval algebra_simps(23))
  sorry

lemma test_3: "prod_list (map (\<lambda>i. real (n i) * h i \<omega>) xs) =
               prod_list (map (\<lambda>i. real (n i)) xs) * 
               prod_list (map (\<lambda>i. h i \<omega>) xs)"
  by (induction xs, simp, simp)

lemma test_2:
  assumes "\<And>i. i \<in> A \<Longrightarrow> integrable \<Omega> (h i)"
  assumes "\<And>I. I \<subseteq> A \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 3 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h A" 
  shows "sum (\<lambda>xs. prob_space.expectation \<Omega> (\<lambda>\<omega>. prod_list (map (\<lambda>i. real (n i) * h i \<omega>) xs))) (lists_set_with_struct [1,1,2] A) = 
    sum (\<lambda>xs. \<alpha>^2 * prod_list (map (\<lambda>i. real (n i)) xs)) (lists_set_with_struct [1,1,2] A)"
proof -
  define f1 where "f1 = (\<lambda>xs. prod_list (map (\<lambda>i. real (n i)) xs))"

  have a:"\<And>xs \<omega>. prod_list (map (\<lambda>i. real (n i) * h i \<omega>) xs) = f1 xs * prod_list (map (\<lambda>i. h i \<omega>) xs)"
    by (simp add: test_3 f1_def) 

  show ?thesis
  apply (simp add:sum_def, rule comm_monoid_set.cong)
      apply (simp add: sum.comm_monoid_set_axioms, simp)
  apply (simp add:use_prod_eval lists_set_with_struct_def test_3) sorry  (* this is really cool *)


(*
  X = Z^2
  X^2 = Z^4

  E Z^4 - (E Z^2)^2


  Var(X) =
  sum_{i1,i2,i3,i4 in I} n(i1) n(i2) n(i3) n(i4) {
    (E h(i1) h(i2) h(i3) h(i4)) - (E h(i1) h(i2)) (Eh(i3) h(i4))}
  
  We cannot reorder anymore

  If {i1,i2,i3,i4} = {4}  then 0
     i1=i2,i3,i4          then 0 again
     i1=i3,i2,i4          then a^2 - a^4
     i1=i4,i2,i3          then a^2 - a^4
     i1,i2=i3,i4          then a^2 - a^4
     i1,i2=i4,i3          then a^2 - a^4
     i1,i2,i3=i4          then 0
     i1=i2=i3,i4          then 0
     i1=i2,i3=i4          then 0
     i1=i3,i2=i4          1
     i1=i4,i2=i3          1
     i1=i2=i3=i4          0

  Var(X) = 2 \sum_{i1,i2} n(i1)^2 n(i2)^2 \<le> 2 F_2^2

  a^2 - 

  E h(i2) E h(i4) - E h(i1) E h(i2) E h(i3) E h(i4)     \<le> 1



  sum_{i1,i2,i3,i4} n(i1) . = \sum n(i))^4 \<le> (\sum n(i)^2)^2


*)


qed

lemma "A^4 = A * (A::real) * A * A" sorry


lemma sum_pow: "(sum (f :: 'a \<Rightarrow> real) A)^n = sum (\<lambda>x. prod_list (map f x)) (lists_set n A)"
proof (induction n)
  case 0
  then show ?case by (simp add:list_set_zero) 
next
  case (Suc n)
  have "inj_on (\<lambda>(u,v). u#v) (A \<times> (lists_set n A))" 
    by (simp add: inj_on_def)
  
  hence a:"sum (\<lambda>x. prod_list (map f x)) (lists_set (Suc n) A) = sum (\<lambda>(u,v). prod_list (map f (u#v))) (A \<times> (lists_set n A))"
    apply (simp only: list_set_suc sum.reindex comp_def)
    by (metis (no_types, lifting) SigmaE split_conv sum.cong)

  show ?case apply (simp only: a) by (simp add: Suc sum_product sum.cartesian_product[symmetric])
qed

definition fun_set
  where "fun_set n A = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A}"

definition fun_set_with_ae
  where "fun_set_with_ae n A a = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A \<and> inj (a \<circ> x)}"


fun shift
  where 
    "shift k = (k+1)"

lemma sum_unroll_1:
  "sum (f :: 'a \<Rightarrow> real) A = sum (\<lambda>x. f (the (x 0))) (fun_set (Suc 0) A)" sorry

lemma sum_unroll_2:
  "sum (\<lambda>x. sum (\<lambda>y. f x y :: real) (fun_set n A)) A = sum (\<lambda>x. f (the (x 0)) (x \<circ> shift)) (fun_set (Suc n) A)" sorry

lemma factor_lint: 
(*  assumes "\<And>a.  a \<in> A \<Longrightarrow> integrable \<Omega> (f x)" *)
  shows "(LINT \<omega>|\<Omega>. (sum (\<lambda>x. f x \<omega>) A)) = sum (\<lambda>x. (LINT \<omega>|\<Omega>. (f x \<omega>))) A" sorry

lemma decomp_aes:
  "fun_set n A = fun_set_with_ae n A (\<lambda>x. x)"
  sorry

definition f2_sketch_summand
  where
    "f2_sketch_summand f xs x \<omega> = real (count_list xs x) * f x \<omega>"

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. f2_sketch_summand f xs x \<omega>)"

definition f2_tr
  where
    "f2_tr h xs n l \<omega> = prod_list (map (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) l)"

lemma c1: "f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr h xs n [k] \<omega>"
  sorry

lemma c2: "f2_tr h xs n a \<omega> * f2_tr h xs n b \<omega> = f2_tr h xs n (a@b) \<omega>"
  sorry

definition f2_tr_mset
  where
    "f2_tr_mset h xs M \<omega> = prod (\<lambda>x. (f2_sketch_summand h xs x \<omega>)^(count M x)) (set_mset M)"

lemma c3: 
  assumes "b \<in> fun_set_with_ae n A f"
  shows "f2_tr h xs b a \<omega> = f2_tr_mset h xs (make_mset f a b) \<omega>"
  sorry

lemma var_f2: (* todo assume that \<Omega> is a probability space *)
  fixes n :: "'a \<Rightarrow> real"
  fixes h :: "'a \<Rightarrow> nat \<Rightarrow> real"
  assumes "finite A"
  assumes "\<And>I. I \<subseteq> set xs \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h I" 
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> \<sigma> \<in> {-1::real, 1} \<Longrightarrow> prob_space.prob \<Omega> (h i -` {\<sigma>}) = 1/2"
  shows "(prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^4))
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch h xs \<omega>)^2))^2 \<le> (sum (\<lambda>i. (n i)^2) A)^2"
proof -
  have a:"\<And>x. x \<in> fun_set (Suc (Suc (Suc (Suc 0)))) (set xs) \<Longrightarrow> x (Suc (Suc 0)) = x 0" sorry
  have b:"\<And>\<omega> x. x \<in> fun_set (Suc (Suc (Suc (Suc 0)))) (set xs) \<Longrightarrow> (f2_sketch_summand h xs (the (x 0)) \<omega>) * (f2_sketch_summand h xs (the (x 0)) \<omega>) = 1"
    sorry

  show ?thesis
    apply (simp only: 
        f2_sketch_def power4_eq_xxxx power2_eq_square sum_product factor_lint 
        sum_distrib_left sum_distrib_right sum_subtractf[symmetric])
    apply (simp add: sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add:c1 c2)
    apply (simp add:decomp_aes)
  apply (simp only: sum_subtractf[symmetric])
  using [[simp_trace=true]]
  apply (simp only: sum_def sum_subtractf[symmetric])
  apply (subst sum_diff')
  apply (subst sum_diff)
  apply (subst sum_diff_lint)
  sorry

(*
  Decompose A into 15 different parts depending on the equivalence classes of {0,1,2,3}

  Evaluate f2_tr using the equivalence classes

  x in fun_set 4 (set xs) [0, 1, 2, 3] \<Longrightarrow> f2_tr h xs [the (x 2), the (x 1), the (x 2), the (x 0)]

  f2 [a,b,c,d]    f2' [(a,2),(b,1),(c,1)]   

  sum {x in A} sum {y in A} sum {z in A} sum {r in A} f x y z r

  sum {x in A} sum {y in list_set n A} f x y
  sum {x in list_set (Suc n) A} f (x ! n) x

  Result: sum_{A^4} n(1) n(2) n(3) n(4) {E h(1) h(2) h(3) h(4) - E h(1) h(2) E h(3) h(4)}
    break down into disjoint sums with conditions
    eliminate empty sums
    use independence to evaluate expectations



  Okey:

  E [sum_A x(a)]^2 = sum_A sum_A E x(a) x(b) * 

  [E [sum_A x(a)]^2]^2
  = E [sum_A x(a) sum_A x(a)] * E [sum_A x(a) sum_A x(a)]
  = E [sum_A x(a) sum_A x(a)] * E [sum_A x(a) sum_A x(a)]


  \<le> 2 (sum (n i))^4 

  (sum_A (n i)^2)^2 = sum_{i,j} n_i^2 n_j^2

*)


lemma var_f2: (* todo assume that \<Omega> is a probability space *)
  assumes "finite A"
  assumes "\<And>I. I \<subseteq> A \<Longrightarrow> finite I \<Longrightarrow> card I \<le> 4 \<Longrightarrow> prob_space.indep_vars \<Omega> (\<lambda>_. borel) h A" 
  assumes "\<And>i. i \<in> A \<Longrightarrow> \<sigma> \<in> {-1::real, 1} \<Longrightarrow> prob_space.prob \<Omega> (h i -` {\<sigma>}) = 1/2"
  shows "prob_space.expectation \<Omega> (\<lambda>\<omega>. ((sum (\<lambda>i. (h i \<omega>) * n i) A)^2)^2) 
       - (prob_space.expectation \<Omega> (\<lambda>\<omega>. (sum (\<lambda>i. (h i \<omega>) * n i) A)^2))^2 \<le> sum (\<lambda>i. (n i)^2) A"
  using assms apply (simp add:sum_4' sum_2')

(*
  Pull in the integral 

  \sum_{A^4} n(1) n(2) n(3) n(4) E h(1) h(2) h(3) h(4) - (\sum_{A^2} n(1) n(2) E h(1) h(2))^2

  \sum_{A^4} n(1) n(2) n(3) n(4) E h(1) h(2) h(3) h(4) - \sum_{A^2xA^2} n(1) n(2) E h(1) h(2) n(3) n(4) E h(3) h(4)
  \sum_{A^4} n(1)..n(4) {E h(1) .. h(4) - E h(1) h(2) E h(3) h(4) 

*)



(* 
  If at least one of elements in the list appears an odd number of times
  we can get a quotient of 1/p.
  However, it is not really feasible, i.e., there will be two of them if there is one.
*)


lemma "sum (f :: 'a \<Rightarrow> 'b:: semiring_0) A * sum g B = sum (\<lambda>(x,y). f x * g y) (A \<times> B)"
  by (simp add: sum.cartesian_product sum_product)

lemma sum_4: "(sum (f :: 'a \<Rightarrow> real) A)^(Suc (Suc (Suc (Suc 0)))) = sum (\<lambda>(x,y,z,u). f x * f y * f z * f u) (A \<times> A \<times> A \<times> A)"
  apply (simp add: sum.cartesian_product sum_product)
  by (metis (mono_tags, lifting) mult.assoc split_def)

definition counts :: "'a list \<Rightarrow> nat list" where
  "counts xs = sort (map (\<lambda>x. count_list xs x) (remdups xs))"

lemma sort_sum_inv: "sum_list (sort xs) = sum_list (xs :: nat list)"
  by (metis mset_sort sum_mset_sum_list)

lemma counts_sum: "sum_list (counts xs) = length xs"
  apply (simp add:counts_def sort_sum_inv)
  by (metis List.finite_set order_refl sum.set_conv_list sum_count_set)

lemma count_list_min: "y \<in> set xs \<Longrightarrow> count_list xs y > 0"
  by (induction xs, simp, simp, blast)

lemma counts_min:
  assumes "x \<in> set (counts xs)"
  shows "x > 0"
  using assms count_list_min apply (simp add:counts_def) by fastforce

lemma counts_max:
  assumes "x \<in> set (counts xs)"
  shows "x \<le> length xs"
  using assms count_le_length apply (simp add:counts_def) by fastforce

lemma counts_sorted: "sorted (counts xs)" by (simp add: counts_def)

lemma counts_are_partitions: "is_partition (length xs) (counts xs)"
  using is_partition_def by (simp add: counts_min counts_sorted counts_sum)

lemma counts_4_cases:
  assumes "length xs = 4"
  shows "
    counts xs = [1,1,1,1] \<or> counts xs = [1,1,2] \<or> counts xs = [1,3] \<or>
    counts xs = [2,2] \<or> counts xs = [4]"
  by (metis counts_are_partitions four_partitions assms)

definition lists_set_like
  where "lists_set_like n A c = {x. length x = n \<and> set x \<subseteq> A \<and> counts x = c}"

lemma decompose_list_set_4:
  "lists_set 4 A = 
    lists_set_like 4 A [1,1,1,1] \<union> lists_set_like 4 A [1,1,2] \<union>
    lists_set_like 4 A [1,3] \<union> lists_set_like 4 A [2,2] \<union> lists_set_like 4 A [4]"
  apply (simp add:lists_set_def lists_set_like_def)
  apply (rule order_antisym)
   apply (rule subsetI)
  using counts_4_cases apply fastforce
  by (rule subsetI, fastforce)

lemma disj_list_set:
  assumes "c \<noteq> d"
  shows "lists_set_like n A c \<inter> lists_set_like n A d = {}"
  apply (simp add:lists_set_like_def)
  apply (rule order_antisym)
   apply (rule subsetI)
  using assms apply force
  by (rule subsetI, force)

lemma decompose_sum:
  assumes "finite A"
  shows "sum (f :: 'a list \<Rightarrow> real) (lists_set 4 A) = sum f (lists_set_like 4 A [1,1,1,1]) + sum f (lists_set_like 4 A [1,1,2]) +
  sum f (lists_set_like 4 A [1,3]) + sum f (lists_set_like 4 A [2,2]) + sum f (lists_set_like 4 A [4])"
proof  -
  have a:"\<And>c. finite (lists_set_like 4 A c)" sorry
  have b:"lists_set_like 4 A [1,1,1,1] \<inter> lists_set_like 4 A [1,1,2] = {}"
    by (simp add: disj_list_set)
  have c:"(lists_set_like 4 A [1,1,1,1] \<union> lists_set_like 4 A [1,1,2]) \<inter> lists_set_like 4 A [1,3] = {}" 
    by (simp add: disj_list_set inf_sup_distrib2)
  have d:"(lists_set_like 4 A [1,1,1,1] \<union> lists_set_like 4 A [1,1,2] \<union> lists_set_like 4 A [1,3]) \<inter> lists_set_like 4 A [2,2] = {}" 
    by (simp add: disj_list_set inf_sup_distrib2)
  have e:"(lists_set_like 4 A [1,1,1,1] \<union> lists_set_like 4 A [1,1,2] \<union> lists_set_like 4 A [1,3] \<union> lists_set_like 4 A [2,2]) \<inter> lists_set_like 4 A [4] = {}" 
    by (simp add: disj_list_set inf_sup_distrib2)
  show ?thesis using a b c d e apply (simp add:sum.union_disjoint[symmetric])
  by (simp add: decompose_list_set_4)
qed

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. (count_list xs x) * f x \<omega>)"

lemma (in prob_space)
  "expectation X + expectation Y = expectation (\<lambda>\<omega>. X \<omega> + Y \<omega>)" 
  using integral_sum
  sorry

lemma
  assumes "prob_space \<Omega>"
  assumes "k \<in> U \<Longrightarrow> prob_space.random_variable \<Omega> (uniform_count_measure {-1,1}) (H k)"
  assumes "k \<in> U \<Longrightarrow> prob_space.prob \<Omega> (H k -` {-1}) = 1/2"
  assumes "k \<in> U \<Longrightarrow> prob_space.prob \<Omega> (H k -` {1}) = 1/2"
  shows "prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch H xs \<omega>)^4) < 3"
proof -
  have "prob_space.expectation \<Omega> (\<lambda>\<omega>. (f2_sketch H xs \<omega>)^4) =
    sum (\<lambda>xs. prob_space.expectation \<Omega> (\<lambda>\<omega>. prod_list (map (\<lambda>x. (count_list xs x) * H x \<omega>) xs))) (lists_set 4 (set xs))" 
    sorry
*)
  
  (*using assms apply (simp add:f2_sketch_def sum_pow integral_sum[symmetric]) *)

(*
  exp (F_2)^4 = exp (sum (\<lambda>x. prod_list (map (\<lambda>u. X u 


*)


  
(*
  E n(i1) * h(i1) * n(i2) * h(i2) * n(i3) * h(i3) * n(i4) * h(i4)
  = n(i1) * n(i2) * n(i3) * n(i4) * E h(i1) h(i2) h(i3) h(i4)
  = if like xs [4] then n(obtain 0 xs)^4 else
    if like xs [1,3] then 1/p^2 n(obtain 0 xs)^1 n(obtain 1 xs)^3 else 
    if like xs [2,2] then n(obtain 0 xs)^2 n(obtain 1 xs)^2 else
    if like xs [1,1,2] then 1/p^2 n(obtain 0 xs) n(obtain 1 xs) n(obtain 2 xs)^2 else
    if like xs [1,1,1,1] then 1/p^4 n(.. xs)

  sum (\x. fold ( * ) (map f x) 1) (lists_set_like 4 A [4]) +
  sum (\x. fold ( * ) (map f x) 1) (lists_set_like 4 A [1,3]) +
  sum (\x. fold ( * ) (map f x) 1) (lists_set_like 4 A [2,2]) +
  sum (\x. fold ( * ) (map f x) 1) (lists_set_like 4 A [1,1,2]) +
  sum (\x. fold ( * ) (map f x) 1) (lists_set_like 4 A [1,1,1,1])



  fold ( * ) (map f x) 1 = prod (x in set xs) (f x)^(count_of x xs)



  sum_i n(i) h(i) * (sum_i n(i))^3
   
  sum_i n(i) h(i) * sum_i n(i) h(i) * sum_i n(i) h(i) * sum_i n(i) h(i)
  






*)




end