theory Frequency_Moment_2
  imports Main "HOL-Probability.Probability_Measure" "HOL-Library.Multiset"
    "HOL-Probability.Independent_Family" "HOL-Algebra.Congruence"
begin

section \<open>Frequency Moment 2\<close>

subsection \<open>Partitions on Indexes\<close>

text \<open>A partition on an index set I (for example I = {0,..,3}) can be represented using a canonical
mapping g that maps each element to the smallest element of its class.

For example the partition {{0,1},{2},{3}} would be represented by the mapping k -> [0,0,2,3] ! k.

In the following we build an enumerator that returns all possible partitions of {0,..,n-1}, 
represented using a list of canonical mappings.\<close>

fun enum_canonical_mapping
  where 
    "enum_canonical_mapping 0 = [id]" |
    "enum_canonical_mapping (Suc n) = [(\<lambda>k. if k < n then x k else y). x \<leftarrow> enum_canonical_mapping n, y \<leftarrow> n#(remdups (map x [0..<n]))]" 

(* TODO: Proof that this indeed works. *)

subsection \<open>Sketch\<close>

definition f2_sketch_summand
  where
    "f2_sketch_summand f xs x \<omega> = real (count_list xs x) * f x \<omega>"

definition f2_sketch
  where
    "f2_sketch f xs \<omega> = (\<Sum> x \<in> set xs. f2_sketch_summand f xs x \<omega>)"

text \<open>Set of mappings with domain ${0,..,n-1}$ and Range A\<close>

definition fun_set
  where "fun_set n A = {x. dom x = {k. k < n} \<and> ran x \<subseteq> A}"

definition fun_set_inj
  where "fun_set_inj n A = 
    {x. dom x = {k. k < n} \<and> ran x \<subseteq> A \<and> inj_on x {k. k < n}}"


text \<open>Set of mappings with domain ${0,..,n-1}$ and Range A inducing a given partition on the domain\<close>

definition fun_set_with_partition
  where "fun_set_with_partition n p A = 
    {x. dom x = {k. k < n} \<and> ran x \<subseteq> A \<and> x \<circ> p = x \<and> inj_on x (p ` {k. k < n})}"

fun shift where "shift k = (k+1)"

lemma sum_unroll_1:
  "sum (f :: 'a \<Rightarrow> real) A = sum (\<lambda>x. f (the (x 0))) (fun_set (Suc 0) A)" sorry

lemma sum_unroll_2:
  "sum (\<lambda>x. sum (\<lambda>y. f x y :: real) (fun_set n A)) A = sum (\<lambda>x. f (the (x 0)) (x \<circ> shift)) (fun_set (Suc n) A)" sorry

lemma factor_lint: 
(*  assumes "\<And>a.  a \<in> A \<Longrightarrow> integrable \<Omega> (f x)" *)
  shows "(LINT \<omega>|\<Omega>. (sum (\<lambda>x. f x \<omega>) A)) = sum (\<lambda>x. (LINT \<omega>|\<Omega>. (f x \<omega>))) A" sorry

lemma split_fun_set_into_partitions:
  "fun_set n A = (\<Union> x \<in> set (enum_canonical_mapping n). fun_set_with_partition n x A)"
  sorry

lemma split_fun_set_sum_into_partitions:
  "sum (f :: ((nat \<Rightarrow> 'a option) \<Rightarrow> real)) (fun_set n A) = sum_list (map (\<lambda>x. sum f (fun_set_with_partition n x A)) (enum_canonical_mapping n))"
  sorry

(*
  [0,1,2,3] \<rightarrow> [0,1]
  g

  {0,1} \<rightarrow> A \<Rightarrow> {0,1,2,3} \<rightarrow> A
  (\x k. x (g k))

  f : ({0,1,2,3} \<rightarrow> A) \<rightarrow> R

  
  
*)


definition f2_tr
  where
    "f2_tr h xs n l \<omega> = prod_list (map (\<lambda>i. f2_sketch_summand h xs (the (n i)) \<omega>) l)"

lemma c1: "f2_sketch_summand h xs (the (n k)) \<omega> = f2_tr h xs n [k] \<omega>"
  sorry

lemma c2: "f2_tr h xs n a \<omega> * f2_tr h xs n b \<omega> = f2_tr h xs n (a@b) \<omega>"
  sorry

definition f2_tr_mset
  where
    "f2_tr_mset h xs y M = (\<lambda>\<omega>. prod (\<lambda>x. (f2_sketch_summand h xs (the (y x)) \<omega>)^(count M x)) (set_mset M))"

(*
  {{0,1,2},{3}}

  x : {0,..,3} \<rightarrow> U
  a : [0,1]

*)

fun test_mset  where
  "test_mset x = (if x = 3 then 2 else 0)"

fun counts where
  "counts xs = map (\<lambda>x. (x,count_list xs x)) (remdups xs)" 


fun make_mset where
  "make_mset a p = counts (map p a)" 

(* map p a *)
(* 3 1 3 *)

lemma c4: 
  assumes "x \<in> fun_set_with_partition n p A"
  shows "integral\<^sup>L \<Omega> (f2_tr h xs x a) = prod_list (map (\<lambda>(i,j). (LINT \<omega>|\<Omega>. (f2_sketch_summand h xs (the (x i)) \<omega>)^j)) (make_mset a p))"
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
  have b:"\<And>x p j \<omega>. x \<in> fun_set_with_partition (Suc (Suc (Suc (Suc 0)))) p (set xs) \<Longrightarrow> j <  (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> 
    (f2_sketch_summand h xs (the (x j)) \<omega>) *  (f2_sketch_summand h xs (the (x j)) \<omega>) = real (count_list xs (the (x j)))"
    sorry

  have c:"\<And>x p j. x \<in> fun_set_with_partition  (Suc (Suc (Suc (Suc 0)))) p (set xs) \<Longrightarrow> j <  (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> (LINT \<omega>|\<Omega>. (f2_sketch_summand h xs (the (x j)) \<omega>)) = 0"
    sorry

  show ?thesis
    apply (simp only: 
        f2_sketch_def power4_eq_xxxx power2_eq_square sum_product factor_lint 
        sum_distrib_left sum_distrib_right sum_subtractf[symmetric])
    apply (simp add: sum_unroll_1[where A="set xs"] sum_unroll_2)
    apply (simp add: c1 c2)
    apply (simp add: split_fun_set_sum_into_partitions) (* TODO *)
    apply (simp add: c4 c b)
  sorry




end