section \<open>Encoding\<close>

theory Encoding
  imports Main "HOL-Library.Sublist" "HOL-Library.Extended_Real" "HOL-Library.FuncSet" 
  "HOL.Transcendental" "HOL-Library.Float" "HOL-Analysis.Complex_Transcendental"
begin

fun is_prefix where 
  "is_prefix (Some x) (Some y) = prefix x y" |
  "is_prefix _ _ = False"

type_synonym 'a encoding = "'a \<rightharpoonup> bool list"

definition is_encoding :: "'a encoding \<Rightarrow> bool"
  where "is_encoding f = (\<forall>x y. is_prefix (f x) (f y) \<longrightarrow> x = y)"

lemma encoding_imp_inj:
  assumes "is_encoding f"
  shows "inj_on f (dom f)"
  apply (rule inj_onI)
  using assms by (simp add:is_encoding_def, force)

definition decode where 
  "decode f t = (
    if (\<exists>!z. is_prefix (f z) (Some t)) then 
      (let z = (THE z. is_prefix (f z) (Some t)) in (z, drop (length (the (f z))) t))
    else 
      (undefined, t)
    )"

lemma decode_elim:
  assumes "is_encoding f"
  assumes "f x = Some r"
  shows "decode f (r@r1) = (x,r1)"
proof -
  have a:"\<And>y. is_prefix (f y) (Some (r@r1)) \<Longrightarrow> y = x"
  proof -
    fix y
    assume "is_prefix (f y) (Some (r@r1))"
    then obtain u where u_1: "f y = Some u" "prefix u (r@r1)"
      by (metis is_prefix.elims(1) option.sel)
    hence "prefix u r \<or> prefix r u" 
      using prefix_def prefix_same_cases by blast
    hence "is_prefix (f y) (f x) \<or> is_prefix (f x) (f y)"
      using u_1 assms(2) by simp
    thus "y = x"
      using assms(1) apply (simp add:is_encoding_def) by blast
  qed
  have b:"is_prefix (f x) (Some (r@r1))" 
    using assms(2) by simp
  have c:"\<exists>!z. is_prefix (f z) (Some (r@r1))" 
    using a b by auto
  have d:"(THE z. is_prefix (f z) (Some (r@r1))) = x" 
    using a b by blast
  show "decode f (r@r1) = (x,r1)"
    using c d assms(2) by  (simp add: decode_def)
qed

lemma decode_elim_2:
  assumes "is_encoding f"
  assumes "x \<in> dom f"
  shows "decode f (the (f x)@r1) = (x,r1)"
  using assms decode_elim by fastforce

lemma snd_decode_suffix:
  "suffix (snd (decode f t)) t"
proof (cases "\<exists>!z. is_prefix (f z) (Some t)")
  case True
  then obtain z where  "is_prefix (f z) (Some t)" by blast
  hence "(THE z. is_prefix (f z) (Some t)) = z" using True by blast
  thus ?thesis using True by (simp add: decode_def suffix_drop)
next
  case False
  then show ?thesis by (simp add:decode_def)
qed

lemma snd_decode_len:
  assumes "decode f t = (u,v)"
  shows "length v \<le> length t"
  using snd_decode_suffix assms suffix_length_le 
  by (metis snd_conv)

lemma encoding_by_witness:
  assumes "\<And>x y. x \<in> dom f \<Longrightarrow> g (the (f x)@y) = (x,y)"
  shows "is_encoding f"
proof -
  have "\<And>x y. is_prefix (f x) (f y) \<Longrightarrow> x = y"
  proof -
    fix x y
    assume a:"is_prefix (f x) (f y)"
    then obtain d where d_def:"the (f x)@d = the (f y)"
      apply (case_tac [!] "f x", case_tac [!] "f y", simp, simp, simp, simp)
      by (metis prefixE)
    have "x \<in> dom f" using a apply (simp add:dom_def del:not_None_eq)
      by (metis is_prefix.simps(2) a)
    hence "g (the (f y)) = (x,d)" using assms by (simp add:d_def[symmetric])
    moreover have "y \<in> dom f" using a apply (simp add:dom_def del:not_None_eq)
      by (metis is_prefix.simps(3) a)
    hence "g (the (f y)) = (y,[])" using assms[where y="[]"] by simp
    ultimately show "x = y" by simp
  qed
  thus ?thesis by (simp add:is_encoding_def)
qed

fun bit_count where
  "bit_count None = \<infinity>" |
  "bit_count (Some x) = ereal (length x)"

fun append_encoding :: "bool list option \<Rightarrow> bool list option \<Rightarrow> bool list option" (infixr "@\<^sub>S" 65)
  where
    "append_encoding (Some x) (Some y) = Some (x@y)" |
    "append_encoding _ _ = None"

lemma bit_count_append: "bit_count (x1@\<^sub>Sx2) = bit_count x1 + bit_count x2"
  by (cases x1, simp, cases x2, simp, simp)

subsection \<open>Lists\<close>

fun list\<^sub>S where
  "list\<^sub>S f [] = Some [False]" |
  "list\<^sub>S f (x#xs) = Some [True]@\<^sub>Sf x@\<^sub>Slist\<^sub>S f xs"

function decode_list :: "('a \<Rightarrow> bool list option) \<Rightarrow> bool list 
  \<Rightarrow> 'a list \<times> bool list" 
  where 
    "decode_list e (True#x0) = (
      let (r1,x1) = decode e x0 in (
        let (r2,x2) = decode_list e x1 in (r1#r2,x2)))" |
    "decode_list e (False#x0) = ([], x0)" |
    "decode_list e [] = undefined"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_,x). length x)")
  by (simp+, metis le_imp_less_Suc snd_decode_len)

lemma list_encoding_dom:
  assumes "set l \<subseteq> dom f"
  shows "l \<in> dom (list\<^sub>S f)"
  using assms apply (induction l, simp add:dom_def, simp) by fastforce

lemma list_bit_count:
  "bit_count (list\<^sub>S f xs) = (\<Sum>x \<leftarrow> xs. bit_count (f x) + 1) + 1"
  apply (induction xs, simp, simp add:bit_count_append) 
  by (metis add.commute add.left_commute one_ereal_def)

lemma list_bit_count_est:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (f x) \<le> a"
  shows "bit_count (list\<^sub>S f xs) \<le> ereal (length xs) * (a+1) + 1"
proof -
  have a:"sum_list (map (\<lambda>_. (a+1)) xs) = length xs * (a+1)"
    apply (induction xs, simp)
    by (simp, subst plus_ereal.simps(1)[symmetric], subst ereal_left_distrib, simp+)

  have b: "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (f x) +1 \<le> a+1"
    using assms add_right_mono by blast

  show ?thesis  
    using assms a  b sum_list_mono[where g="\<lambda>_. a+1" and f="\<lambda>x. bit_count (f x)+1" and xs="xs"]
    by (simp add:list_bit_count ereal_add_le_add_iff2)
qed

lemma list_bit_count_estI:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> bit_count (f x) \<le> a"
  assumes "ereal (real (length xs)) * (a+1) + 1 \<le> h"
  shows "bit_count (list\<^sub>S f xs) \<le> h"
  using list_bit_count_est[OF assms(1)] assms(2) order_trans by fastforce 

lemma list_encoding_aux:
  assumes "is_encoding f"
  shows "x \<in> dom (list\<^sub>S f) \<Longrightarrow> decode_list f (the (list\<^sub>S f x) @ y) = (x, y)"
proof  (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
    apply (cases "f a", simp add:dom_def)
    apply (cases "list\<^sub>S f x", simp add:dom_def)
    using assms by (simp add: dom_def decode_elim)
qed

lemma list_encoding:
  assumes "is_encoding f"
  shows "is_encoding (list\<^sub>S f)"
  by (metis encoding_by_witness[where g="decode_list f"] list_encoding_aux assms)

subsection \<open>Natural numbers\<close>

fun nat_encoding_aux :: "nat \<Rightarrow> bool list" 
  where
    "nat_encoding_aux 0 = [False]" |
    "nat_encoding_aux (Suc n) = True#(odd n)#nat_encoding_aux (n div 2)"

fun N\<^sub>S where "N\<^sub>S n = Some (nat_encoding_aux n)"

fun decode_nat :: "bool list \<Rightarrow> nat \<times> bool list" 
  where
    "decode_nat (False#y) = (0,y)" |
    "decode_nat (True#x#xs) = 
      (let (n, rs) = decode_nat xs in (n * 2 + 1 + (if x then 1 else 0), rs))" |
    "decode_nat _ = undefined"

lemma nat_encoding_aux:
  "decode_nat (nat_encoding_aux x @ y) = (x, y)"
  by (induction x rule:nat_encoding_aux.induct, simp, simp add:mult.commute)

lemma nat_encoding:
  shows "is_encoding N\<^sub>S"
  by (rule encoding_by_witness[where g="decode_nat"], simp add:nat_encoding_aux)

lemma nat_bit_count:
  "bit_count (N\<^sub>S n) \<le> 2 * log 2 (real n+1) + 1"
proof (induction n rule:nat_encoding_aux.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  have "log 2 2 + log 2 (1 + real (n div 2)) \<le> log 2 (2 + real n)"
    apply (subst log_mult[symmetric], simp, simp, simp)
    by (subst log_le_cancel_iff, simp+)
  hence "1 + 2 * log 2 (1 + real (n div 2)) + 1 \<le> 2 * log 2 (2 + real n)"
    by simp
  thus ?case using 2 by (simp add:add.commute) 
qed

lemma nat_bit_count_est:
  assumes "n \<le> m"
  shows "bit_count (N\<^sub>S n) \<le> 2 * log 2 (1+real m) + 1"
proof -
  have "2 * log 2 (1 + real n) + 1 \<le> 2 * log 2 (1+real m) + 1" 
    using assms by simp
  thus ?thesis
    by (metis nat_bit_count le_ereal_le  add.commute)
qed

subsection \<open>Integers\<close>

fun I\<^sub>S :: "int \<Rightarrow> bool list option"
  where 
    "I\<^sub>S n = (if n \<ge> 0 then Some [True]@\<^sub>SN\<^sub>S (nat n) else Some [False]@\<^sub>S (N\<^sub>S (nat (-n-1))))" 

fun decode_int :: "bool list \<Rightarrow> (int \<times> bool list)"
  where 
    "decode_int (True#xs) = (\<lambda>(x::nat,y). (int x, y)) (decode_nat xs)" | 
    "decode_int (False#xs) = (\<lambda>(x::nat,y). (-(int x)-1, y)) (decode_nat xs)" |
    "decode_int [] = undefined"

lemma int_encoding: "is_encoding I\<^sub>S"
  apply (rule encoding_by_witness[where g="decode_int"])
  by (simp add:nat_encoding_aux)

lemma int_bit_count:
  "bit_count (I\<^sub>S x) \<le> 2 * log 2 (\<bar>x\<bar>+1) + 2"
proof -
  have a:"\<not>(0 \<le> x) \<Longrightarrow> 1 + 2 * log 2 (- real_of_int x) \<le> 1 + 2 * log 2 (1 - real_of_int x)"
    by simp
  show ?thesis
    apply (cases "x \<ge> 0")
     using nat_bit_count[where n="nat x"] apply (simp add: bit_count_append add.commute)
     using nat_bit_count[where n="nat (-x-1)"] apply (simp add: bit_count_append add.commute)
     using a order_trans by blast
qed

lemma int_bit_count_est:
  assumes "abs n \<le> m"
  shows "bit_count (I\<^sub>S n) \<le> 2 * log 2 (m+1) + 2"
proof -
  have "2 * log 2 (abs n+1) + 2 \<le> 2 * log 2 (m+1) + 2" using assms by simp
  thus ?thesis using assms le_ereal_le int_bit_count by blast
qed

subsection \<open>Cartesian Product\<close>

fun encode_prod :: "'a encoding \<Rightarrow> 'b encoding \<Rightarrow> ('a \<times> 'b) encoding" (infixr "\<times>\<^sub>S" 65)
  where 
    "encode_prod e1 e2 x = e1 (fst x)@\<^sub>S e2 (snd x)"

fun decode_prod :: "'a encoding \<Rightarrow> 'b encoding \<Rightarrow> bool list \<Rightarrow> ('a \<times> 'b) \<times> bool list"
  where
    "decode_prod e1 e2 x0 = (
      let (r1,x1) = decode e1 x0 in (
        let (r2,x2) = decode e2 x1 in ((r1,r2),x2)))"

lemma prod_encoding_dom:
  "x \<in> dom (e1 \<times>\<^sub>S e2) = (fst x \<in> dom e1 \<and> snd x \<in> dom e2)"
  apply (case_tac [!] "e1 (fst x)")
   apply (case_tac [!] "e2 (snd x)")
  by (simp add:dom_def del:not_None_eq)+

lemma prod_encoding:
  assumes "is_encoding e1"
  assumes "is_encoding e2"
  shows "is_encoding (encode_prod e1 e2)"
proof  (rule encoding_by_witness[where g="decode_prod e1 e2"])
  fix x y
  assume a:"x \<in> dom (e1 \<times>\<^sub>S e2)"

  have b:"e1 (fst x) = Some (the (e1 (fst x)))"
    by (metis a prod_encoding_dom domIff option.exhaust_sel)
  have c:"e2 (snd x) = Some (the (e2 (snd x)))" 
    by (metis a prod_encoding_dom domIff option.exhaust_sel)

  show "decode_prod e1 e2 (the ((e1 \<times>\<^sub>S e2) x) @ y) = (x, y)"
    apply (simp, subst b, subst c)
    apply simp
    using assms b c by (simp add:decode_elim)
qed

lemma prod_bit_count:
  "bit_count ((e\<^sub>1 \<times>\<^sub>S e\<^sub>2) (x\<^sub>1,x\<^sub>2)) = bit_count (e\<^sub>1 x\<^sub>1) + bit_count (e\<^sub>2 x\<^sub>2)"
  by (simp add:bit_count_append)

lemma prod_bit_count_2:
  "bit_count ((e1 \<times>\<^sub>S e2) x) = bit_count (e1 (fst x)) + bit_count (e2 (snd x))"
  by (simp add:bit_count_append)

subsection \<open>Dependent Product\<close>

fun encode_dependent_sum :: "'a encoding \<Rightarrow> ('a \<Rightarrow> 'b encoding) \<Rightarrow> ('a \<times> 'b) encoding" (infixr "\<times>\<^sub>D" 65)
  where 
    "encode_dependent_sum e1 e2 x = e1 (fst x)@\<^sub>S e2 (fst x) (snd x)"

lemma dependent_encoding:
  assumes "is_encoding e1"
  assumes "\<And>x. is_encoding (e2 x)"
  shows "is_encoding (encode_dependent_sum e1 e2)"
proof -
  define d where "d = (\<lambda>x0. 
    let (r1, x1) = decode e1 x0 in 
    let (r2, x2) = decode (e2 r1) x1 in ((r1,r2), x2))"

  have a: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> fst x \<in> dom e1"
    apply (simp add:dom_def del:not_None_eq) 
    using append_encoding.simps by metis
  have b: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> snd x \<in> dom (e2 (fst x))"
    apply (simp add:dom_def del:not_None_eq) 
    using append_encoding.simps by metis
  have c: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> e1 (fst x) = Some (the (e1 (fst x)))"
    using a by (simp add: domIff)
  have d: "\<And>x. x \<in> dom (e1 \<times>\<^sub>D e2) \<Longrightarrow> e2 (fst x) (snd x) = Some (the (e2 (fst x) (snd x)))"
    using b by (simp add: domIff)
  show ?thesis
    apply (rule encoding_by_witness[where g="d"])
    apply (simp add:d_def, subst c, simp, subst d, simp)
    using assms a b by (simp add:d_def decode_elim_2)
qed

lemma dependent_bit_count:
  "bit_count ((e\<^sub>1 \<times>\<^sub>D e\<^sub>2) (x\<^sub>1,x\<^sub>2)) = bit_count (e\<^sub>1 x\<^sub>1) + bit_count (e\<^sub>2 x\<^sub>1 x\<^sub>2)"
  by (simp add:bit_count_append)

subsection \<open>Composition\<close>

lemma encoding_compose:
  assumes "is_encoding f"
  assumes "inj_on g {x. P x}"
  shows "is_encoding (\<lambda>x. if P x then f (g x) else None)"
  using assms by (simp add: inj_onD is_encoding_def)

subsection \<open>Extensional Maps\<close>

definition encode_extensional :: "'a list \<Rightarrow> 'b encoding \<Rightarrow> ('a \<Rightarrow> 'b) encoding"  (infixr "\<rightarrow>\<^sub>S" 65)  where
  "encode_extensional xs e f = (
    if f \<in> extensional (set xs) then 
      list\<^sub>S e (map f xs)
    else
      None)"

lemma encode_extensional:
  assumes "is_encoding e"
  shows "is_encoding (\<lambda>x. (xs \<rightarrow>\<^sub>S e) x)"
  apply (simp add:encode_extensional_def)
  apply (rule encoding_compose[where f="list\<^sub>S e"])
   apply (metis list_encoding assms)
  apply (rule inj_onI, simp)
  using extensionalityI by fastforce

lemma extensional_bit_count:
  assumes "f \<in> extensional (set xs)"
  shows "bit_count ((xs \<rightarrow>\<^sub>S e) f) = (\<Sum>x \<leftarrow> xs. bit_count (e (f x)) + 1) + 1"
  using assms 
  by (simp add:encode_extensional_def list_bit_count comp_def)

subsection \<open>Ordered Sets\<close>

fun set\<^sub>S where "set\<^sub>S e S = (if finite S then list\<^sub>S e (sorted_list_of_set S) else None)"

lemma encode_set:
  assumes "is_encoding e"
  shows "is_encoding (\<lambda>S. set\<^sub>S e S)"
  apply simp
  apply (rule encoding_compose[where f="list\<^sub>S e"])
   apply (metis assms list_encoding)
  apply (rule inj_onI, simp)
  by (metis sorted_list_of_set.set_sorted_key_list_of_set)

lemma set_bit_count:
  assumes "finite S"
  shows "bit_count (set\<^sub>S e S) = (\<Sum>x \<in> S. bit_count (e x)+1)+1"
  using assms sorted_list_of_set
  by (simp add:list_bit_count sum_list_distinct_conv_sum_set)

lemma set_bit_count_est:
  assumes "finite S"
  assumes "card S \<le> m"
  assumes "0 \<le> a"
  assumes "\<And>x. x \<in> S \<Longrightarrow> bit_count (f x) \<le> a"
  shows "bit_count (set\<^sub>S f S) \<le> ereal (real m) * (a+1) + 1"
proof -
  have "bit_count (set\<^sub>S f S) \<le> ereal (length (sorted_list_of_set S)) * (a+1) + 1"
    using assms(4) assms(1) list_bit_count_est[where xs="sorted_list_of_set S"] by simp
  also have "... \<le> ereal (real m) * (a+1) + 1"
    apply (rule add_mono)
    apply (rule ereal_mult_right_mono)
    using assms by simp+
  finally show ?thesis by simp
qed

end
