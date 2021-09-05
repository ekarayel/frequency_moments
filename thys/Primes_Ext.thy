section \<open>Primes\<close>

text \<open>In this section we introduce a function that retrieves the next larger odd prime.\<close>

theory Primes_Ext
imports Main "HOL-Computational_Algebra.Primes" "Bertrands_Postulate.Bertrand"
begin

lemma bigger_odd_prime:
  "\<exists>p. prime p \<and> odd p \<and> (n::nat) < p"
proof -
  obtain p where p_def: "prime p \<and> n < p"
    using bigger_prime by blast
  have a:"\<not> odd p \<Longrightarrow> p = 2" 
    using p_def primes_dvd_imp_eq two_is_prime_nat by blast
  have "prime (3 :: nat)"
    apply (rule prime_nat_naiveI, simp, simp add:numeral_eq_Suc) 
    by (metis One_nat_def Suc_1 Suc_lessI add_2_eq_Suc' dvdE dvd_add_triv_right_iff gr_zeroI mult_0 nat_dvd_not_less old.nat.distinct(1))
  hence b:"n < 2 \<Longrightarrow> prime (3 :: nat) \<and> odd (3 :: nat) \<and> n < 3" by simp 
  show ?thesis 
    using p_def
    apply (cases "odd p", blast, simp add:a)
    using b by blast
qed

lemma inf_primes: "wf ((\<lambda>n. (Suc n, n)) ` {n. \<not> (prime n \<and> odd n)})" (is "wf ?S") 
proof (rule wfI_min)
  fix x :: nat
  fix Q :: "nat set"
  assume a:"x \<in> Q"

  have "\<exists>z \<in> Q. (prime z \<and> odd z) \<or> Suc z \<notin> Q" 
  proof (cases "\<exists>z \<in> Q. Suc z \<notin> Q")
    case True
    then show ?thesis by auto
  next
    case False
    hence b:"\<And>z. z \<in> Q \<Longrightarrow> Suc z \<in> Q" by blast
    have c:"\<And>k. k + x \<in> Q"
    proof -
      fix k
      show "k+x \<in> Q"
        by (induction "k", simp add:a, simp add:b)
    qed
    show ?thesis 
      apply (cases "\<exists>z \<in> Q. prime z \<and> odd z")
       apply blast
        by (metis add.commute less_natE bigger_odd_prime c)
  qed
  thus "\<exists>z \<in> Q. \<forall>y. (y,z) \<in> ?S \<longrightarrow> y \<notin> Q" by blast
qed

function find_odd_prime_above :: "nat \<Rightarrow> nat" where
  "find_odd_prime_above n = (if prime n \<and> odd n then n else find_odd_prime_above (Suc n))"
  by auto
termination
  apply (relation "(\<lambda>n. (Suc n, n)) ` {n. \<not> (prime n \<and> odd n)}")
  using inf_primes apply blast
  by simp

declare find_odd_prime_above.simps [simp del]

lemma find_prime_above_is_prime:
  "prime (find_odd_prime_above n)" "odd (find_odd_prime_above n)"
  apply (induction n rule:find_odd_prime_above.induct)
  by (simp add: find_odd_prime_above.simps)+

lemma find_prime_above_min:
  "find_odd_prime_above n \<ge> 3"
  using find_prime_above_is_prime 
  by (metis One_nat_def Suc_1 even_numeral nle_le not_less_eq_eq numeral_3_eq_3 prime_ge_2_nat)

lemma find_prime_above_lower_bound:
  "find_odd_prime_above n \<ge> n"
  apply (induction n rule:find_odd_prime_above.induct)
  by (metis find_odd_prime_above.simps linorder_le_cases not_less_eq_eq)

lemma find_odd_prime_above_upper_bound:
  assumes "odd m"
  assumes "prime m"
  shows "n \<le> m \<Longrightarrow> find_odd_prime_above n \<le> m"
proof (induction n rule:find_odd_prime_above.induct)
  case (1 n)
  have a:"\<not>(prime n \<and> odd n) \<Longrightarrow> Suc n \<le> m"
    using assms  "1.prems" not_less_eq_eq by fastforce
  show ?case using 1 
    apply (cases "prime n \<and> odd n")
     apply (subst find_odd_prime_above.simps)
    using assms(1)  apply simp
    by (metis a find_odd_prime_above.simps)
qed

lemma find_prime_above_upper_bound:
  "find_odd_prime_above n \<le> 2*n+3"
proof (cases "n \<le> 1")
  case True
  have "find_odd_prime_above n \<le> 3"
    apply (rule find_odd_prime_above_upper_bound, simp, simp) using True by linarith 
  then show ?thesis using trans_le_add2 by blast
next
  case False
  hence a:"n > 1" by auto
  then obtain p where p_bound: "p \<in> {n<..<2*n}" and p_prime: "prime p" 
    using bertrand by metis
  have "p > 2" using a p_bound by simp
  hence "odd p" 
    by (metis p_prime order_less_asym' primes_dvd_imp_eq two_is_prime_nat)
  hence "find_odd_prime_above n \<le> p"
    apply (rule find_odd_prime_above_upper_bound)
     apply (metis p_prime)
    using p_bound by simp
  thus ?thesis using p_bound 
    by (metis greaterThanLessThan_iff nat_le_iff_add nat_less_le trans_le_add1)
qed

end