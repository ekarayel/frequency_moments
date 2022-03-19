section \<open>Primes\<close>

text \<open>This section introduces a function that finds the smallest primes above a given threshold.\<close>

theory Primes_Ext
  imports "HOL-Computational_Algebra.Primes" "Bertrands_Postulate.Bertrand" 
begin

definition prime_above :: "nat \<Rightarrow> nat" where "prime_above n = (SOME x. x \<in> {n..(2*n+2)} \<and> prime x)"

lemma ex_subset:
  assumes "\<exists>x \<in> A. P x"
  assumes "A \<subseteq> B"
  shows "\<exists>x \<in> B. P x"
  using assms by auto

lemma
  shows prime_above_prime: "prime (prime_above n)"
  and prime_above_range: "prime_above n \<in> {n..(2*n+2)}"
proof -
  define r where "r = (\<lambda>x. x \<in> {n..(2*n+2)} \<and> prime x)"
  have "\<exists>x. r x"
  proof (cases "n>2")
    case True
    hence "n-1 > 1" by simp
    hence "\<exists>x \<in> {(n-1)<..<(2*(n-1))}. prime x"
      using bertrand by simp
    moreover have "{n - 1<..<2 * (n - 1)} \<subseteq> {n..2 * n + 2}"
      by (intro subsetI, auto) 
    ultimately have "\<exists>x \<in> {n..(2*n+2)}. prime x"
      by (rule ex_subset)
    then show ?thesis by (simp add:r_def Bex_def)
  next
    case False
    hence "2 \<in> {n..(2*n+2)}" 
      by simp
    moreover have "prime (2::nat)" 
      using two_is_prime_nat by blast
    ultimately have "r 2"
      using r_def by simp
    then show ?thesis by (rule exI)
  qed
  moreover have "prime_above n = (SOME x. r x)"
    by (simp add:prime_above_def r_def)
  ultimately have a:"r (prime_above n)"
    using someI_ex by metis
  show "prime (prime_above n)"
    using a unfolding r_def by blast
  show "prime_above n \<in> {n..(2*n+2)}"
    using a unfolding r_def by blast
qed

lemma prime_above_min:  "prime_above n \<ge> 2"
  using prime_above_prime 
  by (simp add: prime_ge_2_nat)

lemma prime_above_lower_bound: "prime_above n \<ge> n"
  using prime_above_range
  by simp

lemma prime_above_upper_bound: "prime_above n \<le> 2*n+2"
  using prime_above_range
  by simp

end
