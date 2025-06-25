section \<open> Example of probabilistic relation programming: simple random walk \<close>

theory utp_prob_rel_lattice_symmetric_random_walker
  imports 
    "UTP_prob_relations.utp_prob_rel_lattice_laws" 
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL.Binomial"
    "Catalan_Numbers.Catalan_Numbers"
    "HOL.Real" (* Explicitly import for real exponents *)
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Definitions \<close>

subsubsection \<open> Distribution functions \<close>
text \<open> The distribution function of the while loop below. \<close>
fun mu_lp :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("\<mu>\<^sub>l\<^sub>p") where 
"\<mu>\<^sub>l\<^sub>p p 0 0 = 1" |
"\<mu>\<^sub>l\<^sub>p p 0 (Suc n) = 0" |
"\<mu>\<^sub>l\<^sub>p p (Suc m) 0 = 0" |
"\<mu>\<^sub>l\<^sub>p p (Suc m) (Suc n) = p * (\<mu>\<^sub>l\<^sub>p p m n) + (1 - p) * (\<mu>\<^sub>l\<^sub>p p (Suc (Suc m)) n)" 

thm "mu_lp.induct"

lemma mu_lp_nonneg: 
  assumes "p \<ge> 0" "p \<le> 1"
  shows "(\<mu>\<^sub>l\<^sub>p p m n) \<ge> 0"
(* https://stackoverflow.com/questions/19011374/induction-on-recursive-function-with-a-twist *)
  using assms 
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p n)
  then show ?case by simp
next
  case (3 p m)
  then show ?case by simp
next
  case (4 p m n)
  then show ?case by fastforce
qed

lemma mu_lp_zero:
  assumes "m > 0"
  assumes "n > 0"
  assumes "m > n"
  shows "(\<mu>\<^sub>l\<^sub>p p m n) = 0"
  using assms 
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by fastforce
next
  case (2 p n)
  then show ?case by blast
next
  case (3 p m)
  then show ?case by blast
next
  case (4 p m n)
  then show ?case
    by (metis (no_types, opaque_lifting) add_0 less_Suc_eq mu_lp.simps(3) mu_lp.simps(4) mult_zero_right not_less_eq old.nat.exhaust)
qed

lemma mu_lp_zero':
  shows "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> m > n \<Longrightarrow> (\<mu>\<^sub>l\<^sub>p p m n) = 0"
proof (induct p m n rule: mu_lp.induct)
  case (4 p m n)
  thus ?case by (metis (no_types, opaque_lifting) add_0 less_Suc_eq mu_lp.simps(3) mu_lp.simps(4) mult_zero_right not_less_eq old.nat.exhaust)
qed auto

lemma mu_lp_zero_not_odd_or_even:
  assumes "m > 0"
  assumes "n > 0"
  assumes "(m+n) mod 2 \<noteq> 0"
  shows "(\<mu>\<^sub>l\<^sub>p p m n) = 0"
  using assms 
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by fastforce
next
  case (2 p n)
  then show ?case by blast
next
  case (3 p m)
  then show ?case by blast
next
  case (4 p m n)
  then show ?case
    by (smt (verit, del_insts) Suc_less_eq add.commute add_0 add_Suc_right add_self_mod_2 
        bot_nat_0.not_eq_extremum less_Suc_eq less_Suc_eq_0_disj less_iff_Suc_add less_nat_zero_code 
        mod2_Suc_Suc mu_lp.simps(2) mu_lp.simps(4) mu_lp_zero' mult.commute mult_eq_0_iff 
        mult_zero_left not_less_eq not_less_iff_gr_or_eq numeral_1_eq_Suc_0 order_less_trans 
        zero_less_Suc)
qed

lemma mu_lp_leq_1:
  shows "p \<ge> 0 \<Longrightarrow> p \<le> 1 \<Longrightarrow> (\<mu>\<^sub>l\<^sub>p p m n) \<le> 1"
proof (induct p m n rule: mu_lp.induct)
  case (4 p m n)
  thus ?case by (smt (verit) mu_lp.simps(4) mult_left_le)
qed auto

lemma mu_lp_p_m:
  assumes "m = n"
  shows "\<mu>\<^sub>l\<^sub>p p m n = p ^ m"
  using assms
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p n)
  then show ?case by simp
next
  case (3 p m)
  then show ?case by simp
next
  case (4 p m n)
  then show ?case
    by (smt (verit, del_insts) bot_nat_0.not_eq_extremum less_Suc_eq mu_lp.simps(3) mu_lp.simps(4) mu_lp_zero' mult_cancel_right1 nat.inject power_Suc)
qed

lemma mu_lp_p_m_plus_1:
  shows "(\<mu>\<^sub>l\<^sub>p p m m) * p = \<mu>\<^sub>l\<^sub>p p (m+1) (m+1)"
  using mu_lp_p_m by fastforce

subsubsection \<open> Mathematical theory \<close>
text \<open> This is the distribution function or constant facts in probability generation functions 
  @{text "\<Sum>n \<in> {0..}. \<phi> n * z ^ n "}
\<close>

definition phi :: "real \<Rightarrow> nat \<Rightarrow> real" where
"phi p m = (if even m then 0 else 
  (let m' = ((m-1) div 2) in (real (catalan m')) * (p ^ (m' + 1)) * ((1 - p) ^ m'))
)"

(* "phi p m = (if even m then (catalan (m div 2) * (p ^ (m div 2 + 1)) * (1 - p) ^ (m div 2)) else 0)" *)

lemma phi_odd_calatan:
  assumes "p \<ge> 0" "p \<le> 1"
  shows "phi p (2*m + 1) = (real (catalan m)) * (p ^ (m+1)) * ((1-p) ^ m)"
  by (simp add: phi_def)

lemma phi_even_0: 
  assumes "even m"
  shows "phi p m = 0"
  by (simp add: assms phi_def)

lemma phi_nonneg:
  assumes "p \<ge> 0" "p \<le> 1"   
  shows "phi p m \<ge> 0"
  by (smt (verit) assms(1) assms(2) bot_nat_0.not_eq_extremum mult_nonneg_nonneg of_nat_0 of_nat_0_less_iff phi_def zero_le_power)

lemma phi_p_1: 
  shows "phi p 1 = p"
  by (simp add: phi_def)

(*
fun sun_rec :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"sun_rec p 0 n = 1" |
"sun_rec p (Suc m) 0 = 1" |
"sun_rec p (Suc m) (Suc n) = (\<Sum>i\<^sub>1 \<in> {0..(n)}. (phi p ((n+1) - i\<^sub>1)) * (sun_rec p m i\<^sub>1))"

value "sun_rec (1/2) 1 2"
*)

fun nu_lp :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("\<nu>\<^sub>l\<^sub>p") where 
"\<nu>\<^sub>l\<^sub>p p 0 0 = 1" |
"\<nu>\<^sub>l\<^sub>p p 0 (Suc n) = 0" |
"\<nu>\<^sub>l\<^sub>p p (Suc m) 0 = 0" |
"\<nu>\<^sub>l\<^sub>p p (Suc m) (Suc n) = (\<Sum>i\<^sub>1 \<in> {0..(n)}. (phi p (Suc n - i\<^sub>1)) * (\<nu>\<^sub>l\<^sub>p p m i\<^sub>1))"

find_theorems name: "nu_lp"

lemma nu_lp_m_zero: "\<forall>n. n \<noteq> 0 \<longrightarrow> \<nu>\<^sub>l\<^sub>p p (0::\<nat>) n = 0 \<and> n = 0 \<longrightarrow> \<nu>\<^sub>l\<^sub>p p (0::\<nat>) n = 1"
  using nu_lp.elims by blast

lemma nu_lp_0_n_neq_0:
  assumes "n \<noteq> 0"
  shows "\<nu>\<^sub>l\<^sub>p p (0::\<nat>) n = 0"
  using assms not0_implies_Suc nu_lp.simps(2) by blast

lemma nu_lp_1_n_eq_0:
  shows "\<nu>\<^sub>l\<^sub>p p (0::\<nat>) 0 = 1"
  by simp

lemma nu_lp_nonneg:
  assumes "p \<ge> 0" "p \<le> 1"
  shows "\<nu>\<^sub>l\<^sub>p p m n \<ge> 0"
  using assms
proof (induct p m n rule: nu_lp.induct)
  case (1 p)
  then show ?case by fastforce
next
  case (2 p n)
  then show ?case by simp
next
  case (3 p m)
  then show ?case by simp
next
  case (4 p m n)
  then show ?case
    apply simp
    apply (rule sum_nonneg)
    apply (rule mult_nonneg_nonneg)
    apply (subst phi_nonneg)
    by auto
qed

lemma nu_lp_zero_not_odd_or_even:
  assumes "m > 0"
  assumes "n > 0"
  assumes "(m+n) mod 2 \<noteq> 0"
  assumes "p \<ge> 0" "p \<le> 1"
  shows "(\<nu>\<^sub>l\<^sub>p p m n) = 0"
  using assms 
proof (induct p m n rule: nu_lp.induct)
  case (1 p)
  then show ?case by fastforce
next
  case (2 p n)
  then show ?case by blast
next
  case (3 p m)
  then show ?case by blast
next
  case (4 p m n)
  then show ?case
    apply (simp)
    apply (subst sum_nonneg_eq_0_iff)
    apply blast
    apply (rule mult_nonneg_nonneg)
    apply (subst phi_nonneg)
    apply blast
    apply blast
    apply simp
    using nu_lp_nonneg apply presburger
    apply auto
    apply (rule phi_even_0)
    by (metis (no_types, lifting) even_Suc less_Suc_eq_0_disj mod_eq_dvd_iff_nat not_le_minus 
        nu_lp.elims odd_add odd_one parity_cases)
qed
  
lemma nu_lp_zero:
  assumes "m > 0"
  assumes "n > 0"
  assumes "m > n"
  shows "(\<nu>\<^sub>l\<^sub>p p m n) = 0"
  using assms 
proof (induct p m n rule: nu_lp.induct)
  case (1 p)
  then show ?case by fastforce
next
  case (2 p n)
  then show ?case by blast
next
  case (3 p m)
  then show ?case by blast
next
  case (4 p m n)
  then show ?case
    apply (simp)
    apply (subst sum_nonneg_eq_0_iff)
    apply blast
    apply (metis Suc_pred atLeast0AtMost atMost_iff dual_order.refl lambda_zero less_le mult.commute 
        nu_lp.simps(3) trace_class.less_iff zero_le)
    by (metis arith_simps(63) atLeastAtMost_iff less_imp_Suc_add nu_lp.simps(3) zero_less_iff_neq_zero)
qed

lemma nu_lp_m_1_is_phi: "\<nu>\<^sub>l\<^sub>p p 1 n = phi p n"
  apply (induction n)
  apply (simp add: phi_def)
  apply (simp)
proof -
  fix n :: "\<nat>"
  assume a1: "\<nu>\<^sub>l\<^sub>p p (Suc (0::\<nat>)) n = phi p n"

  let ?f = "\<lambda>i\<^sub>1. phi p (Suc n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (0::\<nat>) i\<^sub>1"
  have f0: "(\<Sum>i\<^sub>1::\<nat>\<in>{0::\<nat>}. ?f i\<^sub>1) = phi p (Suc n)"
    by simp
  have f1n: "(\<Sum>i\<^sub>1::\<nat> = 1::\<nat>..n. ?f i\<^sub>1) = 0"
    using nu_lp_0_n_neq_0 by simp
    
  have f2: "(\<Sum>i\<^sub>1::\<nat> = 0::\<nat>..n. phi p (Suc n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (0::\<nat>) i\<^sub>1) = 
        (\<Sum>i\<^sub>1 \<in> {0} \<union> {1..(n)}. phi p (Suc n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (0::\<nat>) i\<^sub>1)"
    by (smt (verit) One_nat_def Un_Diff_cancel atLeast0AtMost atLeast1_atMost_eq_remove0 atMost_iff 
        insert_absorb insert_is_Un zero_order(1))
  have f3: "... = phi p (Suc n)"
    apply (subst sum_Un[where A = "{0}" and B = "{1..n}" ])
    apply (simp)
    apply (simp)
    apply (simp only: f0 f1n)
    by (simp add: comm_monoid_set.empty)
  then show "(\<Sum>i\<^sub>1::\<nat> = 0::\<nat>..n. ?f i\<^sub>1) = phi p (Suc n)"
    using f2 by presburger
qed

lemma phi_2n_1_eq_nu_lp:
  assumes "n \<ge> 1"
  shows "phi p (2*n + 1) = (1 - p) * \<nu>\<^sub>l\<^sub>p p 2 (2*n)"
proof -
  let ?h = "(\<lambda>k. 2*k + 1)"
  have h_inj_on: "inj_on ?h {0..(n-1)}"
    by (simp add: inj_on_def)

  let ?A = "{0..(2*n-1)}"
  let ?A1 = "{k. k \<in> {0..(2*n-1)} \<and> odd k}"
  let ?A2 = "{k. k \<in> {0..(2*n-1)} \<and> even k}"
  let ?A' = "{0..(n-1)}"

  have A1_A2_A: "?A1 \<union> ?A2 = {0..(2*n-1)}"
    by auto
    
  have hA: "(?h ` ?A') = ?A1"
    apply (simp add: image_def)
    apply (simp add: set_eq_iff)
    apply auto
    using assms apply linarith
  proof -
    fix x :: "nat"
    assume a1: "x \<le> (2::\<nat>) * n - Suc (0::\<nat>)"
    assume a2: "\<not> even x"
    show "\<exists>xa::\<nat>\<in>{0::\<nat>..n - Suc (0::\<nat>)}. x = Suc ((2::\<nat>) * xa)"
      apply (simp add: Bex_def)
      apply (rule_tac x = "(x - 1) div 2" in exI)
      apply auto
      using a1 apply auto[1]
      using a2 by force
  qed

  have n_k: "\<forall>k\<le>n-1. n - Suc k + k = n - 1"
    by auto

  let ?f = "\<lambda>i\<^sub>1. (phi p ((2*n) - i\<^sub>1)) * (\<nu>\<^sub>l\<^sub>p p 1 i\<^sub>1)"
  let ?f1 = "\<lambda>i\<^sub>1. (phi p ((2*n) - i\<^sub>1)) * (phi p i\<^sub>1)"
  let ?f2 = "\<lambda>i\<^sub>1. phi p (Suc n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (0::\<nat>) i\<^sub>1"

  have nu_lp_2_2n_def: "nu_lp p 2 (2*n) = (\<Sum>i\<^sub>1 \<in> {0..(2*n-1)}. ?f i\<^sub>1)"
    by (smt (verit) One_nat_def assms cancel_ab_semigroup_add_class.add_diff_cancel_left' 
        le_numeral_extra(2) mult_eq_0_iff nu_lp.elims numerals(2) plus_1_eq_Suc sum.cong zero_neq_numeral)

  also have nu_lp_2_2n_phi: "... = (\<Sum>i\<^sub>1 \<in> {0..(2*n-1)}. ?f1 i\<^sub>1)"
    by (simp only: nu_lp_m_1_is_phi)

  also have nu_lp_2_2n_phi_un: "... = (\<Sum>i\<^sub>1 \<in> ?A1 \<union> ?A2. ?f1 i\<^sub>1)"
    using A1_A2_A by presburger

  also have nu_lp_2_2n_phi_A1: "... = (\<Sum>i\<^sub>1 \<in> ?A1. ?f1 i\<^sub>1)"
    apply (subst sum_Un)
    apply simp+
    by (smt (verit, ccfv_SIG) IntE Rings.ring_distribs(4) mem_Collect_eq phi_def sum.neutral)

  (* also have "... = (\<Sum>i\<^sub>1 \<in> (?h ` ?A'). ?f1 i\<^sub>1)"
    using hA by presburger *)

  (* also have "... = (\<Sum>i\<^sub>1 \<in> ?A'. ?f1 i\<^sub>1)"
    apply (subst comm_monoid_set.reindex_cong[where ?A = ""]) *)
    (*apply (simp add: comm_monoid_set.reindex_cong[where ?h = "(\<lambda>x::\<nat>. Suc ((2::\<nat>) * x))" and 
          ?A = "{0::\<nat>..n - Suc (0::\<nat>)}" and ?g = "\<lambda>i\<^sub>1. phi p ((2::\<nat>) * n - i\<^sub>1) * phi p i\<^sub>1"])*)

  also have mu_lp_2_2n_phi: "... = (\<Sum>k \<in> ?A'. (phi p (2*(n-1-k) + 1)) * (phi p (2*k+1)))"
    apply (subst sum.reindex_cong[where A = ?A1 and B = ?A' and g = ?f1 and l = "(\<lambda>k. 2*k + 1)" and 
       h = "\<lambda>k. (phi p (2*(n-k-1) + 1)) * (phi p (2*k+1))"])
    using h_inj_on apply blast
    using hA apply presburger
    apply auto
    by (smt (verit, ccfv_SIG) One_nat_def Suc_diff_diff Suc_diff_le add_Suc_shift assms diff_Suc_1 
        diff_Suc_Suc diff_mult_distrib2 distrib_left mult_2 plus_1_eq_Suc)

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>).
        (let m'::\<nat> = n - Suc k in real (catalan m') * (p * p ^ m') * ((1::\<real>) - p) ^ m') *
        (real (catalan k) * (p * p ^ k) * ((1::\<real>) - p) ^ k))"
    by (simp add: phi_def)

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>). (let m'::\<nat> = n - Suc k in 
    real (catalan m') * real (catalan k) * (p ^ m' * p ^ k * p * p) * ((1::\<real>) - p) ^ (m'+k)))"
    by (metis (mono_tags, opaque_lifting) Groups.mult_ac(3) more_arith_simps(11) power_add)

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>). (let m'::\<nat> = n - Suc k in 
    real (catalan m') * real (catalan k) * (p ^ (n - Suc k + k) * p * p) * ((1::\<real>) - p) ^ (n - Suc k + k)))"
    by (metis (no_types, opaque_lifting) power_add)

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>). (let m'::\<nat> = n - Suc k in 
    real (catalan m') * real (catalan k) * (p ^ (n - 1) * p * p) * ((1::\<real>) - p) ^ (n - 1)))"
    by (simp add: n_k)

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>). (let m'::\<nat> = n - Suc k in 
    real (catalan m') * real (catalan k) * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)))"
    by (metis (no_types, opaque_lifting) One_nat_def Suc_n_not_le_n Suc_pred add_Suc_shift assms 
        bot_nat_0.not_eq_extremum mult.commute nat_arith.rule0 power_Suc)

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>). (let m'::\<nat> = n - Suc k in 
    real (catalan m') * real (catalan k)) * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1))"
    by presburger
  
  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - Suc (0::\<nat>). real (catalan (n - Suc k)) * real (catalan k)) 
            * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    apply (subst sum_distrib_right[symmetric])
    apply (subst sum_distrib_right[symmetric])
    by simp

  also have "... = (\<Sum>k::\<nat> = 0::\<nat>..n - 1. real ((catalan ((n - 1) - k)) * (catalan k))) 
            * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    using One_nat_def diff_diff_left plus_1_eq_Suc by auto

  also have "... = real (\<Sum>k::\<nat> = 0::\<nat>..n - 1. ((catalan k) * (catalan ((n - 1) - k)))) 
            * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    apply (simp only: of_nat_sum[symmetric])
    by (meson Groups.mult_ac(2))

  also have "... = real (\<Sum>k\<le>n - 1. ((catalan k) * (catalan ((n - 1) - k)))) 
            * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    using atLeast0AtMost by presburger
  
  also have "... = real (catalan (Suc (n - 1))) * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    using catalan_Suc by presburger

  also have "... = real (catalan n) * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    using assms by auto

  then have mu_lp_2_2n_simp: "nu_lp p 2 (2*n) = real (catalan n) * (p ^ (n + 1)) * ((1::\<real>) - p) ^ (n - 1)"
    using calculation by presburger

  show ?thesis
    apply (simp add: mu_lp_2_2n_simp)
    using phi_def by (smt (verit, best) Nat.diff_add_assoc2 Suc_1 Suc_eq_numeral add_is_0 
        add_self_div_2 assms diff_Suc_numeral diff_cancel2 diff_mult_distrib even_Suc 
        le_numeral_extra(4) mult_2 numeral_1_eq_Suc_0 numeral_One odd_two_times_div_two_nat 
        ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc power_eq_if 
        vector_space_over_itself.scale_left_commute zero_less_one_class.zero_le_one)
qed

lemma mu_nu_eq:
  assumes "p \<ge> 0" "p \<le> 1"
  shows "mu_lp p m n = nu_lp p m n"
  using assms
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by auto
next
  case (2 p n)
  then show ?case by auto
next
  case (3 p m)
  then show ?case by auto
next
  case (4 p m n)
  then show ?case
    proof (cases "n < m")
      case True
      then show ?thesis using Suc_mono mu_lp_zero nu_lp_zero zero_less_Suc by presburger
    next
      case False
      then have m_le_n: "m \<le> n"
        by auto
      then show ?thesis 
        proof (cases "(m+n) mod 2 = 0")
          case True
          then show ?thesis
            proof (cases "n = 0")
              case True
              then have m_0: "m = 0"
                using m_le_n by blast
              from True show ?thesis 
                apply simp
                apply (simp add: m_0)
                by (simp add: phi_def)
            next
              case False
              then show ?thesis 
                apply simp
                proof -
                  assume a1: "(0::\<nat>) < n"

                  have phi_p_suc_n_i: "\<forall>i \<le> n-1. phi p (Suc n - i) = (1-p) * (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..n-1-i. phi p ((n - i) - i\<^sub>0) * phi p i\<^sub>0)"
                    apply (rule allI, rule impI)
                    proof -
                      fix i
                      assume i_n_1: "i \<le> n - 1"
                      show "phi p (Suc n - i) = ((1::\<real>) - p) * (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..n - (1::\<nat>) - i. phi p (n - i - i\<^sub>0) * phi p i\<^sub>0)" 
                        proof (cases "even (Suc n - i)")
                          case True
                          then show ?thesis 
                          proof -
                            have phi_0: "phi p (Suc n - i) = 0"
                              using True phi_even_0 by blast
                            have "\<forall>i\<^sub>0 \<le> n - i. even (n - i - i\<^sub>0) \<or> even i\<^sub>0"
                              apply (auto)
                              apply (meson True dvd_diffD even_Suc le_SucI not_less trans_less_add1)
                              using True by fastforce
                            then have "(\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..n - (1::\<nat>) - i. phi p (n - i - i\<^sub>0) * phi p i\<^sub>0) = 0"
                              using phi_even_0 
                              by (metis (no_types, lifting) even_diff_nat linorder_not_less mult_eq_0_iff sum.neutral)
                            then show ?thesis
                              by (metis mult_zero_right phi_0)
                          qed
                        next
                          case False
                          obtain l where P_l: "2*l + 1 = (Suc n - i)" 
                            by (metis False oddE)

                          have "phi p (Suc n - i) = phi p (2*l + 1)"
                            using P_l by simp
                          also have "... = (1 - p) * \<nu>\<^sub>l\<^sub>p p 2 (2*l)"
                            using phi_2n_1_eq_nu_lp i_n_1
                            by (metis False Nat.le_diff_conv2 P_l Suc_leI Suc_n_not_le_n a1 
                                add.commute add_diff_inverse_nat bot_nat_0.not_eq_extremum 
                                even_diff_nat numeral_nat(7) plus_1_eq_Suc semiring_norm(64))
                          also have "... = (1 - p) * \<nu>\<^sub>l\<^sub>p p (Suc 1) (Suc (2*l-1))"
                            by (metis Groups.add_ac(2) One_nat_def Suc_1 Suc_diff_1 
                                  bot_nat_0.not_eq_extremum le_add_diff_inverse lessI not_le_minus 
                                  nu_lp.simps(3) nu_lp_zero semiring_norm(174) zero_less_Suc)
                          also have "... = (1 - p) * (\<Sum>i\<^sub>1 \<in> {0..(2*l-1)}. (phi p (2*l - i\<^sub>1)) * (\<nu>\<^sub>l\<^sub>p p 1 i\<^sub>1))"
                            apply (simp only: nu_lp.simps(4))
                            by (metis (mono_tags, opaque_lifting) Suc_le_eq Suc_pred' 
                                bot_nat_0.not_eq_extremum diff_is_0_eq' nu_lp_m_1_is_phi 
                                odd_Suc_minus_one phi_even_0 semiring_norm(64) zero_diff zero_less_Suc)
                          also have "... = (1 - p) * (\<Sum>i\<^sub>1 \<in> {0..(2*l-1)}. (phi p (2*l - i\<^sub>1)) * (phi p i\<^sub>1))"
                            using nu_lp_m_1_is_phi by presburger
                          also have "... = (1 - p) * (\<Sum>i\<^sub>1 \<in> {0..((Suc n - i)-2)}. (phi p ((Suc n - i) - 1 - i\<^sub>1)) * (phi p i\<^sub>1))"
                            using P_l by (metis (no_types, lifting) Suc_1 Suc_eq_plus1 diff_Suc_1 diff_diff_left sum.cong)
                          finally show ?thesis
                            by force
                        qed
                      qed

                  (* Swap sum *)
                  have sigma_xy: "(SIGMA x::\<nat>:{0::\<nat>..n - (1::\<nat>)}. {x..n - (1::\<nat>)}) = {(x, y). 0 \<le> x \<and> x \<le> n - 1 \<and> x \<le> y \<and> y \<le> n - 1}"
                    apply (simp add: Sigma_def)
                    by auto

                  have sigma_yx: "(SIGMA x::\<nat>:{0::\<nat>..n - (1::\<nat>)}. {0..x}) = {(x, y). 0 \<le> x \<and> x \<le> n - 1 \<and> 0 \<le> y \<and> y \<le> x}"
                    apply (simp add: Sigma_def)
                    by auto

                  have sigma_xy_swap: "{(x, y). 0 \<le> x \<and> x \<le> n - 1 \<and> x \<le> y \<and> y \<le> n - 1} 
                         = prod.swap ` {(x, y). 0 \<le> x \<and> x \<le> n - 1 \<and> 0 \<le> y \<and> y \<le> x}"
                    apply (simp add: image_def)
                    by auto

                  have sigma_xy_swap': "(SIGMA x::\<nat>:{0::\<nat>..n - (1::\<nat>)}. {x..n - (1::\<nat>)})
                        = prod.swap ` (SIGMA x::\<nat>:{0::\<nat>..n - (1::\<nat>)}. {0..x})"
                    using sigma_xy sigma_xy_swap sigma_yx by presburger

                  have "(\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..n. phi p (Suc n - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0) = 
                    (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1} \<union> {n}. phi p (Suc n - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"
                    apply (subgoal_tac "{0::\<nat>..n} = {0..n-1} \<union> {n}")
                    apply presburger
                    by (metis Suc_pred' Un_insert_right atLeast0_atMost_Suc atLeastAtMost_singleton 
                        boolean_algebra_cancel.sup0 insert_absorb2 less_zeroE nat_neq_iff not_le_minus 
                        not_one_le_zero)
    
                  also have "... = (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1}. phi p (Suc n - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0) + phi p (Suc n - n) * \<nu>\<^sub>l\<^sub>p p m n"
                    apply (subst sum_Un)
                    apply blast
                    apply simp+
                    apply (subgoal_tac "{0::\<nat>..n - Suc (0::\<nat>)} \<inter> {n} = {}")
                    apply (metis sum_clauses(1))
                    using a1 by fastforce

                  also have "... = (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1}. phi p (Suc n - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0) + phi p 1 * \<nu>\<^sub>l\<^sub>p p m n"
                    by simp+

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1}. phi p (Suc n - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"
                    using phi_p_1 "4.hyps"(1) "4.prems"(1) "4.prems"(2) by auto

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1}. 
                      (1-p) * (\<Sum>i\<^sub>1::\<nat> = 0::\<nat>..n-1-i\<^sub>0. phi p ((n - i\<^sub>0) - i\<^sub>1) * phi p i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"
                    by (simp add: phi_p_suc_n_i)

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1}. 
                      (\<Sum>i\<^sub>1::\<nat> = 0::\<nat>..n-1-i\<^sub>0. phi p ((n - i\<^sub>0) - i\<^sub>1) * phi p i\<^sub>1 * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0))"
                    by (simp add: mult.commute mult.left_commute sum_distrib_left)

                  (* reindex *)
                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>0::\<nat> \<in> {0..n-1}. 
                      (\<Sum>i\<^sub>1::\<nat> = i\<^sub>0::\<nat>..n-1. phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0))"
                    apply (subst sum.cong_simp[where B = "{0..n-1}" and 
                      g = "\<lambda>i\<^sub>0. (\<Sum>i\<^sub>1::\<nat> = i\<^sub>0::\<nat>..n-1. phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"
                      and h = "\<lambda>i\<^sub>0. (\<Sum>i\<^sub>1::\<nat> = 0::\<nat>..n-1-i\<^sub>0. phi p ((n - i\<^sub>0) - i\<^sub>1) * phi p i\<^sub>1 * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"])
                    apply auto
                    apply (simp add: simp_implies_def)
                    apply (subst sum.reindex_cong[where l = "\<lambda>y. x + y" and B = "{0::\<nat>..n - Suc x}"
                         and A = "{x..n - Suc (0::\<nat>)}" and g = "\<lambda>i\<^sub>1. phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - x) * \<nu>\<^sub>l\<^sub>p p m x"
                         and h = "\<lambda>i\<^sub>1. phi p (n - (x + i\<^sub>1)) * phi p i\<^sub>1 * \<nu>\<^sub>l\<^sub>p p m x"])
                    by auto

                 (* i\<^sub>1 \<longrightarrow> i\<^sub>1 - i\<^sub>0 *)
                 (* i\<^sub>0 \<in> [0..n-1], i\<^sub>1 \<in> [i\<^sub>0..n-1] *)
                 (* i\<^sub>1 \<in> [0..n-1], i\<^sub>0 \<in> [0..i\<^sub>1-1] *)
                 (*                            phi p (n - i\<^sub>0 - i\<^sub>1)     phi p i\<^sub>1     \<nu>\<^sub>l\<^sub>p p m i\<^sub>0
                     if n = 3,
                      i\<^sub>0 [0..2], i\<^sub>1 [i\<^sub>0..2], phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - i\<^sub>0) * * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0
                          0, 0
                          0, 1
                          0, 2
                          1, 1 
                          1, 2
                          2, 2

                    i\<^sub>1 [0..n-1], i\<^sub>0 [0..i\<^sub>1], phi p (n - i\<^sub>1 + 1) * phi p (i\<^sub>1 - 1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0
                          0, 0 
                          1, 0
                          1, 1
                          2, 0
                          2, 1
                          2, 2
                  *)

                  (* (i\<^sub>0::\<nat>, i\<^sub>1::\<nat>)\<in>(SIGMA x::\<nat>:{0::\<nat>..n - (1::\<nat>)}. {x..n - (1::\<nat>)}) *)
                  (* (i\<^sub>1::\<nat>, i\<^sub>0::\<nat>)\<in>(SIGMA x::\<nat>:{0::\<nat>..n - (1::\<nat>)}. {0..x}) *)

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0..n-1}.
                      (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..i\<^sub>1. phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0))"
                    apply (subst sum.Sigma)
                    apply blast
                    apply blast
                    apply (subst sum.Sigma)
                    apply blast
                    apply blast
                    apply (simp only: sigma_xy_swap')
                    apply (subst sum.reindex_bij_witness [where i = "\<lambda>(i, j). (j, i)" and j = "\<lambda>(i, j). (j, i)" and
                          S = "prod.swap ` Sigma {0::\<nat>..n - (1::\<nat>)} (atLeastAtMost (0::\<nat>))" and
                          T = "Sigma {0::\<nat>..n - (1::\<nat>)} (atLeastAtMost (0::\<nat>))" and
                          h = "\<lambda> (i\<^sub>1, i\<^sub>0). phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0"])
                    apply fastforce
                    apply force
                    apply auto[1]
                    using swap_simp apply fastforce
                    apply (simp add: image_def Sigma_def prod.swap_def)
                     apply force
                    by simp

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0..n-1}.
                      (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..i\<^sub>1. phi p (n - i\<^sub>1) * (phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)))"
                    apply (subgoal_tac "\<forall>i\<^sub>0 i\<^sub>1. phi p (n - i\<^sub>1) * phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0 = 
                      (phi p (n - i\<^sub>1) * (phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0))")
                    apply presburger
                    using cross3_simps(10) by blast

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0..n-1}. phi p (n - i\<^sub>1) *
                      (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..i\<^sub>1. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0))"
                    apply (subst sum.cong[where A = "{0..n-1}" and B = "{0..n-1}" and 
                          h = "\<lambda>i\<^sub>1. phi p (n - i\<^sub>1) * (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..i\<^sub>1. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)" and 
                          g = "\<lambda>i\<^sub>1. \<Sum>i\<^sub>0::\<nat> = 0::\<nat>..i\<^sub>1. phi p (n - i\<^sub>1) * (phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"])
                    apply simp
                    apply (rule sum_distrib_left[symmetric])
                    by simp
                  
                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0..n-1}. phi p (n - i\<^sub>1) *
                      ((\<Sum>i\<^sub>0::\<nat> \<in> {0::\<nat>..i\<^sub>1-1} \<union> {i\<^sub>1}. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)))"
                    apply (subgoal_tac "\<forall>i\<^sub>1. {0::\<nat>..i\<^sub>1-1} \<union> {i\<^sub>1} = {0::\<nat>..i\<^sub>1}")
                    apply presburger
                    using atLeast0AtMost by auto

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0..n-1}. phi p (n - i\<^sub>1) *
                      ((\<Sum>i\<^sub>0::\<nat> \<in> {0::\<nat>..i\<^sub>1-1}. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)))"
                    apply (subst sum.cong_simp[where B = "{0..n-1}" and 
                      g = "\<lambda>i\<^sub>1. phi p (n - i\<^sub>1) * (\<Sum>i\<^sub>0::\<nat>\<in>{0::\<nat>..i\<^sub>1 - (1::\<nat>)} \<union> {i\<^sub>1}. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)"
                      and h = "\<lambda>i\<^sub>1. phi p (n - i\<^sub>1) * ((\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..i\<^sub>1 - (1::\<nat>). phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0) + 
                            (phi p (i\<^sub>1 - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>1))"])
                    apply meson
                    apply (simp only: simp_implies_def)
                    apply (subst sum_Un[where A = "{0::\<nat>..x - (1::\<nat>)}" and B = "{x}"])
                    apply simp
                    apply simp
                    using Int_empty_right empty_iff mult_eq_0_iff phi_even_0 apply auto[1]
                    apply (subgoal_tac "phi p 0 = 0")
                    apply fastforce
                    by (simp add: phi_def)
                  (* Take out of i\<^sub>1 = 0 *)
                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0} \<union> {1..n-1}. phi p (n - i\<^sub>1) *
                      ((\<Sum>i\<^sub>0::\<nat> \<in> {0::\<nat>..i\<^sub>1-1}. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)))"
                    by (smt (verit) Suc_eq_plus1 Un_Diff_cancel Un_insert_left add_0 atLeast0AtMost 
                        atLeast1_atMost_eq_remove0 atMost_iff insert_absorb sup_bot_left zero_le)

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {1..n-1}. phi p (n - i\<^sub>1) *
                      ((\<Sum>i\<^sub>0::\<nat> \<in> {0::\<nat>..i\<^sub>1-1}. phi p (i\<^sub>1 - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)))"
                    apply (subst sum_Un)
                    apply simp+
                    using phi_even_0 by auto

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {1..n-1}. phi p (n - i\<^sub>1) *
                      ((\<Sum>i\<^sub>0::\<nat> \<in> {0::\<nat>..i\<^sub>1-1}. phi p (Suc (i\<^sub>1 - 1) - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)))"
                    apply (subgoal_tac "\<forall>x \<in> {1.. n - 1}. (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..x - 1. phi p (x - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0) =
                                        (\<Sum>i\<^sub>0::\<nat> = 0::\<nat>..x - 1. phi p (Suc (x - 1) - i\<^sub>0) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>0)")
                    apply auto[1]
                    by auto

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {1..n-1}. phi p (n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (Suc m) (Suc (i\<^sub>1 - 1)))"
                    using nu_lp.simps(4) by presburger

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {1..n-1}. phi p (n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (Suc m) i\<^sub>1)"
                    by auto

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0} \<union> {1..n-1}. phi p (n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (Suc m) i\<^sub>1)"
                    by auto
    
                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * (\<Sum>i\<^sub>1::\<nat> \<in> {0..n-1}. phi p (Suc (n-1) - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p (Suc m) i\<^sub>1)"
                    apply (subgoal_tac "{0} \<union> {1..n-1} = {0..n-1}")
                    using Suc_pred' a1 apply presburger
                    by auto

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * \<nu>\<^sub>l\<^sub>p p (Suc (Suc m)) (Suc (n - 1))"
                    using nu_lp.simps(4) a1 by presburger

                  also have "... = p * \<mu>\<^sub>l\<^sub>p p m n + (1-p) * \<nu>\<^sub>l\<^sub>p p (Suc (Suc m)) n"
                    using Suc_pred' a1 by presburger

                  finally show "p * \<mu>\<^sub>l\<^sub>p p m n + ((1::\<real>) - p) * \<mu>\<^sub>l\<^sub>p p (Suc (Suc m)) n = 
                        (\<Sum>i\<^sub>1::\<nat> = 0::\<nat>..n. phi p (Suc n - i\<^sub>1) * \<nu>\<^sub>l\<^sub>p p m i\<^sub>1)"
                    using "4"(4) "4.hyps"(2) "4.prems"(1) by presburger
                qed
            qed
        next
          case False
          then show ?thesis
            apply (subst mu_lp_zero_not_odd_or_even)
            apply (simp)
            apply (simp)
            apply (simp)
            apply (subst nu_lp_zero_not_odd_or_even)
            using assms apply simp_all
            using "4"(3) apply blast
            using "4"(4) by fastforce
        qed
    qed
  qed

subsection \<open> Programs \<close>
alphabet state = time + 
  x :: nat

definition step:: "ureal \<Rightarrow> state prhfun" where
"step p = if\<^sub>p \<guillemotleft>p\<guillemotright> then (x := x - 1) else (x := x + 1)"

definition srw_loop where
"srw_loop p  = while\<^sub>p\<^sub>t (x\<^sup>< > 0)\<^sub>e do step p od"

definition Ht:: "ureal \<Rightarrow> state rvhfun" where 
"Ht p = ((\<lbrakk>\<not>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>x\<^sup>> = x\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) + 
        \<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>x\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (
          \<lbrakk>t\<^sup>> \<ge> t\<^sup>< + x\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>(t\<^sup>> - (t\<^sup>< + x\<^sup><)) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (\<mu>\<^sub>l\<^sub>p (ureal2real \<guillemotleft>p\<guillemotright>) (x\<^sup>< - 1) (t\<^sup>> - t\<^sup>< - 1)) * (ureal2real \<guillemotleft>p\<guillemotright>) +
          \<lbrakk>t\<^sup>> \<ge> t\<^sup>< + x\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>(t\<^sup>> - (t\<^sup>< + x\<^sup>< + 2)) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (\<mu>\<^sub>l\<^sub>p (ureal2real \<guillemotleft>p\<guillemotright>) (x\<^sup>< + 1) (t\<^sup>> - t\<^sup>< - 1)) * (1 - ureal2real \<guillemotleft>p\<guillemotright>)
        )
  )\<^sub>e"

definition Pt_step_alt :: "ureal \<Rightarrow> state rvhfun" where
"Pt_step_alt p \<equiv> (\<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + 
                  \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))\<^sub>e"

lemma step_simp: "rvfun_of_prfun (step p)  = 
  (
    \<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
  )\<^sub>e"
  apply (simp only: step_def pchoice_def)
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (simp add: pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: rvfun_of_prfun_def)
  apply (expr_simp_1)
  by (pred_auto)

lemma Pt_step_simp: "rvfun_of_prfun (Pt (step p)) = Pt_step_alt p"
  apply (simp add: Pt_def)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)+
  apply (simp add: step_def)
  apply (subst pvfun_pchoice_is_dist)
  apply (simp add: pvfun_assignment_is_dist)+
  using ureal_is_prob apply blast
  apply (simp add: step_simp pvfun_assignment_inverse)
  apply (simp add: Pt_step_alt_def)
  apply (expr_simp_1)
  apply (subst fun_eq_iff)
  apply (rule allI)
proof -
  fix xa :: "state \<times> state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if get\<^bsub>x\<^esub> v\<^sub>0 = get\<^bsub>x\<^esub> (fst xa) - Suc (0::\<nat>) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>x\<^esub> v\<^sub>0 = Suc (get\<^bsub>x\<^esub> (fst xa)) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          (if \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd xa) then 1::\<real> else (0::\<real>)))"
  let ?rhs = "(if get\<^bsub>x\<^esub> (snd xa) = get\<^bsub>x\<^esub> (fst xa) - Suc (0::\<nat>) \<and> get\<^bsub>t\<^esub> (snd xa) = Suc (get\<^bsub>t\<^esub> (fst xa)) then 1::\<real> else (0::\<real>)) *
       ureal2real p + (if get\<^bsub>x\<^esub> (snd xa) = Suc (get\<^bsub>x\<^esub> (fst xa)) \<and> get\<^bsub>t\<^esub> (snd xa) = Suc (get\<^bsub>t\<^esub> (fst xa)) then 1::\<real> else (0::\<real>)) *
       ((1::\<real>) - ureal2real p)"

  have s1: "{s::state. x\<^sub>v s = x\<^sub>v (fst xa) - Suc (0::\<nat>) \<and> t\<^sub>v s = t\<^sub>v (fst xa) \<and> snd xa = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>} 
      = (if snd xa = \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst xa)), x\<^sub>v = x\<^sub>v (fst xa) - Suc (0::\<nat>)\<rparr> then {\<lparr>t\<^sub>v = t\<^sub>v (fst xa), x\<^sub>v = x\<^sub>v (fst xa) - Suc (0::\<nat>)\<rparr>} else {})"
    by auto
  have s2: "{s::state. x\<^sub>v s = Suc (x\<^sub>v (fst xa)) \<and> t\<^sub>v s = t\<^sub>v (fst xa) \<and> snd xa = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>} 
      = (if snd xa = \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst xa)), x\<^sub>v = Suc (x\<^sub>v (fst xa))\<rparr> then {\<lparr>t\<^sub>v = t\<^sub>v (fst xa), x\<^sub>v = Suc (x\<^sub>v (fst xa))\<rparr>} else {})"
    by auto
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          (if get\<^bsub>x\<^esub> v\<^sub>0 = get\<^bsub>x\<^esub> (fst xa) - Suc (0::\<nat>) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) \<and> 
            \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd xa) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>x\<^esub> v\<^sub>0 = Suc (get\<^bsub>x\<^esub> (fst xa)) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) \<and> 
            \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd xa) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p))"
    apply (rule infsum_cong)
    by simp
  have f2: "... = ?rhs"
    apply (subst infsum_constant_finite_states_cmult_2)
    apply (pred_auto)
    using s1 apply simp
    apply (pred_auto)
    using s2 apply simp
    apply (pred_auto)
    apply (smt (z3) One_nat_def card.empty card.insert empty_iff finite.intros(1) mult_if_delta of_nat_0 of_nat_1 s1 s2 show_unit.elims state.simps(1) state.surjective)
    apply (smt (verit, ccfv_threshold) One_nat_def card.empty card.insert empty_iff eq_add_iff2 finite.intros(1) mult_cancel_right2 of_nat_0 of_nat_1 s1 s2 show_unit.elims state.simps(1) state.surjective)
    using s1 s2 apply force
    using s1 s2 by force+

  then show "?lhs = ?rhs"
    using f1 by presburger
qed

lemma Pt_step_is_dist: "is_final_distribution (rvfun_of_prfun (Pt (step p)))"
  apply (simp add: Pt_def)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)+
  apply (simp add: step_def)
  apply (subst pvfun_pchoice_is_dist) 
  apply (simp add: pvfun_assignment_is_dist)+
  using ureal_is_prob apply blast
  apply (subst rvfun_seqcomp_is_dist)
  apply (simp only: step_def)
  apply (subst pvfun_pchoice_is_dist)
  by (simp add: pvfun_assignment_is_dist)+

lemma Ht_is_fp: "\<F> (x\<^sup>< > 0)\<^sub>e (Pt (step p)) (prfun_of_rvfun (Ht p)) = prfun_of_rvfun (Ht p)"
  apply (simp add: Ht_def loopfunc_def pskip_def)
  apply (simp only: prfun_pcond_altdef rvfun_skip_inverse)
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: Pt_step_is_dist)
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
  apply (expr_auto)
  apply (simp only: is_prob_def expr_defs)
  apply (rule allI, rule conjI)
  apply (smt (verit, best) mu_lp_nonneg mult_nonneg_nonneg ureal_lower_bound ureal_upper_bound)
  apply (auto)
  apply (meson mu_lp_leq_1 mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (metis diff_Suc_1 gr0_conv_Suc mu_lp.simps(4) mu_lp_leq_1 mult.commute numeral_1_eq_Suc_0 one_eq_numeral_iff ureal_lower_bound ureal_upper_bound)
  apply (metis diff_Suc_1 gr0_conv_Suc mu_lp.simps(4) mu_lp_leq_1 mult.commute numeral_1_eq_Suc_0 numeral_eq_one_iff ureal_lower_bound ureal_upper_bound)
  apply (metis mu_lp.simps(4) mu_lp_leq_1 mult.commute odd_Suc_minus_one ureal_lower_bound ureal_upper_bound)
  apply (metis diff_Suc_1 gr0_conv_Suc mu_lp.simps(4) mu_lp_leq_1 mult.commute numeral_1_eq_Suc_0 numeral_eq_one_iff ureal_lower_bound ureal_upper_bound)
  apply (simp add: Pt_step_simp Pt_step_alt_def skip_def)
  apply (pred_auto)
  proof -
    fix t::"\<nat>" and x::"\<nat>" and t\<^sub>v':: "\<nat>" and x\<^sub>v'::"\<nat>"
    let ?b1 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = x\<^sub>v (fst s) - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst s))"
    let ?b2 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = Suc (x\<^sub>v (fst s)) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst s))"
    let ?b3 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v (snd s) = t\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd s) = x\<^sub>v v\<^sub>0"
    let ?b4 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd s) = (0::\<nat>) \<and> 
                  t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd s) \<and> (t\<^sub>v (snd s) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>)"
    let ?b5 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd s) = (0::\<nat>) \<and> 
                  Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd s) \<and> 
                  (t\<^sub>v (snd s) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>)"
    
    let ?lhs = "\<lambda>s::state \<times> state. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                 ((if ?b1 s v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
                  (if ?b2 s v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                 ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v (snd s) = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd s) = x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                  (if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd s) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                  ((if t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) * (if (t\<^sub>v (snd s) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd s) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
                   (if Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) *
                   (if (t\<^sub>v (snd s) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd s) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))))"
    let ?rhs = "(\<lambda>s::state \<times> state.
              (if x\<^sub>v (fst s) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v (snd s) = t\<^sub>v (fst s) then 1::\<real> else (0::\<real>)) *
              (if x\<^sub>v (snd s) = x\<^sub>v (fst s) then 1::\<real> else (0::\<real>)) +
              (if (0::\<nat>) < x\<^sub>v (fst s) then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd s) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ((if t\<^sub>v (fst s) + x\<^sub>v (fst s) \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) *
               (if (t\<^sub>v (snd s) - (t\<^sub>v (fst s) + x\<^sub>v (fst s))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst s) - Suc (0::\<nat>)) (t\<^sub>v (snd s) - Suc (t\<^sub>v (fst s))) *
               ureal2real p +
               (if Suc (Suc (t\<^sub>v (fst s) + x\<^sub>v (fst s))) \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) *
               (if (t\<^sub>v (snd s) - Suc (Suc (t\<^sub>v (fst s) + x\<^sub>v (fst s)))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst s))) (t\<^sub>v (snd s) - Suc (t\<^sub>v (fst s))) *
               ((1::\<real>) - ureal2real p)))"
  
    have "prfun_of_rvfun
          (\<lambda>\<s>::state \<times> state.
              (if (0::\<nat>) < x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * ?lhs \<s> +
              (if x\<^sub>v (fst \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd \<s> = fst \<s> then 1::\<real> else (0::\<real>)))
        = prfun_of_rvfun ?rhs"
      apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
      apply (simp only: fun_eq_iff) 
      apply (rule allI)
      proof -
        fix x :: "state \<times> state"
    
        have s1: "{s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v (snd x) = t\<^sub>v s \<and> x\<^sub>v (snd x) = x\<^sub>v s} 
          = (if x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x) then {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = 0\<rparr>} else {})"
          by (smt (verit, best) Collect_cong Collect_empty_eq old.unit.exhaust singleton_conv state.surjective)
        then have fin_s1: "finite {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v (snd x) = t\<^sub>v s \<and> x\<^sub>v (snd x) = x\<^sub>v s}"
          by auto
    
        have s2: "{s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s 
            \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}
          = (if x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = x\<^sub>v (fst x) - Suc (0::\<nat>)\<rparr>} else {})"
          by (auto)
        then have fin_s2: "finite {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s 
            \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have s3: " {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}
          = (if x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>)))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = x\<^sub>v (fst x) - Suc (0::\<nat>)\<rparr>} else {})"
          by (auto)
        then have fin_s3: "finite {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have s4: "{s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and> 
              x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}
          = (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = Suc (x\<^sub>v (fst x))\<rparr>} else {})"
          by auto
        then have fin_s4: "finite {s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and> 
              x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have s5: "{s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}
          = (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = Suc (x\<^sub>v (fst x))\<rparr>} else {})"
          by auto
        then have fin_s5: "finite {s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have lhs_1: "?lhs x = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                   ((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
                    (if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                   ((if ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                    (if ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                      \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
                    (if ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                      \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)
                    ))"
        apply (rule infsum_cong)
        by (simp)
        also have lhs_2: "... =  (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                     (((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) * 
                       (if ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                      ((if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                      (if ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>))
                    ) + 
                    (((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) *
                     ((if ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
                     ((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) *
                     ((if ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)) + 
                     ((if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                     ((if ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
                     ((if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                     ((if ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
                  )
              )"
          apply (rule infsum_cong)
          by (simp add: comm_semiring_class.distrib distrib_left)
        also have lhs_3: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
             (if ?b1 x v\<^sub>0 \<and> ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
             ((if ?b1 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p)) +
             ((if ?b1 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))) + 
             ((if ?b2 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p)) +
             ((if ?b2 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
             )
          )"
          apply (rule infsum_cong)
          by (smt (verit) less_Suc_eq_0_disj less_numeral_extra(3) mult.assoc mult_cancel_left1 mult_eq_0_iff)
        also have lhs_4: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
             (if ?b1 x v\<^sub>0 \<and> ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
             ((if ?b1 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p)) +
             ((if ?b1 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))) + 
             ((if ?b2 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p)) +
             ((if ?b2 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))
             )
          )"
          apply (rule infsum_cong)
          by (smt (verit) mult_cancel_left1)
        also have lhs_5: "... =  card {v\<^sub>0. ?b1 x v\<^sub>0 \<and> ?b3 x v\<^sub>0} * ureal2real p + 
            card {v\<^sub>0. ?b1 x v\<^sub>0 \<and> ?b4 x v\<^sub>0} * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) + 
            card {v\<^sub>0. ?b1 x v\<^sub>0 \<and> ?b5 x v\<^sub>0} * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p)) + 
            card {v\<^sub>0. ?b2 x v\<^sub>0 \<and> ?b4 x v\<^sub>0} * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) + 
            card {v\<^sub>0. ?b2 x v\<^sub>0 \<and> ?b5 x v\<^sub>0} * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))
          "
          apply (subst infsum_constant_finite_states_cmult_5)
          using fin_s1 apply blast
          using fin_s2 apply blast
          using fin_s3 apply blast
          using fin_s4 apply blast
          using fin_s5 apply blast
          by linarith
        also have lhs_6: "... = (if x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
            (if x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) +
            (if (x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p)) +
            (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) + 
            (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))"
          using s1 s2 s3 s4 s5 by (smt (verit) One_nat_def card.empty card_1_singleton_iff of_nat_0 of_nat_1)
        (* Rewrite these inequalities*)
        have t'_ieq_1: "(Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x)) = (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x))"
          by simp
        have even_1: "((t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>)) =
              ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>))"
          using One_nat_def add_Suc diff_Suc_1 by presburger
        
        have t'_ieq_2: "(Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x)) = (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x))"
          by simp
      
        have even_2: "(Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<Longrightarrow> 
              ((t\<^sub>v (snd x) - Suc (Suc ((t\<^sub>v (fst x)) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) =
              ((t\<^sub>v (snd x) - ((t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>))"
          by fastforce
        
        have t'_ieq_3: "(Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x)) =
                        (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x))"
          by auto
        have even_3: "((t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) = 
                ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>))"
          by presburger
      
        have t'_ieq_4: "(Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) =
                        (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x))"
          by auto
        have even_4: "(Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<Longrightarrow>
                ((t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>)) = 
                ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>))"
          by fastforce
      
        have operand_2_split: "
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)
          = 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>2.2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)"
          by (smt (verit, del_insts) cancel_comm_monoid_add_class.diff_zero diff_add_inverse2 diff_diff_cancel 
              diff_diff_left le_Suc_eq mult_not_zero nat_1_add_1 not_less_eq_eq one_mod_two_eq_one plus_1_eq_Suc)
        
        have operands_2_3_merge: "
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and>
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - ((t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p))
          =
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * ((\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p +
                     (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)))"
          apply (simp only: operand_2_split)
          by (simp add: distrib_left)
        have operands_2_3_merge': "... = 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (x\<^sub>v (fst x) - 2)) * ureal2real p) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x))))))"
          using mu_lp.simps(4) by (smt (verit) Suc_diff_Suc add.commute add_Suc diff_add_inverse2 
             diff_is_0_eq le_Suc_eq le_numeral_extra(3) left_diff_distrib' mu_lp.elims mult.commute 
             nat_1_add_1 not_less_eq_eq plus_1_eq_Suc zero_less_Suc zero_less_diff)
      
        have operand_4_split: " 
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)
        =
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)"
          using le_Suc_eq not_less_eq_eq by auto
      
        have operands_4_5_merge: " 
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) + 
       \<comment> \<open>5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) 
        =
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * ((\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p +
                  (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)))"
          apply (simp only: operand_4_split)
          by (simp add: distrib_left)
        have operands_4_5_merge': "... = 
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x))))))"
          using mu_lp.simps(4)
          by (smt (verit) Suc_diff_Suc add.commute bot_nat_0.not_eq_extremum diff_Suc_Suc diff_add_inverse 
              diff_is_0_eq distrib_left le_Suc_eq mu_lp.simps(3) mult.commute plus_1_eq_Suc zero_less_diff)
      
        have lhs_7: "(if (0::\<nat>) < x\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) * ?lhs x +
                  (if x\<^sub>v (fst x) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd x = fst x then 1::\<real> else (0::\<real>))
          = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> (x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) + 
       \<comment> \<open>5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          apply (simp only: lhs_1 lhs_2 lhs_3 lhs_4 lhs_5 lhs_6)
          by auto
        have lhs_8: "... = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - ((t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) + 
       \<comment> \<open>5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          using t'_ieq_1 t'_ieq_2 t'_ieq_3 t'_ieq_4 even_1 even_2 even_3 even_4 by (smt (verit) One_nat_def add.commute add_Suc_right diff_Suc_1)
        have lhs_9: "... = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (x\<^sub>v (fst x) - 2)) * ureal2real p) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          using operands_2_3_merge operands_2_3_merge' operands_4_5_merge operands_4_5_merge' by (smt (verit, best))
      
        have lhs_10: "... =
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (x\<^sub>v (fst x) - 1))) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (x\<^sub>v (fst x) + 1))) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          using mu_lp_p_m_plus_1
          by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_pred diff_diff_left left_diff_distrib mu_lp_p_m mult.assoc mult.commute plus_1_eq_Suc power_Suc)
      
        have lhs_11: "... = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by (smt (verit) add.commute add_Suc_right cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_commute mult_cancel_left plus_1_eq_Suc)
      
        have lhs_12: "... =
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by simp
      
        have lhs_13: "... =
       \<comment> \<open> Rewrite 1 \<close>
       \<comment> \<open>1\<close> (if x\<^sub>v (fst x) = 1 \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by (simp)
      
        have lhs_14: "... =
       \<comment> \<open> Rewrite 1: from (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) to (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<close>
       \<comment> \<open>1\<close> (if x\<^sub>v (fst x) = 1 \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and> 
                ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by (smt (z3) Suc_1 Suc_diff_1 Suc_eq_plus1 bot_nat_0.not_eq_extremum 
              cancel_comm_monoid_add_class.diff_zero diff_diff_cancel diff_self_eq_0 mod_less mu_lp.simps(2) mult.commute mult_if_delta nat_le_linear)
      
        have lhs_15: "... =
       \<comment> \<open> Rewrite 1: from (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) to (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<close>
       \<comment> \<open>1+2.1+2.2+3\<close> (if x\<^sub>v (fst x) \<ge> 1 \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by fastforce
      
        have lhs_16: "... =
       \<comment> \<open> Rewrite 1: from (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) to (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<close>
       \<comment> \<open>1+2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by fastforce
   
        have rhs_1: "?rhs x =
          (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>)) +
          (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x) \<and> 
              (t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
            \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v (fst x))) * ureal2real p +
          (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
              (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
            \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - Suc (t\<^sub>v (fst x))) * ((1::\<real>) - ureal2real p)"
          by auto
      
        show "(if (0::\<nat>) < x\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) * ?lhs x +
                (if x\<^sub>v (fst x) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd x = fst x then 1::\<real> else (0::\<real>)) 
          = ?rhs x"
          apply (simp only: lhs_7 lhs_8 lhs_9 lhs_10 lhs_11 lhs_12 lhs_13 lhs_14 lhs_15 lhs_16)
          apply (simp only: rhs_1)
          by auto
      qed
    then show "prfun_of_rvfun
          (\<lambda>\<s>::state \<times> state.
              (if (0::\<nat>) < x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * ?lhs \<s> +
              (if x\<^sub>v (fst \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd \<s> = fst \<s> then 1::\<real> else (0::\<real>)))
          (\<lparr>t\<^sub>v = t, x\<^sub>v = x\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', x\<^sub>v = x\<^sub>v'\<rparr>) = prfun_of_rvfun ?rhs (\<lparr>t\<^sub>v = t, x\<^sub>v = x\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', x\<^sub>v = x\<^sub>v'\<rparr>)"
      by presburger
  qed

(*
iterdiff 0 (x\<^sup>< > 0)\<^sub>e (Pt (step p)) = 1\<^sub>p
iterdiff 1 _ _ = [x>0]
iterdiff 2 _ _ = [x=1]*(1-p) + [x>1]
iterdiff 3 _ _ 
  = 
    [x>0]([x-1=1]*p*(1-p) + [x-1>1]*p + [x+1=1]*(1-p)^2 + [x+1>1]*(1-p))
  =
    [x>0]([x=2]*p*(1-p) + [x>2]*p + [x=0]*(1-p)^2 + [x>0]*(1-p))
  =   (Combine: i.e [x>0](1-p) = [x=1](1-p) + [x=2](1-p) + [x>2](1-p))
    [x=1]*(1-p) + [x=2](p*(1-p) + (1-p)) + [x>2]*(p + (1-p))
  =   (p + 1 - p = 1) 
    [x=1]*(1-p) + [x=2](p*(1-p) + (1-p)) + [x>2]

iterdiff 4 _ _ 
  = 
    [x>0]([x-1=1]p(1-p) + [x-1=2]p(p*(1-p) + (1-p)) + [x-1>2]p +
          [x+1=1](1-p)^2 + [x+1=2](1-p)(p*(1-p) + (1-p)) + [x+1>2](1-p))
  =
    [x=1](1-p)(p*(1-p) + (1-p)) + [x=2](p(1-p) + (1-p)) + [x=3](p(p*(1-p) + (1-p)) + (1-p)) + [x > 3]

Assume (pdiff\<^sub>n\<^sup>0 = pdiff\<^sub>n\<^sup>n = 0)
  iterdiff n _ _ = (\<Sum>i:{1..n-1}. [x=i] * pdiff\<^sub>n\<^sup>i) + [x>n-1]
then
  iterdiff (Suc n) _ _ 
  =
    (\<Sum>i:{2..n}. [x=i]*p*pdiff\<^sub>n\<^sup>i\<^sup>-\<^sup>1) + [x>n]*p +
    (\<Sum>i:{0..n-2}. [x=i]*(1-p)*pdiff\<^sub>n\<^sup>i\<^sup>+\<^sup>1) + [x>n-2]*(1-p)
  =   (Combine)
    [x=1]*(1-p)*pdiff\<^sub>n\<^sup>2 + (\<Sum>i:{2..n-2}. [x=i]*(p*pdiff\<^sub>n\<^sup>i\<^sup>-\<^sup>1 + (1-p)*pdiff\<^sub>n\<^sup>i\<^sup>+\<^sup>1)) + 
    [x=n-1]*(p*pdiff\<^sub>n\<^sup>n\<^sup>-\<^sup>2 + (1-p)) + [x=n]*(p*pdiff\<^sub>n\<^sup>n\<^sup>-\<^sup>1 + (1-p)) + [x>n]
*)

text \<open> The probability difference of @{text "x"} being @{text "m"} after @{text "n"} steps, denotes as 
  @{text "pdiff p m n"}, where @{text "p"} is the probability, @{text "m"} is the value of 
  @{text "x"} (such as @{text "\<lbrakk>x\<^sup>< = m\<rbrakk>"}) and @{text "n"} is the number of steps in @{text "iterdiff n _ _"}.
  So @{text "iterdiff n (x\<^sup>< > 0)\<^sub>e (Pt (step p)) = \<Sum>m::nat. pdiff p m n * \<lbrakk>x\<^sup>< = m\<rbrakk>"}
\<close>
fun pdiff :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"pdiff p 0 _ = 0" |
"pdiff p _ 0 = 0" |
"pdiff p _ (Suc 0) = 1" |
"pdiff p (Suc 0) (Suc (Suc 0)) = 1-p" |
"pdiff p (Suc i) (Suc (Suc 0)) = 1" |
\<comment> \<open>pdiff 1 (Suc n)\<close>
"pdiff p (Suc 0) (Suc n) = (1-p) * pdiff p 2 n " |
"pdiff p (Suc i) (Suc n) = (if i \<le> n - 2 
  then 
    p * pdiff p i n + (1-p) * pdiff p (Suc (Suc i)) n 
  else 
    p * pdiff p i n + (1-p)
)"

(*
	m=0	1	2	3	4	5	6	7	8
n=0	0	0	0	0	0	0	0	0	0
1	0	1	1	1	1	1	1	1	1
2	0	0.5	1	1	1	1	1	1	1
3	0	0.5	0.75	1	1	1	1	1	1
4	0	0.375	0.75	0.875	1	1	1	1	1
5	0	0.375	0.625	0.875	0.9375	1	1	1	1
6	0	0.3125	0.625	0.78125	0.9375	0.96875	1	1	1
7	0	0.3125	0.546875	0.78125	0.875	0.96875	0.984375	1	1
8	0	0.2734375	0.546875	0.7109375	0.875	0.9296875	0.984375	0.9921875	1
*)

(*
  For "pdiff p m n", it can reach to position (0 or 1, n=1) to (m + n - 1, 1) in (n - 1) steps

    S1. if m = 0 \<or> n = 0,  pdiff p m n = 0
    S2. else if m \<ge> n,   pdiff p m n = 1
    S3. else (m < n) 
      pdiff p m n = \<Sum>k \<in> {(if even(m+n) then 1 else 0) .. m+n-1}. 
        ((n-1) choose r) * (pdiff p k 1) * p ^ (n - 1 - r) * q ^ r 
      where r = (((n - 1) + (k - m)) / 2), represent the number of right-moving steps
*)

(*
  illustrations: if n = 4, m = 2, (m+n-1=5). \<Sum>{1,3,5}. 
      (3 choose (3 - 1) / 2) * p^(3-1)*q^1 = 3 * p^2*q^1
      (3 choose (3 + 1) / 2) * p^1*q^2  = 3 * p^1*q^2  
      (3 choose (3 + 3) / 2) * p^0*q^3 = q^3
*)
value "pdiff p 0 1"
value "pdiff p 1 1"
value "pdiff p 0 2"
value "pdiff p 1 2"
value "pdiff p 2 2"
value "pdiff p 3 2"
value "pdiff p 5 2"
value "pdiff p 1 3"
value "pdiff p 2 3"
value "pdiff p 3 3"
value "pdiff p 5 3"
value "pdiff p 1 4"
value "pdiff p 2 4"
value "pdiff p 3 4"
value "pdiff p 5 4"
thm "pdiff.induct"
thm "pdiff.elims"
thm "pdiff.simps"

fun pdiff1 :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"pdiff1 p 0 _ = 0" |
"pdiff1 p _ 0 = 0" |
"pdiff1 p _ (Suc 0) = 1" |
"pdiff1 p (Suc i) (Suc n) = (if i < n
  then 
    p * pdiff1 p i n + (1-p) * pdiff1 p (Suc (Suc i)) n 
  else 
    p * pdiff1 p i n + (1-p)
)"

value "pdiff1 p 0 1 = pdiff p 0 1"
value "pdiff1 p 1 1 = pdiff p 1 1"
value "pdiff1 p 0 2 = pdiff p 0 2"
value "pdiff1 p 1 2 = pdiff p 1 2"
value "pdiff1 p 2 2 = pdiff p 2 2"
value "pdiff1 p 3 2 = pdiff p 3 2"
value "pdiff1 p 5 2 = pdiff p 5 2"
value "pdiff1 p 1 3 = pdiff p 1 3"
value "pdiff1 p 2 3 = pdiff p 2 3"
value "pdiff1 p 3 3 = pdiff p 3 3"
value "pdiff1 p 5 3 = pdiff p 5 3"
value "pdiff1 p 1 4 = pdiff p 1 4"
value "pdiff1 p 2 4 = pdiff p 2 4"
value "pdiff1 p 3 4 = pdiff p 3 4"
value "pdiff1 p 5 4 = pdiff p 5 4"

fun pdiff2 :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"pdiff2 p 0 _ = 0" |
"pdiff2 p _ 0 = 0" |
"pdiff2 p _ (Suc 0) = 1" |
"pdiff2 p (Suc i) (Suc n) = p * pdiff2 p i n + (1-p) * pdiff2 p (Suc (Suc i)) n"

value "pdiff2 p 0 1 = pdiff p 0 1"
value "pdiff2 p 1 1 = pdiff p 1 1"
value "pdiff2 p 0 2 = pdiff p 0 2"
value "pdiff2 p 1 2 = pdiff p 1 2"
value "pdiff2 p 2 2 = pdiff p 2 2"
value "pdiff2 p 3 2 = pdiff p 3 2"
value "pdiff2 p 5 2 = pdiff p 5 2"
value "pdiff2 p 1 3 = pdiff p 1 3"
value "pdiff2 p 2 3 = pdiff p 2 3"
value "pdiff2 p 3 3 = pdiff p 3 3"
value "pdiff2 p 5 3 = pdiff p 5 3"
value "pdiff2 p 1 4 = pdiff p 1 4"
value "pdiff2 p 2 4 = pdiff p 2 4"
value "pdiff2 p 3 4 = pdiff p 3 4"
value "pdiff2 p 5 4 = pdiff p 5 4"

lemma pdiff2_closed_form:
  assumes "1 \<le> i" "i \<le> n"
  shows "pdiff2 p i n = (of_nat ((n - 1) choose (i - 1))) * p^(i - 1) * (1 - p)^(n - i)"

lemma pdiff_m_0_0:
  shows "pdiff p 0 n = 0"
  by auto

lemma pdiff_n_0_0:
  shows "pdiff p m 0 = 0"
  using pdiff.elims by blast

lemma pdiff_n_1_1:
  assumes "m > 0"
  shows "pdiff p m 1 = 1"
  using assms gr0_conv_Suc by fastforce

lemma pdiff_m_1_n_2_1_p:
  shows "pdiff p 1 2 = 1 - p"
  using One_nat_def Suc_1 pdiff.simps(4) by presburger

lemma pdiff_m_n_2_1:
  assumes "m > 0"
  shows "pdiff p (m+1) 2 = 1"
  by (metis One_nat_def Suc_1 Suc_pred add.commute assms pdiff.simps(5) plus_1_eq_Suc)

lemma pdiff_m_1_n_1:
  assumes "n > 1"
  shows "pdiff p 1 (Suc n) = (1-p) * pdiff p 2 n"
  by (metis assms less_natE numeral_nat(7) pdiff.simps(6) plus_1_eq_Suc)

lemma pdiff_m_gt_n_0:
  assumes "n \<ge> 2" "m \<ge> n"
  shows "pdiff p m n = (m div n) * (n choose ((n+m) div 2)) * p^((n+m) div 2) * (1 - p)^((n - m) div 2)"
  sorry

lemma pdiff_m_gt_n_1:
  assumes "n \<ge> 1" "n \<le> m"
  shows "pdiff p m n = 1"
  sledgehammer

(* https://en.wikipedia.org/wiki/Bertrand%27s_ballot_theorem *)
(* Feller, "An Introduction to Probability Theory and Its Applications", Vol. 1, Section III.6 (Ballot problem) *)
lemma 
  assumes "(m::nat) \<ge> 0" "n \<ge> m" "even (m+n)"
  shows "pdiff p m n = (m div n) * (n choose ((n+m) div 2)) * p^((n+m) div 2) * (1 - p)^((n - m) div 2)"
  sorry


definition "P k N = pdiff (1/2) k N"
value "pdiff (1/2) 4 9"

fun pdiff' :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"pdiff' p _ 0 = 1" |
"pdiff' p 0 _ = 0" |
"pdiff' p (Suc m) (Suc n) = p * pdiff' p m n + (1-p) * pdiff' p (Suc (Suc m)) n"

value "pdiff' p 0 1"
value "pdiff' p 2 2"
value "pdiff' 0.5 2 2"
value "pdiff' 0.5 2 3"
value "pdiff' 0.5 2 4"
value "pdiff' 0.5 2 5"
value "pdiff' 0.5 2 6"
value "pdiff' 0.5 2 7"
value "pdiff' 0.5 2 8"
value "pdiff' 0.5 5 20"

lemma 
  assumes "(m::nat) \<ge> 0" "n \<ge> m" "even (m+n)"
  shows "pdiff' p m n = (n choose ((n+m) div 2)) * p^((n+m) div 2) * (1 - p)^((n - m) div 2)"
  sorry

lemma pdiff_1: "m \<ge> n \<Longrightarrow> pdiff p (Suc m) (Suc n) = 1"
proof (induct p m n rule: pdiff.induct)
  case (1 p uu)
  then show ?case by auto
next
  case (2 p v)
  then show ?case by auto
next
  case (3 p v)
  then show ?case by auto
next
  case (4 p)
  then show ?case by auto
next
  case (5 p v)
  then show ?case by auto
next
  case (6 p va)
  then show ?case by auto
next
  case ("7_1" p va vb)
  then show ?case by auto
next
  case ("7_2" p v va)
  then show ?case by auto
qed

lemma pdiff_geq_0: 
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "pdiff p m n \<ge> 0"
  using assms
proof (induct p m n rule: pdiff.induct)
  case (1 p uu)
  then show ?case by auto
next
  case (2 p v)
  then show ?case by auto
next
  case (3 p v)
  then show ?case by auto
next
  case (4 p)
  then show ?case by auto
next
  case (5 p v)
  then show ?case by auto
next
  case (6 p va)
  then show ?case by auto
next
  case ("7_1" p va vb)
  then show ?case by auto
next
  case ("7_2" p v va)
  then show ?case by auto
qed

lemma pdiff_leq_1: 
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "pdiff p m n \<le> 1"
  using assms
proof (induct p m n rule: pdiff.induct)
  case (1 p uu)
  then show ?case by auto
next
  case (2 p v)
  then show ?case by auto
next
  case (3 p v)
  then show ?case by auto
next
  case (4 p)
  then show ?case by auto
next
  case (5 p v)
  then show ?case by auto
next
  case (6 p va)
  then show ?case by (simp add: mult_le_one pdiff_geq_0)
next
  case ("7_1" p va vb)
  then show ?case
    by (smt (verit, ccfv_threshold) mult_left_le pdiff.simps(7))
next
  case ("7_2" p v va)
  then show ?case
    by (smt (verit, best) mult_left_le pdiff.simps(7))
qed

lemma pdiff_7_1_simps: 
  assumes "m \<ge> 2" "n \<ge> 3"
  shows "pdiff p m n = p * pdiff p (m-1) (n-1) + (1-p) * pdiff p (Suc m) (n-1)"
  using assms
  proof (induct p m n rule: pdiff.induct)
    case (1 p uu)
    then show ?case by auto
  next
    case (2 p v)
    then show ?case by auto
  next
    case (3 p v)
    then show ?case by auto
  next
    case (4 p)
    then show ?case by auto
  next
    case (5 p v)
    then show ?case by auto
  next
    case (6 p va)
    then show ?case by auto
  next
    case ("7_1" p va vb)
    then show ?case using pdiff_1 by force
  next
    case ("7_2" p v va)
    then show ?case by (simp add: pdiff_1)
  qed

lemma pdiff_7_2_simps: 
  assumes "m \<ge> 2" "\<not> (m-1 \<le> (n-1) - 2)" "n \<ge> 3"
  shows "pdiff p m n = p * pdiff p (m-1) (n-1) + (1-p)"
  using assms
  proof (induct p m n rule: pdiff.induct)
    case (1 p uu)
    then show ?case by auto
  next
    case (2 p v)
    then show ?case by auto
  next
    case (3 p v)
    then show ?case by auto
  next
    case (4 p)
    then show ?case by auto
  next
    case (5 p v)
    then show ?case by auto
  next
    case (6 p va)
    then show ?case by auto
  next
    case ("7_1" p va vb)
    then show ?case using pdiff_1 by force
  next
    case ("7_2" p v va)
    then show ?case by (simp add: pdiff_1)
  qed

thm "eventually_mono"
lemma pdiff_dec_n:
  assumes "m > 0" "n \<ge> 1"
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "pdiff p m (Suc n) \<le> pdiff p m n"
  using assms
  proof (induct p m n rule: pdiff.induct)
    case (1 p uu)
    then show ?case by auto
  next
    case (2 p v)
    then show ?case using not_one_le_zero by blast
  next
    case (3 p v)
    then show ?case by (simp add: pdiff_leq_1)
  next
    case (4 p)
    then show ?case by (simp add: mult_left_le pdiff_leq_1)
  next
    case (5 p v)
    then show ?case using pdiff.simps(5) pdiff_leq_1 by presburger
  next
    case (6 p va)
    then show ?case apply (subst pdiff.simps(6))
      by (simp add: ordered_comm_semiring_class.comm_mult_left_mono)
  next
    case ("7_1" p va vb)
    then show ?case apply (subst pdiff.simps(7))
      apply (auto)
      apply (smt (verit, best) mult_left_mono)
      apply (smt (verit, best) ordered_comm_semiring_class.comm_mult_left_mono)
      apply (simp add: ordered_comm_semiring_class.comm_mult_left_mono pdiff_1)
      using mult_left_mono by blast
  next
    case ("7_2" p v va)
    then show ?case apply (subst pdiff.simps(7))
    apply (auto)
    apply (smt (verit, best) mult_left_mono)
    apply (smt (verit, best) ordered_comm_semiring_class.comm_mult_left_mono)
    apply (simp add: ordered_comm_semiring_class.comm_mult_left_mono pdiff_1)
    using mult_left_mono by blast
  qed

lemma pdiff_dec_m:
  assumes "m > 0" "n \<ge> 1"
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "pdiff p m n \<le> pdiff p (Suc m) n"
  using assms
  proof (induct p m n rule: pdiff.induct)
    case (1 p uu)
    then show ?case by auto
  next
    case (2 p v)
    then show ?case using not_one_le_zero by blast
  next
    case (3 p v)
    then show ?case by (simp add: pdiff_leq_1)
  next
    case (4 p)
    then show ?case using pdiff.simps(5) pdiff_leq_1 by presburger
  next
    case (5 p v)
    then show ?case by auto
  next
    case (6 p va)
    then show ?case apply (subst pdiff.simps(6))
      by (smt (verit) One_nat_def Suc_1 less_Suc_eq_le mult_left_le mult_nonneg_nonneg not_less_eq_eq 
          ordered_comm_semiring_class.comm_mult_left_mono pdiff.simps(7) pdiff_geq_0 pdiff_leq_1 zero_less_Suc)
  next
    case ("7_1" p va vb)
    then show ?case apply (subst pdiff.simps(7))
      apply (auto)
      apply (smt (verit, best) mult_left_mono)
      apply (simp add: ordered_comm_semiring_class.comm_mult_left_mono pdiff_1)
      using mult_left_mono by blast
  next
    case ("7_2" p v va)
    then show ?case apply (subst pdiff.simps(7))
    apply (auto)
    apply (smt (verit, best) mult_left_mono)
    apply (simp add: ordered_comm_semiring_class.comm_mult_left_mono pdiff_1)
    using mult_left_mono by blast
  qed

lemma pdiff'_tends_to_0:
  shows "(\<lambda>n::\<nat>. pdiff' (1/2) m (Suc n)) \<longlonglongrightarrow> (0::\<real>)"
proof (induction m rule: less_induct)
  case (less m)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis by simp
  next
    case (Suc m')
    have eq: "pdiff' (1/2) (Suc m') (Suc n) = (1/2) * pdiff' (1/2) m' n + (1/2) * pdiff' (1/2) (Suc (Suc m')) n"
      by simp
    have lim1: "(\<lambda>n. (1/2) * pdiff' (1/2) m' n) \<longlonglongrightarrow> 0"
      using less.IH[of m'] tendsto_mult_right_zero less_Suc_eq
      by (metis LIMSEQ_imp_Suc Suc)
    have lim2: "(\<lambda>n. (1/2) * pdiff' (1/2) (Suc (Suc m')) n) \<longlonglongrightarrow> 0"
      using less.IH[of "Suc (Suc m')"] tendsto_mult_right_zero less_Suc_eq apply auto
      sledgehammer
    show ?thesis
      by (simp add: eq lim1 lim2 tendsto_add)
  qed
qed

proof (induction m)
  case 0
  show ?case
    by simp
next
  case (Suc m)
  have eq: "pdiff' (1/2) (Suc m) (Suc n) = (1/2) * pdiff' (1/2) m n + (1/2) * pdiff' (1/2) (Suc (Suc m)) n"
    by simp
  have lim1: "(\<lambda>n. (1/2) * pdiff' (1/2) m n) \<longlonglongrightarrow> 0"
    using Suc.IH(1) tendsto_mult_right_zero LIMSEQ_imp_Suc by blast
  have lim2: "(\<lambda>n. (1/2) * pdiff' (1/2) (Suc (Suc m)) n) \<longlonglongrightarrow> 0"
    using Suc.IH(2) tendsto_mult_right_zero LIMSEQ_imp_Suc sledgehammer
  show ?case
    by (simp add: eq lim1 lim2 tendsto_add)
qed

lemma pdiff_tends_to_0:
  assumes "m > 0" 
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "(\<lambda>n::\<nat>. pdiff p m (Suc n)) \<longlonglongrightarrow> (0::\<real>)"
  apply (rule decreasing_tendsto)
  apply (simp add: assms(2) assms(3) pdiff_geq_0)
  apply (subst eventually_sequentially)
proof -
  fix x :: "real"
  assume a1: "(0::\<real>) < x"

  show "\<exists>N::\<nat>. \<forall>n::\<nat>. N \<le> n \<longrightarrow> pdiff p m (Suc n) < x"
    using assms a1
    proof (induct p m xa rule: pdiff.induct)
      case (1 p uu)
      then show ?case by auto
    next
      case (2 p v)
      then show ?case by auto
    next
      case (3 p v)
      then show ?case by auto
    next
      case (4 p)
      then show ?case by auto
    next
      case (5 p v)
      then show ?case sorry
    next
      case (6 p va)
      then show ?case sorry
    next
      case ("7_1" p va vb)
      then show ?case sorry
    next
      case ("7_2" p v va)
      then show ?case sorry
    qed

(*
(x\<^sup>< > 0) * ((\<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))
; 1)
= 
(x\<^sup>< > 0) 

(x\<^sup>< > 0) * ((\<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))
; [])()
*)
lemma loop_body_iterdiff_simp:
  shows "(iter\<^sub>d 0 (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = 1\<^sub>p"
        "(iter\<^sub>d (Suc n) (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * pdiff (ureal2real \<guillemotleft>p\<guillemotright>) ($x\<^sup><) (\<guillemotleft>n\<guillemotright>+1))\<^sub>e)"
proof -
  show "(iter\<^sub>d 0 (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = 1\<^sub>p"
    by auto
  show "(iter\<^sub>d (Suc n) (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * pdiff (ureal2real \<guillemotleft>p\<guillemotright>) ($x\<^sup><) (\<guillemotleft>n\<guillemotright>+1))\<^sub>e)"
    apply (induction n)
    apply (simp)
    apply (subst prfun_seqcomp_one)
    using Pt_step_is_dist apply auto[1]
    apply (simp add: pfun_defs)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (simp add: prfun_of_rvfun_def)
     apply (pred_auto)
    apply (metis Suc_diff_1 pdiff.simps(3))
    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    using Pt_step_is_dist apply auto[1]
    apply (simp add: ureal_is_prob)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    using pdiff_geq_0 ureal_lower_bound ureal_upper_bound apply presburger
    using pdiff_leq_1 ureal_lower_bound ureal_upper_bound apply blast

    apply (simp add: mult_le_one power_le_one ureal_lower_bound ureal_upper_bound)+
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (simp only: Pt_step_simp Pt_step_alt_def)
    apply (expr_auto)
    defer
    apply (simp add: pzero_def rvfun_of_prfun_def ureal2real_0)
  proof -
    fix n::"\<nat>" and ta::"\<nat>" and xa::"\<nat>"
    assume a1: "(0::\<nat>) < xa"

    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = xa - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if x\<^sub>v v\<^sub>0 = Suc xa \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          ((if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * pdiff (ureal2real p) (x\<^sub>v v\<^sub>0) (Suc n)))"

    have set1: "{s::state. x\<^sub>v s = xa - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc ta \<and> (0::\<nat>) < x\<^sub>v s} = 
        (if xa > Suc 0 then {\<lparr>t\<^sub>v = Suc ta, x\<^sub>v = xa - Suc (0::\<nat>)\<rparr>} else {})"
      by auto

    have set2: "{s::state. x\<^sub>v s = Suc xa \<and> t\<^sub>v s = Suc ta \<and> (0::\<nat>) < x\<^sub>v s} = 
        {\<lparr>t\<^sub>v = Suc ta, x\<^sub>v = Suc xa\<rparr>}"
      by auto
    have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = xa - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc ta \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
              (ureal2real p * pdiff (ureal2real p) (xa - Suc (0::\<nat>)) (Suc n)) +
           (if x\<^sub>v v\<^sub>0 = Suc xa \<and> t\<^sub>v v\<^sub>0 = Suc ta \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
              (((1::\<real>) - ureal2real p) * pdiff (ureal2real p) (Suc xa) (Suc n))))"
      apply (rule infsum_cong)
      by force
    also have "... = (if xa > Suc 0 then (ureal2real p * pdiff (ureal2real p) (xa - Suc (0::\<nat>)) (Suc n)) else 0) + 
        ((1::\<real>) - ureal2real p) * pdiff (ureal2real p) (Suc xa) (Suc n)"
      apply (subst infsum_constant_finite_states_cmult_2)
      apply (simp add: set1)
      apply (simp add: set2)
      by (simp add: set1 set2)
    also have "... = pdiff (ureal2real p) xa (Suc (Suc n))"
      apply (cases "xa > Suc 0")
      apply (simp)
      apply (cases "xa - 1 \<le> (Suc n) - 2")
      apply (rule sym)
      apply (subst pdiff_7_1_simps)
      apply simp+
      apply (cases "n = 0")
      apply (smt (verit) Suc_diff_Suc Suc_pred a1 mult_cancel_left1 pdiff.simps(3) pdiff.simps(5))
      apply (rule sym)
      apply (subst pdiff_7_1_simps)
      apply simp+
      apply (cases "xa = 0")
      using a1 apply blast
      apply (cases "n = 0")
      using Suc_lessI apply fastforce
      by (metis Suc_1 less_antisym linorder_less_linear not0_implies_Suc not_less0 numeral_1_eq_Suc_0 one_eq_numeral_iff pdiff.simps(6))
    then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = xa - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if x\<^sub>v v\<^sub>0 = Suc xa \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          ((if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * pdiff (ureal2real p) (x\<^sub>v v\<^sub>0) (Suc n))) =
       pdiff (ureal2real p) xa (Suc (Suc n))"
      using calculation by presburger
  qed
qed

lemma loop_body_iterdiff_tendsto_0:
  assumes "p < 1"
  shows "\<forall>s::state \<times> state. (\<lambda>n::\<nat>. ureal2real (iter\<^sub>d n (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have f1: "(\<lambda>n::\<nat>. ureal2real (iterdiff (Suc n) (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst loop_body_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    using pdiff_geq_0 ureal_lower_bound ureal_upper_bound apply presburger
    apply (simp add: pdiff_leq_1 ureal_lower_bound ureal_upper_bound)
    defer
    apply (simp add: real2ureal_inverse)
    sorry
  then show "(\<lambda>n::\<nat>. ureal2real (iter\<^sub>d n (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst (asm) Suc_eq_plus1)
    by (rule LIMSEQ_offset[where k = 1])
qed

(*
while\<^sub>p\<^sub>t (x\<^sup>< > 0)\<^sub>e do 
  if c = F then (c := F \<oplus>\<^bsub>pFF\<^esub> c := B) else (c := F \<oplus>\<^bsub>pBF\<^esub> c := B);
  if c = F then (o := H \<oplus>\<^bsub>pFH\<^esub> o := T) else (o := H \<oplus>\<^bsub>pBH\<^esub> o := T);
od

(\<lbrakk>c = F \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFH +
\<lbrakk>c = F \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFT +
\<lbrakk>c = F \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBH +
\<lbrakk>c = F \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBT +
\<lbrakk>c = B \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFH +
\<lbrakk>c = B \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFT +
\<lbrakk>c = B \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBH +
\<lbrakk>c = B \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBT) 

(
\<lbrakk>c = F \<and> c0 = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFH +
\<lbrakk>c = F \<and> c0 = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFT +
\<lbrakk>c = F \<and> c0 = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBH +
\<lbrakk>c = F \<and> c0 = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBT +
\<lbrakk>c = B \<and> c0 = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFH +
\<lbrakk>c = B \<and> c0 = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFT +
\<lbrakk>c = B \<and> c0 = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBH +
\<lbrakk>c = B \<and> c0 = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBT
) * 
 (
\<lbrakk>c = F \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFH +
\<lbrakk>c = F \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFT +
\<lbrakk>c = F \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBH +
\<lbrakk>c = F \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBT +
\<lbrakk>c = B \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFH +
\<lbrakk>c = B \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFT +
\<lbrakk>c = B \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBH +
\<lbrakk>c = B \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBT
)

*)

thm "arg_cong"

end
