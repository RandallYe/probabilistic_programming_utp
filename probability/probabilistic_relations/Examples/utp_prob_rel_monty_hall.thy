section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_monty_hall
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> No Change \<close>

alphabet DWTA_state = 
  p :: nat
  c :: nat
  m :: nat

term "p\<^sup>>"
term "p\<^sup><"
term "$p\<^sup>>"

term "\<^bold>N \<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e"
term "\<^bold>N\<^sub>\<alpha> x (\<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
term "((\<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e)) * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

term "(prel_of_rfrel (p \<^bold>\<U> {0, 1, 2}))"

definition INIT_p :: "DWTA_state phrel" where 
"INIT_p = prel_of_rfrel (p \<^bold>\<U> {0, 1, 2})"

lemma infsum_alt_3: 
  "(\<Sum>\<^sub>\<infinity>v::\<nat>. if v = (0::\<nat>) \<or> Suc (0::\<nat>) = v \<or> v = (2::\<nat>) then 1::\<real> else (0::\<real>)) = (3::\<real>)"
  apply (simp add: infsum_constant_finite_states)
  apply (subgoal_tac "{s::\<nat>. s = (0::\<nat>) \<or> Suc (0::\<nat>) = s \<or> s = (2::\<nat>)} = {0, Suc 0, 2}")
   apply simp
  apply (simp add: set_eq_iff)
  by meson

lemma INIT_p_simp: 
  "INIT_p = prel_of_rfrel ((\<lbrakk>p\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 3)\<^sub>e"
  apply (simp add: INIT_p_def)
  apply (simp add: dist_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp_all add: infsum_alt_3)

definition INIT_c :: "DWTA_state phrel" where 
"INIT_c = prel_of_rfrel (c \<^bold>\<U> {0, 1, 2})"

lemma INIT_c_simp: 
  "INIT_c = prel_of_rfrel ((\<lbrakk>p\<^sup>> = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 3)\<^sub>e"
  apply (simp add: INIT_c_def)
  apply (simp add: dist_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp_all add: infsum_alt_3)

definition INIT:: "DWTA_state phrel" where 
"INIT = INIT_p ; INIT_c"

term "(x)\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr>"
find_theorems name:"DWTA_state"
record x = i :: nat

thm "DWTA_state.select_convs"
thm "DWTA_state.surjective"
thm "DWTA_state.update_convs"

(*
lemma "\<lbrakk>r1\<lparr>c\<^sub>v := a\<rparr> = r2\<lparr>c\<^sub>v := b\<rparr>\<rbrakk> \<Longrightarrow> (a = b)"
  by (metis DWTA_state.select_convs(2) DWTA_state.surjective DWTA_state.update_convs(2))

lemma "\<lbrakk>(a \<noteq> b)\<rbrakk> \<Longrightarrow> r1\<lparr>c\<^sub>v := a\<rparr> \<noteq> r2\<lparr>c\<^sub>v := b\<rparr>"
  by (metis DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(2))
*)

lemma record_update_simp:
  assumes "m\<^sub>v (r\<^sub>1::DWTA_state) = m\<^sub>v r\<^sub>2"
  shows "(r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>v (r\<^sub>2), c\<^sub>v := x\<rparr> = r\<^sub>2) \<longleftrightarrow> c\<^sub>v r\<^sub>2 = x"
  apply (auto)
  apply (metis DWTA_state.select_convs(2) DWTA_state.surjective DWTA_state.update_convs(2))
  by (simp add: assms)

lemma card_1_singleton:
  assumes "\<exists>!x. P x"
  shows "card {x. P x} = Suc (0::\<nat>)"
  using assms card_1_singleton_iff by fastforce

lemma card_0_singleton:
  assumes "\<not>(\<exists>x. P x)"
  shows "card {x. P x} = (0::\<nat>)"
  using assms by auto

lemma card_0_false:
  shows "card {x. False} = (0::\<real>)"
  by simp

find_theorems name:"fun_eq_iff"
lemma INIT_simp: "INIT = prel_of_rfrel ((\<lbrakk>p\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 9)\<^sub>e"
  apply (simp add: INIT_def INIT_p_def INIT_c_def)
  apply (simp add: prel_defs)
  apply (simp add: uniform_dist_altdef')
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp only: fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "DWTA_state \<times> DWTA_state"
  let ?rhs = "(if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = m\<^sub>v (fst x) then 1::\<real> else (0::\<real>))"
  let ?rhs_1 = "(if (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (m\<^sub>v (snd x) = m\<^sub>v (fst x)) then 1::\<real> else (0::\<real>))"

  let ?lhs_1 = "\<lambda>v\<^sub>0. (if fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real>
           else (0::\<real>)) *
     (if v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "\<lambda>v\<^sub>0. (if (fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0) \<and>
          (v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x) then 1::\<real>
           else (0::\<real>))"

  have fr: "?rhs / (9::\<real>) = ?rhs_1 / (9::\<real>)"
    by simp

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_1 v\<^sub>0 / (9::\<real>)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_2 v\<^sub>0 / (9::\<real>))"
    by (simp add: infsum_cong)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_2 v\<^sub>0 * ( 1 / (9::\<real>)))"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_2 v\<^sub>0) * ( 1 / (9::\<real>))"
    apply (subst infsum_cmult_left[where c = "1 / (9::real)"])
    apply (simp add: infsum_constant_finite_states_summable)
    by simp

  also have fl: "... = 
    (1 * card {v\<^sub>0. (fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0) \<and>
          (v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x)}
    ) * ( 1 / (9::\<real>))"
    by (simp add: infsum_constant_finite_states)

  have ff1: "card {v\<^sub>0. (fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0) \<and>
        (v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x)}
    = ?rhs_1"
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "fst x\<lparr>p\<^sub>v := p\<^sub>v (snd x)\<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply presburger
    apply (simp add: record_update_simp)
    apply (erule conjE)+
    apply (smt (z3) DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2))
    apply (rule conjI)
    apply (rule impI)
    apply (smt (verit, ccfv_threshold) DWTA_state.ext_inject DWTA_state.surjective 
          DWTA_state.update_convs(1) DWTA_state.update_convs(2) less_nat_zero_code)
    apply (rule conjI)
    apply (rule impI)
    apply (smt (verit, ccfv_threshold) DWTA_state.ext_inject DWTA_state.surjective 
          DWTA_state.update_convs(1) DWTA_state.update_convs(2) less_nat_zero_code)
    apply (rule impI)
    by (smt (verit, ccfv_threshold) DWTA_state.ext_inject DWTA_state.surjective 
          DWTA_state.update_convs(1) DWTA_state.update_convs(2) less_nat_zero_code)

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_1 v\<^sub>0 / (9::\<real>)) = ?rhs / (9::\<real>) "
    apply (simp only: fr fl)
    using ff1 calculation fl by linarith
qed

end
