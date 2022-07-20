section \<open> Probabilistic relation programming \<close>

theory utp_prob_rel_prog
  imports 
    (* "HOL.Series" *)
    "HOL-Analysis.Infinite_Sum" 
    "utp_iverson_bracket" 
    "utp_distribution"
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems prel_defs

(* Real-valued functions whose domain is Cartesian product of initial and final states. *)
type_synonym ('s\<^sub>1, 's\<^sub>2) rfrel = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rfhrel = "('s, 's) rfrel"

\<comment> \<open>A question here: can we use existing PMFs as types for prel? Why a new type here. \<close>
typedef ('s\<^sub>1, 's\<^sub>2) prel = "{f::('s\<^sub>1, 's\<^sub>2) rfrel. is_final_distribution f}"
  morphisms rfrel_of_prel prel_of_rfrel
  apply (simp add: dist_defs taut_def)
  apply (rule_tac x = "\<lambda>(a,b). if b = c then 1 else 0" in exI)
  apply (auto)
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  by (auto)

find_theorems "prel.rfrel_of_prel"
term "prel_of_rfrel"
term "rfrel_of_prel"
thm "prel_of_rfrel_inverse"
thm "rfrel_of_prel"

type_synonym 's phrel = "('s, 's) prel"

text \<open> Reachable states of @{text P} from an initial state @{text s} are such states @{text s'} 
that have probability @{text "P (s, s')"} larger than 0. 
\<close>
definition reachable_states :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> 's\<^sub>1 \<Rightarrow> 's\<^sub>2 set" where
[prel_defs]: "reachable_states P s = {s'. (curry (rfrel_of_prel P)) s s' > 0}"

(*
text \<open> A deadlock state has no reachable states from it. \<close>
definition deadlock_state where
[prel_defs]: "deadlock_state P s = (reachable_states P s = {})"
*)

subsection \<open> Probabilistic programming \<close>
(* Priorities from larger (tighter) to smaller:
  II, :=\<^sub>p, pif then else, ;, \<parallel> 
*)

(* deadlock: zero and not a distribution *)
abbreviation zero_f ("0\<^sub>f") where
  "zero_f \<equiv> (\<lambda> s. 0::\<real>)"

(* This is underspecified and could be assigned an arbitrary value. 
TODO: How to deal with this?
*)
definition pzero :: "('s\<^sub>1, 's\<^sub>2) prel" ("0\<^sub>p") where
[prel_defs]: "pzero = prel_of_rfrel zero_f"

(*
lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: prel_defs)
  by (simp add: is_prob_def prel_of_rfrel_inverse)
*)

subsubsection \<open> Skip \<close>
(* The purpose of this abbreviation is to make later reference to this function inside pskip easier. *)
abbreviation pskip\<^sub>_f ("II\<^sub>f") where
  "pskip\<^sub>_f \<equiv> \<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition pskip :: "'s phrel" ("II\<^sub>p") where
[prel_defs]: "pskip = prel_of_rfrel (pskip\<^sub>_f)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s phrel"
term "x := ($x + 1)"
term "x\<^sup>> := ($x\<^sup>< + 1)"

text \<open> The change of precedence of := in utp_rel.thy from 76 to 61 (otherwise x := x+1 won't be 
parsed correctly). But this change, as discussed in @{url \<open>https://github.com/isabelle-utp/UTP/pull/1\<close>} 
may cause a problem for \relcomp (\Zcomp) because its precedence is 75 now. After this change, \Zcomp will 
be bound stronger than := .
\<close>
term "((x := 1)::'s rel) \<Zcomp> y := c"

text \<open>As Simon recommended, we could use another annotation with difference precedence for relcomp. \<close>

notation relcomp (infixr ";;" 55)
term "x := $x + 1" (* OK. := (61) and + (65) *)
term "x := $x + 1 ;; P" 
term "x := $x + 1 \<Zcomp> P" (* Not parsed because \<Zcomp> (75) *)
term "x := $x + 1 ;; y := $y - 1" 
term "p \<union> q \<Zcomp> P" (* (p \<union> (q \<Zcomp> P)) *) (* \<union> (65) *)
term "p \<union> q ;; P" (* (p \<union> q) ;; P*)
term "p \<inter> q ;; P \<union> Q" (* (p \<inter> q) ;; (P \<union> Q) *) (* \<inter> (70) *)
term "p  \<inter> q \<Zcomp> P \<union> Q" (* (p \<inter> (q ;; P)) \<union> Q *)

term "((x := 1)::'s rel) ;; y := c"
term "((x := 1)::'s rel) ;; (y + 1)"
term "\<lambda>q. x"
term "if b then c else q"
term "1/2"
term "a - {}"
term "f o g"

subsubsection \<open> Assignment \<close>
abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prel" where 
[prel_defs]: "passigns \<sigma> = prel_of_rfrel (passigns_f \<sigma>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s phrel"
term "(s := e)::'s rel"
(* assignment *)
(*
definition passign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's phrel" (*(infix ":=\<^sub>p" 162)*) where
[prel_defs]: "passign x e = prel_of_rfrel (\<lbrakk> \<lbrakk>(x := e)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

syntax 
  "_passign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix ":=\<^sub>p" 30) 

translations
  "_passign x e" == "CONST passign x (e)\<^sub>e"
  "_passign x e" <= "_passign x (e)\<^sub>e"
*)
term "(x := 1)::'s rel"
term "(x := C)::'s phrel"
(* Question: what priority should I give? 
If the priority of :=\<^sub>p is larger (tighter) than + (65), then the syntax below is incorrect.
Otherwise, it should be correct
*)
(* term "x :=\<^sub>p 1 + p" *)
(* TODO: Simon: contact Christine about suggestion precedence ... reference from ITree: *)
term "(x := $x + 1)::'s rel"
term "(x := ($x + 1))::'s rel"
(* \<^bold>v shouldn't be the LHS of an assignment *)
term "(\<^bold>v\<^sup>> := $\<^bold>v\<^sup><)::'s phrel"
term "($\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)"

term "((rfrel_of_prel P))"
term "(r * @(rfrel_of_prel P) + (1 - r) * @(rfrel_of_prel  Q))\<^sub>e"

subsubsection \<open> Probabilistic choice \<close>
abbreviation pchoice_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" 
("(_ \<oplus>\<^sub>f\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where 
"pchoice_f P r Q \<equiv> (r * P + (1 - r) * Q)\<^sub>e"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[prel_defs]: "pchoice P r Q = prel_of_rfrel (pchoice_f (rfrel_of_prel P) r (rfrel_of_prel Q))"

(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[prel_defs]: "pchoice' r P Q = prel_of_rfrel (r * @(rfrel_of_prel P) + (1 - r) * @(rfrel_of_prel Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

text \<open> The definition @{text "lift_pre"} below lifts a real-valued function @{text r} over the initial 
state to over the initial and final states. In the definition of @{term "pchoice"}, we use a general 
function for the weight @{text r}, which is @{text "'s \<times> 's \<Rightarrow> \<real>"}. However, now we only consider 
the probabilistic choice whose weight is only over the initial state. Then @{text "lift_pre"} is 
useful to lift a such function to a more general function used in @{term "pchoice"}.
\<close>
abbreviation lift_pre where "lift_pre r \<equiv> (\<lambda>(s, s'). r s)"
notation lift_pre ("_\<^sup>\<Up>")
expr_ctr lift_pre

subsubsection \<open> Conditional choice \<close>
(* conditional choice *)
abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

definition pcond :: "('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where 
[prel_defs]: "pcond b P Q \<equiv> prel_of_rfrel (pcond_f (rfrel_of_prel P) b (rfrel_of_prel Q))"

syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>c (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pcond b P Q" == "CONST pcond (b)\<^sub>e P Q"
  "_pcond b P Q" <= "_pcond (b)\<^sub>e P Q"

term "if\<^sub>c True then P else Q"

subsubsection \<open> Sequential composition \<close>
term "(rfrel_of_prel (P::('s phrel)))\<lbrakk>v\<^sub>0/\<^bold>v\<^sup>>\<rbrakk>"
term "\<^bold>v\<^sup>>"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. (P\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>) * (Q\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sub>e"
term "[ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (rfrel_of_prel (P::'s phrel))"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"
term "(\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
term "if True then a else b"
term " 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> v\<^sub>0 ] \<dagger> @(rfrel_of_prel P)) * ([ \<^bold>v\<^sup>< \<leadsto> v\<^sub>0 ] \<dagger> @(rfrel_of_prel Q)))\<^sub>e"
thm "pred_seq_hom"

abbreviation pseqcomp_f :: "'s rfhrel \<Rightarrow> 's rfhrel \<Rightarrow> 's rfhrel" (infixl ";\<^sub>f" 59) where 
"pseqcomp_f P Q \<equiv> (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e" 

definition pseqcomp :: "'s phrel \<Rightarrow> 's phrel \<Rightarrow> 's phrel" (*(infixl ";\<^sub>p" 59)*) where
[prel_defs]: "pseqcomp P Q = prel_of_rfrel (pseqcomp_f (rfrel_of_prel P) (rfrel_of_prel Q))"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp_f and 
  pseqcomp_c pseqcomp

term "(P::('s, 's) rfrel) ; Q"
term "(P::'s phrel) ; Q"

subsubsection \<open> Parallel composition \<close>

abbreviation pparallel_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" (infixl "\<parallel>\<^sub>f" 58)
  where "pparallel_f P Q \<equiv> (\<^bold>N (P * Q)\<^sub>e)"

abbreviation pparallel_f' :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel"
  where "pparallel_f' P Q \<equiv> ((P * Q) / (\<Sum>\<^sub>\<infinity> s'. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> Q)))\<^sub>e"

lemma pparallel_f_eq: "pparallel_f P Q = pparallel_f' P Q"
  apply (simp add: dist_defs)
  by (expr_auto)

text \<open> We provide four variants (different combinations of types for their parameters) of parallel 
composition for convenience and they use a same notation @{text "\<parallel>"}. All of them defines 
probabilistic programs of type @{typ "('a\<^sub>1, 'a\<^sub>2) prel"}.
\<close>
definition pparallel :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" (infixl "\<parallel>\<^sub>p" 58) where
[prel_defs]: "pparallel P Q = prel_of_rfrel (pparallel_f P Q)"

definition pparallel_pp :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where
[prel_defs]: "pparallel_pp P Q = pparallel (rfrel_of_prel P) (rfrel_of_prel Q)"

definition pparallel_fp :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where
[prel_defs]: "pparallel_fp P Q = pparallel P (rfrel_of_prel Q)"

definition pparallel_pf :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where
[prel_defs]: "pparallel_pf P Q = pparallel (rfrel_of_prel P) Q"

no_notation Sublist.parallel (infixl "\<parallel>" 50)
consts
  parallel_c :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<parallel>" 58)

adhoc_overloading
  parallel_c pparallel and 
  parallel_c pparallel_pp and
  parallel_c pparallel_fp and
  parallel_c pparallel_pf and
  parallel_c Sublist.parallel

term "((P::('s, 's) rfrel) \<parallel> (Q::('s, 's) rfrel))"
term "((P::('s, 's) rfrel) \<parallel> (Q::('s, 's) prel))"
term "((P::('s, 's) prel) \<parallel> (Q::('s, 's) rfrel))"
term "((P::('s, 's) prel) \<parallel> (Q::('s, 's) prel))"
term "((P::'s list) \<parallel> Q)"
term "([] \<parallel> [a])"

subsubsection \<open> Recursion \<close>
text \<open> How to define a recursion or loop construct? 
One way is to use a similar weakest or strongest solution in UTP, which is based on complete lattice.
For this purpose, we need to define an order relation for distributions.

Another way is to use a simpler form as described in the Hehner's paper. For this purpose, we need to 
introduce a time variable of type (extended natural numbers or reals) where infinity accounts for 
non-termination. 
Without this variable, we are not able to define a recursive function in Isabelle because we are not 
able to prove its termination.
\<close>
(*
function pwhile :: "('s, 's) rpred \<Rightarrow> 's phrel \<Rightarrow> 's phrel" ("while\<^sub>p _ do _ od") where
[prel_defs]: "pwhile b P = (if\<^sub>c b then (P ; (while\<^sub>p b do P od)) else II) "
  by auto

term "while\<^sub>p ($x=$y)\<^sub>e do II od"
*)
alphabet time = 
  t :: nat

definition while_body:: "'a time_scheme  phrel \<Rightarrow> ('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>)
     \<Rightarrow> 'a time_scheme  phrel \<Rightarrow> 'a time_scheme  phrel" where
"while_body P b X = (if\<^sub>c b then (P ; (t := $t + 1) ; X) else II)"

function pwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) 
  \<Rightarrow> ('a time_scheme, 'a time_scheme) prel \<Rightarrow> ('a time_scheme, 'a time_scheme) prel" 
("while\<^sub>p _ do _ od") where
[prel_defs]: "pwhile b P = while_body P b (pwhile b P)"
  by auto

text \<open> Without the proof of termination, this function @{term "pwhile"} is just partial. In order to 
prove its termination, we need to prove  @{text "\<forall>a, b. pwhile_dom (a, b)"}. See Section~8 of the 
manual ``Defining Recursive Functions in Isabelle/HOL'' for more details about partial functions.
\<close>
(*
termination pwhile
  apply (auto)
  oops
*)
find_theorems name: "pwhile"
thm "pwhile.cases"
(* (\<And>b P.
      (?x::(?'a time_scheme \<times> ?'a time_scheme \<Rightarrow> \<bool>) \<times> (?'a time_scheme, ?'a time_scheme) prel) = (b, P) 
      \<Longrightarrow> ?P::\<bool>
   )  \<Longrightarrow> ?P 
*)
thm "pwhile.psimps"
(*
pwhile_dom (?b, ?P) \<Longrightarrow>
while\<^sub>p ?b do ?P od = 
  pcond [?b]\<^sub>e (?P ; \<langle>subst_upd [\<leadsto>] t [\<lambda>\<s>::?'a time_scheme. get\<^bsub>t\<^esub> \<s> + (1::enat)]\<^sub>e\<rangle>\<^sub>a ; while\<^sub>p ?b do ?P od) II
*)
thm "pwhile.pinduct"
(*
pwhile_dom (?a0.0, ?a1.0) \<Longrightarrow>
(\<And>b P.
    pwhile_dom (b, P) \<Longrightarrow> 
    (?P::(?'a time_scheme \<times> ?'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> (?'a time_scheme, ?'a time_scheme) prel \<Rightarrow> \<bool>) b P 
    \<Longrightarrow> ?P b P
) \<Longrightarrow>
?P ?a0.0 ?a1.0
*)

definition repeat_body:: "'a time_scheme  phrel \<Rightarrow> ('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>)
     \<Rightarrow> 'a time_scheme  phrel \<Rightarrow> 'a time_scheme  phrel" where
[prel_defs]: "repeat_body P b X = P ; (t := $t + 1) ; (if\<^sub>c b then II else X)"

function (*(domintros)*) prepeat :: "('a time_scheme, 'a time_scheme) prel 
  \<Rightarrow> ('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> ('a time_scheme, 'a time_scheme) prel"
("repeat _ until _") where
[prel_defs]: "prepeat P b = repeat_body P b (prepeat P b)"
  by auto

term "prepeat_dom"
find_theorems name: "prepeat"
(* thm "prepeat.domintros" *)
(*
termination prepeat
  apply (auto)
*)

text \<open> Can we also treat recursion as a limit of sequence of approximation. See Hehner's 
``Specifications, Programs, and Total Correctness'' for more information.
\<close>
fun while' where
"while' 0 b P = II" |
"while' (Suc n) b P = (if\<^sub>c b then (P ; while' n b P) else II)"

fun prepeat' where 
"prepeat' 0 P b = P ; (if\<^sub>c b then II else II)" |
"prepeat' (Suc n) P b = P ; (if\<^sub>c b then II else (prepeat' (n) P b))"

(*
term "pwhile_dom"
termination pwhile
  apply auto
*)

(*
bundle UTP_Prob_Rel_Syntax
begin

(* no_notation uskip ("II") *)
(* notation pskip ("II") *)
(* how to no_notation a notation that is given in the syntax translation, like below.

no_notation _assign (infix ":=" 76)
*)
(* no_notation (infixl "\<parallel>" 166) *)
(* no_notation If ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10) *)


(* notation passign (infix ":=" 162) *)
notation pseqcomp (infixl ";" 59)
(* notation pchoice ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) *)
(* notation pparallel (infixl "\<parallel>" 166) *)

end

unbundle UTP_Prob_Rel_Syntax
*)
(*
syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if (_)/ then (_)/ else (_))" [0, 0, 167] 167)

translations
  "_pcond P b Q" == "CONST pcond P b Q"
*) 
(*
consts pchoice_cond :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167)

adhoc_overloading
  pchoice_cond pcond
  pchoice_cond pchoice'


term "if True then P else Q"
term "if\<^sub>p R then P else Q"
*)

end
