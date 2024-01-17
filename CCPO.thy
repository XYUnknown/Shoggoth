(*  Title:         CCPO.thy
    Authors:       Xueying Qin, U Edinburgh; Liam O'Connor, U Edinburgh; Peter Hoefner, ANU
    Contributions: Ohad Kammar, U Edinburgh; Rob van Glabbeek, U Edinburgh; Michel Steuwer, U Edinburgh
    Maintainer:    Xueying Qin <xueying.qin@ed.ac.uk>
*)

section \<open>Chain Complete Partial Order\<close>

text \<open>The Chain-Complete Partial Order for defining the denotational semantics of extended System S\<close>

theory CCPO
  imports Main "HOL.Complete_Partial_Order" "HOL-Library.Product_Order"
begin

datatype label = PLUS | MULT | Nat nat | APP | ABS | Var nat | EMPTY
datatype exp = Leaf label | Node label exp exp 
print_theorems
datatype exp_err_div = Err | E exp  | Div 

(* intros for datatype )*)
lemma EI:
  "(case x of E p \<Rightarrow> p \<in> P | _ \<Rightarrow> False) \<Longrightarrow> (x \<in> E ` P)"
  by (fastforce split: exp_err_div.splits)

lemma ErrI:
  "(case x of Err \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (x = Err)"
  by (fastforce split: exp_err_div.splits)

lemma DivI:
  "(case x of Div \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (x = Div)"
  by (fastforce split: exp_err_div.splits)

lemmas exp_err_div_intros = EI ErrI DivI


typedef powerdomain = "{x | x :: exp_err_div set .  x \<noteq> {}}"
  by auto

lemma chain_fst_exist : 
  "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow> Complete_Partial_Order.chain (\<le>) (fst ` A)"
  using chain_imageI fst_mono by blast

lemma chain_snd_exist : 
  "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow> Complete_Partial_Order.chain (\<le>) (snd ` A)"
  using chain_imageI snd_mono by blast

instance prod :: (ccpo, ccpo) ccpo
  apply intro_classes
   apply (simp add: ccpo_Sup_upper chain_fst_exist chain_snd_exist fst_Sup snd_Sup less_eq_prod_def)
  apply (simp add: less_eq_prod_def fst_Sup snd_Sup)
  by (metis ccpo_Sup_least imageE chain_fst_exist chain_snd_exist)

instantiation exp_err_div :: ord
begin
definition exp_err_div_less_eq : "a \<le> b \<longleftrightarrow> a = Div \<or> a = b"
definition exp_err_div_less : "a < b \<longleftrightarrow> a = Div"
instance ..
end

abbreviation fix_syn :: "(('a::ccpo) \<Rightarrow> 'a) \<Rightarrow> 'a"  (binder "\<mu> " 10)
  where "fix_syn (\<lambda>x. f x) \<equiv> Complete_Partial_Order.fixp (\<lambda> x. f x)"

text \<open>The porcupine ordering presented in paper\<close>
(* The porcupine ordering on a flat domain *)
definition porcupine_less_eq_paper :: "powerdomain \<Rightarrow> powerdomain \<Rightarrow> bool" where
 "porcupine_less_eq_paper a b \<longleftrightarrow> a = b 
                       \<or> (Div \<in> Rep_powerdomain a \<and> Rep_powerdomain a - {Div} \<subseteq> Rep_powerdomain b)"

(* The porcupine ordering on a flat domain, isabelle friendly version*)
definition porcupine_less_eq :: "powerdomain \<Rightarrow> powerdomain \<Rightarrow> bool" where
  "porcupine_less_eq a b \<longleftrightarrow> (Rep_powerdomain a - {Div} \<subseteq> Rep_powerdomain b - {Div})
                       \<and> (Div \<notin> Rep_powerdomain a \<longrightarrow> a = b)"

theorem porcupine_eq: 
  "porcupine_less_eq_paper a b = porcupine_less_eq a b"
  unfolding porcupine_less_eq_paper_def porcupine_less_eq_def 
  by fastforce

subsection \<open>The powerdomain for defining our denotational semantics\<close>

instantiation powerdomain :: ord
begin
text \<open>This is the Egli-Milner ordering  \cite{plotkin:powerdomain}\<close>
definition pd_less_eq : 
  "a \<le> b \<longleftrightarrow> (\<forall> x \<in> (Rep_powerdomain a) . \<exists> y \<in> (Rep_powerdomain b) . x \<le> y) 
                     \<and> (\<forall> y \<in> (Rep_powerdomain b) . \<exists> x \<in> (Rep_powerdomain a) . x \<le> y)" 
                          (* Egli-Milner ordering *)
definition pd_less : "(a:: powerdomain) < b \<longleftrightarrow> a \<le> b \<and> a \<noteq> b "
instance ..
end

lemma porcupine_eglimilner : 
  "a \<le> b \<longleftrightarrow> porcupine_less_eq a b "
  apply (simp add: porcupine_less_eq_def pd_less_eq)
  apply (rule iffI)
   using Rep_powerdomain_inject exp_err_div_less_eq apply fastforce
   using Rep_powerdomain exp_err_div_less_eq  by auto[1]

declare porcupine_less_eq_def[simp]

lemma pd_ord_anti_sym : "(a :: powerdomain) \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b "
  by (fastforce intro: Rep_powerdomain_inject[THEN iffD1] simp: pd_less_eq exp_err_div_less_eq)

instantiation powerdomain :: preorder
begin
instance
  apply(intro_classes)
    by (fastforce simp: pd_less pd_less_eq exp_err_div_less_eq pd_ord_anti_sym)+
end

instantiation powerdomain :: order
begin
instance
  apply intro_classes
  by (rule pd_ord_anti_sym)
end

(* They are used in defining the sup *)
definition upclose :: "exp_err_div set \<Rightarrow> exp_err_div set" where
  "upclose P = {x. \<exists>y \<in> P. y \<le> x}" 

definition downclose :: "exp_err_div set \<Rightarrow> exp_err_div set" where
  "downclose P = {x. \<exists>y \<in> P. x \<le> y}" 

instantiation powerdomain :: Sup
begin
text \<open>
Basically, if any element of the chain has no Div, the upper bound is that element.
Otherwise, if all elements of the chain have Div, the upper bound is the union of all elements.

The definitions from the literature define the same in terms of unions and intersections,
so we define it that way here. But below the definition I prove some theorems that 
confirm the above intuition. \<close>
definition pd_Sup : "Sup (a :: powerdomain set) = 
  (if a = {} then Abs_powerdomain {Div} 
             else (Abs_powerdomain ((\<Union> (downclose ` Rep_powerdomain ` a)) 
                                    \<inter> (\<Inter> (upclose ` Rep_powerdomain ` a)))))"
instance ..
end

lemma upclose_no_div[simp]: "Div \<notin> x \<Longrightarrow> upclose x = x"
  by (fastforce simp: upclose_def exp_err_div_less_eq)

lemma upclose_div[simp]: "Div \<in> x \<Longrightarrow> upclose x = UNIV"
  by (fastforce simp: upclose_def exp_err_div_less_eq)

lemma upclose_eq: "upclose x = (if Div \<in> x then UNIV else x)" 
  by simp

lemma downclose[simp]: "x \<noteq> {} \<Longrightarrow> downclose x = insert Div x"
  by (fastforce simp: downclose_def exp_err_div_less_eq)

lemma no_div_means_eq:
  assumes "Div \<notin> Rep_powerdomain pd1"
    and "pd1 \<le> pd2"
  shows "pd1 = pd2"
  using assms 
   by(fastforce simp: porcupine_eglimilner)

lemma no_div_collapses:
  assumes "Complete_Partial_Order.chain (\<le>) (A :: powerdomain set)" 
  and "pd1 \<in> A"
  and "pd2 \<in> A"
  and "Div \<notin> Rep_powerdomain pd1"
shows "pd2 \<le> pd1"
  using assms 
  by(fastforce dest: no_div_means_eq
               simp: chain_def) 

text \<open>If any element of the chain has no Div, that is the upper bound 
       @{text "no_div_Sup_ub"}: 
       If there is a point in the Chain with no Div, it is the upper bound:
       @{term "p \<in> A \<Longrightarrow> Div \<notin> Rep_powerdomain p \<Longrightarrow> Sup A = p"} \<close>
theorem no_div_Sup_ub : 
  assumes "Complete_Partial_Order.chain (\<le>) A"
  and     "p \<in> A"
  and     "Div \<notin> Rep_powerdomain p"
shows   "Sup A = p"
proof - 
  have "(\<Inter>a\<in>A. upclose (Rep_powerdomain a)) = Rep_powerdomain p"
  proof
    show "(\<Inter>a\<in>A. upclose (Rep_powerdomain a)) \<subseteq> Rep_powerdomain p"
      by (fastforce simp: assms upclose_eq)
    show "Rep_powerdomain p \<subseteq> (\<Inter>a\<in>A. upclose (Rep_powerdomain a))"
      using assms apply clarsimp
      by (metis UNIV_I no_div_collapses no_div_means_eq upclose_eq)
  qed
  thus ?thesis
    using assms apply (clarsimp simp: pd_Sup)
  by (metis (no_types, lifting) Rep_powerdomain_inverse Sup_upper downclose empty_iff empty_subsetI 
                                image_iff inf.order_iff inf_commute insert_subset)
qed

declare Abs_powerdomain_inverse[simp]

text \<open> @{text "div_Sup_ub"}:
  If Div is in all points on the chain, then the upper bound is the union:
  @{term "(\<forall>p \<in> A. Div \<in> Rep_powerdomain p) \<Longrightarrow> Sup A = Abs_powerdomain (\<Union> (Rep_powerdomain ` A))"}\<close>
theorem div_Sup_ub : 
  assumes "A \<noteq> {}" 
  shows "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow>
          (\<forall>p \<in> A. Div \<in> Rep_powerdomain p) \<Longrightarrow> Sup A = Abs_powerdomain (\<Union> (Rep_powerdomain ` A))"
  using assms Rep_powerdomain 
  by (simp add: pd_Sup porcupine_eglimilner pd_ord_anti_sym)

text \<open> Div is the bottom element \<close>
theorem bottom_element: "Abs_powerdomain {Div} \<le> x"
  by (simp add: porcupine_eglimilner)

theorem bottom_element': "(\<forall> y. x \<le> y) \<Longrightarrow> Abs_powerdomain {Div} = x"
  using bottom_element pd_ord_anti_sym by blast

text \<open> @{text "Sup_empty"}: 
       If the chain A contains no elements at all, the LUB is just the bottom element {Div}
       @{term "Sup {} = Abs_powerdomain {Div}"}\<close>
theorem Sup_empty: "Sup {} = Abs_powerdomain {Div}"
  by (simp add: pd_Sup)

lemma powerdomain_supA:
  assumes "Complete_Partial_Order.chain (\<le>) (A:: powerdomain set)"
  and "x1 \<in> A"
shows "x1 \<le> Sup A"
 apply(cases "\<exists>x\<in>A. Div \<notin> Rep_powerdomain x")
  using assms apply (fastforce simp: no_div_Sup_ub no_div_collapses)
  using assms  apply (auto simp add: porcupine_eglimilner)[1]
 by (metis (mono_tags, lifting) Abs_powerdomain_inverse UN_I div_Sup_ub empty_not_insert
                                mem_Collect_eq mk_disjoint_insert)

lemma powerdomain_supA':
  assumes "Complete_Partial_Order.chain (\<le>) (A:: powerdomain set)"
  and "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
shows "Sup A \<le> z"
proof - 
  have "(\<exists>x\<in>A. Div \<notin> Rep_powerdomain x) \<or> (A={}) \<or> (A\<noteq>{} \<and> \<not>(\<exists>x\<in>A. Div \<notin> Rep_powerdomain x))"
    by blast
  moreover 
  { assume "\<exists>x\<in>A. Div \<notin> Rep_powerdomain x"
    hence ?thesis
      using assms no_div_Sup_ub by blast
  } 
  moreover
  { assume "A={}"
    hence ?thesis
      by (simp add: CCPO.Sup_empty bottom_element)
  }
  moreover 
  { assume "A\<noteq>{} \<and> \<not>(\<exists>x\<in>A. Div \<notin> Rep_powerdomain x)"
    hence ?thesis
      using assms apply (subst div_Sup_ub; clarsimp)
      using  Rep_powerdomain porcupine_eglimilner apply (clarsimp)
      by fastforce
  }
  ultimately show ?thesis
    by blast
qed

instantiation powerdomain :: ccpo
begin
instance
  apply(intro_classes)   
  using powerdomain_supA powerdomain_supA' by blast+
end

text \<open> point-wise lifting to the domain D \<close>
type_synonym D = "exp \<Rightarrow> powerdomain"

instance "fun" :: (type, ccpo) ccpo
  apply intro_classes
  unfolding le_fun_def
  by (fastforce intro!: ccpo_Sup_least simp: chain_imageI  ccpo_Sup_upper)+
  
abbreviation "PdToSet == Rep_powerdomain"
abbreviation "SetToPd == Abs_powerdomain"

end
