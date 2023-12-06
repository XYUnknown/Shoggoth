section \<open>Chain Complete Partial Order\<close>

text \<open>The Chain-Complete Partial Order for defining the denotational semantics of extended System S\<close>

theory CCPO
  imports Main "HOL.Complete_Partial_Order" "HOL-Library.Product_Order"
begin

datatype label = PLUS | MULT | Nat nat | APP | ABS | Var nat | EMPTY
datatype exp = Leaf label | Node label exp exp 
print_theorems
datatype exp_err_div = Err | E exp  | Div 

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

theorem porcupine_eq: "porcupine_less_eq_paper a b = porcupine_less_eq a b"
  using porcupine_less_eq_paper_def porcupine_less_eq_def by auto

subsection \<open>The powerdomain for defining our denotational semantics\<close>

instantiation powerdomain :: ord
begin
text \<open>This is the Egli-Milner ordering  \cite{plotkin:powerdomain}\<close>
definition pd_less_eq : "a \<le> b \<longleftrightarrow> (\<forall> x \<in> (Rep_powerdomain a) . \<exists> y \<in> (Rep_powerdomain b) . x \<le> y) 
                        \<and> (\<forall> y \<in> (Rep_powerdomain b) . \<exists> x \<in> (Rep_powerdomain a) . x \<le> y)" 
                          (* Egli-Milner ordering *)
definition pd_less : "(a:: powerdomain) < b \<longleftrightarrow> a \<le> b \<and> a \<noteq> b "
instance ..
end

lemma porcupine_eglimilner : "a \<le> b \<longleftrightarrow> porcupine_less_eq a b "
  apply (rule iffI)
   apply (simp_all add: porcupine_less_eq_def pd_less_eq)
  using Rep_powerdomain_inject exp_err_div_less_eq apply fastforce
  using Rep_powerdomain exp_err_div_less_eq by auto[1]

declare porcupine_less_eq_def[simp]

lemma pd_ord_anti_sym : "(a :: powerdomain) \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b "
  apply (simp add: pd_less_eq exp_err_div_less_eq)
  apply (rule Rep_powerdomain_inject[THEN iffD1])
  by fastforce

instantiation powerdomain :: preorder
begin
instance
  apply intro_classes
  using pd_less pd_ord_anti_sym apply fastforce
  using exp_err_div_less_eq pd_less_eq by fastforce+
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
  apply (rule Rep_powerdomain_inject[THEN iffD1])
  using assms by (simp add: porcupine_eglimilner)

lemma no_div_collapses:
  assumes "Complete_Partial_Order.chain (\<le>) (A :: powerdomain set)" 
  and "pd1 \<in> A"
  and "pd2 \<in> A"
  and "Div \<notin> Rep_powerdomain pd1"
shows "pd2 \<le> pd1"
  by (metis assms chain_def no_div_means_eq)

theorem helper : "\<exists>x. x \<in> P \<Longrightarrow> P \<noteq> {} "
  by force

text \<open>If any element of the chain has no Div, that is the upper bound 
       @{text "no_div_Sup_ub"}: 
       If there is a point in the Chain with no Div, it is the upper bound:
       @{term "p \<in> A \<Longrightarrow> Div \<notin> Rep_powerdomain p \<Longrightarrow> Sup A = p"} \<close>
theorem no_div_Sup_ub : "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow>
           p \<in> A \<Longrightarrow> Div \<notin> Rep_powerdomain p \<Longrightarrow> Sup A = p"
  apply (clarsimp simp: pd_Sup)
  apply (rule conjI, clarsimp)
  apply (rule impI)
  apply (rule Rep_powerdomain_inject[THEN iffD1])
  apply (subgoal_tac "(\<Inter>a\<in>A. upclose (Rep_powerdomain a)) = Rep_powerdomain p")
   apply (subst Abs_powerdomain_inverse)  
  using Rep_powerdomain apply fastforce
  using Rep_powerdomain apply fastforce
  apply (subst upclose_eq)
  apply(rule equalityI)
   apply force
  apply clarsimp
  apply (erule disjE)
   apply blast
  by (metis (no_types, lifting) Int_Collect image_iff no_div_collapses no_div_means_eq)

declare Abs_powerdomain_inverse[simp]

text \<open> @{text "div_Sup_ub"}:
  If Div is in all points on the chain, then the upper bound is the union:
  @{term "(\<forall>p \<in> A. Div \<in> Rep_powerdomain p) \<Longrightarrow> Sup A = Abs_powerdomain (\<Union> (Rep_powerdomain ` A))"}\<close>
theorem div_Sup_ub : 
  assumes "A \<noteq> {}" 
  shows "Complete_Partial_Order.chain (\<le>) A \<Longrightarrow>
          (\<forall>p \<in> A. Div \<in> Rep_powerdomain p) \<Longrightarrow> Sup A = Abs_powerdomain (\<Union> (Rep_powerdomain ` A))"
  using Rep_powerdomain assms 
  apply (simp add: pd_Sup)
  by (rule pd_ord_anti_sym; simp add: porcupine_eglimilner)

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
  assumes "Complete_Partial_Order.chain (\<le>) A"
  and "x1 \<in> A"
  and "\<exists>x\<in>A. Div \<notin> Rep_powerdomain x \<or> \<not>(\<exists>x\<in>A. Div \<notin> Rep_powerdomain x)"
shows "x1 \<le> Sup A"
 apply(cases "\<exists>x\<in>A. Div \<notin> Rep_powerdomain x")
  using assms  no_div_Sup_ub no_div_collapses apply blast
 using assms apply (auto simp: porcupine_eglimilner)[1]
  by (metis (mono_tags, lifting) Abs_powerdomain_inverse UN_I div_Sup_ub empty_not_insert 
                                 mem_Collect_eq mk_disjoint_insert)

lemma powerdomain_supA':
  assumes "Complete_Partial_Order.chain (\<le>) A"
  and "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  and "\<exists>x\<in>A. Div \<notin> Rep_powerdomain x \<or> \<not>(\<exists>x\<in>A. Div \<notin> Rep_powerdomain x)"
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
      using assms(3) by blast
  }
  moreover 
  { assume "A\<noteq>{} \<and> \<not>(\<exists>x\<in>A. Div \<notin> Rep_powerdomain x)"
    hence ?thesis
      using assms apply simp
      apply (subst div_Sup_ub)
         apply (simp_all  add : porcupine_eglimilner)
      apply (subst Abs_powerdomain_inverse)
       apply fastforce
      apply (subst Abs_powerdomain_inverse)
      using Rep_powerdomain apply (force)
      by blast
  }
  ultimately show ?thesis
    by blast
qed

instantiation powerdomain :: ccpo
begin
instance
  apply(intro_classes)   
  using powerdomain_supA apply blast
  using powerdomain_supA' 
  by (metis CCPO.Sup_empty bottom_element ex_in_conv)
end

text \<open> point-wise lifting to the domain D \<close>
type_synonym D = "exp \<Rightarrow> powerdomain"

instance "fun" :: (type, ccpo) ccpo
  apply intro_classes
   apply (simp_all add: le_fun_def)
   apply (metis (mono_tags, lifting) ccpo_Sup_upper chain_imageI image_iff le_funE)
  apply (clarsimp, rule ccpo_Sup_least)
   by (fastforce simp: chain_def le_fun_def)+

abbreviation "PdToSet == Rep_powerdomain"
abbreviation "SetToPd == Abs_powerdomain"

end
