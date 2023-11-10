section \<open>The Monotonicity Proofs for the Denotational Semantics\<close>

theory MonoDenotational
  imports CCPO Denotational
begin

subsection \<open>Preliminary Lemmas\<close>

text \<open> 
   This section consists of ported proofs from HOLCF cite\<open>"holcf"\<close> that allow us to define a parallel 
   fixp induction principle over two mus at once.

   HOLCF does this by transforming induction over two mus into induction over one mu for a product
   type.

   To do the same here, we must prove some theorems about `iterates`, from Complete_Partial_Order. 

   `iterates f` is the set of all repeated iterations of a function f. Starting from a bottom 
   element, we can imagine it as the results of applying `f` any number of times, including 
   infinitely. 

   The least fixed point of f is the least upper bound of `iterates f`.


   We have four tedious lemmas that allow us to prove some theorems about `iterates`
   for a function on products and relating it to `iterates` for each side of the product.

   These first two lemmas show each direction of the equivalence iterates_fst:
   (iterates f) = fst ` (iterates (\<lambda>(x,y). (f x, g y)))
\<close>

lemma iterates_fst1: "x \<in> ccpo_class.iterates (\<lambda>(x, y). (f x, g y)) \<Longrightarrow> fst x \<in> ccpo_class.iterates f"
  apply (induct rule: ccpo_class.iterates.induct)
  by (auto simp add: chain_fst_exist prod_Sup iterates.step iterates.Sup)

(* Now the other direction of the equivalence, which is extremely hard.. *)
lemma iterates_fst2: 
  assumes mono: "mono (\<lambda>(x,y). (f x, g y))"
  shows "x \<in> ccpo_class.iterates f \<Longrightarrow> x \<in> fst ` ccpo_class.iterates (\<lambda>(x, y). (f x, g y))"
  apply (induct rule: iterates.induct)
    (* Case: If x is in iterates f from just one iteration step, we make the same step on the product side *)
   apply clarsimp
   apply (metis (mono_tags, lifting) case_prod_conv fst_conv image_iff iterates.step)
    (* Case: If x is the Sup of some chain Msubset of `iterates f`, we must construct a new chain 
     of products, whose left side is M. First, we postulate its existence, and prove it later. *)
  apply (rename_tac M)
  apply (subgoal_tac "\<exists>M'. M' \<subseteq> ccpo_class.iterates  (\<lambda>(x, y). (f x, g y)) 
                         \<and> Complete_Partial_Order.chain (\<le>) M' \<and> fst ` M' = M")
   apply (clarsimp)
   apply (frule iterates.Sup [where f = "(\<lambda>(x, y). (f x, g y))"], force)
   apply (force simp: prod_Sup)
    (* Now we prove that the chain exists *)
    (* We use Isabelle's SOME operator to non-constructively pick the element of the right side of the product
     that matches the left side one from the chain M *)
  apply (rule_tac x = "{ (x, SOME y. (x, y) \<in> ccpo_class.iterates (\<lambda>(x, y). (f x, g y))) | x. x \<in> M } " in exI)
  apply (intro conjI)
    apply clarsimp
    apply (rule someI_ex, fastforce)
   apply (rule chain_subset[OF chain_iterates[OF mono]])
   apply (clarsimp)
   apply (rule someI_ex, fastforce)
  apply force+
  done

text \<open> The next two lemmas show each direction of the equivalence iterates_snd, much the same way:
       (iterates g) = snd ` (iterates (\<lambda>(x,y). (f x, g y))) \<close>
lemma iterates_snd1: "x \<in> ccpo_class.iterates (\<lambda>(x, y). (f x, g y)) \<Longrightarrow> snd x \<in> ccpo_class.iterates g"
  apply (induct rule: ccpo_class.iterates.induct)
  by (auto simp add: chain_snd_exist prod_Sup iterates.step iterates.Sup)

text \<open> And the other direction, which is structurally the same as for iterates_fst2. \<close>
lemma iterates_snd2:
  assumes mono: "mono (\<lambda>(x,y). (f x, g y))"
  shows "x \<in> ccpo_class.iterates g \<Longrightarrow> x \<in> snd ` ccpo_class.iterates (\<lambda>(x, y). (f x, g y))"
  apply (induct rule: iterates.induct)
   apply clarsimp
   apply (metis (mono_tags, lifting) case_prod_conv snd_conv image_iff iterates.step)
  apply (rename_tac M)
  apply (subgoal_tac "\<exists>M'. M' \<subseteq> ccpo_class.iterates  (\<lambda>(x, y). (f x, g y)) 
                         \<and> Complete_Partial_Order.chain (\<le>) M' \<and> snd ` M' = M")
   apply (clarsimp)
   apply (frule iterates.Sup [where f = "(\<lambda>(x, y). (f x, g y))"], force)
   apply (force simp: prod_Sup)
  apply (rename_tac M)
  apply (rule_tac x = "{ ((SOME x. (x, y) \<in> ccpo_class.iterates (\<lambda>(x, y). (f x, g y)), y)) | y. y \<in> M } " in exI)
  apply (intro conjI)
    apply clarsimp
    apply (rule someI_ex, fastforce)
   apply (rule chain_subset[OF chain_iterates[OF mono]])
   apply (clarsimp)
   apply (rule someI_ex, fastforce)
  apply force+
  done

(* and here are the two equivalences described above *)
lemma iterates_fst:
  assumes mono: "mono (\<lambda>(x,y). (f x, g y))"
  shows "(ccpo_class.iterates f) = fst ` (ccpo_class.iterates (\<lambda>(x,y). (f x, g y)))" 
  apply rule
  using iterates_fst2 mono apply auto[1]
  by (simp add: image_subset_iff iterates_fst1)

lemma iterates_snd:
  assumes mono: "mono (\<lambda>(x,y). (f x, g y))"
  shows "(ccpo_class.iterates g) = snd ` (ccpo_class.iterates (\<lambda>(x,y). (f x, g y)))" 
  apply rule
  using iterates_snd2 mono apply auto[1]
  by (simp add: image_subset_iff iterates_snd1)

subsection \<open>Parallel fixed point induction principle\<close>

(* This is just a specialisation of the definition of admissible
   specifically for use with binary predicates. *)
lemma admissibleD2:
  assumes "ccpo.admissible Sup (\<le>) (\<lambda>x. P (fst x) (snd x))"
  assumes "Complete_Partial_Order.chain (\<le>) (A :: (('a :: ccpo) \<times> ('b :: ccpo)) set)"
  assumes "A \<noteq> {}"
  assumes "\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y"
  shows "P (Sup (fst ` A)) (Sup (snd ` A))"
  using assms 
  apply (simp add: ccpo.admissible_def)
  by (simp add: prod_Sup)

text 
 \<open> First, we define parallel fixpoint induction using a unary predicate that takes in 
   a product type. This is more convenient to prove but not easy to use because the 
   product types interfere with Isabelle's unifier sometimes.

   The parallel_fix_ind theorem below, which is derived from this, should be used instead.

   Most of this proof code was copied from the fixp_induct proof in Complete_Partial_Order,
   with modifications inspired by HOLCF. \<close>
lemma parallel_fixp_induct_prod:
  assumes adm: "ccpo.admissible Sup (\<le>) (\<lambda>x. P x)"
  assumes base: "P (Sup {}, Sup {})"
  assumes mono: "monotone (\<le>) (\<le>) (\<lambda>(x,y). (f x, g y))"
  assumes step: "\<And> x y. P (x, y) \<Longrightarrow> P (f x, g y) "
  shows "P ((\<mu> X. f X),( \<mu> X. g X))"
  unfolding fixp_def
  using adm chain_iterates[OF mono]
  apply (subst iterates_fst[where f=f and g = g, OF mono])
  apply (subst iterates_snd[where f = f and g = g, OF mono])
proof (rule admissibleD2)
  show "Complete_Partial_Order.iterates (\<lambda>(x, y). (f x, g y)) \<noteq> {}"
    using bot_in_iterates by auto
next
  fix x
  assume "x \<in> Complete_Partial_Order.iterates (\<lambda>(x, y). (f x, g y))"
  then show "P x"
  proof (induct rule: iterates.induct)
    case prems: (step xy)
    from this(2) show ?case
      by (metis case_prod_conv local.step old.prod.exhaust)
  next
    case (Sup M)
    then show ?case
      apply (case_tac "M = {}")
       apply (simp add: prod_Sup base)
      by (auto intro: step base ccpo.admissibleD adm)
  qed
qed (auto)

(* Fixed point induction for two mus *)
theorem parallel_fixp_induct:
  assumes adm: "ccpo.admissible Sup (\<le>) (\<lambda>x. P (fst x) (snd x))"
  assumes base: "P (Sup {}) (Sup {})"
  assumes mono1: "mono f"
  assumes mono2: "mono g"
  assumes step: "\<And> x y. P x y \<Longrightarrow> P (f x) (g y) "
  shows "P (\<mu> X. f X) ( \<mu> X. g X)"
  apply (rule parallel_fixp_induct_prod[where P = "\<lambda>p. P (fst p) (snd p)", simplified])
     apply (simp add: assms)+
  using assms apply (simp add: mono_def)
   apply (simp add: prod_less_eq, force intro: assms)
  done

subsection \<open>A missing theorem about parallel chains\<close>

text 
 \<open> This theorem, Sup_mono, is proven in HOLCF (as lub_mono) but not Complete_Partial_Order.

   It says that if one chain A is always less than another chain B, the Sup of A will also be 
   less than the Sup of B.

   By "always less than", we mean that the chains are arranged in parallel ordering. In countable 
   chains like HOLCF, this means \<forall>i. A i \<le> B i, for all indices i. But for our uncountable chains,
   we must use a chain of pairs, and the individual chains A and B are retrieved by using 
   fst and snd. \<close>

lemma below_Sup: "Complete_Partial_Order.chain (\<le>) (S :: ('a::ccpo) set) \<Longrightarrow>
                  x \<in> S \<Longrightarrow> i \<le> x \<Longrightarrow> i \<le> Sup S"
  using ccpo_Sup_upper dual_order.trans by blast

lemma Sup_below: "Complete_Partial_Order.chain (\<le>) (S :: ('a::ccpo) set) \<Longrightarrow> 
                  Sup S \<le> x \<longleftrightarrow> (\<forall>i \<in> S. i \<le> x)"
  apply (rule)
   apply clarsimp
  using ccpo_Sup_upper order_trans apply blast
  using ccpo_Sup_least by blast

theorem Sup_mono:
  " Complete_Partial_Order.chain (\<le>) (fst ` A) \<Longrightarrow>
         Complete_Partial_Order.chain (\<le>) (snd ` A) \<Longrightarrow>
         \<forall>x\<in>(A :: (('a :: ccpo) \<times> ('a :: ccpo)) set). fst x \<le> snd x \<Longrightarrow> Sup (fst ` A) \<le> Sup (snd ` A)"
  apply (subst Sup_below, simp, clarsimp)
  apply (rule below_Sup, simp, force, force)
  done

subsection \<open>Basic Semantic Operations are Monotonic\<close>

theorem seq_s_mono [simp]:
assumes "a1 \<le> a2"
and     "b1 \<le> b2"
shows "(a1 ;;s b1) \<le> (a2 ;;s b2)"
  using assms apply (simp add: le_fun_def seq_s_def porcupine_eglimilner)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse,clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain equals0I exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse,clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  by metis

theorem choice_s_mono [simp]:
assumes "a1 \<le> a2"
and     "b1 \<le> b2"
shows "(a1 ><s b1) \<le> (a2 ><s b2)"
  using assms apply (simp add: le_fun_def choice_s_def porcupine_eglimilner)
  using assms apply (simp add: le_fun_def seq_s_def porcupine_eglimilner)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain all_not_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply clarsimp
  by blast

theorem lchoice_s_mono [simp]:
assumes "a1 \<le> a2"
and     "b1 \<le> b2"
shows "(a1 <+s b1) \<le> (a2 <+s b2)"
  using assms apply (simp add: le_fun_def lchoice_s_def  porcupine_eglimilner)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   using Rep_powerdomain mem_Collect_eq apply fastforce
  apply (subst Abs_powerdomain_inverse, clarsimp)
   using Rep_powerdomain apply fastforce
  apply (subst Abs_powerdomain_inverse, clarsimp)
   using Rep_powerdomain insert_iff apply fastforce
 using Rep_powerdomain by fastforce

theorem one_s_mono [simp]:
  assumes "a \<le> b"
  shows "one_s a \<le> one_s b"
  using assms apply (simp add: le_fun_def one_s_def porcupine_eglimilner)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse,clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply(elim disjE, clarsimp)
       apply force
      apply force
     apply force
    apply force
   apply force  
  apply clarsimp
  apply (rule powerdomain.Abs_powerdomain_inject[THEN iffD2], clarsimp)
    apply (rename_tac x)
    apply (case_tac "x", clarsimp)
    apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
   apply clarsimp
   apply (rename_tac x)
   apply (case_tac "x", clarsimp)
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (rule set_eqI)
  by fastforce

theorem some_s_mono [simp]:
  assumes "a \<le> b"
  shows "some_s a \<le> some_s b"  
  using assms apply (simp add: le_fun_def some_s_def porcupine_eglimilner)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse)
   apply (rename_tac x)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply clarsimp
 apply (rename_tac x)
  apply (rule powerdomain.Abs_powerdomain_inject[THEN iffD2])
    apply (case_tac "x", simp)
    apply clarsimp
    apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain ex_in_conv exp_err_div.exhaust mem_Collect_eq)
  apply (rule set_eqI, clarsimp)
  by fastforce

theorem all_s_mono [simp]:
  assumes "a \<le> b"
  shows "all_s a \<le> all_s b"
  using assms apply (simp add: le_fun_def all_s_def porcupine_eglimilner)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain equals0I exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain equals0I exp_err_div.exhaust mem_Collect_eq)
  apply (subst Abs_powerdomain_inverse, clarsimp)
   apply (rename_tac x)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain equals0I exp_err_div.exhaust mem_Collect_eq)
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (rename_tac x)
  apply (rule powerdomain.Abs_powerdomain_inject[THEN iffD2], clarsimp)
    apply (case_tac "x", simp)
    apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain equals0I exp_err_div.exhaust mem_Collect_eq)
   apply (case_tac "x", simp)
   apply clarsimp
   apply (metis (mono_tags, lifting) Rep_powerdomain equals0I exp_err_div.exhaust mem_Collect_eq)
  apply (rule set_eqI, clarsimp)
  by fastforce

subsection \<open>Mu is monotonic\<close>

text
 \<open> I proved monotonicity here for the fixed point of a function `f` that takes an environment as 
   input. When this is used for the proof of monotonicity of exec, the function `f` is `exec s`.

   Assuming the input environments are ordered (pointwise), then the result of the mu 
   applied to the function f are ordered similarly.

   The function f must itself be monotone with respect to the environment ordering.

   The proof of this uses the parallel induction principle we ported over from HOLCF. \<close>
(* NB this feels more specialised than necessary... *)
theorem mu_s_mono [simp]:
assumes input_ordered: "\<forall>x. env1 x \<le> env2 x"  
assumes f_mono: "(\<And>env1 env2. (\<forall>x. env1 x \<le> env2 x) \<Longrightarrow> f env1 \<le> f env2)"
shows "(\<mu> x. f (env1(x1 := x))) \<le> (\<mu> x. f (env2(x1 := x)))"
  apply (rule parallel_fixp_induct)
      apply (force simp: ccpo.admissible_def prod_Sup dest: chain_fst_exist chain_snd_exist intro: Sup_mono)
     apply simp
    apply (fastforce simp: mono_def intro: f_mono)[1]
  apply (fastforce simp: mono_def intro: f_mono)[1]
  using input_ordered by (auto intro: f_mono)

subsection \<open>Exec is monotonic\<close>

text
 \<open> The theorem that exec is monotonic in its input environment.
   By induction over the strategy. All the existing monotonicity theorems make this proof 
   go through easily.\<close>
theorem exec_mono [simp]:
  assumes "\<forall>x. env1 x \<le> env2 x"  
  shows "exec s env1 \<le> exec s env2"
  using assms apply (induct s arbitrary: env1 env2)
  by simp_all

(* fst snd are mono *)
theorem fun_fst_mono:
  assumes "p1 \<le> p2"
  shows "(fst p1) x \<subseteq> (fst p2) x "
  using assms
  by (simp add: le_fun_def prod_less_eq)

theorem fun_snd_mono:
  assumes "p1 \<le> p2"
  shows "(snd p1) x \<subseteq> (snd p2) x"
  using assms
  by (simp add: le_fun_def prod_less_eq)

theorem funs_mono:
  assumes "mono f1"
    and "f1 \<le> f2"
    and "p1 \<subseteq> p2"
  shows "f1 p1 \<subseteq> f2 p2"
  using assms
  by (meson dual_order.trans le_funD monoE)

end
