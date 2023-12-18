section \<open>The Denotational Semantics and Big-Step Operational Semantics are Equivalent\<close>

theory SemanticsEquivalence
  imports Denotational Operational WpSoundness
begin

fun fv :: "strategy \<Rightarrow> var set" 
  where
    "fv SKIP = {}" 
  | "fv ABORT = {}"
  | "fv \<lparr>v\<rparr> = {v}"
  | "fv \<llangle>atomic\<rrangle> = {}"
  | "fv (Seq s1 s2) = fv s1 \<union> fv s2"
  | "fv (Left_Choice s1 s2) = fv s1 \<union> fv s2"
  | "fv (Choice s1 s2) = fv s1 \<union> fv s2"
  | "fv (One s) = fv s"
  | "fv (CSome s) = fv s"
  | "fv (All s) = fv s"
  | "fv (Mu v s) = fv s - {v}"

lemma env_irrelevant:
  assumes "\<forall> X \<in> fv s. \<xi>1 X = \<xi>2 X"
  shows "exec s \<xi>1 = exec s \<xi>2"
  using assms
proof (induct s arbitrary: \<xi>1 \<xi>2)
  case (Seq s1 s2)
  thus ?case
    apply clarsimp
    by (metis Un_iff)
next
  case (Left_Choice s1 s2)
  thus ?case
    apply clarsimp
    by (metis Un_iff)
next
  case (Choice s1 s2)
  thus ?case
    apply clarsimp
    by (metis Un_iff)
next
  case (Mu x1 s)
  thus ?case
  proof - 
    have "\<forall> x. exec s (\<xi>1(x1 := x)) =  exec s (\<xi>2(x1 := x))"
      by (simp add: Mu.hyps Mu.prems)
    thus ?thesis
      by simp
  qed
qed (fastforce+)


subsection \<open>Computational soundness one\<close>
lemma substitution: 
  assumes "fv s' = {}"
  shows "exec (s \<lbrace> X \<mapsto> s'\<rbrace>) \<xi> = exec s (\<xi>(X := (exec s' \<xi>)))"
  using assms
proof (induct s arbitrary: \<xi>)
  case (Mu x1 s)
  thus ?case
    apply simp
    apply (intro impI conjI)
     apply (subgoal_tac "\<forall> x. ((\<lambda>a. if a = X then exec s' \<xi> else \<xi> a)(X := x)) = (\<xi>(X := x))")
      apply simp
     apply auto[1]
    apply (subgoal_tac "\<forall> x. (\<lambda>a. if a = X then exec s' (\<xi>(x1 := x)) else (\<xi>(x1 := x)) a) = ((\<lambda>a. if a = X then exec s' \<xi> else \<xi> a)(x1 := x))")
     apply simp
    apply clarsimp
    apply (rule ext)
    apply clarsimp
    apply (rule env_irrelevant)
    by simp
qed ((fastforce|simp)+)

lemma subst_var_empty: "fv Y = {} \<Longrightarrow> fv (s\<lbrace>X\<mapsto>Y\<rbrace>) = fv s - {X}"
  apply (induct s arbitrary: X Y)
            by (simp|fastforce)+

text \<open>Computational soundness one for non-diverging executions\<close>
theorem soundness:
  assumes "(s , e) \<Down> e'"
    and "fv s = {}"
  shows "e' \<in> PdToSet (exec s \<xi> e)"
  using assms
proof (induct "(s, e)" "e'" arbitrary: s \<xi> e rule: big_step.induct)
  case (Skip e)
  thus ?case 
    by simp
next
  case (Abort e)
  thus ?case
    by simp
next
  case (Atomic atomic e)
  thus ?case  
    by (simp split: option.split)
next
  case (Seq s1 e1 e2 s2 e3)
  thus ?case
    apply (simp add: PdToSet_seq)
    by fastforce
next
  case (SeqEr1 s1 e1 s2)
  thus ?case 
    by (simp add: PdToSet_seq)
next
  case (SeqEr2 s1 e1 e2 s2)
  thus ?case 
    apply (simp add: PdToSet_seq)
    by auto
next
  case (LeftL s1 e e1 s2)
  thus ?case 
    by (simp add: PdToSet_lc)
next
  case (LeftR s1 e s2 e1)
  thus ?case 
    by (simp add: PdToSet_lc)
next
  case (LeftEr s1 e s2)
  thus ?case  
    by (simp add: PdToSet_lc)
next
  case (ChoiceL s1 e e1 s2)
  thus ?case 
    by (simp add: PdToSet_choice)
next
  case (ChoiceR s2 e e1 s1)
  thus ?case 
    by (simp add: PdToSet_choice)
next
  case (ChoiceEr s1 e s2)
  thus ?case 
    by (simp add: PdToSet_choice)
next
  case (OneLeaf s label)
  thus ?case 
    by (simp add: PdToSet_one)
next
  case (OneNodeL s l l' r)
  thus ?case
    by (simp add: PdToSet_one)
next
  case (OneNodeR s r r' l)
  thus ?case
    by (simp add: PdToSet_one)
next
  case (OneNodeEr s l r)
  thus ?case 
    by (simp add: PdToSet_one)
next
  case (SomeLeaf s label)
  thus ?case
    by (simp add: PdToSet_some)
next
  case (SomeNodeL s l l' r)
  thus ?case 
    by (simp add: PdToSet_some)
next
  case (SomeNodeR s r r' l)
  thus ?case
    by (simp add: PdToSet_some)
next
  case (SomeNode s l l' r r')
  thus ?case 
    by (simp add: PdToSet_some)
next
  case (SomeNodeEr s l r)
  thus ?case
    by (simp add: PdToSet_some)
next
  case (AllLeaf s label)
  thus ?case
    by (simp add: PdToSet_all)
next
  case (AllNode s l l' r r')
  thus ?case
    by (simp add: PdToSet_all)
next
  case (AllNodeErL s l r)
  thus ?case
    by (simp add: PdToSet_all)
next
  case (AllNodeErR s r l)
  thus ?case
    by (simp add: PdToSet_all)
next
  case (FixedPoint s X e e')
  thus ?case
    apply (simp add: substitution)
    apply (subst fixp_unfold)
     apply (simp add: ord.mono_on_def)
    using subst_var_empty by force
next
  case (FixedPointEr s X e)
  thus ?case
    apply (simp add: substitution)
    apply (subst fixp_unfold)
    apply (simp add: ord.mono_on_def)
    using subst_var_empty by force
qed

subsection \<open>Computational adequacy one\<close>
definition approximate :: "strategy \<Rightarrow> D \<Rightarrow> bool"
  where
    "approximate s d \<longleftrightarrow> (fv s = {}) \<and> (\<forall> e e'. (e' \<in> PdToSet (d e)) \<and> (e' \<noteq> Div) \<longrightarrow> (s, e) \<Down> e')"

type_synonym \<Theta> = "var \<Rightarrow> strategy"

fun map_strategy :: "\<Theta> \<Rightarrow> strategy \<Rightarrow> strategy"
  where
    "map_strategy f SKIP = SKIP"
  | "map_strategy f ABORT = ABORT"
  | "map_strategy f \<lparr>X\<rparr> = f X"
  | "map_strategy f \<llangle>atomic\<rrangle> = \<llangle>atomic\<rrangle>"
  | "map_strategy f (s1 ;; s2) = (map_strategy f s1) ;; (map_strategy f s2)"
  | "map_strategy f (s1 <+ s2) = (map_strategy f s1) <+ (map_strategy f s2)"
  | "map_strategy f (s1 >< s2) = (map_strategy f s1) >< (map_strategy f s2)"
  | "map_strategy f (one s) = one (map_strategy f s)"
  | "map_strategy f (some s) = some (map_strategy f s)"
  | "map_strategy f (all s) = all (map_strategy f s)"
  | "map_strategy f (mu X. s) = mu X. (map_strategy (f(X := \<lparr>X\<rparr>)) s)"

lemma approximate_seq: 
  assumes "approximate s1 d1"
    and "approximate s2 d2"
  shows "approximate (s1 ;; s2) (d1 ;;s d2)"
  using assms 
  unfolding approximate_def
  apply (simp add: PdToSet_seq)
  using Seq SeqEr1 SeqEr2
  by (metis exp_err_div.distinct(5) exp_err_div.exhaust)

lemma approximate_lc: 
  assumes "approximate s1 d1"
    and "approximate s2 d2"
  shows "approximate (s1 <+ s2) (d1 <+s d2)"
  using assms
  unfolding approximate_def
  apply (simp add: PdToSet_lc)
  using  LeftEr LeftL LeftR
  by (metis exp_err_div.exhaust exp_err_div.simps(5))

lemma approximate_choice: 
  assumes "approximate s1 d1"
    and "approximate s2 d2"
  shows "approximate (s1 >< s2) (d1 ><s d2)"
  using assms
  unfolding approximate_def
  apply (simp add: PdToSet_choice)
  using ChoiceEr ChoiceL ChoiceR by blast

lemma approximate_one: 
  assumes "approximate s d"
  shows "approximate (one s) (one_s d)"
  using assms
  unfolding approximate_def
  apply (simp add: PdToSet_one)
  using OneLeaf OneNodeEr OneNodeL OneNodeR by fastforce

lemma approximate_some: 
  assumes "approximate s d"
  shows "approximate (some s) (some_s d)"
  using assms
  unfolding approximate_def
  apply (simp add: PdToSet_some)
  using SomeLeaf SomeNode SomeNodeEr SomeNodeL SomeNodeR by fastforce

lemma approximate_all:
  assumes "approximate s d"
  shows "approximate (all s) (all_s d)"
  using assms
  unfolding approximate_def
  apply (simp add: PdToSet_all)
  using AllLeaf AllNode AllNodeErL AllNodeErR
  by fastforce

lemma map_strategy_closed:
  assumes "\<forall>y\<in>fv s. fv (\<theta> y) \<subseteq> vs"
  shows " fv (map_strategy \<theta> s) \<subseteq> vs"
  using assms
proof (induct s arbitrary: \<theta> vs)
  case (Mu x1 s)
  thus ?case
  proof -
    have "fv (map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) s) \<subseteq> vs \<union> {x1}" 
      using Mu.prems Mu.hyps 
      by (simp add: subset_insertI2)
    thus ?case
      by fastforce
  qed
qed (simp+)

lemma subst_does_nothing: "x \<notin> fv s \<Longrightarrow>  s \<lbrace>x\<mapsto>s'\<rbrace> = s"
  apply (induct s)
  by auto

(*
(map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s\<lbrace>x1\<mapsto>(mux1.map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s)\<rbrace>,  e)
*)
lemma map_strategy_subst:
  assumes "\<forall> y \<in> fv(s) - {x}. x \<notin> fv (\<theta> y)"
  shows "map_strategy (\<theta>(x := \<lparr>x\<rparr>)) s\<lbrace>x \<mapsto> s'\<rbrace> = map_strategy (\<theta>(x := s')) s"
  using assms
proof (induct s arbitrary: \<theta>)
  case (FixVar x)
  thus ?case
    by (simp add: subst_does_nothing)
next
  case (Mu x1 s)
  thus ?case
    using Mu.hyps Mu.prems
    by (smt (verit, ccfv_SIG) DiffD2 Diff_empty Diff_insert0 fun_upd_other fun_upd_same 
                              fun_upd_twist fun_upd_upd fv.simps(11) fv.simps(3) insert_Diff 
                              insert_iff map_strategy.simps(11) substitute.simps(11))
(* if smt needs to be avoided *)
(*    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "((\<lambda>a. if a = x then \<lparr>x\<rparr> else \<theta> a)(x := \<lparr>x\<rparr>)) = ((\<lambda>a. if a = x then s' else \<theta> a)(x := \<lparr>x\<rparr>))")
      apply simp
     apply (rule ext)
     apply simp
    apply clarsimp
    apply (drule_tac x="\<theta>(x1 := \<lparr>x1\<rparr>)" in meta_spec)
    apply (drule meta_mp)
     apply simp
    apply (subgoal_tac "(\<lambda>a. if a = x then \<lparr>x\<rparr> else (\<theta>(x1 := \<lparr>x1\<rparr>)) a) = ((\<lambda>a. if a = x then \<lparr>x\<rparr> else \<theta> a)(x1 := \<lparr>x1\<rparr>))")
     apply (subgoal_tac "(\<lambda>a. if a = x then s' else (\<theta>(x1 := \<lparr>x1\<rparr>)) a) = ((\<lambda>a. if a = x then s' else \<theta> a)(x1 := \<lparr>x1\<rparr>))")
      apply simp
     apply (rule ext)
     apply simp
    apply (rule ext)
    by simp
*)
qed (simp+)

lemma approximation_lemma : 
  assumes "\<forall> y \<in> (fv s). approximate (\<theta> y) (\<xi> y)"
    and "sc = map_strategy \<theta> s"
  shows "approximate sc (exec s \<xi>)"
  using assms
proof (induct s arbitrary: \<theta> sc \<xi>)
  case SKIP
  thus ?case
    unfolding approximate_def
    using big_step.Skip by fastforce
next
  case ABORT
  thus ?case
    unfolding approximate_def
    using big_step.Abort by fastforce
next
  case (FixVar X)
  thus ?case
    by fastforce
next
  case (Atomic atomic)
  thus ?case
    unfolding approximate_def
    apply (simp split: option.split)
    by (metis big_step.Atomic option.sel option.split_sel)
next
  case (Seq s1 s2)
  thus ?case
    by (simp add: approximate_seq)
next
  case (Left_Choice s1 s2)
  thus ?case
    by (simp add: approximate_lc)
next
  case (Choice s1 s2)
  thus ?case
    by (simp add: approximate_choice)
next
  case (One s)
  thus ?case
    by (simp add: approximate_one)
next
  case (CSome s)
  thus ?case
    by (simp add: approximate_some)
next
  case (All s)
  thus ?case 
    by (simp add: approximate_all)
next
  case (Mu x1 s)
  thus ?case
    apply simp
    apply (rule fixp_induct[where f="\<lambda> x. exec s (\<xi>(x1 := x))"])
       apply (rule ccpo.admissibleI)
       apply (simp add: approximate_def)
       apply (rule conjI)
    using map_strategy_closed apply auto[1]
       apply clarsimp
       apply (subgoal_tac "Complete_Partial_Order.chain (\<le>) ((\<lambda> b. b e) ` A)")
        apply (case_tac "\<exists> a \<in> A. Div \<notin> PdToSet (a e)")
         apply clarsimp
         apply(frule_tac A="(\<lambda> b. b e) ` A" in no_div_Sup_ub[rotated 2])
           apply simp
          apply simp
         apply simp
        apply clarsimp
        apply (frule div_Sup_ub[rotated])
          apply simp
         apply blast
        apply simp
    using Rep_powerdomain apply auto[1]
       apply (metis (no_types, lifting) chain_imageI le_funE)
      apply (rule monoI)
      apply (rule exec_mono)
      apply auto[1]
     apply (simp add: Sup_empty approximate_def)
    using map_strategy_closed apply simp
    apply clarsimp
    apply (drule_tac x="\<theta>(x1 := map_strategy \<theta> (mu x1. s))" in meta_spec)
    apply (drule_tac x="\<xi>(x1 := x)" in meta_spec)
    apply (drule_tac x = "map_strategy (\<theta>(x1 := map_strategy \<theta> (mu x1. s))) s" in meta_spec)
    apply (drule meta_mp)
     apply clarsimp
     apply (simp add: fun_upd_def)
    apply (drule meta_mp)
     apply (simp add: fun_upd_def)
    apply (simp add: approximate_def)
    apply clarsimp
    apply (rename_tac e e')
    apply (case_tac e' ; simp)
     apply (rule big_step.FixedPointEr)
     apply (subst map_strategy_subst[simplified fun_upd_def])
      apply simp
     apply (rotate_tac 5)
     apply (drule_tac x="e" in spec)
     apply (rotate_tac 7)
     apply (drule_tac x="Err" in spec)
     apply (drule mp)
      apply (simp add: fun_upd_def)
     apply (subgoal_tac "(\<lambda>a. if a = x1 then mu x1. map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) s else \<theta> a) = (\<lambda>x. if x = x1 then mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) s else \<theta> x)")
      apply simp
     apply (rule ext)
     apply (simp add: fun_upd_def)
    apply (rule big_step.FixedPoint)
    apply (subst map_strategy_subst[simplified fun_upd_def])
     apply simp
    apply (auto simp add: fun_upd_def)[1]
    using Mu.prems(2) exp_err_div.distinct(5) map_strategy.simps(11) by presburger
qed

lemma map_closed_strategy_unchanged:
  assumes "\<forall> y \<in> fv s. \<theta> y = \<lparr> y \<rparr>"
  shows "map_strategy \<theta> s = s"
  using assms
apply(induct s arbitrary: \<theta>)
  by simp+

text \<open> The computational adequacy theorem one for non-diverging executions \<close>
theorem computational_adequacy:
  assumes "fv (s) = {}"
    and "e' \<in> PdToSet (exec s \<xi> e)"
    and "e' \<noteq> Div"
  shows "(s, e) \<Down> e'"
  using assms
  by (metis approximate_def approximation_lemma empty_iff map_closed_strategy_unchanged)

subsection \<open>Computational soundness two\<close>
definition rel :: "strategy \<Rightarrow> D \<Rightarrow> bool" where
  rel_def: "rel s d \<longleftrightarrow> (fv s = {}) \<and> (\<forall>e. (((s,e) \<Up>) \<longrightarrow> Div \<in> PdToSet (d e)) \<and> (d e \<le> exec s (\<lambda>x. undefined) e) )" 

fun semantics_subst :: "(var \<Rightarrow> strategy) \<Rightarrow> env \<Rightarrow> env" where
  "semantics_subst \<theta> \<xi> y = exec (\<theta> y) \<xi>" 

theorem exec_mono_fv:
  assumes "\<forall>x \<in> fv s. env1 x \<le> env2 x"  
  shows "exec s env1 \<le> exec s env2"
proof -
  have "exec s env1 = exec s (\<lambda>x. if x \<in> fv s then env1 x else (\<lambda>e. SetToPd {Div}))"
   and "exec s env2 = exec s (\<lambda>x. if x \<in> fv s then env2 x else (\<lambda>e. SetToPd {Div}))"
    by (simp add: env_irrelevant)+
  with assms 
  show ?thesis
    by force
qed

lemma simul_substitution: 
  assumes "\<forall>y \<in> fv s1. fv (\<theta> y) = {} \<or> fv (\<theta> y) = {y}"
  shows "exec (map_strategy \<theta> s1) \<xi> = exec s1 (semantics_subst \<theta> \<xi>)"
  using assms 
proof (induct s1 arbitrary: \<theta> \<xi>)
  case (Mu x1 s1)
  thus ?case
  proof -
    have "\<And> x. exec (map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) s1) (\<xi>(x1 := x)) 
                     =  exec s1 ((semantics_subst \<theta> \<xi>)(x1 := x))"
      using Mu.hyps Mu.prems
      by (smt (verit) DiffI env_irrelevant exec.simps(3) fun_upd_other fun_upd_same fv.simps(3,11) 
                     insertE insert_absorb insert_not_empty semantics_subst.elims)
    thus ?case
      using exec.simps(11) map_strategy.simps(11) by presburger
  qed
qed (simp+)

lemma map_strategy_irrelevant:
  assumes "\<forall>y \<in> fv t. \<theta>1 y = \<theta>2 y" 
  shows "map_strategy \<theta>1 t = map_strategy \<theta>2 t" 
  using assms 
  by (induct t arbitrary: \<theta>1 \<theta>2; simp)

lemma double_substitution: 
  assumes "\<forall>y \<in> fv t. fv (\<theta>1 y) \<subseteq> {y}"
    and     "\<forall>y \<in> fv (map_strategy \<theta>1 t). fv (\<theta>2 y) \<subseteq> {y}"
  shows "map_strategy \<theta>2 (map_strategy \<theta>1 t) = map_strategy (\<lambda>y. map_strategy \<theta>2 (\<theta>1 y)) t"
  using assms 
proof (induct t arbitrary: \<theta>1 \<theta>2)
  case (Mu x1 t)
  thus ?case 
    apply (simp add: fun_upd_def)
    apply (rule map_strategy_irrelevant, clarsimp)
    apply (rule map_strategy_irrelevant, clarsimp)
    by blast
qed (simp+)

lemma map_strategy_decomp:
  assumes "fv u = {}"
    and     "\<forall>y \<in> fv t - {x1}. fv (\<theta> y) = {}"
  shows "map_strategy (\<theta>(x1 := u)) t 
       = map_strategy (\<theta>(x1 := u)) (map_strategy (\<theta>(x1 := \<lparr> x1 \<rparr>)) t)"
proof (subst double_substitution)
  show "\<forall>y\<in>fv t. fv ((\<theta>(x1 := \<lparr>x1\<rparr>)) y) \<subseteq> {y}"
    using assms by clarsimp
  show "\<forall>y\<in>fv (map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) t). fv ((\<theta>(x1 := u)) y) \<subseteq> {y}"
    using assms apply clarsimp 
    by (metis DiffI Diff_eq_empty_iff empty_iff fv.simps(11) insertE map_strategy.simps(11) 
              map_strategy_closed)
  show "map_strategy (\<theta>(x1 := u)) t = map_strategy (\<lambda>y. map_strategy (\<theta>(x1 := u)) ((\<theta>(x1 := \<lparr>x1\<rparr>)) y)) t"
    using assms apply clarsimp
    by (simp add: map_closed_strategy_unchanged map_strategy_irrelevant)
qed

lemma div_soundness_lemma: 
  assumes "\<forall> y \<in> fv s. rel (\<theta> y) (\<xi> y)"
  shows "rel (map_strategy \<theta> s) (exec s \<xi>)"
  using assms 
proof (induct s arbitrary: \<theta> \<xi>)
  case SKIP
  thus ?case
    by (auto simp: rel_def elim: big_step_div.cases) 
next
  case ABORT
  thus ?case 
    by (auto simp: rel_def  elim: big_step_div.cases)
next
  case (FixVar x)
  thus ?case 
    by (auto simp: rel_def  elim: big_step_div.cases)
next
  case (Atomic x)
  thus ?case 
    by (auto simp: rel_def elim: big_step_div.cases)
next
  case (Seq s1 s2)
  thus ?case 
(*  proof - 
    have "(exec s1 \<xi>;;s exec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined);;s exec (map_strategy \<theta> s2) (\<lambda>x. undefined))"
      using Seq.prems Seq.hyps
      apply (simp add: le_fun_def)
      by (metis UnCI le_funD le_funI rel_def seq_s_mono)
    thus ?thesis
*)
    unfolding rel_def apply (intro conjI)
     apply (metis map_strategy_closed subset_empty)
    apply clarsimp
    apply (intro conjI)
     apply clarsimp
     (* takes a few seconds *)
     apply (erule big_step_div.cases; fastforce elim: big_step_div.cases
                                                simp: PdToSet_seq porcupine_eglimilner simul_substitution
                                                dest: soundness[where \<xi>="(\<lambda>x. undefined)"])
    apply (subgoal_tac "(exec s1 \<xi>;;s exec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined);;s exec (map_strategy \<theta> s2) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule seq_s_mono)
     apply (simp add: le_fun_def)
    by (simp add: le_fun_def)
next
  case (Left_Choice s1 s2)
  thus ?case 
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
      apply fast
      apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (drule_tac x = \<theta> in meta_spec)
      apply (drule_tac x = \<xi> in meta_spec)
      apply (drule meta_mp)
       apply auto[1]
      apply (clarsimp)
      apply (rename_tac e)
      apply (drule_tac x = e in spec)
      apply simp
      apply (simp add: PdToSet_lc)
     apply (simp add: PdToSet_lc)
     apply (drule_tac x = \<theta> in meta_spec)
     apply (drule_tac x = \<xi> in meta_spec)
     apply (drule meta_mp)
      apply blast
     apply (erule conjE, simp)
     apply (rename_tac e s1')
     apply (drule_tac x = e in spec)
     apply (erule conjE)
     apply (case_tac "Div \<in> PdToSet (exec s1 \<xi> e)")
      apply simp
     apply (rule disjI2)
     apply (rule conjI)
      apply (drule_tac x = \<theta> in meta_spec)
      apply (drule_tac x = \<xi> in meta_spec)
      apply (drule meta_mp)
       apply simp
      apply clarsimp
     apply (frule_tac \<xi>=" (\<lambda>x. undefined)" in soundness)
      apply fast
     apply (simp add: porcupine_eglimilner)
    apply (subgoal_tac "(exec s1 \<xi><+sexec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined)<+sexec (map_strategy \<theta> s2) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule lchoice_s_mono)
     apply (drule_tac x = \<theta> in meta_spec)
     apply (drule_tac x = \<xi> in meta_spec)
     apply (drule meta_mp)
      apply simp
     apply clarsimp
     apply (simp add: le_fun_def)
    apply (drule_tac x = \<theta> in meta_spec)
    apply (drule_tac x = \<xi> in meta_spec)
    apply (drule meta_mp)
     apply simp
    apply clarsimp
    by (simp add: le_fun_def)
next
  case (Choice s1 s2)
  thus ?case 
   apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
      apply fast
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_choice)
      apply blast
     apply (simp add: PdToSet_choice)
     apply blast
    apply (subgoal_tac "(exec s1 \<xi>><sexec s2 \<xi>)
         \<le> (exec (map_strategy \<theta> s1) (\<lambda>x. undefined)><sexec (map_strategy \<theta> s2) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule choice_s_mono)
    using le_fun_def apply fast
    using le_fun_def by fast
next
  case (One s)
  thus ?case 
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_one)
     apply (simp add: PdToSet_one)
    apply (subgoal_tac "one_s (exec s \<xi>) \<le> one_s (exec (map_strategy \<theta> s) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule one_s_mono)
    using le_fun_def by fast
next
  case (CSome s)
  thus ?case
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_some)
     apply (simp add: PdToSet_some)
    apply (subgoal_tac "some_s (exec s \<xi>) \<le> some_s (exec (map_strategy \<theta> s) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule some_s_mono)
    using le_fun_def by fast
next
  case (All s)
  thus ?case
    apply simp
    apply (simp add: rel_def)
    apply (intro conjI)
     apply fast
    apply (clarsimp)
    apply (rule conjI)
     apply clarsimp
     apply (erule big_step_div.cases; simp)
      apply (simp add: PdToSet_all)
     apply (simp add: PdToSet_all)
    apply (subgoal_tac "all_s (exec s \<xi>) \<le> all_s (exec (map_strategy \<theta> s) (\<lambda>x. undefined))")
     apply (simp add: le_fun_def)
    apply (rule all_s_mono)
    using le_fun_def by fast
next
  case (Mu x1 t)
  thus ?case
    apply simp 
    apply (rule fixp_induct[where f ="\<lambda> x. exec t (\<xi>(x1 := x))"])
       apply (rule ccpo.admissibleI)
       apply (simp add: rel_def)
       apply (rule conjI)
        apply (rule map_strategy_closed)
        apply simp
       apply (rule allI)
       apply (rename_tac A e)
       apply (rule conjI)
        apply (rule impI)
        apply (subgoal_tac "Complete_Partial_Order.chain (\<le>) ((\<lambda>x. x e) ` A)")
         apply (rotate_tac 5)
         apply (frule div_Sup_ub[rotated])
           apply clarsimp
          apply simp
         apply simp
         apply (subst Abs_powerdomain_inverse)
          apply auto[1]
          apply fast
         apply auto[1]
        apply (simp add: chain_def)
        apply (simp add: le_fun_def)
        apply metis
       apply (rule ccpo_Sup_least)
        apply (simp add: chain_def)
        apply (simp add: le_fun_def)
        apply metis
       apply auto[1]
      apply (rule monoI)
      apply (rule exec_mono)
      apply auto[1]
     apply (simp add: rel_def Sup_empty)
     apply (simp add: bottom_element)
     apply (rule map_strategy_closed)
     apply simp
    apply (rename_tac x)
    apply (drule_tac x = "\<theta>(x1 := map_strategy \<theta> (mu x1. t))" in meta_spec)
    apply (drule_tac x = "\<xi>(x1 := x)" in meta_spec)
    apply (drule meta_mp)
     apply (simp add: rel_def)
     apply clarsimp
     apply (rule conjI)
      apply (rule map_strategy_closed)
      apply simp
     apply (simp add: fun_upd_def)
    apply (simp add: rel_def)
    apply clarsimp
    apply (rename_tac x e)
    apply (rule conjI)
     apply clarsimp
     apply (drule_tac x = e in spec)
     apply simp
     apply clarsimp
     apply (drule_tac x = e in spec)
     apply (erule conjE)
     apply (drule mp)
      apply (erule big_step_div.cases; simp)
      apply (rotate_tac 6)
      apply (drule sym)
      apply clarsimp
      apply (subgoal_tac "(map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) t)\<lbrace>x1\<mapsto>(mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) t)\<rbrace>
                      = map_strategy (\<lambda>a. if a = x1 then (mu x1. map_strategy (\<lambda>a. if a = x1 then \<lparr>x1\<rparr> else \<theta> a) t) else \<theta> a) t") 
       apply simp
       apply (subst fun_upd_def)
       apply simp
      apply (simp add: map_strategy_subst[simplified fun_upd_def])
     apply (simp add: fun_upd_def)
    apply (rename_tac x e)
    apply (rule_tac y = "exec t (semantics_subst (\<theta>(x1 := map_strategy \<theta> (mu x1. t)))  (\<lambda>x. undefined)) e" in order_trans)
     apply (rule_tac f = "exec t (\<xi>(x1 := x))" and g = "exec t (semantics_subst (\<theta>(x1 := map_strategy \<theta> (mu x1. t))) (\<lambda>x. undefined))" in le_funD)
     apply (subgoal_tac "exec t (\<xi>(x1 := x)) = exec t (\<lambda>y. if y \<in> fv t then (\<xi>(x1 := x)) y else (\<lambda>x. SetToPd {Div}))")
      apply simp
      apply (rule exec_mono)
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (rule conjI)
        apply clarsimp
        apply (subst le_fun_def)
        apply (rule allI)
        apply (rename_tac xa)
        apply (drule_tac x = xa in spec)
        apply (simp add: fun_upd_def)
       apply clarsimp
       apply (simp add: le_fun_def bottom_element)
      apply (clarsimp)
      apply (rule conjI)
       apply clarsimp
       apply (rename_tac xa)
       apply (erule_tac x = xa in ballE)
        apply (erule conjE)
        apply (simp add: le_fun_def)
       apply blast
      apply clarsimp
      apply (simp add: le_fun_def bottom_element)
     apply (rule env_irrelevant)
     apply simp
    apply (subst simul_substitution[THEN sym])
     apply (rule ballI)
     apply simp
     apply (rule impI)
     apply (rule disjI1)
     apply (rule map_strategy_closed)
     apply auto[1]
    apply (subst fixp_unfold)
     apply (rule monoI)
     apply (rule exec_mono)
     apply simp
    apply (rotate_tac 4)
    apply (drule_tac x = e in spec)
    apply (clarsimp)
    apply (subgoal_tac " exec (map_strategy (\<theta>(x1 := map_strategy \<theta> (mu x1. t))) t) (\<lambda>x. undefined) e
                       = exec (map_strategy (\<theta>(x1 := map_strategy \<theta> (mu x1. t))) (map_strategy (\<theta>(x1 := \<lparr> x1 \<rparr>)) t)) (\<lambda>x. undefined) e")
     apply simp
     apply (subst simul_substitution)
      apply simp
      apply (subgoal_tac "fv (map_strategy (\<theta>(x1 := \<lparr>x1\<rparr>)) t) \<subseteq> {x1}")
       apply blast
    using map_strategy_closed apply auto[1]
     apply (simp add: fun_upd_def)
     apply (rule exec_mono_fv[simplified le_fun_def, rule_format])
     apply clarsimp
     apply (rule conjI)
      apply (simp add: fun_upd_def)
     apply (subgoal_tac " fv (map_strategy (\<lambda>x. if x = x1 then \<lparr>x1\<rparr> else \<theta> x) t) \<subseteq> {x1}")
      apply blast
     apply (rule map_strategy_closed)
     apply auto[1]
    apply (subst map_strategy_decomp)
      apply (simp add: map_strategy_closed)
     apply blast
    apply simp
    done
qed


lemma map_strategy_fixvar[simp]: "map_strategy (\<lambda>x. \<lparr> x \<rparr>) s = s" 
  by (induct s; simp)

text \<open>Computational soundness two for diverging executions\<close>
theorem div_soundness:
  assumes "fv s = {}"
  shows "(s, e) \<Up> \<Longrightarrow> Div \<in> PdToSet (exec s \<xi> e)"
  using assms div_soundness_lemma map_closed_strategy_unchanged rel_def by force

subsection \<open>Computational adequacy two\<close>
lemma fixp_unfoldE: (*[rule_format, rotated]:*)
  assumes "mono f" 
  shows   "P (\<mu> X. f X) \<longrightarrow> (P (f (\<mu> X. f X)) \<longrightarrow> R) \<longrightarrow> R" 
  apply (subst fixp_unfold)
  using assms by simp_all

text \<open>Computational adequacy two for diverging executions\<close>
theorem div_adequacy:
  assumes "fv s = {}" 
    and "Div \<in> PdToSet (exec s (\<lambda>x. undefined) e)" 
  shows "(s,e) \<Up>"
  apply -
  apply (rule_tac X = "\<lambda>(s, e). fv s = {} \<and> Div \<in> PdToSet (exec s (\<lambda>x. undefined) e)" in big_step_div.coinduct)
   apply (simp split: prod.split)
  using assms apply simp
  apply (simp split: prod.split)
  apply (rename_tac x)
  apply (case_tac x)
  apply simp
  apply (rename_tac a b)
  apply (erule conjE)
  apply (case_tac a)
            apply simp
           apply simp
          apply simp
         apply simp
         apply (rename_tac x1)
         apply (case_tac "x1 b"; simp)
        apply (rename_tac x2 x3)
        apply simp
        apply (simp add: PdToSet_seq)
        apply (elim exE conjE disjE)
         apply (rule disjI2)
         apply (rule disjI2)
         apply simp
         apply (frule computational_adequacy, simp, simp)
         apply (rename_tac xa xb)
         apply (rule_tac x = xb in exI)
         apply simp
        apply simp
       apply (simp add: PdToSet_lc)
       apply (elim exE conjE disjE)
        apply simp
       apply (rule disjI2)
       apply (frule computational_adequacy, simp, simp)
       apply (rule disjI2)
       apply simp
      apply (simp add: PdToSet_choice)
      apply (elim exE conjE disjE)
       apply simp
      apply simp
     apply (simp add: PdToSet_one)
     apply blast
    apply (simp add: PdToSet_some)
    apply blast
   apply (simp add: PdToSet_all)
   apply blast
  apply simp
  apply (rename_tac x1 x2)
  apply (erule_tac f = "\<lambda>x. exec x2 ((\<lambda>x. undefined)(x1 := x))" and P = "\<lambda>m. Div \<in> PdToSet (m b)" in fixp_unfoldE[rule_format, rotated])
   apply (rule disjI1)
   apply (subst substitution)
    apply simp
   apply simp
  using subst_var_empty apply simp
  apply (rule monoI)
  apply (rule exec_mono)
  by simp

subsection \<open>The semantic equivalence theorem\<close>
theorem sem_equivalence: 
  assumes "fv s = {}" 
  shows "PdToSet (exec s (\<lambda>x. undefined) e) = { r |r. (s,e) \<Down> r } \<union> { r |r. r = Div \<and> ((s,e) \<Up>) }"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using assms apply -
    apply(rule subsetI)
    using computational_adequacy div_adequacy by blast
  show "?rhs \<subseteq> ?lhs"
    using assms apply -
    apply(rule subsetI)
    using div_soundness soundness by blast
qed
end