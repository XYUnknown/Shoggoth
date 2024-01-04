section \<open>Examples of Using the Location Based Weakest Precondition Calculus to Reason about Strategies \<close>
theory WpExamples
  imports Wp WpSoundness
begin
(* Example in section 5.1 *)
(* Repeat(SIKP) is a bad strategy *)
theorem repeat_skip_div : "wp (repeat SKIP) \<epsilon> UNIV (\<lambda> x. undefined) = {} \<and> wp_err (repeat SKIP) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  apply simp
  apply (rule fixp_induct)
     apply (rule ccpo.admissibleI)
     apply (simp add: fst_Sup snd_Sup)
     apply (simp add: Sup_pt)
     apply (subst Abs_pt_inverse)
      apply simp
      apply (intro mono_intros)
     apply (subst Abs_pt_inverse)
      apply simp
      apply (intro mono_intros)
     apply simp
    apply (intro mono_intros)
   apply (simp add: fst_Sup snd_Sup)
   apply (simp add: Sup_pt)
   apply (subst Abs_pt_inverse)
    apply simp
    apply (intro mono_intros)
   apply simp
  apply simp
  apply (subst Abs_pt_inverse)
   apply simp
   apply (intro mono_intros)
  by simp

theorem repeat_skip_div_tot : "wp (repeat SKIP) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  using repeat_skip_div by (rule conjunct1)

(* Example in section 5.1 *)
(* Demonic treatment for nondeterministic choice *)
(* SKIP >< Repeat(SIKP) is a bad strategy *)
theorem choice_has_div_will_div: "wp (SKIP >< (repeat SKIP)) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  apply simp
  using repeat_skip_div by simp


(* Example in section 5.1 *)
(* SKIP <+ Repeat(SIKP) is a good strategy *)
theorem lchoice_has_div_might_not_div :"wp (SKIP <+ (repeat SKIP)) \<epsilon> UNIV (\<lambda> x. undefined) = defined \<epsilon>"
  by simp

theorem lchoice_has_div_might_div_left: "wp ((repeat SKIP) <+ s) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  apply simp
  using repeat_skip_div by simp

theorem lchoice_has_div_might_div_right: "wp (ABORT <+ (repeat SKIP)) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  apply simp
  using repeat_skip_div by simp


(* Example in section 5.2 *)
fun plus_comm :: "exp \<Rightarrow> exp option"
  where
    "plus_comm (Node PLUS n m) = Some (Node PLUS m n)" |
    "plus_comm _ = None"
print_theorems

fun mult_comm :: "exp \<Rightarrow> exp option"
  where
    "mult_comm (Node MULT n m) = Some (Node MULT m n)" |
    "mult_comm _ = None"

fun mult_zero :: "exp \<Rightarrow> exp option"
  where
    "mult_zero (Node MULT (Leaf (Nat 0)) m) = Some (Leaf (Nat 0))" |
    "mult_zero _ = None"

fun plus_zero :: "exp \<Rightarrow> exp option"
  where
    "plus_zero (Node PLUS (Leaf (Nat 0)) m) = Some m" |
    "plus_zero _ = None"

(* Example in section 5.2 *)
(* A not well composed strategy is a bad strategy *)
theorem mult_comm_plus_comm_bad: "wp (\<llangle>mult_comm\<rrangle> ;; \<llangle>plus_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  apply (simp split: option.split)
  apply (rule allI)
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (erule mult_comm.elims; simp)
  by fastforce

(* Example in section 5.2 *)
(* A well composed strategy is a good strategy *)
lemma cases_plus_zero: "plus_comm x = Some xa \<Longrightarrow>
       a = xa \<Longrightarrow> plus_zero xa = None \<longrightarrow> Err \<in> range E \<Longrightarrow> \<exists>m::exp. x = Node PLUS m (Leaf (label.Nat (0::nat)))"
proof -
  fix a xa
  show "plus_comm x = Some xa \<Longrightarrow>
       a = xa \<Longrightarrow> plus_zero xa = None \<longrightarrow> Err \<in> range E \<Longrightarrow> \<exists>m::exp. x = Node PLUS m (Leaf (label.Nat (0::nat)))"
    apply (cases "plus_zero xa")
     apply blast 
    apply (erule plus_zero.elims; simp)
    by (erule plus_comm.elims; simp)
qed

theorem plus_comm_seq_plus_zero_good: "wp (\<llangle>plus_comm\<rrangle> ;; \<llangle>plus_zero\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = 
                                       {e | e m. e = (Node PLUS m (Leaf (Nat 0)))}"
proof (rule set_eqI)
  fix x
  show "(x \<in> wp (\<llangle>plus_comm\<rrangle>;; \<llangle>plus_zero\<rrangle>) \<epsilon> UNIV (\<lambda>x::int \<times> tag. undefined)) =
       (x \<in> {u::exp. \<exists>(e::exp) m::exp. u = e \<and> e = Node PLUS m (Leaf (label.Nat (0::nat)))})"
    apply (cases "plus_comm x")
     apply auto[1]
    apply (simp split: option.split)
    apply (rule iffI)
     apply (erule imageE)
     apply (simp add: cases_plus_zero)
    by auto
qed

theorem plus_zero_seq_plus_comm_good: "wp (\<llangle>plus_zero\<rrangle> ;; \<llangle>plus_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = 
                  {e | e m n. e = (Node PLUS (Leaf (Nat 0)) (Node PLUS m n))}"
  apply simp
  apply (rule set_eqI)
  apply simp
  apply (rename_tac x)
  apply (case_tac "plus_zero x")
   apply simp
   apply auto[1]
  apply (simp split: option.split)
  apply (rule iffI)
   apply (erule imageE)
   apply simp
   apply (rename_tac a xa)
   apply (case_tac "plus_comm xa")
    apply auto[1]
   apply (erule plus_zero.elims; simp)
   apply (erule plus_comm.elims; simp)
  by auto

theorem plus_comm_mult_comm_bad: "wp (\<llangle>plus_comm\<rrangle> ;; \<llangle>mult_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = {}"
  apply (simp split: option.split)
  apply (rule allI)
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (erule plus_comm.elims; simp)
  by fastforce

theorem choice_mult_comm_plus_comm_good : "wp ((\<llangle>mult_comm\<rrangle> >< \<llangle>plus_comm\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) 
                                      = {e | e m n. e = (Node MULT n m)}"
  apply (simp split: option.split)
  apply (rule set_eqI)
  apply simp
  apply (rename_tac x)
  apply (case_tac "mult_comm x")
   apply simp
   apply (case_tac "plus_comm x")
    apply simp
    apply auto[1]
   apply simp
   apply (erule plus_comm.elims; simp)
   apply auto[1]
  apply simp
  apply (case_tac "plus_comm x")
   apply simp
   apply (erule mult_comm.elims; simp)
  apply simp
  by (erule plus_comm.elims; simp)

theorem lchoice_mult_comm_plus_comm_good : "wp ((\<llangle>mult_comm\<rrangle> <+ \<llangle>plus_comm\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) 
                                      = {e | e m n. e = (Node MULT n m)}"
  apply (simp split: option.split)
  apply (rule set_eqI)
  apply simp
  apply (rename_tac x)
  apply (case_tac "mult_comm x")
   apply simp
   apply (case_tac "plus_comm x")
    apply simp
    apply auto[1]
   apply simp
   apply  (erule plus_comm.elims; simp)
   apply auto[1]
  apply simp
  by (erule mult_comm.elims; simp)

theorem choice_mult_comm_id_bad : "wp ((\<llangle>mult_comm\<rrangle> >< \<llangle>mult_zero\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> 
      {e | e m. e = Node MULT (Leaf (Nat 0)) m} (\<lambda> x. undefined) = {}" 
  apply (simp split: option.split)
  apply (rule conjI)
   apply (rule set_eqI)
   apply simp
   apply (rename_tac x)
   apply (case_tac "mult_comm x")
    apply clarsimp
   apply clarsimp
   apply (case_tac "mult_zero x")
    apply clarsimp
    apply (rename_tac xa)
    apply (case_tac "mult_comm xa")
     apply force
    apply (erule mult_comm.elims; simp)
    apply (erule imageE)
    apply clarsimp
   apply clarsimp
   apply (rename_tac xa xb)
   apply (case_tac "mult_comm xa")
    apply force
   apply (erule mult_comm.elims; simp)
   apply (erule imageE)
   apply clarsimp
  apply (rule set_eqI)
  apply simp
  apply (rename_tac x)
  apply (case_tac "mult_comm x")
   apply clarsimp
   apply (case_tac " mult_zero x")
    apply clarsimp
   apply clarsimp
   apply (rename_tac xa)
   apply (case_tac "mult_comm xa")
    apply force
   apply (erule mult_comm.elims; simp)
  apply clarsimp
  apply (case_tac " mult_zero x")
   apply clarsimp
  apply clarsimp
  apply (rename_tac xa xb)
  apply (case_tac "mult_comm xa")
   apply force
  apply (erule mult_comm.elims; simp)
  apply (erule imageE)
  by clarsimp

theorem lchoice_mult_comm_id_good : "wp ((\<llangle>mult_comm\<rrangle> <+ \<llangle>mult_zero\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> 
      {e | e m. e = Node MULT (Leaf (Nat 0)) m} (\<lambda> x. undefined) = {e | e m. e = Node MULT (Leaf (Nat 0)) m}"
  apply (simp split: option.split)
  apply (rule set_eqI)
  apply simp
  apply (rename_tac x)
  apply (case_tac "mult_comm x")
   apply clarsimp
   apply (case_tac "mult_zero x")
    apply clarsimp
    apply auto[1]
   apply clarsimp
   apply (erule mult_comm.elims; simp)
  apply clarsimp
  apply (rename_tac a)
  apply (case_tac "mult_comm a")
   apply (erule mult_comm.elims; simp)
  apply (rule iffI)
   apply (erule disjE)
    apply (erule imageE)
    apply simp
    apply (erule imageE)
    apply clarsimp
    apply (erule mult_comm.elims; simp)
   apply clarsimp
   apply (erule mult_comm.elims; simp)
  by clarsimp

theorem one_plus_zero : "wp (one \<llangle>plus_zero\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = 
                        {e | l e m n. e = Node l (Node PLUS (Leaf (Nat 0)) m) n}
                      \<union> {e | l e m n. e = Node l n (Node PLUS (Leaf (Nat 0)) m)}"
  apply (simp split: option.split)
  apply (rule set_eqI)
  apply simp
  apply (rename_tac x)
  apply (case_tac "plus_zero (lookup (pos.Left\<triangleleft>\<epsilon>) x)")
   apply clarsimp
   apply (case_tac "plus_zero (lookup (pos.Right\<triangleleft>\<epsilon>) x)")
    apply clarsimp
    apply auto[1]
   apply clarsimp
   apply (rotate_tac)
   apply (erule plus_zero.elims; simp)
   apply auto[1]
  apply clarsimp
  apply (case_tac "plus_zero (lookup (pos.Right\<triangleleft>\<epsilon>) x)")
   apply clarsimp
   apply (erule plus_zero.elims; simp)
   apply auto[1]
  apply clarsimp
  apply (erule plus_zero.elims; simp)
  by auto
end