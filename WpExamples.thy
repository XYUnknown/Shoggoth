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

lemma cases_plus_comm: "plus_zero x = Some xa \<Longrightarrow>
                        a = xa \<Longrightarrow>
                        plus_comm xa = None \<longrightarrow> Err \<in> range E \<Longrightarrow>
                        \<exists>(m::exp) n::exp. x = Node PLUS (Leaf (label.Nat (0::nat))) (Node PLUS m n)"

proof -
  fix a xa
  show "plus_zero x = Some xa \<Longrightarrow>
        a = xa \<Longrightarrow>
        plus_comm xa = None \<longrightarrow> Err \<in> range E \<Longrightarrow>
        \<exists>(m::exp) n::exp. x = Node PLUS (Leaf (label.Nat (0::nat))) (Node PLUS m n)"
    apply (cases "plus_comm xa")
     apply auto[1]
    apply (erule plus_zero.elims; simp)
    by (erule plus_comm.elims; simp)
qed

theorem plus_zero_seq_plus_comm_good: "wp (\<llangle>plus_zero\<rrangle> ;; \<llangle>plus_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = 
                  {e | e m n. e = (Node PLUS (Leaf (Nat 0)) (Node PLUS m n))}"
proof (rule set_eqI)
  fix x
  show "(x \<in> wp (\<llangle>plus_zero\<rrangle>;; \<llangle>plus_comm\<rrangle>) \<epsilon> UNIV (\<lambda>x::int \<times> tag. undefined)) =
        (x \<in> {u::exp.
          \<exists>(e::exp) (m::exp) n::exp. u = e \<and> e = Node PLUS (Leaf (label.Nat (0::nat))) (Node PLUS m n)})"
  proof (cases "plus_zero x")
    case None
    then show ?thesis
      by auto
  next
    case (Some a)
    then show ?thesis
      apply (simp split: option.split)
      apply (rule iffI)
      apply (erule imageE)
       apply (simp add: cases_plus_comm)
      by auto
  qed
qed

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
proof (rule set_eqI)
  fix x
  show "(x \<in> wp (\<llangle>mult_comm\<rrangle>>< \<llangle>plus_comm\<rrangle>;; \<llangle>mult_comm\<rrangle>) \<epsilon> UNIV (\<lambda>x::int \<times> tag. undefined)) =
        (x \<in> {u::exp. \<exists>(e::exp) (m::exp) n::exp. u = e \<and> e = Node MULT n m})"
  proof (cases "mult_comm x")
    case None
    then show ?thesis
      apply (cases "plus_comm x")
       apply auto[1]
      apply (erule plus_comm.elims; simp)
      by auto[1]
  next
    case (Some a)
    then show ?thesis
      apply (cases "plus_comm x")
       apply (erule mult_comm.elims; simp)
      by (erule plus_comm.elims; simp)
  qed
qed

theorem lchoice_mult_comm_plus_comm_good : "wp ((\<llangle>mult_comm\<rrangle> <+ \<llangle>plus_comm\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) 
                                      = {e | e m n. e = (Node MULT n m)}"
proof (rule set_eqI)
  fix x
  show "(x \<in> wp (\<llangle>mult_comm\<rrangle><+ \<llangle>plus_comm\<rrangle>;; \<llangle>mult_comm\<rrangle>) \<epsilon> UNIV (\<lambda>x::int \<times> tag. undefined)) =
        (x \<in> {u::exp. \<exists>(e::exp) (m::exp) n::exp. u = e \<and> e = Node MULT n m})"
  proof (cases "mult_comm x")
    case None
    then show ?thesis 
      apply (cases "plus_comm x")
       apply auto[1]
      apply  (erule plus_comm.elims; simp)
      by auto[1]
  next
    case (Some a)
    then show ?thesis 
      apply simp
      by (erule mult_comm.elims; simp)
  qed
qed

lemma cases_conj_one: "{u::exp.
     (mult_comm u = None \<longrightarrow>
      Err
      \<in> E ` {u::exp.
              (mult_comm u = None \<longrightarrow>
               Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
              (\<forall>x2::exp.
                  mult_comm u = Some x2 \<longrightarrow>
                  E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}) \<and>
     (\<forall>x2::exp.
         mult_comm u = Some x2 \<longrightarrow>
         E x2
         \<in> E ` {u::exp.
                 (mult_comm u = None \<longrightarrow>
                  Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                 (\<forall>x2::exp.
                     mult_comm u = Some x2 \<longrightarrow>
                     E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})})} \<inter>
    {u::exp.
     \<forall>x2::exp.
        mult_zero u = Some x2 \<longrightarrow>
        E x2
        \<in> E ` {u::exp.
                (mult_comm u = None \<longrightarrow>
                 Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                (\<forall>x2::exp.
                    mult_comm u = Some x2 \<longrightarrow>
                    E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}} =
    {}"
proof (rule set_eqI)
  fix x
  show "(x \<in> {u::exp.
           (mult_comm u = None \<longrightarrow>
            Err
            \<in> E ` {u::exp.
                    (mult_comm u = None \<longrightarrow>
                     Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                    (\<forall>x2::exp.
                        mult_comm u = Some x2 \<longrightarrow>
                        E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}) \<and>
           (\<forall>x2::exp.
               mult_comm u = Some x2 \<longrightarrow>
               E x2
               \<in> E ` {u::exp.
                       (mult_comm u = None \<longrightarrow>
                        Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                       (\<forall>x2::exp.
                           mult_comm u = Some x2 \<longrightarrow>
                           E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})})} \<inter>
          {u::exp.
           \<forall>x2::exp.
              mult_zero u = Some x2 \<longrightarrow>
              E x2
              \<in> E ` {u::exp.
                      (mult_comm u = None \<longrightarrow>
                       Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                      (\<forall>x2::exp.
                          mult_comm u = Some x2 \<longrightarrow>
                          E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}}) =
    (x \<in> {})"
  proof (cases "mult_comm x")
    case None
    then show ?thesis
      by clarsimp
  next
    case (Some a)
    then show ?thesis
      apply clarsimp
      apply (cases "mult_zero x")
       apply clarsimp
       apply (cases "mult_comm a")
        apply blast
       apply (erule mult_comm.elims; simp)
       apply (erule imageE)
       apply clarsimp
      apply clarsimp
      apply (cases "mult_comm a")
       apply blast
      apply (erule mult_comm.elims; simp)
      apply (erule imageE)
      by clarsimp
  qed
qed

lemma cases_mult_comm: "mult_comm x = None \<Longrightarrow>
       mult_zero x = Some xa \<Longrightarrow>
       mult_comm xa = None \<longrightarrow> Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m} \<Longrightarrow>
       \<forall>x2::exp.
          mult_comm xa = Some x2 \<longrightarrow> E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m} \<Longrightarrow>
       False"
proof -
  fix x xa
  show "mult_comm x = None \<Longrightarrow>
        mult_zero x = Some xa \<Longrightarrow>
        mult_comm xa = None \<longrightarrow> Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m} \<Longrightarrow>
        \<forall>x2::exp.
           mult_comm xa = Some x2 \<longrightarrow> E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m} \<Longrightarrow>
        False"
    apply (cases "mult_comm xa")
     apply force
    by (erule mult_comm.elims; simp)
qed

lemma cases_conj_two: "{u::exp.
     \<forall>x2::exp.
        mult_comm u = Some x2 \<longrightarrow>
        E x2
        \<in> E ` {u::exp.
                (mult_comm u = None \<longrightarrow>
                 Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                (\<forall>x2::exp.
                    mult_comm u = Some x2 \<longrightarrow>
                    E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}} \<inter>
    {u::exp.
     (mult_zero u = None \<longrightarrow>
      Err
      \<in> E ` {u::exp.
              (mult_comm u = None \<longrightarrow>
               Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
              (\<forall>x2::exp.
                  mult_comm u = Some x2 \<longrightarrow>
                  E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}) \<and>
     (\<forall>x2::exp.
         mult_zero u = Some x2 \<longrightarrow>
         E x2
         \<in> E ` {u::exp.
                 (mult_comm u = None \<longrightarrow>
                  Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                 (\<forall>x2::exp.
                     mult_comm u = Some x2 \<longrightarrow>
                     E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})})} =
    {}"
proof (rule set_eqI)
  fix x
  show "(x \<in> {u::exp.
              \<forall>x2::exp.
                 mult_comm u = Some x2 \<longrightarrow>
                 E x2
                 \<in> E ` {u::exp.
                         (mult_comm u = None \<longrightarrow>
                          Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                         (\<forall>x2::exp.
                             mult_comm u = Some x2 \<longrightarrow>
                             E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}} \<inter>
             {u::exp.
              (mult_zero u = None \<longrightarrow>
               Err
               \<in> E ` {u::exp.
                       (mult_comm u = None \<longrightarrow>
                        Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                       (\<forall>x2::exp.
                           mult_comm u = Some x2 \<longrightarrow>
                           E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})}) \<and>
              (\<forall>x2::exp.
                  mult_zero u = Some x2 \<longrightarrow>
                  E x2
                  \<in> E ` {u::exp.
                          (mult_comm u = None \<longrightarrow>
                           Err \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m}) \<and>
                          (\<forall>x2::exp.
                              mult_comm u = Some x2 \<longrightarrow>
                              E x2 \<in> E ` {u::exp. \<exists>m::exp. u = Node MULT (Leaf (label.Nat (0::nat))) m})})}) =
       (x \<in> {})"
  proof (cases "mult_comm x")
    case None
    then show ?thesis 
    proof (cases "mult_zero x")
      case None
      then show ?thesis by clarsimp
    next
      case (Some a)
      then show ?thesis 
        apply clarsimp
        apply (cases "mult_comm a")
         apply force
        using None cases_mult_comm by force
    qed
  next
    case (Some a)
    then show ?thesis
      apply clarsimp
      apply (cases "mult_zero x")
       apply clarsimp
      apply (cases "mult_comm a")
       apply force
      apply (erule mult_comm.elims; simp)
      apply (erule imageE)
      by clarsimp
  qed
qed

theorem choice_mult_comm_id_bad : "wp ((\<llangle>mult_comm\<rrangle> >< \<llangle>mult_zero\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> 
      {e | e m. e = Node MULT (Leaf (Nat 0)) m} (\<lambda> x. undefined) = {}" 
  apply (simp split: option.split)
  apply (rule conjI)
   apply (simp add: cases_conj_one)
  by (simp add: cases_conj_two)

theorem lchoice_mult_comm_id_good : "wp ((\<llangle>mult_comm\<rrangle> <+ \<llangle>mult_zero\<rrangle>) ;; \<llangle>mult_comm\<rrangle>) \<epsilon> 
      {e | e m. e = Node MULT (Leaf (Nat 0)) m} (\<lambda> x. undefined) = {e | e m. e = Node MULT (Leaf (Nat 0)) m}"
proof (rule set_eqI)
  fix x
  show "(x \<in> wp (\<llangle>mult_comm\<rrangle><+ \<llangle>mult_zero\<rrangle>;; \<llangle>mult_comm\<rrangle>) \<epsilon> 
           {u::exp. \<exists>(e::exp) m::exp. u = e \<and> e = Node MULT (Leaf (label.Nat (0::nat))) m}
           (\<lambda>x::int \<times> tag. undefined)) =
        (x \<in> {u::exp. \<exists>(e::exp) m::exp. u = e \<and> e = Node MULT (Leaf (label.Nat (0::nat))) m})"
  proof (cases "mult_comm x")
    case None
    then show ?thesis
      apply clarsimp
      apply (cases "mult_zero x")
       apply clarsimp
       apply auto[1]
      apply clarsimp
      by (erule mult_comm.elims; simp)
  next
    case (Some a)
    then show ?thesis
      apply clarsimp
      apply (cases "mult_comm a")
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
  qed
qed

theorem one_plus_zero : "wp (one \<llangle>plus_zero\<rrangle>) \<epsilon> UNIV (\<lambda> x. undefined) = 
                        {e | l e m n. e = Node l (Node PLUS (Leaf (Nat 0)) m) n}
                      \<union> {e | l e m n. e = Node l n (Node PLUS (Leaf (Nat 0)) m)}"
proof (rule set_eqI)
  fix x
  show "(x \<in> wp (one \<llangle>plus_zero\<rrangle>) \<epsilon> UNIV (\<lambda>x::int \<times> tag. undefined)) =
        (x \<in> {u::exp.
              \<exists>(l::label) (e::exp) (m::exp) n::exp.
                 u = e \<and> e = Node l (Node PLUS (Leaf (label.Nat (0::nat))) m) n} \<union>
             {u::exp.
              \<exists>(l::label) (e::exp) (m::exp) n::exp.
                 u = e \<and> e = Node l n (Node PLUS (Leaf (label.Nat (0::nat))) m)})"
  proof (cases "plus_zero (lookup (pos.Left\<triangleleft>\<epsilon>) x)")
    case None
    then show ?thesis
      apply clarsimp
      apply (cases "plus_zero (lookup (pos.Right\<triangleleft>\<epsilon>) x)")
       apply clarsimp
       apply auto[1]
      apply clarsimp
      apply rotate_tac
      apply (erule plus_zero.elims; simp)
      by auto[1]
  next
    case (Some a)
    then show ?thesis
      apply clarsimp
      apply (cases "plus_zero (lookup (pos.Right\<triangleleft>\<epsilon>) x)")
       apply clarsimp
       apply (erule plus_zero.elims; simp)
       apply auto[1]
      apply clarsimp
      apply (erule plus_zero.elims; simp)
      by auto
  qed
qed
end