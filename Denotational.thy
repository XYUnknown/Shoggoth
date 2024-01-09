(*  Title:         Denotational.thy
    Authors:       Xueying Qin, U Edinburgh; Liam O'Connor, U Edinburgh; Peter Hoefner, ANU
    Contributions: Ohad Kammar, U Edinburgh; Rob van Glabeek, U Edinburgh; Michel Steuwer, U Edinburgh
    Maintainer:    Xueying Qin <xueying.qin@ed.ac.uk>
*)

section \<open> The denotational semantics of System S \<close>

theory Denotational
  imports CCPO Syntax
begin

definition seq_s :: "D \<Rightarrow> D \<Rightarrow> D" ("_;;s/ _" [60, 61] 60) where 
  "seq_s s t e = SetToPd (\<Union>{PdToSet (t x) | x. E x \<in> PdToSet (s e)} 
                          \<union> {x | x. x \<in> PdToSet (s e) \<inter> {Div, Err}})"

definition lchoice_s :: "D \<Rightarrow> D \<Rightarrow> D" ("_<+s/_" [60, 61] 60) where 
  "lchoice_s s t e = SetToPd ((PdToSet (s e) - {Err}) 
                              \<union> {x | x. x \<in> PdToSet (t e) \<and> Err \<in> PdToSet (s e)})"

definition choice_s ::  "D \<Rightarrow> D \<Rightarrow> D" ("_><s/_" [60, 61] 60) where 
  "choice_s s t e = SetToPd ({E x | x. E x \<in> PdToSet (s e)}
                             \<union> {d. d = Div \<and> Div \<in> PdToSet (s e)}
                             \<union> {E y | y. E y \<in> PdToSet (t e)}
                             \<union> {d. d = Div \<and> Div \<in> PdToSet (t e)}
                             \<union> {err. err = Err \<and> Err \<in> PdToSet (s e) \<inter> PdToSet (t e)})"

definition one_s :: "D \<Rightarrow> D" where 
  "one_s s e = 
   SetToPd ({E (Node l x e2) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e1)}
            \<union> {d | l e1 e2 d. e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e1)}
            \<union> {E (Node l e1 x) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e2)}
            \<union> {d | l e1 e2 d. e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e2)}
            \<union> {err | e1 e2 l err. err = Err 
                     \<and> (e = Leaf l \<or> (e = Node l e1 e2 \<and> Err \<in> PdToSet (s e1) \<inter> PdToSet (s e2)))})"

definition some_s :: "D \<Rightarrow> D" where 
  "some_s s e = 
  SetToPd ({E (Node l x1 x2) | l x1 x2 e1 e2. e = Node l e1 e2 \<and> E x1 \<in> PdToSet (s e1)
                                              \<and> E x2 \<in> PdToSet (s e2)}
           \<union> {E (Node l x e2) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e1) 
                                           \<and> Err \<in> PdToSet (s e2)} 
           \<union> {E (Node l e1 x) | l x e1 e2. e = Node l e1 e2 \<and> E x \<in> PdToSet (s e2) 
                                           \<and> Err \<in> PdToSet (s e1)}
           \<union> {d | l e1 e2 d. (e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e1) \<union> PdToSet (s e2))}
           \<union> {err | e1 e2 l err. err = Err 
                      \<and> (e = Leaf l \<or> (e = Node l e1 e2 \<and> Err \<in> PdToSet (s e1) \<inter> PdToSet (s e2)))})"

(* all shall succeed on leaf node *)
definition all_s :: "D \<Rightarrow> D" where 
  "all_s s e = 
   SetToPd ({E (Node l x1 x2) | l x1 x2 e1 e2. e = Node l e1 e2 \<and> E x1 \<in> PdToSet (s e1) 
                                               \<and> E x2 \<in> PdToSet (s e2)}
            \<union> {E (Leaf l) | l.  e = Leaf l} 
            \<union> {d | l e1 e2 d. (e = Node l e1 e2 \<and> d = Div \<and> Div \<in> PdToSet (s e1) \<union> PdToSet (s e2))}
            \<union> {err | e1 e2 l err. err = Err
                                   \<and> (e = Node l e1 e2 \<and> Err \<in> PdToSet (s e1) \<union> PdToSet (s e2))})"

fun exec ::  "strategy \<Rightarrow> env \<Rightarrow> D" where
  "exec SKIP \<xi> = (\<lambda> e. SetToPd {E e})" 
| "exec ABORT \<xi> =  (\<lambda> e. SetToPd {Err})"  
| "exec \<lparr>X\<rparr> \<xi> = \<xi> X"
| "exec \<llangle>atomic\<rrangle> \<xi> = (\<lambda> e. case (atomic e) of None \<Rightarrow> SetToPd {Err} | Some e' \<Rightarrow> SetToPd {E e'})"
| "exec (s ;; t) \<xi> = ((exec s \<xi>) ;;s (exec t \<xi>))"
| "exec (s <+ t) \<xi> = ((exec s \<xi>) <+s (exec t \<xi>))"
| "exec (s >< t) \<xi> = ((exec s \<xi>) ><s (exec t \<xi>))"
| "exec (one s) \<xi> = (one_s (exec s \<xi>))"
| "exec (some s) \<xi> = (some_s (exec s \<xi>))"
| "exec (all s) \<xi> = (all_s (exec s \<xi>))"
| "exec (mu X. s) \<xi> = (\<mu> \<X>. exec s (\<xi>(X := \<X>)))"


theorem exec_try : "exec (try s) \<xi> = exec (s <+ SKIP) \<xi>"
  unfolding Try_def by fastforce

theorem exec_repeat : "exec (repeat s) \<xi> = exec (mu 0 . try (s ;; \<lparr>0\<rparr>)) \<xi>"
  unfolding Repeat_def by fastforce

theorem exec_topDown : "exec (topDown s) \<xi> = exec (mu 0. (s <+ one \<lparr>0\<rparr>)) \<xi>"
  unfolding TopDown_def by fastforce

end
