(*  Title:         Operational.thy
    Authors:       Xueying Qin, U Edinburgh; Liam O'Connor, U Edinburgh; Peter Hoefner, ANU
    Contributions: Ohad Kammar, U Edinburgh; Rob van Glabeek, U Edinburgh; Michel Steuwer, U Edinburgh
    Maintainer:    Xueying Qin <xueying.qin@ed.ac.uk>
*)

section \<open> The big-step operational semantics extended with divergence of System S \<close>

theory Operational
  imports CCPO Syntax
begin

fun substitute :: "strategy \<Rightarrow> var \<Rightarrow> strategy \<Rightarrow> strategy" ("_\<lbrace>_\<mapsto>_\<rbrace>" [59, 60, 61] 60)
  where
    "SKIP \<lbrace> X \<mapsto> s \<rbrace> = SKIP" |
    "ABORT \<lbrace> X \<mapsto> s \<rbrace> = ABORT" |
    "\<lparr>V\<rparr> \<lbrace> X \<mapsto> s \<rbrace> = (if V = X then s else \<lparr>V\<rparr>)" |
    "\<llangle>atomic\<rrangle> \<lbrace> X \<mapsto> s \<rbrace> = \<llangle>atomic\<rrangle>" |
    "(s1 ;; s2) \<lbrace> X \<mapsto> s \<rbrace> = s1 \<lbrace> X \<mapsto> s \<rbrace> ;; (s2 \<lbrace> X \<mapsto> s \<rbrace>)" |
    "(s1 <+ s2) \<lbrace> X \<mapsto> s \<rbrace> = s1 \<lbrace> X \<mapsto> s \<rbrace> <+ (s2 \<lbrace> X \<mapsto> s \<rbrace>)" |
    "(s1 >< s2) \<lbrace> X \<mapsto> s \<rbrace> = s1 \<lbrace> X \<mapsto> s \<rbrace> >< (s2 \<lbrace> X \<mapsto> s \<rbrace>)" |
    "(one s1)  \<lbrace> X \<mapsto> s2 \<rbrace> = one (s1\<lbrace> X \<mapsto> s2 \<rbrace>)" |
    "(some s1)  \<lbrace> X \<mapsto> s2 \<rbrace> = some (s1\<lbrace> X \<mapsto> s2 \<rbrace>)" |
    "(all s1)  \<lbrace> X \<mapsto> s2 \<rbrace> = all (s1\<lbrace> X \<mapsto> s2 \<rbrace>)" |
    "(mu V. s1) \<lbrace> X \<mapsto> s2 \<rbrace>  = (if V = X then (mu V. s1) else (mu V. (s1 \<lbrace> X \<mapsto> s2 \<rbrace>)))"

subsection \<open>Non-diverging cases\<close>
inductive big_step :: "strategy \<times> exp \<Rightarrow> exp_err_div \<Rightarrow> bool" (infix "\<Down>" 55)
  where
    Skip:     "(SKIP, e) \<Down> E e"  |
    Abort:    "(ABORT, e) \<Down> Err" |
    Atomic:   "(\<llangle>atomic\<rrangle>, e) \<Down> (case (atomic e) of None \<Rightarrow> Err | Some e' \<Rightarrow> E e')" |
    Seq:      "\<lbrakk> (s1, e1) \<Down> E e2; (s2, e2) \<Down> E e3 \<rbrakk> \<Longrightarrow> (s1;;s2, e1) \<Down> E e3" |
    SeqEr1:    "(s1, e1) \<Down> Err \<Longrightarrow> (s1;;s2, e1) \<Down> Err" |
    SeqEr2:    "\<lbrakk> (s1, e1) \<Down> E e2; (s2, e2) \<Down> Err \<rbrakk> \<Longrightarrow> (s1;;s2, e1) \<Down> Err" |
    LeftL:    "(s1, e) \<Down> E e1 \<Longrightarrow> (s1<+s2, e) \<Down> E e1" |
    LeftR:    "\<lbrakk> (s1, e) \<Down> Err; (s2, e) \<Down> E e1 \<rbrakk> \<Longrightarrow> (s1<+s2, e) \<Down> E e1" |
    LeftEr:   "\<lbrakk> (s1, e) \<Down> Err; (s2, e) \<Down> Err \<rbrakk> \<Longrightarrow> (s1<+s2, e) \<Down> Err" |
    ChoiceL:  "(s1, e) \<Down> E e1 \<Longrightarrow> (s1><s2, e) \<Down> E e1" |
    ChoiceR:  "(s2, e) \<Down> E e1 \<Longrightarrow> (s1><s2, e) \<Down> E e1" |
    ChoiceEr: "\<lbrakk> (s1, e) \<Down> Err; (s2, e) \<Down> Err \<rbrakk> \<Longrightarrow> (s1><s2, e) \<Down> Err" |
    OneLeaf:    "(one s, Leaf label) \<Down> Err" |
    OneNodeL:  "(s, l) \<Down> E l' \<Longrightarrow> (one s, Node la l r) \<Down> E(Node la l' r)" |
    OneNodeR:  "(s, r) \<Down> E r' \<Longrightarrow> (one s, Node la l r) \<Down> E(Node la l r')" |
    OneNodeEr: "\<lbrakk> (s, l) \<Down> Err; (s, r) \<Down> Err \<rbrakk> \<Longrightarrow> (one s, Node la l r) \<Down> Err" |
    SomeLeaf:    "(some s, Leaf label) \<Down> Err" |
    SomeNodeL:  "\<lbrakk> (s, l) \<Down> E l'; (s, r) \<Down> Err \<rbrakk> \<Longrightarrow> (some s, Node la l r) \<Down> E(Node la l' r)" |
    SomeNodeR:  "\<lbrakk> (s, r) \<Down> E r'; (s, l) \<Down> Err \<rbrakk> \<Longrightarrow> (some s, Node la l r) \<Down> E(Node la l r')" |
    SomeNode:  "\<lbrakk> (s, l) \<Down> E l'; (s, r) \<Down> E r' \<rbrakk> \<Longrightarrow> (some s, Node la l r) \<Down> E(Node la l' r')" |
    SomeNodeEr: "\<lbrakk> (s, l) \<Down> Err; (s, r) \<Down> Err \<rbrakk> \<Longrightarrow> (some s, Node la l r) \<Down> Err" |
    AllLeaf:    "(all s, Leaf label) \<Down> E (Leaf label)" |
    AllNode:  "\<lbrakk> (s, l) \<Down> E l'; (s, r) \<Down> E r' \<rbrakk> \<Longrightarrow> (all s, Node la l r) \<Down> E(Node la l' r')" |
    AllNodeErL: "(s, l) \<Down> Err \<Longrightarrow> (all s, Node la l r) \<Down> Err" |
    AllNodeErR: "(s, r) \<Down> Err \<Longrightarrow> (all s, Node la l r) \<Down> Err" |
    FixedPoint: "(s\<lbrace> X \<mapsto> (mu X. s)\<rbrace>, e) \<Down> E e' \<Longrightarrow> (mu X. s, e) \<Down> E e'" |
    FixedPointEr: "(s\<lbrace> X \<mapsto> (mu X. s)\<rbrace>, e) \<Down> Err \<Longrightarrow> (mu X. s, e) \<Down> Err"

subsection \<open>Diverging cases\<close>
coinductive big_step_div :: "strategy \<times> exp \<Rightarrow> bool" ( "_ \<Up>" 55) where
  SeqCompDiv1: "(s1, e) \<Up> \<Longrightarrow> (s1 ;; s2 , e) \<Up>" |
  SeqCompDiv2: "\<lbrakk> (s1, e) \<Down> E e1 ; (s2, e1) \<Up> \<rbrakk> \<Longrightarrow>  (s1 ;; s2 , e) \<Up>" | 
  LChoiceDiv1: "(s1, e) \<Up> \<Longrightarrow> (s1 <+ s2, e) \<Up>" |
  LChoiceDiv2: "\<lbrakk> (s1, e) \<Down> Err ; (s2, e) \<Up> \<rbrakk> \<Longrightarrow> (s1 <+ s2, e) \<Up>" |
  ChoiceDiv1: "(s1, e) \<Up> \<Longrightarrow> (s1 >< s2, e) \<Up>" |
  ChoiceDiv2: "(s2, e) \<Up> \<Longrightarrow> (s1 >< s2, e) \<Up>" | 
  OneNodeDiv1: "(s, el) \<Up> \<Longrightarrow> (one s, Node la  el er) \<Up>" |
  OneNodeDiv2: "(s, er) \<Up> \<Longrightarrow> (one s, Node la el er) \<Up>" |
  SomeNodeDiv1: "(s, el) \<Up> \<Longrightarrow> (some s, Node la el er) \<Up>" |
  SomeNodeDiv2: "(s, er) \<Up> \<Longrightarrow> (some s, Node la el er) \<Up>" |
  AllNodeDiv1: "(s, el) \<Up> \<Longrightarrow> (all s, Node la el er) \<Up>" |
  AllNodeDiv2: "(s, er) \<Up> \<Longrightarrow> (all s, Node la el er) \<Up>" |
  FixedPointDiv: "(s\<lbrace> X \<mapsto> (mu X. s) \<rbrace>, e) \<Up> \<Longrightarrow> (mu X. s, e) \<Up>"

inductive_cases SkipE: "(SKIP, e) \<Down> x"
inductive_cases AbortE: "(ABORT, e) \<Down> x"

end

