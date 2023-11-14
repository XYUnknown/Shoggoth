# Documentation for Artifact Evaluation
This is the artifact for the POPL 2024 submission: Shoggoth - A Formal Foundation for Strategic Rewriting. We provide all mechanised proofs developed in Isabelle/HOL. In total nine files (with .thy extension) containing our proof scripts are provided. This document explains the correspondence between the Isabelle/HOL mechanisation and our paper, as well as how to setup and run these proofs.

Here are some general information about this artifact:
- Isabelle/HOL version: 2022. This artifact is also compatible with Isabelle/HOL 2023. 
- There is no incomplete proof in this artifact.
- Running Isabelle/HOL proofs consumes a lot of memory. The author's machine is a MacBook pro with 32GB memory and 2.4 GHz 8-Core Intel Core i9 processor. When running these proofs on a MacBook pro with 8GB memory, some of them can take >1 minute to finish. 

## List of claims
- `CCPO.thy` contains:
	- the chain-complete partial order, powerdomain, domain, Egli-Milner ordering and porcupine ordering for defining the denotational semantics in section 3.1 and 3.2.
		- the Egli-Milner ordering in section 3.1 corresponds to the `definition pd_less_eq` (l85)
		- the Porcupine ordering in section 3.1 corresponds to the `definition porcupine_less_eq_paper` (l71)
		- the equivalence of Egli-Milner ordering and Porcupine ordering is shown in `lemma porcupine_eglimilner` (l91)
		- the Plotkin powerdomain introducted in section 3.2 is instantiated as a chain complete partial order in `instantiation powerdomain :: ccpo` (l218)
- `Syntax.thy` contains:
	- the syntax of System S introduced in section 2;
		- the syntax shown in figure 1 corresponds to the `datatype strategy` (l258)
- `Denotational.thy` contains the denotational semantics of System S in section 3.2:
	- semantic combinators shown in figure 2 and semantic traversals shown in figure 3 have correponding definitions in Isabelle/HOL from l7 to l41;
	- the denotational semantics of System S shown in figure 4 corresponds to `fun exec` (l53).
- `MonoDenotational.thy` contains the monotonicity proofs of the denotational semantics in section 3.2:
	- theorem 3.1 (semantics monotonicity theorem) corresponds to `theorem exec_mono` (l376)
- `Operational.thy` contains the big-step operational semantics of System S in section 3.3:
	- the big-step operational semantics of non-diverging cases shown in figure 5 corresponds to `inductive big_step` (l22)
	- the big-step operational semantics of diverging cases shown in figure 6 corresponds to `coinductive big_step_div` (l52)
- `SemanticsEquivalence.thy` contains:
	- proofs for computational soundness and computational adequacy theorems for non-diverging cases in section 3.4;
		- theorem 3.2 (computational soundness theorem one) corresponds to `theorem soundness` (l187)
		- lemma 3.3 (substitution lemma one) corresponds to `lemma substitution` (l76)
		- theorem 3.4 (computational adequacy theorem one) corresponds to `theorem computational_adequacy` (l728)
		- definition 3.1 (approximation relation one) corresponds to `definition approximate` (l323)
		- lemma 3.5 (approximation lemma one) corresponds to `lemma approximation_lemma` (l578)
	- proofs for computational soundness and computational adequacy theorems for diverging cases in section 3.4;
		- theorem 3.6 (computational soundness theorem two) corresponds to `theorem div_soundness` (l1150)
		- definition 3.2 (approximation relation two) corresponds to `definition rel` (l744)
		- lemma 3.7 (approximation lemma two) corresponds to `lemma div_soundness_lemma` (l823)
		- theorem 3.8 (computational adequacy theorem two) corresponds to `theorem div_adequacy` (l1168)
	- the proof for the equivalence theorem in section 3.4.
		- theorem 3.9 (equivalence between semantics) corresponds to `theorem sem_equivalence` (l1225)
- `Wp.thy` contains the location-based weakest precondition in section 4: 
	- helper (partial) functions `update` and `lookup` shown in figure 7 correspond to `fun update` (l78) and `fun lookup` (l85)
	- weakest must succeed preconditions and weakest may error preconditions for combinators, traversals and the fixed point operator shown in figure 10, figure 11 and figure 12 correspond to mutually defined `fun wp` and `fun wp_err` (l99).
	- we prove weakest must succeed preconditions and weakest may error preconditions are monotone by `theorem wp_wp_err_mono` (l254)
- `WpSoundness.thy` contains the soundess proof of the location-based weakest precondition with respect to the denotational semantics in section 4.3:
	- theorem 4.1 (soundness theorem for weakest must succeed precondition) and theorem 4.2 (soundness theorem for weakest may error precondition) correspond to `theorem wp_wp_err_soundness` (l1846).
- `WpExamples.thy` contains examples of using the weakest precondition calculus for reasoning the execution of strategies in section 5.1 and 5.2:
	- in section 5.1, the example strategy `repeat(SIKP)` being a bad strategy is proven by `theorem repeat_skip_div_tot` (l32)
	- in section 5.1, the example startegy `SKIP <+> repeat(SIKP)` being a bad stategy is proven by `theorem choice_has_div_will_div` (l38)
	- in section 5.1, the example strategy `SKIP <+ repeat(SIKP)` being a good strategy is proven by `theorem lchoice_has_div_might_not_div` (l45)
	- in section 5.2, the example strategy `mult_com ; add_com` being a bad strategy is proven by `theorem mult_comm_plus_comm_bad` (l81)
	- in section 5.2, the example strategy `add_com ; add_id` being a good strategy is proven by `theorem plus_comm_seq_plus_zero_good` (l92)
- `LambdaCalc.thy` contains the normalisation example for lambda calculus in section 5.3.
	- the strategy `normalise(s)` corresponds to the `definition normalise` (l352)
	- we show Omega cannot be normalised into a beta-eta normal form by `theorem omega_bad` (l357)
	- the last example in section 5.3 demonstrating that a long expressions can be normalised into a beta-eta normal form is shown by `theorem long_exp_good` (l452)

## Download, installation, and sanity-testing
- Download Isabelle/HOL 2022 or Isabelle/HOL 2023 from [the official website](https://isabelle.in.tum.de).
- Install Isabelle/HOL.
- Open Isabelle/HOL's build-in editor, and make sure "continuous checking", "proof state" and "auto update" options are enabled.
- For sanity-testing, open the `CCPO.thy` file and scroll to the end, all proofs in the file should be automatically checked and there should be no error.
## Evaluation instructions
- Please follow the list of claims and check the proof scripts one by one.
- No additional command or input is required. Simply scolling down the opened script to the end and all proofs should be automatically checked. 
- There should be no error.
## Additional artifact description
- File structure:
```
.
.
├── CCPO.thy
├── Denotational.thy
├── LambdaCalc.thy
├── MonoDenotational.thy
├── Operational.thy
├── README.md
├── ROOT
├── SemanticsEquivalence.thy
├── Syntax.thy
├── Wp.thy
├── WpExamples.thy
├── WpSoundness.thy
└── document
    ├── root.bib
    └── root.tex
``````
- All important theorems are highlighted in the list of claims.
- Using a machine with <=8 GB memory to run these proofs is not recommended since it will be very slow.
- To build the proof document, use the command: `isabelle build -D . -v -c -o document=pdf -o document_output=output`
## Misc
- All powerdomain constructions are currently specific to `exp_err_div`, since we are working with flat domains and we take advantage of such a construction for defining the partial order on the powerdomain. A future improvement can be done to make the powerdomain construction more modular by parameterising the construction by an arbitrary set.
