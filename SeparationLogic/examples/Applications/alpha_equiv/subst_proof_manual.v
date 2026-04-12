Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications.alpha_equiv Require Import subst_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_democases Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.Applications.alpha_equiv Require Import ast_lib.
From SimpleC.EE.Applications Require Import malloc.
From SimpleC.EE.Applications Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_subst_var_safety_wit_5 : subst_var_safety_wit_5.
Proof. 
    pre_process.
    unfold termtypeID in *.
    destruct trm; lia.
Qed.

Lemma proof_of_subst_var_return_wit_1 : subst_var_return_wit_1.
Proof.    
    pre_process.
    unfold list_Z_cmp in H.
    rewrite H10 in H.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_v.
    rewrite H1, Heq.
    unfold store_term at 2.
    simpl.
    fold store_term.
    Exists y z. 
    entailer!.
Qed.  

Lemma proof_of_subst_var_return_wit_2 : subst_var_return_wit_2.
Proof. 
    pre_process.
    unfold list_Z_cmp in H0.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ contradiction | ].
    unfold term_subst_v.
    rewrite H2, Heq.
    fold term_subst_v.
    unfold store_term at 2.
    simpl.
    fold store_term.
    Exists y z.
    rewrite H.
    entailer!.
Qed.

Lemma proof_of_subst_var_return_wit_3 : subst_var_return_wit_3.
Proof. 
    pre_process.
    unfold term_subst_v at 3.
    rewrite H2.
    fold term_subst_v.
    unfold store_term at 3.
    simpl.
    fold store_term.
    Exists y z.
    rewrite H, H0.
    entailer!.
Qed. 

Lemma proof_of_subst_var_return_wit_4 : subst_var_return_wit_4.
Proof.
    pre_process.
    unfold term_subst_v.
    rewrite H0.
    unfold store_term.
    entailer!.
Qed. 

Lemma proof_of_subst_var_return_wit_5 : subst_var_return_wit_5.
Proof. 
    pre_process.
    unfold list_Z_cmp in H0.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ contradiction | ].
    unfold term_subst_v.
    rewrite H2, Heq.
    unfold store_term.
    Exists y.
    entailer!.
Qed.

Lemma proof_of_subst_var_return_wit_6 : subst_var_return_wit_6.
Proof.
    pre_process.
    unfold list_Z_cmp in H1.
    rewrite H0 in H1.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_v.
    rewrite H3, Heq.
    unfold store_term.
    Exists retval_2.
    entailer!.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_4_pure : subst_var_partial_solve_wit_4_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2 n3.
    entailer!.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_8_pure : subst_var_partial_solve_wit_8_pure.
Proof. 
    pre_process.
    unfold store_string.
    Intros n1 n2.
    sep_apply store_term_unfold.
    entailer!.
Qed.

Lemma proof_of_subst_var_partial_solve_wit_9_pure : subst_var_partial_solve_wit_9_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2.
    sep_apply store_term_unfold.
    entailer!.
Qed.
    
Lemma proof_of_subst_var_partial_solve_wit_12_pure : subst_var_partial_solve_wit_12_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2 n3.
    sep_apply (store_term_unfold z qterm).
    entailer!.
Qed.

Lemma proof_of_subst_var_which_implies_wit_1 : subst_var_which_implies_wit_1.
Proof. 
    pre_process.
    sep_apply store_term_unfold.
    entailer!.
Qed.

Lemma proof_of_subst_var_which_implies_wit_2 : subst_var_which_implies_wit_2.
Proof.
    pre_process.
    sep_apply store_term'_Var; [ | tauto | tauto].
    Intros var y.
    Exists y var.
    entailer!.
Qed. 

Lemma proof_of_subst_var_which_implies_wit_3 : subst_var_which_implies_wit_3.
Proof. 
    pre_process.
    sep_apply store_term'_Const; [ | tauto | tauto].
    Intros y z.
    Exists y z.
    entailer!.
Qed. 

Lemma proof_of_subst_var_which_implies_wit_4 : subst_var_which_implies_wit_4.
Proof. 
    pre_process.
    sep_apply store_term'_Apply; [ | tauto | tauto].
    Intros lt rt y z.
    Exists z y lt rt.
    entailer!.
Qed.

Lemma proof_of_subst_var_which_implies_wit_5 : subst_var_which_implies_wit_5.
Proof. 
    pre_process.
    sep_apply store_term'_Quant; [ | tauto | tauto].
    Intros typ v b y z.
    Exists z y typ v b.
    entailer!.
Qed. 

Lemma proof_of_subst_term_safety_wit_5 : subst_term_safety_wit_5.
Proof. 
    pre_process. 
    unfold termtypeID in *.
    destruct trm; lia.
Qed.

Lemma proof_of_subst_term_return_wit_1 : subst_term_return_wit_1.
Proof. 
    pre_process.
    unfold list_Z_cmp in H.
    rewrite H10 in H.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_t.
    rewrite H1, Heq.
    unfold store_term at 3.
    fold store_term.
    Exists y z. 
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_2 : subst_term_return_wit_2.
Proof.  
    pre_process.
    unfold list_Z_cmp in H.
    destruct (list_Z_eqb qvar src_str) eqn:Heq; [ contradiction | ].
    unfold term_subst_t.
    rewrite H1, Heq.
    fold term_subst_t.
    unfold store_term at 3.
    fold store_term.
    Exists y retval_2.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_3 : subst_term_return_wit_3.
Proof. 
    pre_process.
    unfold term_subst_t at 3.
    rewrite H0.
    fold term_subst_t.
    unfold store_term at 4.
    fold store_term.
    Exists retval retval_2.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_4 : subst_term_return_wit_4.
Proof.  
    pre_process.
    unfold term_subst_t.
    rewrite H0.
    unfold store_term at 2.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_5 : subst_term_return_wit_5.
Proof. 
    pre_process.
    unfold list_Z_cmp in H0.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ contradiction | ].
    unfold term_subst_t.
    rewrite H2, Heq.
    unfold store_term at 2.
    Exists y.
    entailer!.
Qed.

Lemma proof_of_subst_term_return_wit_6 : subst_term_return_wit_6.
Proof. 
    pre_process.
    unfold list_Z_cmp in H1.
    rewrite H0 in H1.
    destruct (list_Z_eqb var src_str) eqn:Heq; [ | discriminate ].
    unfold term_subst_t.
    rewrite H3, Heq.
    entailer!.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_9_pure : subst_term_partial_solve_wit_9_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n.
    sep_apply (store_term_unfold y lt).
    entailer!.
Qed.

Lemma proof_of_subst_term_partial_solve_wit_10_pure : subst_term_partial_solve_wit_10_pure.
Proof. 
    pre_process.
    unfold store_string.
    Intros n.
    sep_apply (store_term_unfold z rt).
    entailer!.
Qed. 

Lemma proof_of_subst_term_partial_solve_wit_13_pure : subst_term_partial_solve_wit_13_pure.
Proof.
    pre_process.
    unfold store_string.
    Intros n1 n2.
    sep_apply (store_term_unfold z qterm).
    entailer!.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_1 : subst_term_which_implies_wit_1.
Proof. 
    pre_process.
    sep_apply store_term_unfold.
    entailer!.
Qed.

Lemma proof_of_subst_term_which_implies_wit_2 : subst_term_which_implies_wit_2.
Proof. 
    pre_process.
    sep_apply store_term'_Var; [ | tauto | tauto].
    Intros var y.
    Exists y var.
    entailer!.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_3 : subst_term_which_implies_wit_3.
Proof. 
    pre_process.
    rewrite H0.
    unfold store_term.
    Exists y.
    entailer!.
Qed.

Lemma proof_of_subst_term_which_implies_wit_4 : subst_term_which_implies_wit_4.
Proof.
    pre_process.
    sep_apply store_term'_Const; [ | tauto | tauto].
    Intros y z.
    Exists y z.
    entailer!.
Qed. 

Lemma proof_of_subst_term_which_implies_wit_5 : subst_term_which_implies_wit_5.
Proof. 
    pre_process.
    sep_apply store_term'_Apply; [ | tauto | tauto].
    Intros lt rt y z.
    Exists z y lt rt.
    entailer!.
Qed.

Lemma proof_of_subst_term_which_implies_wit_6 : subst_term_which_implies_wit_6.
Proof. 
    pre_process.
    sep_apply store_term'_Quant; [ | tauto | tauto].
    Intros typ v b y z.
    Exists z y typ v b.
    entailer!.
Qed.
