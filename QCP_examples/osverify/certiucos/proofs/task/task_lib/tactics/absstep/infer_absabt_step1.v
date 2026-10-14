
Require Import base_tac1. 
Require Import opsem1.
Require Import cancel_abs1. 
Require Import seplog_lemmas1. 
Require Import seplog_tactics1. 
Require Import abs_infer_step1.

Ltac absimp_abt_solver := 
  unfolds; intros;
  eexists; exgamma;
  (first [ splits ; 
         [ try simpl_subst_gamma;
           try hmstep_call_consturctor; try eapply spec_prim_step_abt; 
           [ unfolds; repeat eexists; subst;
             try (eapply absdata_elim; eauto with abst_solver_base); try eauto 
           | try apply map_join_emp 
           |  repeat hmstep_call_consturctor
           | .. ]
         | sep remember (1 :: nil)%nat; simpl in *; simpljoin ;
           do 6 eexists ; splits ; try eauto ; eapply change_aop_rule; eauto]
       | idtac] ).

