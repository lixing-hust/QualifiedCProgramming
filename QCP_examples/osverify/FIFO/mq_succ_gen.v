
Require Import memory. 
Require Import log_language.

Require Import FIFO_sys. 


Inductive has_succ0: spec_code -> spec_code -> Prop :=
  
  hs_seq1 (cd1 cd2 cds0: spec_code):
    has_succ0 cd1 cds0 ->
    has_succ0 (spec_seq cd1 cd2) (spec_seq cds0 cd2)

| hs_seq2 (cd1 cd2: spec_code):
  has_succ0 (spec_seq cd1 cd2) cd2
           
| hs_seq3 (cd1 cd2 cds0: spec_code):
  has_succ0 cd2 cds0 ->
  has_succ0 (spec_seq cd1 cd2) cds0

| hs_choice10 (cd1 cd2: spec_code):
  has_succ0 (spec_choice cd1 cd2) cd1
           
| hs_choice1 (cd1 cd2 cds0: spec_code):
  has_succ0 cd1 cds0 ->
  has_succ0 (spec_choice cd1 cd2) cds0

| hs_choice20 (cd1 cd2: spec_code):
  has_succ0 (spec_choice cd1 cd2) cd2
 
| hs_choice2 (cd1 cd2 cds0: spec_code):
  has_succ0 cd2 cds0 ->
  has_succ0 (spec_choice cd1 cd2) cds0
. 


Require Import log_opsem. 

Lemma step_succ0:
  forall sc cd cd' O O',
    spec_step sc cd O cd' O' ->
    has_succ0 cd cd' \/ cd' = spec_abort \/ (exists vo, cd' = spec_done vo).  
Proof.
  introv Hsp.
  inductions Hsp; 
    try (right; right; eexists; eauto; fail);
    try (right; left; eauto; fail);
    try (left; constructors; fail).
  - destruct IHHsp as [Hsc | [Habt | Hend]].
    left. constructors.  auto.
    simpljoin; tryfalse.
    simpljoin. false. apply H; eexists; eauto. 
Qed. 

Lemma succ0_step_preserve:
  forall sc cd0 cd cd' O O',
    has_succ0 cd0 cd ->
    spec_step sc cd O cd' O' ->
    has_succ0 cd0 cd' \/ cd' = spec_abort \/ (exists vo, cd' = spec_done vo).  
Proof.
  introv Hsu.
  remember cd0 as CD0.
  remember cd as CD.
  gen cd0 cd cd'.
  inductions Hsu; introv Heq1 Heq2 Hstep; subst;
    try (
        lets H__: step_succ0 Hstep; eauto; 
        destruct H__ as [Hsu_ | [Habt | Hend]]; 
        [left; constructors; eauto | 
          right; auto | 
          right; right; eauto]; fail);
    try (
        specializes IHHsu; eauto; 
        destruct IHHsu as [Hsu_ | [Habt | Hend]]; 
        [left; constructors; eauto | 
          right; auto | 
          right; right; eauto]; fail).
  -
    lets H__: step_succ0 Hstep; eauto.
    inverts Hstep.
    left. constructors.
    right; left; auto.
    specializes IHHsu; eauto.
    destruct IHHsu as [Hsu_ | [Habt | Hend]].
    left. constructors. eauto.
    simpljoin; tryfalse.
    simpljoin. false. apply H0; eexists; eauto.
Qed. 

Definition has_succ (cd cd': spec_code) : Prop :=
  cd' = cd \/ has_succ0 cd cd'. 


Lemma succ_step_preserve:
  forall sc cd0 cd cd' O O',
    has_succ cd0 cd ->
    spec_step sc cd O cd' O' ->
    has_succ cd0 cd' \/ cd' = spec_abort \/ (exists vo, cd' = spec_done vo).  
Proof.
  introv Hsu Hsp.
  unfold has_succ in *.
  destruct Hsu as [Heq | Hsu].
  - subst.
    lets H__: step_succ0 Hsp; eauto.
    specializes H__; eauto.
    tauto.
  - lets H__: succ0_step_preserve Hsu Hsp; eauto.
    tauto.
Qed.
