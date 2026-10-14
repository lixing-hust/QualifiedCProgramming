
Require Import memory. 
Require Import PIF_language.

Require Import PIF_sys. 


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

| hs_loop1 ini cond body vl vl':
  has_succ0 (spec_loop ini cond body) (spec_seq (body vl vl') (spec_lp vl' cond body))

| hs_loop2 ini cond vl vl' body cd:
  has_succ0 (body vl vl') cd ->
  has_succ0 (spec_loop ini cond body) (spec_seq cd (spec_lp vl' cond body))

| hs_loop3 ini cond body vl: 
  has_succ0 (spec_loop ini cond body) (spec_lp vl cond body)
. 

(* | hs_lp1 cond body vl vl': *)
(*   has_succ0 (spec_lp vl cond body) (spec_seq (body vl vl') (spec_lp vl' cond body)) *)

(* | hs_lp2 cd cond body vl vl': *)
(*   has_succ0 (spec_seq (body vl vl') (spec_lp vl' cond body)) cd -> *)
(*   has_succ0 (spec_lp vl cond body) cd *)
(* . *)


Require Import PIF_memory.
Require Import PIF_opsem. 


Inductive has_spec_lp: spec_code -> Prop :=
  hs_lp vl cond body:
    has_spec_lp (spec_lp vl cond body)

| hs_seq cd1 cd2:
  (has_spec_lp cd1 \/ has_spec_lp cd2) -> 
  has_spec_lp (spec_seq cd1 cd2)

| hs_chc cd1 cd2:
  (has_spec_lp cd1 \/ has_spec_lp cd2) -> 
  has_spec_lp (spec_choice cd1 cd2)

| hs_loop ini cond body vl vl':
  has_spec_lp (body vl vl') -> 
  has_spec_lp (spec_loop ini cond body). 
  

Lemma step_succ0:
  forall sc cd cd' O O',
    spec_step sc cd O cd' O' ->
    (~has_spec_lp cd) -> 
    has_succ0 cd cd' \/ cd' = spec_abort \/ (exists vo, cd' = spec_done vo).  
Proof.
  introv Hsp.
  inductions Hsp; 
    try (right; right; eexists; eauto; fail);
    try (right; left; eauto; fail);
    try (left; constructors; fail);
    introv Hn.
  - left.
    specializes IHHsp; eauto. 
    introv Hf. apply Hn. constructors. left; auto.
    destruct IHHsp as [Hsu_ | [Habt | Hend]].
    * constructors. auto. 
    * simpljoin. false. 
    * simpljoin. false; apply H; eexists; eauto. 
  - false.
    apply Hn.
    constructors. 
Qed. 

Lemma succ0_step_preserve:
  forall sc cd0 cd cd' O O',
    has_succ0 cd0 cd ->
    ~has_spec_lp cd0 -> 
    spec_step sc cd O cd' O' ->
    has_succ0 cd0 cd' \/ cd' = spec_abort \/ (exists vo, cd' = spec_done vo).  
Proof.
  introv Hsu.
  remember cd0 as CD0.
  remember cd as CD.
  gen cd0 cd cd'.
  inductions Hsu; introv Heq1 Heq2 Hn Hstep; subst; 
    try (
        lets H__: step_succ0 Hstep; eauto;  
        specializes H__; eauto; 
        [introv Hf; apply Hn; simpl; constructors; auto 10 | 
          destruct H__ as [Hsu_ | [Habt | Hend]]; 
          [left; constructors; eauto | 
            right; auto | 
            right; right; eauto]
        ]; fail        
      );
    try (
        specializes IHHsu; eauto;
        [introv Hf; apply Hn; simpl; constructors; auto 10 |  
          destruct IHHsu as [Hsu_ | [Habt | Hend]]; 
          [left; constructors; eauto | 
            right; auto | 
            right; right; eauto]
        ]; fail
      ).
  -
    inverts Hstep.
    + left. constructors.
    + right; left; auto.
    + left. specializes IHHsu; eauto.
      introv Hf. apply Hn; simpl; constructors. auto 10. 
      destruct IHHsu as [Hsu_ | [Habt | Hend]].
      * constructors; auto.
      * subst. simpljoin. false.
      * simpljoin. false; eapply H0; eauto. 
  -
    inverts Hstep. 
    + left. constructors. 
    + right; left; auto.
    + lets H__: step_succ0 H2; eauto. 
      specializes H__; eauto.
      introv Hf. apply Hn. constructors. eauto.
      destruct H__ as [Hsu_ | [Habt | Hend]].
      * left. constructors. eauto.
      * subst. simpljoin. false.
      * simpljoin. false. apply H0. eexists; eauto.
  -
    inverts Hstep.
    + left. constructors. 
    + right; left; eauto.
    + specializes IHHsu; eauto.
      introv Hf. apply Hn; eauto. constructors. eauto. 
      destruct IHHsu as [Hsu_ | [Habt | Hend]].
      * left. constructors; eauto.
      * subst. simpljoin. false.
      * simpljoin. false; eapply H0; eauto. 
  -
    inverts Hstep.
    + left. constructors. 
    + right; right; eexists; eauto. 
Qed. 

Definition has_succ (cd cd': spec_code) : Prop :=
  cd' = cd \/ has_succ0 cd cd'. 


Lemma succ_step_preserve:
  forall sc cd0 cd cd' O O',
    has_succ cd0 cd ->
    ~has_spec_lp cd0 -> 
    spec_step sc cd O cd' O' ->
    has_succ cd0 cd' \/ cd' = spec_abort \/ (exists vo, cd' = spec_done vo).  
Proof.
  introv Hsu Hlp Hsp.
  unfold has_succ in *.
  destruct Hsu as [Heq | Hsu].
  - subst.
    lets H__: step_succ0 Hsp; eauto.
    specializes H__; eauto.
    tauto.
  - lets H__: succ0_step_preserve Hsu Hlp Hsp; eauto.
    tauto.
Qed.




