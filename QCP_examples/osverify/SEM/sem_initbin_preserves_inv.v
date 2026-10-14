
Require Import memory.
Require Import sem_language.
Require Import sem_init.
Require Import sem_invs.
Require Import sem_sys.
Require Import succ_gen.

Require Import join_lib.
Require Import seplog_lemmas.

Require Import sem_tacs. 
Require Import sem_lemmas.
Require Import init_common_lemmas.

Require Import math_auto.

Require Import assms.

Require Import steq_inv_preserve. 

Set Keyed Unification. 

Ltac invstep1 := 
  match goal with H: context [spec_step], H': context [spec_step] |- _ => inverts H end.

Ltac solve_endabt :=
  simpljoin; solve
               [ tryfalse
               | false;
                 match goal with
                   H: ~(exists _, END _ = END _) |- _ => apply H; eexists; eauto 
                 | H: ABORT <> ABORT |- _ => apply H; auto
                 end]. 

Set Printing Depth 1000.

(* for debugging *) 
Ltac symexe_ :=
  match goal with
    H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; idtac "inverts a step"
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; idtac "inverts an atomic op"
  | H: ~(get ?O _ = get ?O _ /\ _ /\ _ /\ _ /\ ?lau = ?lau) |- _ => false; apply H; splits; auto; idtac "solve_steq"
  | H: _ :: _ = _ :: _ |- _ => inverts H; idtac "inverts equality of lists"
  | H: _ \/ _ /\ Some _ = None |- _ => inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: _ /\ None = Some _ \/ _ |- _=> inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: _ /\ Some _ = None \/ _ |- _ => inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: _ \/ _ /\ None = Some _ |- _ => inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: Some _ = Some _ |- _ => inverts H; idtac "inv_some"
  | H: Some _ = None |- _ => inverts H; idtac "Some _ = None" 
  | H: None = Some _ |- _ => inverts H; idtac "None = Some _"
  | H: join ?O0 ?Of ?O, H': join ?O0 ?Of ?O' |- _ =>
      assert (O = O') by (join auto); subst; idtac "same O"
  | _ => idtac
  end.

Ltac symexe0 :=
  match goal with
    H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; symexe0
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; symexe0
  | H: ~(get ?O _ = get ?O _ /\ _ /\ _ /\ _ /\ ?lau = ?lau) |- _ => false; apply H; splits; auto; symexe0
  | H: _ :: _ = _ :: _ |- _ => inverts H; symexe0
  | H: _ \/ _ /\ Some _ = None |- _ => inverts H; simpljoin; tryfalse; symexe0
  | H: _ /\ None = Some _ \/ _ |- _=> inverts H; simpljoin; tryfalse; symexe0
  | H: _ /\ Some _ = None \/ _ |- _ => inverts H; simpljoin; tryfalse; symexe0
  | H: _ \/ _ /\ None = Some _ |- _ => inverts H; simpljoin; tryfalse; symexe0
  | H: Some _ = Some _ |- _ => inverts H; symexe0
  | H: Some _ = None |- _ => inverts H; symexe0
  | H: None = Some _ |- _ => inverts H; symexe0
  | H: join ?O0 ?Of ?O, H': join ?O0 ?Of ?O' |- _ =>
      assert (O = O') by (join auto); subst; symexe0  
  | _ => idtac
  end.

Ltac symexe k :=
  destruct k; [
      match goal with
        H: context [nth_error] |- _ => 
          simpl in H;
          inverts H;
          symexe0        
      end |
      idtac
    ].

Set Printing Depth 1000.

Lemma sem_initbin_preserves_inv_: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (seminitbin vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau') -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hneq Hct Hlau Hlau' Hsatinv.
  repeat (destruct vl; 
          [simpl in Hnth; 
           apply abt_succs_contra in Hnth;
           subst; 
           inverts Hstep | idtac]).
  destruct vl.  
  2: {
    simpl in Hnth. apply abt_succs_contra in Hnth; subst.
    inverts Hstep.
  }

  symexe k. 
  symexe k. 
  symexe k. 
  symexe k. 
  symexe k. 
  symexe k. 
  symexe k. 
  symexe k. 
  symexe k. 

  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.
    {
      assert (Hseq: set laump t lau' = laump).
      { eapply get_set_same; eauto. }
      rewrite Hseq in Hlau'. subst.  
      eapply dtinv_seminit_set_placeholder_preserve; eauto. 
    }
    invstep0.    
    solve_steq.
    invstep0; solve_endabt. 
  }

  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.

    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.  
    
    eapply dtinv_semcre_ecb_activate_preserve; eauto.

    invstep0. 
    {
      match goal with
        H: semcre_ecb_activate _ _ _ |- _ => inverts H
      end.
      simpljoin.
      false. 
    }    
    invstep0; solve_endabt. 
  }

  symexe k.
  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.
    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.
    match goal with
      H: context[seminit_set_ecb_ptr] |- _ => 
        lets H__: seminit_set_ecb_ptr_geq H; eauto
    end.
    specializes H__; eauto.
    false.
    simpljoin.
    eapply Hneq; eauto.

    {
      match goal with
        H: seminit_set_ecb_ptr _ _ _ |- _ => inverts H
      end.
      simpljoin.
      splits; eauto.
      rem_dis; inv_some. 
      lets H__: join_get_same_l atidlsid H12 H13; eauto.
      repeat rewsimp; auto.
      lets H__: join_get_same_l atidlsid H12 H13; eauto.
      repeat rewsimp; auto.      
    }    

    invstep0. 
    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.
    auto.
    invstep0; solve_endabt. 
  }
  
  symexe k.
  symexe k.
  symexe k.
  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.
    match goal with
      H: context[seminit_set_type_bin] |- _ => 
        lets H__: seminit_set_type_bin_geq H; eauto
    end.
    specializes H__; eauto.
    simpljoin. 
    false. 
    eapply Hneq; eauto.

    {
      match goal with
        H: seminit_set_type_bin _ _ _ |- _ => inverts H
      end.
      simpljoin.
      inv_some.
      lets H__: join_get_same_l atidlsid H12 H13; eauto.
      repeat rewsimp; auto.
    }

    invstep0. 
    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.
    auto.
    invstep0; solve_endabt. 
  }

  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    match goal with
      H: context[seminit_set_sem] |- _ => 
        lets H__: seminit_set_sem_geq H2; eauto
    end.
    specializes H__; eauto.
    simpljoin. 
    false. 
    eapply Hneq; eauto.

    {
      match goal with
        H: seminit_set_sem _ _ _ |- _ => inverts H
      end.
      simpljoin.
      rem_dis.
      inv_some.
      lets H__: join_get_same_l atidlsid H11 H12; eauto.
      repeat rewsimp; auto.      
    }

    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.
    auto.         
  }

  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false. 

Qed. 

  
