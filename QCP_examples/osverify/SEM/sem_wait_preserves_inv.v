
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
Require Import wait_common_lemmas.

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

Ltac solve_steq :=
  match goal with
    H: ~(_ /\ _ /\ _ /\ _ /\ _) |- _ => false; apply H; auto 
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

Require Import asrt_sat_apis. 

Lemma nml_asrt_eq: 
  forall laust, 
    nml_asrt laust ->
    laust = {| tskpt := PtNormal |}. 
Proof.
  introv Hna.
  unfolds in Hna.
  auto. 
Qed.

Lemma sem_wait_preserves_inv_: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semwait vl)) k = Some cd ->
    head_asrt_sat cd lau -> 
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
  introv Hnth Hhsat Hstep Hneq Hct Hlau Hlau' Hsatinv.
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

  simpl in Hnth.
  symexe k.
  symexe k. 
  symexe k. 
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.  
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
  (* k=27 *)
  simpl in Hnth.
  inverts Hnth.
  {
    invstep0.
    invstep0.
    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.  

    eapply dtinv_sem_pend_inst_get_succ_preserve; eauto.

    invstep0.
    {
      match goal with
        H: sem_pend_inst_get_succ _ _ _ |- _ => inverts H
      end.
      simpljoin. rem_dis.
      solve_steq.
    }
    invstep0; solve_endabt. 
  }

  destruct k.
  (* k=28 *)
  simpl in Hnth.
  inverts Hnth.
  simpl in Hhsat. 
  {
    inverts Hstep.
    invstep0.
    invstep0.
    invstep0.
    invstep0.
    invstep0.
    invstep0.
    invstep1.
    invstep0.
    invstep0.
    invstep0.    
    eapply dtinv_sem_pend_block_preserve; eauto.
    {
      match goal with
        H: context[sem_pend_block] |- _ => inverts H
      end.
      simpljoin.
      inv_lst. eexists; eauto. 
    }
    {
      eapply nml_asrt_eq in Hhsat; eauto.
      congruence.
    }
    {
      invstep1.
      invstep0.
      invstep0.
      invstep1.
    }
    invstep1.
    invstep0.
    invstep1.
    invstep0; solve_endabt. 
    solve_endabt.
    invstep0; solve_endabt.
  }

  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  
  destruct k. 
  simpl in Hnth.
  inverts Hnth.
  simpl in Hhsat. 
  {
    invstep0.
    invstep0.
    invstep0.
    invstep1. 
    invstep0.
    invstep0.
    invstep0.    
    {
      match goal with
        H: context [sem_pend_timeout_err_rdy] |- _ =>
          assert (Hspt:=H); inverts H; simpljoin
      end.
      inv_lst.
      unfolds in Hhsat.
      rewrite Hhsat in Hlau.
      simpl in Hlau.
      kvext O0 curtid O.
      l_rew21 (get O curtid).
      eapply dtinv_sem_pend_to_preserve; eauto.
    }
    invstep1; solve_endabt.
    invstep1.
    invstep0.
    invstep1.
    invstep0; solve_endabt. 
    invstep0.
    invstep0; solve_endabt. 
  }
  
  destruct k. 
  simpl in Hnth.
  inverts Hnth.
  simpl in Hhsat. 
  {
    invstep0.
    invstep0.
    invstep0.
    invstep1.
    invstep0.
    invstep0.
    invstep0.
    {
      match goal with
        H: context [sem_pend_block_get_succ] |- _ =>
          assert (Hspt:=H); inverts H; simpljoin
      end.
      inv_lst.
      unfolds in Hhsat.
      rewrite Hhsat in Hlau.
      simpl in Hlau.
      kvext O0 curtid O.
      l_rew21 (get O curtid).
      eapply dtinv_sem_block_get_preserve; eauto.
    }
    invstep0.
    invstep1; solve_endabt.
    inverts H0; solve_endabt. 
    invstep1. 
    invstep0.
    invstep1.
    invstep0; solve_endabt.
    invstep0.
    invstep0; solve_endabt. 
  }
    
  symexe k.
  symexe k.
  symexe k.
  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false.   

Qed. 

    
  
 
