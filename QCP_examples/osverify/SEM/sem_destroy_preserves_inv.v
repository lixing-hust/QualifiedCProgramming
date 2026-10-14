
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

Lemma cond_ge_sem_destroy_preserve:
  forall gau els gau' els' eid n ga, 
    cond_pv1 gau els ->
    join els' (sig eid (abssem n, nil)) els ->
    join gau' (sig eid ga) gau -> 
    cond_pv1 gau' els'.
Proof.
  introv Hcg Hjoe Hjog.
  unfold cond_pv1 in *.
  introv Hg'.
  assert (Hge_: get els eid0 = Some (abssem n0, wls)).
  {
    eapply join_get_get_l; eauto. 
  }
  assert (Hneq: eid0 <> eid).
  {
    clear- Hjoe Hg'.
    introv Heq.
    subst.
    false. 
    eapply map_join_get_some with (x:=els') (y:=sig eid (abssem n, nil)); eauto.
    rewrite get_a_sig_a. eauto. 
  }
  specializes Hcg; eauto.
  simpljoin.
  split; eauto.
  eexists.
  split; eauto.
  eapply join_get_or in Hjog; eauto.
  destruct Hjog.
  auto. 
  rewrite get_a_sig_a' in H2; eauto.
  false.
Qed.

Lemma cond_aux_sem_destroy_preserve:
  forall els tls ts gaump laump els' gaump' n ga eid, 
    cond_pv0 els tls ts gaump laump ->
    join els' (sig eid (abssem n, nil)) els -> 
    join gaump' (sig eid ga) gaump -> 
    cond_pv0 els' tls ts gaump' laump.
Proof.
  introv Hca Hjoe Hjog.
  unfold cond_pv0 in *.
  introv Hge'.
  assert (Hge_: get els eid0 = Some (abssem n0, wls)).
  {
    eapply join_get_get_l; eauto. 
  }
  assert (Hneq: eid0 <> eid).
  {
    clear- Hjoe Hge'.
    introv Heq.
    subst.
    false. 
    eapply map_join_get_some with (x:=els') (y:=sig eid (abssem n, nil)); eauto.
    rewrite get_a_sig_a. eauto. 
  }
  specializes Hca; eauto.
  destruct Hca as (ga_ & Hgg & Heqv).
  eapply join_get_or in Hjog; eauto.
  destruct Hjog.
  eexists. split; eauto.
  rewrite get_a_sig_a' in H; eauto. 
  false. 
Qed.

Lemma wait_progpt_sem_destroy_preserve: 
  forall els laump els' eid n, 
    wait_progpt els laump ->
    join els' (sig eid (abssem n, nil)) els ->
    wait_progpt els' laump.
Proof.
  introv Hwp Hjo.
  unfold wait_progpt in *.
  introv Hg'.
  assert (Hge_: get els eid0 = Some (abssem n0, wls)).
  {
    eapply join_get_get_l; eauto. 
  }
  assert (Hneq: eid0 <> eid).
  {
    clear- Hjo Hg'.
    introv Heq.
    subst.
    false. 
    eapply map_join_get_some with (x:=els') (y:=sig eid (abssem n, nil)); eauto.
    rewrite get_a_sig_a. eauto. 
  }
  introv Hin.
  specializes Hwp; eauto.
Qed.

Lemma dtinv_sem_destroy_succ_preserve:
  forall O0 O0' Of O O' v v' laump, 
    dtinv O laump ->
    join O0 Of O ->
    semdestroy_succ (v :: nil) O0 (v', Some O0') ->     
    join O0' Of O' -> 
    (forall a : addrval,
        semdestroy_succ (|v :: nil|) = semdestroy_succ (|Vptr a :: nil|) ->
        exists pbls posv semeibs eid tp ts,
          get O pblsid = Some (pblist pbls) /\
            get pbls a = Some posv /\
            get O seminfoid = Some (seminfo semeibs) /\
            get semeibs posv = Some (infotid eid, tp) /\
            get O atidlsid = Some (atidls ts) /\
            (forall t : tid, In t ts -> get laump t <> Some {| tskpt := PtPend (Vptr eid) |})) -> 
    dtinv O' laump.       
Proof.
  introv Hdti Hjo Hss Hjo' Hassm.
  inverts Hss.
  simpljoin.
  inv_some.
  inv_lst.
  unfold dtinv in *.
  simpljoin.
  kvext O0 absecblsid O.
  kvext O0 gauxstid O.
  l_rew21 (get O absecblsid).
  l_rew21 (get O gauxstid).
  kvext_h Hjo' gauxstid O'.
  kvext_h Hjo' absecblsid O'. 
  assert (Hgteq: get O abstcblsid = get O' abstcblsid). 
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto. 
    repeat rewsimp. auto. 
  }
  assert (Hteq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto. 
    repeat rewsimp. auto.         
  }
  rewrite <- Hgteq.
  rewrite <- Hteq.
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto. 
  split; eauto.
  match goal with
    H: join ?e' (sig ?i (abssem _, _)) ?e |- _ =>
      rename e' into els'; rename e into els; rename i into eid
  end.
  match goal with
    H: get O' gauxstid = Some (gauxst ?x) |- _ =>
      rename x into gau'
  end.
  match goal with
    H: cond_pv1 ?g els |- _ => rename g into gau
  end.

  splits.
  - (* atids_valid *)
    auto.
  - (* cond_pv1 *) 
    eapply cond_ge_sem_destroy_preserve; eauto.
  - (* cond_pv0 *) 
    eapply cond_aux_sem_destroy_preserve; eauto.
  - (* wait_progpt *) 
    eapply wait_progpt_sem_destroy_preserve; eauto.        
  - (* none_progpt *) 
    unfold none_progpt in *.
    introv Hnex Hin.
    specialize (Hassm _ (eq_refl _)).
    simpljoin. 
    clear Hteq. 
    l_rew21 (get O atidlsid).
    kvext O0 seminfoid O.
    l_rew21 (get O seminfoid).
    kvext O0 pblsid O.
    l_rew21 (get O pblsid).
    casetac eid eid0 Ht Hf.
    +
      subst.
      assert (x1 = x7).
      {
        rewrite H4 in H25.
        inverts H25. auto. 
      }
      subst.
      assert (x9 = eid0).
      {
        rewrite H7 in H27.
        inverts H27.
        auto. 
      }
      subst.
      eapply H29; eauto.
    +
      assert (Hne: ~ (exists n wl, get els eid0 = Some (abssem n, wl))).
      {
        introv Hex.
        apply Hnex.
        destruct Hex as (n & wl & Hge).
        match goal with
          H: join els' _ els |- _ => eapply join_get_or in H; eauto; rename H into Hor
        end.
        rewrite get_a_sig_a' in Hor; eauto. 
        destruct Hor.
        do 2 eexists; eauto.
        false. 
      }
      eauto.
Qed.

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

Definition no_pend_on_deletion cd O laump := 
    (forall a,
        cd = semdestroy_succ (| (Vptr a) :: nil |) ->
        exists pbls posv semeibs eid tp ts,
          get O pblsid = Some (pblist pbls) /\ 
            get pbls a = Some posv /\ 
            get O seminfoid = Some (seminfo semeibs) /\
            get semeibs posv = Some (infotid eid, tp) /\
            get O atidlsid = Some (atidls ts) /\
            forall t, In t ts -> get laump t <> Some {| tskpt := PtPend (Vptr eid) |} 
    ). 
  
Lemma sem_destroy_preserves_inv_: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semdestroy vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau') -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    no_pend_on_deletion cd O laump -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hneq Hct Hlau Hlau' Hassm Hsatinv.
  unfolds in Hassm. 
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
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.

    assert (Hseq: set laump t lau' = laump).
    { eapply get_set_same; eauto. }
    rewrite Hseq in Hlau'. subst.  

    eapply dtinv_sem_destroy_succ_preserve; eauto.

    {
      match goal with
        H: semdestroy_succ _ _ _ |- _ => inverts H
      end.
      simpljoin. false. 
    }
    
  }

  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false.
  
Qed. 

