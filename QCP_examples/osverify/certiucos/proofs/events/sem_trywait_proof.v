Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import os_sem_cap.
Require Import ifun_spec.
Require Import abs_op.

(* absimp lemmas *)
Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.

Require Import sem_common.
Require Import gjb_common.
Require Import gjb_sem_common.

Require Import ev_aux_code.
Require Import pos_list_common.
Require Import seplog_trm_tacs. 
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.

Lemma semtrywait_absimp_semerr_abt:
  forall sch v'4 v P s,
    (cmpaddr Cle v'4 userAddrStart = true \/ cmpaddr Clt userAddrEnd v'4 = true) ->  
    v <> Vint32 Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (semtrywait_semerr (|Vptr v'4 :: v :: nil|)
              ?? semtrywait_sem_pos (|Vptr v'4 :: v :: nil|));; s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semtrywait_absimp_semerr_cont: 
  forall sch vsem v P s,
    (vsem = Vnull \/
       exists v'4, vsem = Vptr v'4 /\ 
                     (cmpaddr Cle v'4 userAddrStart = true \/
                        cmpaddr Clt userAddrEnd v'4 = true)) ->   
    v = Vint32 Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (semtrywait_semerr (|vsem :: v :: nil|)
              ?? semtrywait_sem_pos (|vsem :: v :: nil|));; s ||>  ** P)
      (<|| s ||> ** P). 
Proof.
intros.
substs.
eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
2 : { eapply absinfer_seq_end; eauto. }
infer_solver 0%nat.
Qed.

Lemma semtrywait_absimp_semok_abt_null:
  forall sch v P s,
    can_change_aop P ->
    v <> Vint32 Int.mone -> 
    absinfer sch
      (<|| (semtrywait_semerr (|Vnull :: v :: nil|)
              ?? semtrywait_sem_pos (|Vnull :: v :: nil|));; s ||>  ** P)
      (<|| ABORT ||> ** P).
Proof.
intros.
eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
eapply absinfer_seq; try eauto.
eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
eapply absinfer_abt; try eauto.
absimp_abt_solver.
Qed.

Lemma semtrywait_absimp_sem_get_none:
  forall sch v'4 v pbls P s,
    cmpaddr Clt userAddrStart v'4 = true ->
    cmpaddr Cle v'4 userAddrEnd = true -> 
    get pbls v'4 = None -> 
    can_change_aop P ->
    absinfer sch
     (<|| (semtrywait_semerr (|Vptr v'4 :: v :: nil|)
             ?? semtrywait_sem_pos (|Vptr v'4 :: v :: nil|));; s ||>  ** Hpbls pbls ** P) 
     (<|| ABORT ||>  ** Hpbls pbls ** P).
Proof.
  introv Hrgn1 Hrgn2 Hnone Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_choice2.
  pure_auto. pure_auto.
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt.
  pure_auto. pure_auto.
  absimp_abt_solver.
  right. 
  eexists; eauto. splits; eauto. 
  destruct H. simpljoin1. 
  simpl in H3. destruct H3.
  simpl in H2. subst x2.
  eapply join_sig_get; eauto. 
  pure_auto. 
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma semtrywait_absimp_sem_get_outtype_err_abt:
  forall sch v'4 v P s,
    cmpaddr Clt userAddrStart v'4 = true ->
    cmpaddr Cle v'4 userAddrEnd = true -> 
    ~(exists i, v = Vint32 i) -> 
    can_change_aop P ->
    absinfer sch
     (<|| (semtrywait_semerr (|Vptr v'4 :: v :: nil|)
             ?? semtrywait_sem_pos (|Vptr v'4 :: v :: nil|));; s ||>  ** P)
     (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn1 Hrgn2 Htp Hcop. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_choice2; try pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt; try pure_auto. 
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto. 
  Unshelve.
  exact None. 
Qed. 

Lemma semtrywait_absimp_sem_get_pos_abt: 
  forall sch vsem pbls posv v P s, 
    cmpaddr Clt userAddrStart vsem = true ->
    cmpaddr Cle vsem userAddrEnd = true -> 
    get pbls vsem = Some posv ->
    v <> Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<|| (semtrywait_semerr (|Vptr vsem :: v :: nil|) ??
             semtrywait_sem_pos (|Vptr vsem :: v :: nil|));; s ||> ** Hpbls pbls ** P)
     (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  can_change_aop_solver. 
  eapply absinfer_choice2.
  pure_auto.
  pure_auto.
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  right. eexists; splits; eauto.
  pure_auto.
  destruct H. simpljoin1. 
  simpl in s1. destruct s1.
  subst x2.
  simpl in j0. 
  eapply join_sig_get; eauto. 
  left. eexists; splits; eauto.
  pure_auto. 
  eapply absinfer_seq_abt; pure_auto.
Qed.  

Lemma semtrywait_absimp_sem_get_pos_ok: 
  forall sch vsem pbls posv v P s, 
    cmpaddr Clt userAddrStart vsem = true ->
    cmpaddr Cle vsem userAddrEnd = true -> 
    get pbls vsem = Some posv ->
    v = Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<|| (semtrywait_semerr (|Vptr vsem :: v :: nil|) ??
             semtrywait_sem_pos (|Vptr vsem :: v :: nil|));; s ||> ** Hpbls pbls ** P)
     (<||s||> ** Hpbls pbls ** P).
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto. 
  eapply absinfer_choice2; try pure_auto. 
  infer_solver 0%nat.  
  repeat eexists; eauto.
  right. exists pbls. 
  splits; eauto. 
  destruct H. simpljoin1. simpl in H3. simpl in H2.
  destruct H3. 
  subst x2.
  eapply join_sig_get; eauto.
  left. 
  eexists; splits; eauto.
Qed.

Lemma semtrywait_absimp_poserr0:
  forall posv v1 v4 P sch s,
    v1 = Vint32 posv ->
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    v4 = Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch
      ( <|| (semtrywait_poserr (|v1::v4::nil|) ??  s) ||> ** P)
      ( <|| END (Some  (Vint32 (Int.mone))) ||> ** P ).
Proof.
  infer_solver 0%nat.  
  subst v1.
  do 2 eexists. splits; eauto.
  left. splits; auto. subst v4. auto.
Qed.

Lemma semtrywait_absimp_poserr_abt:
  forall posv v1 v4 P sch s0,
    v1 = Vint32 posv ->
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    v4 <> Vint32 (Int.mone) -> 
    can_change_aop P -> 
    absinfer sch
      ( <|| semtrywait_poserr (|Vint32 posv::v4::nil|) ?? s0 ||> ** P)
      ( <|| ABORT ||> ** P ).
Proof.   
  unfold semtrywait.
  introv Hv1 Hrgn Hv4 Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice1; try eauto.
  eapply absinfer_abt; try can_change_aop_solver.
  absimp_abt_solver.
  Unshelve.
  exact (None).
Qed.

Lemma semtrywait_absimp_posok_choice:
  forall posv v4 P sch s0,
    (Int.ltu posv Int.zero = false /\
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| semtrywait_poserr (|Vint32 posv::v4::nil|) ??  s0 ||> ** P) 
      (<|| s0 ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  pure_auto.
Qed.

Lemma semtrywait_absimp_before_abt_hold: 
  forall i tp sembls sch v P s0 sc, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get sembls i = Some (infohold, tp, sc) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| semtrywait_get_ecb_ptr (|Vint32 i :: v :: nil|);; s0 ||>  ** HSEMInfo sembls ** P) 
      (<|| ABORT ||>  ** HSEMInfo sembls ** P). 
Proof. 
  introv Hrgn Hsi Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  right. split; auto. left. split. intro. destruct H0. inv H0. intro Hf. inv Hf.
  pure_auto.
  eapply absinfer_seq_abt; auto.
  pure_auto.
  pure_auto.
  Unshelve.
  exact None.
Qed.  

Lemma semtrywait_absimp_before_abt_hold2:
  forall (i : int32) (tp : sem_tp) (i1 i2 : int32) (sembls : EmbMod.map)
         (sch : ossched) (v vv : val) (P : asrt) s0 sc,
    Int.ltu i Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> $ (OS_USER_MAX_EVENTS / 3) ->
    get sembls i = Some (infohold, tp, sc) ->
    can_change_aop P ->
    sch
      ⊢  <|| (semtrywait_get_ecb_ptr1 (|Vint32 i :: vv :: nil|) ?? 
                  semtrywait_get_ecb_ptr2 (|Vint32 i :: vv :: nil|) ??
                  semtrywait_ecb_ptr_holder_abt (|Vint32 i :: vv :: nil|));; s0 ||> **
             HSEMInfo sembls ** P
           ⇒  <|| ABORT ||>  ** HSEMInfo sembls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. 2: eauto. can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. 2: eauto. can_change_aop_solver.  
  eapply absinfer_abt; try pure_auto.
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  can_change_aop_solver.
  eapply absinfer_seq_abt; auto.
  pure_auto.
  pure_auto.
  Unshelve.
  exact None.
Qed.

Lemma semtrywait_absimp_before_abt_out: 
  forall i eo tp sembls v sch P s0 sc, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get sembls i = Some (eo, tp, sc) -> 
         ((exists eid, eo = infotid eid /\ v <> Vptr eid) \/ eo = infonull /\ v <> Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| semtrywait_get_ecb_ptr (|Vint32 i :: v :: nil|);; s0 ||>  ** HSEMInfo sembls ** P)
           (<|| ABORT ||>  ** HSEMInfo sembls ** P). 
Proof.
  introv Hrgn Hsi Hcs Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  pure_auto. 
  eapply absinfer_seq_abt; auto.
  pure_auto.
  pure_auto.
  Unshelve.
  exact None.
Qed.

Lemma semtrywait_absimp_before_abt_out2: 
  forall i eo tp sc sembls v sch P s0 ptrmp t eid, 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get sembls i = Some (eo, tp, sc) -> 
    ((eo = infotid eid /\ v <> Vptr eid) \/ eo = infonull /\ v <> Vnull) -> 
    get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
          (<|| (semtrywait_get_ecb_ptr1 (|Vint32 i :: v :: nil|) ??
                   semtrywait_get_ecb_ptr2 (|Vint32 i :: v :: nil|) ?? 
                   semtrywait_ecb_ptr_holder_abt (| Vint32 i :: v :: nil |));; s0 ||>  ** 
                 HSEMInfo sembls ** HEvPtr ptrmp ** HCurTCB t ** P)
           (<|| ABORT ||>  ** HSEMInfo sembls ** HEvPtr ptrmp ** HCurTCB t ** P).  
Proof.
  introv Hrgn Hsi Hcs Hgetp Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq1.
  pure_auto.
  instantiate (1:=ABORT).
  destruct Hcs.
  -
    eapply absinfer_trans.
    eapply absinfer_choice2.
    can_change_aop_solver.
    2: eauto. can_change_aop_solver.
    eapply absinfer_trans.
    eapply absinfer_choice1.
    can_change_aop_solver.
    2: eauto. can_change_aop_solver.
    apply absinfer_abt.
    pure_auto.
    pure_auto.
    simpljoin1.
    absimp_abt_solver.
    apply i_ge_z; auto.
    apply i_lt_user_max_event; auto.
    instantiate (1:=HSEMInfo sembls ** HCurTCB t ** P).
    instantiate (1:=semtrywait_get_ecb_ptr2 (|Vint32 i :: v :: nil|)).
    instantiate (1:=s).
    sep auto.
    instantiate (1:=HSEMInfo sembls ** HEvPtr ptrmp ** P).
    instantiate (1:=semtrywait_get_ecb_ptr2 (|Vint32 i :: v :: nil|)).
    instantiate (1:=s).
    sep auto.
    can_change_aop_solver.
  -
    eapply absinfer_trans.
    eapply absinfer_choice1.
    can_change_aop_solver.
    2: eauto. can_change_aop_solver.
    apply absinfer_abt.
    pure_auto.
    pure_auto.
    simpljoin1.
    absimp_abt_solver.
    can_change_aop_solver.
  -
    eapply absinfer_seq_abt; auto.
    pure_auto.
    pure_auto.
    Unshelve.
    exact None. trivial. exact None. trivial. trivial. exact infonull. trivial. trivial. trivial. trivial. auto.
Qed.

Lemma semtrywait_absimp_if_null_yes_abt: 
  forall i v sch v1 P s0, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         v = Vnull -> 
         v1 <> Vint32 Int.mone -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| semtrywait_if_null_yes (|v :: v1 :: nil|) ?? s0 ||>  **  P) 
           (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn Hv Hv1 Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
Qed.

Lemma semtrywait_absimp_if_null_yes_end: 
  forall i v sch v1 P s0, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         v = Vnull -> 
         v1 = Vint32 Int.mone -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| semtrywait_if_null_yes (|v :: v1 :: nil|) ?? s0 ||>  **  P) 
           (<|| END (Some (Vint32 Int.mone)) ||>  ** P). 
Proof.
  introv Hrgn Hv Hv1 Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  infer_solver 0%nat.
  eexists. splits; eauto.
  subst v. auto.
Qed.

Lemma semtrywait_absimp_before_ok: 
  forall i eo tp sc sembls v sch P s0, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get sembls i = Some (eo, tp, sc) -> 
         (exists eid,  eo = infotid eid /\ v = Vptr eid) \/ eo = infonull /\ v = Vnull ->
         can_change_aop P -> 
         absinfer sch 
           (<|| semtrywait_get_ecb_ptr (|Vint32 i :: v :: nil|);; s0 ||>  ** HSEMInfo sembls ** P)
           (<|| s0 ||>  ** HSEMInfo sembls ** P).  
Proof.
  introv Hrgn Hsi Heo Hcop.   
  infer_solver 0%nat.  
  destruct s as [[[[]]]].
  destruct H. simpljoin1. 
  destruct H3.
  simp_mem_abst.
  change_smo_hyps.
  simpl in H. simpl in H1.
  exists v. exists i.
  exists sembls.
  inversion Heo.
  destruct H3 as (eid & Heo' & Hv).
  
  exists (infotid eid). 
  do 2 eexists. 
  splits; eauto.
  split. 
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  subst x2.
  eapply join_sig_get; eauto.
  rewrite <- Heo'. eauto.
  left. split; auto. left. 
  eexists. split; eauto.

  exists eo. do 2 eexists. 
  splits; eauto.
  split. 
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  subst x2.
  eapply join_sig_get; eauto.

  Unshelve. 
  exact None.
Qed.

Lemma semtrywait_absimp_before_ok2_null: 
  forall i eo tp sc sembls sch vv P t ptrmp s0, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get sembls i = Some (eo, tp, sc) -> 
         eo = infonull /\ vv = Vnull ->
         get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<|| (semtrywait_get_ecb_ptr1 (|Vint32 i :: vv :: nil|) ??
                    semtrywait_get_ecb_ptr2 (|Vint32 i :: vv :: nil|) ?? 
                    semtrywait_ecb_ptr_holder_abt (|Vint32 i :: vv :: nil|));; s0 ||>  **  
             HSEMInfo sembls ** HEvPtr ptrmp ** HCurTCB t ** P) 
           (<|| s0 ||>  ** HSEMInfo sembls ** HEvPtr ptrmp ** HCurTCB t ** P). 
Proof.
  introv Hrgn Hsi Heo Hptr Hcop.
  simpljoin1.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HSEMInfo sembls ** HEvPtr ptrmp ** HCurTCB t ** P).
  can_change_aop_solver.
  instantiate (1:=END None).
  infer_solver 0%nat.  
  destruct s as [[[[]]]].
  destruct H. simpljoin1. 
  simp_mem_abst.
  change_smo_hyps.

  do 9 eexists.
  left.
  splits; eauto.
  split.
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  simpl in H6. simpljoin1. 
  eapply join_sig_get; eauto.
  simpl in H7. simpljoin1.
  eapply join_sig_get; eauto.
  assert (Hjo': join x3 x2 O) by join auto.
  eapply join_join_merge23_join; eauto.
  sep remember (2::nil)%nat in H7.
  simpl in H7. simpljoin1.
  eapply join_sig_get; eauto.
  assert (Hjo': join x3 x2 O) by join auto.
  eapply join_join_merge23_join; eauto.

  eapply absinfer_seq_end. can_change_aop_solver. can_change_aop_solver.
  intros; eauto.
Qed. 

Lemma semtrywait_absimp_before_ok2_ptr: 
  forall i eid tp sc sembls sch vv P s0 t ptrmp ptrmp', 
    (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get sembls i = Some (infotid eid, tp, sc) -> 
    vv = Vptr eid ->
    get ptrmp t = Some (Vnull, Vnull, Vnull) -> 
    ptrmp' = set ptrmp t (Vnull, Vptr eid, Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
           (<|| (semtrywait_get_ecb_ptr1 (|Vint32 i :: vv :: nil|) ??
                    semtrywait_get_ecb_ptr2 (|Vint32 i :: vv :: nil|) ?? 
                    semtrywait_ecb_ptr_holder_abt (|Vint32 i :: vv :: nil|));; s0 ||>  ** 
             HSEMInfo sembls ** HEvPtr ptrmp ** HCurTCB t ** P) 
           (<|| s0 ||> ** HSEMInfo sembls ** HEvPtr ptrmp' ** HCurTCB t ** P). 
Proof.
  introv Hrgn Hsi Hvv Hptr Hptr' Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1:=HSEMInfo sembls ** HEvPtr ptrmp' ** HCurTCB t ** P). 
  can_change_aop_solver.
  instantiate (1:=END None).
  simpljoin1.

  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver.
  2: eauto.
  can_change_aop_solver.
  eapply absinfer_prim.
  can_change_aop_solver.
  can_change_aop_solver.
  unfold absimp.
  introv Hsat.
  eexists. exists (END None).
  split.
  eapply spec_stepS.
  instantiate (2:=END None).
  instantiate (1:=set O evptrid (evptr (set ptrmp t (Vnull, Vptr eid, Vnull)))).
  assert (gamma=semtrywait_get_ecb_ptr2 (|Vint32 i :: Vptr eid :: nil|)).
  simpl in Hsat.  simpljoin1.
  subst.
  eapply spec_prim_step with (O:=O) (O':=set O evptrid (evptr (set ptrmp t (Vnull, Vptr eid, Vnull)))).
  simpl.
  do 8 eexists. splits; eauto.
  split. 
  apply i_ge_z; auto.
  apply i_lt_user_max_event; auto.
  simpl in Hsat. simpljoin1. 
  destruct s as [[[[]]]].
  simpl in *.
  eapply join_sig_get; eauto.
  sep remember (2::nil)%nat in Hsat.  simpl in Hsat. simpljoin1.
  destruct s as [[[[]]]].
  simpl in *. simpljoin1.
  eapply join_sig_get; eauto.
  apply map_join_comm in H6.
  eapply join_join_merge23_join; eauto.
  sep remember (3::nil)%nat in Hsat.
  simpl in Hsat. simpljoin1.
  destruct s as [[[[]]]].
  simpl in *. simpljoin1.  
  eapply join_sig_get; eauto.
  apply map_join_comm in H13.
  eapply join_join_merge23_join; eauto.
  apply map_join_comm in H6.
  eapply join_join_merge23_join; eauto.
  eapply step_prop.eqdomO_set2.
  2: { introv Hf. inverts Hf. }
  sep remember (3::nil)%nat in Hsat.
  simpl in Hsat.  simpljoin1.
  assert (get O evptrid = Some (evptr ptrmp)).
  eapply join_sig_get; eauto.
  join auto.
  unfold tidsame. rewrite set_a_get_a'; eauto.
  join auto.
  join auto.
  eapply spec_stepO.
 
  apply astar_l_aop'_elim in Hsat.
  simpljoin1.
  eapply astar_l_aop'_intro; eauto.
  sep lift 2%nat in H3. sep lift 2%nat.
  eapply cancel_absdata_p; auto.
  2: { sep auto. }
  intros. sep auto.

  eapply absinfer_seq_end.
  can_change_aop_solver. can_change_aop_solver.
  intros; auto.  

  Unshelve. trivial.
Qed.

Lemma semtrywait_absimp_if_null_no: 
  forall i v sch v1 P s0, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         (exists eid, v =Vptr eid) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||semtrywait_if_null_yes (|v :: v1 :: nil|) ??
                 (semtrywait_if_null_no (|v :: nil|);; s0) ||>  **  P)
           (<|| s0 ||>  ** P). 
Proof.
  introv Hrgn Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto.
  instantiate (1:=P). pure_auto. 
  pure_auto.
  infer_solver 0%nat.  
  destruct Hv. exists x.
  splits; eauto. 
  subst v. auto.
Qed. 

Lemma semtrywait_absimp_afteracc1:
  forall  v v' ptrmp t ptrmp' P sch,
    Int.ltu Int.zero v = true ->
    v' = Vint32 Int.zero ->
    can_change_aop P ->
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) -> 
    absinfer sch
      (<|| (semtrywait_after_acc_1 (| Vint32 v :: v':: nil|) ??
              semtrywait_after_acc_2 (| Vint32 v :: v' :: nil|)) ||> ** HCurTCB t ** HEvPtr ptrmp ** P)
      (<|| END (Some (Vint32 Int.zero)) ||> ** HCurTCB t ** HEvPtr ptrmp' ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  can_change_aop_solver. 2: eauto. can_change_aop_solver.
  simpljoin1.
  infer_solver 0%nat.
Qed.

Lemma semtrywait_absimp_afteracc1_abt:
  forall v v' ptrmp t P sch,
    Int.ltu Int.zero v = true ->
    v' <> Vint32 Int.zero ->
    can_change_aop P -> 
    absinfer sch
      (<|| (semtrywait_after_acc_1 (| Vint32 v :: v':: nil|) ??
               semtrywait_after_acc_2 (| Vint32 v :: v' :: nil|)) ||> ** HCurTCB t ** HEvPtr ptrmp ** P)
      (<|| ABORT ||> ** HCurTCB t ** HEvPtr ptrmp ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1. 
  can_change_aop_solver. 2: eauto. can_change_aop_solver.
  eapply absinfer_abt.
  can_change_aop_solver. can_change_aop_solver.
  absimp_abt_solver.  
  instantiate (1:=HCurTCB t ** P).
  instantiate (1:=ptrmp).
  instantiate (1:=semtrywait_after_acc_1 (|Vint32 v :: v' :: nil|)).
  instantiate (1:=s).
  sep auto.
  can_change_aop_solver.
  Unshelve. 
  exact None.
Qed.

Lemma semtrywait_absimp_afteracc2:
  forall  v v' ptrmp t ptrmp' P sch,
    Int.ltu Int.zero v = false ->
    v' = Vint32 Int.mone ->
    can_change_aop P ->
    ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) -> 
    absinfer sch
      (<|| (semtrywait_after_acc_1 (| Vint32 v :: v':: nil|) ??
              semtrywait_after_acc_2 (| Vint32 v :: v' :: nil|)) ||> ** HCurTCB t ** HEvPtr ptrmp ** P)
      (<|| END (Some (Vint32 Int.mone)) ||> ** HCurTCB t ** HEvPtr ptrmp' ** P).  
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. 2: eauto. can_change_aop_solver.
  simpljoin1.
  infer_solver 0%nat.
Qed.

Lemma semtrywait_absimp_afteracc2_abt:
  forall  v v' ptrmp t P sch,
    Int.ltu Int.zero v = false ->
    v' <> Vint32 Int.mone ->
    can_change_aop P -> 
    absinfer sch
      (<|| (semtrywait_after_acc_1 (| Vint32 v :: v':: nil|) ??
               semtrywait_after_acc_2 (| Vint32 v :: v' :: nil|)) ||> ** HCurTCB t ** HEvPtr ptrmp ** P)
      (<|| ABORT ||> ** HCurTCB t ** HEvPtr ptrmp ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  can_change_aop_solver. 2: eauto. can_change_aop_solver.
  eapply absinfer_abt.
  can_change_aop_solver. can_change_aop_solver. 
  absimp_abt_solver.
  instantiate (1:=HCurTCB t ** P).
  instantiate (1:=ptrmp).
  instantiate (1:=semtrywait_after_acc_2 (|Vint32 v :: v' :: nil|)).
  instantiate (1:=s).
  sep auto.
  can_change_aop_solver.

  Unshelve.
  exact None.
Qed.

Open Scope code_scope.

(* copy form OSMutex_common.v *)
Goal forall x y, Int.eq x y = true  -> x=y.
intros.
int auto.
apply unsigned_inj.
auto.
Save inteqeq.
(* end of copy *)

Lemma OSSemTrywaitPartProof:
  forall tid vsem v v0 v1 v4 v5 v6 v7 v'0 v'1 v'2 v'3 vv i jj er,
  {|OS_spec, GetHPrio, OSLInv, I,
  fun v2 : option val =>
  ( <|| END v2 ||>  **
   p_local OSLInv tid init_lg **
   ((EX v3 : val, LV sem @ (long) ∗ |-> v3) **
    (EX v3 : val, LV os_code_defs.pos @ long |-> v3) **
    (EX v3 : val, LV x @ char_t |-> v3) **
    (EX v3 : val, LV y @ Int16u |-> v3) ** 
    (EX v3 : val, LV p @ OS_EVENT ∗ |-> v3)** 
    (EX v3 : val, LV temp_dom @ char_t |-> v3) **
    (EX v3 : val, LV temp_num @ char_t |-> v3)
    ** Aemp) **
   Aie true ** Ais nil ** Acs nil ** Aisr empisr  ** (EX er, Aier er)) **
  A_dom_lenv
    ((sem, (long) ∗)
     :: (os_code_defs.pos, long) :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil), Afalse|}
  |- tid
  {{ <||
    semtrywait_poserr (|Vint32 i :: v1 :: nil|)
    ?? semtrywait_get_ecb_ptr (|Vint32 i :: v :: nil|);;
       (semtrywait_if_null_yes (|v :: v1 :: nil|)
        ?? semtrywait_if_null_no (|v :: nil|);;
           kscurdom_ext (|nil|);;
           get_temp_dom (|v4 :: nil|);;
           get_temp_num (|v5 :: nil|);;
          (pos_lt_rgn_err (|Vint32 i :: v4 :: v5 :: nil|)
           ?? kscurdom_ext (|nil|);;
              get_temp_dom (|v6 :: nil|);;
              get_temp_num (|v7 :: nil|);;
              (pos_ge_rgn_err (|Vint32 i :: v6 :: v7 :: nil|)??
           (semtrywait_get_ecb_ptr1 (|Vint32 i :: vv :: nil|) ?? 
             semtrywait_get_ecb_ptr2 (|Vint32 i :: vv :: nil|) ?? 
             semtrywait_ecb_ptr_holder_abt (|Vint32 i :: vv :: nil|)) ;;
           semacc (vv :: v0 :: nil);;
           (semtrywait_after_acc_1 (|v0 :: v1 :: nil|)
            ?? semtrywait_after_acc_2 (|v0 :: v1 :: nil|))))) ||>  **
    LV os_code_defs.pos @ long |-> Vint32 i **
    LV x @ char_t |-> Vint32 jj **
    LV temp_num @ char_t |-> v'2 **
    LV temp_dom @ char_t |-> v'3 **
    LV p @ OS_EVENT ∗ |-> v'1 **
    LV y @ Int16u |-> v'0 **
    LV sem @ (long) ∗ |-> vsem **
    Aisr empisr **
    Aie true **
    Ais nil **
    Acs nil **
    Aier er **
    p_local OSLInv tid init_lg **
    A_dom_lenv
      ((sem, (long) ∗)
       :: (os_code_defs.pos, long) :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t) ::nil)}} 
  If (′ 0 >ₑ os_code_defs.pos ′ ||ₑ os_code_defs.pos ′ ≥ ′ OS_USER_MAX_EVENTS ÷ ′ 3){RETURN (econst32 (Int.mone))};ₛ
  ENTER_CRITICAL;ₛ
  p ′ =ₑ efield (Sem_info ′ [os_code_defs.pos ′]) pevent;ₛ
  EXIT_CRITICAL;ₛ
  If (p ′ ==ₑ NULL){RETURN (econst32 (Int.mone))};ₛ
  ENTER_CRITICAL;ₛ
  temp_dom ′ =ₑ Domain2Index ′ [ksCurDomain ′];ₛ
  EXIT_CRITICAL;ₛ
  ENTER_CRITICAL;ₛ
  temp_num ′ =ₑ Core_partition_num ′;ₛ
  EXIT_CRITICAL;ₛ
  If (′ OS_USER_MAX_EVENTS ÷ ′ 3 ÷ temp_num ′ × temp_dom ′ >ₑ
      os_code_defs.pos ′){RETURN (econst32 (Int.mone))};ₛ
  ENTER_CRITICAL;ₛ
  temp_dom ′ =ₑ Domain2Index ′ [ksCurDomain ′];ₛ
  EXIT_CRITICAL;ₛ
  ENTER_CRITICAL;ₛ
  temp_num ′ =ₑ Core_partition_num ′;ₛ
  EXIT_CRITICAL;ₛ
  If (os_code_defs.pos ′
      ≥ ′ OS_USER_MAX_EVENTS ÷ ′ 3 ÷ temp_num ′ × (temp_dom ′ +ₑ ′ 1))
  {RETURN (econst32 (Int.mone))};ₛ
  ENTER_CRITICAL;ₛ
  p′ =ₑ efield (Sem_info′[os_code_defs.pos′]) pevent;ₛ
  OSTCBCur′→__OSTskSemPtr =ₑ p′;ₛ 
  EXIT_CRITICAL;ₛ
  y ′ =ᶠ OSSemAccept (·p ′·);ₛ
  ENTER_CRITICAL;ₛ
  OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ 
  EXIT_CRITICAL;ₛ
  If (y ′ >ₑ ′ 0){RETURN ′ 0};ₛ
  RETURN (econst32 (Int.mone)) {{Afalse}}. 
Proof.
  intros.
  
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  assert (Hdiveq: (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3))).
  { unfold Int.divs in *.
     rewrite zdiv_equiv in *.
     rewrite Hsieq in *.
     auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
  }
  assert (Hchg: Int.eq ($ 3) Int.zero ||
                Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) && 
                Int.eq ($ 3) Int.mone = false).
  { rewrite Heqf.
     change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
     auto.
  }

  hoare forward;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  rewrite Hdiveq.
  hoare unfold.
  assert (Hposv_cond: Int.ltu i Int.zero = true \/ Int.ltu ($ OS_USER_MAX_EVENTS / 3) i = true \/ i = $ OS_USER_MAX_EVENTS / 3).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.ltu i Int.zero) eqn:eq1;
    simpl in *; auto.
    destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) i) eqn: eq2;
    simpl in *; auto.
    destruct (Int.eq i ($ OS_USER_MAX_EVENTS / 3)) eqn: eq3;
    simpl in *; try (apply inteqeq in eq3; subst; auto).
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; simpl in *).
    tryfalse.
  }
  assert (Hdisj: v1 = Vint32 (Int.mone) \/ v1 <> Vint32 (Int.mone)) by tauto.
  destruct Hdisj as [Hv1eq | Hv1ne].
  (* v1 = Vint32 (Int.mone) *) 
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply semtrywait_absimp_poserr0; eauto.
  can_change_aop_solver.  
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.
  (* v1 <> Vint32 (Int.mone) *)  
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply semtrywait_absimp_poserr_abt; eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  apply absabort_rule.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  assert (Hposv_range: Int.ltu i Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    rewrite Hdiveq in *.
    destruct (Int.ltu i Int.zero) eqn:eq1;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i) eqn: eq2;
    destruct (Int.eq i ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    try (apply inteqeq in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
    try destruct H;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  clear H.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply semtrywait_absimp_posok_choice; eauto.
  pure_auto.
  apply absinfer_eq.
  destruct Hposv_range as (E1 & E2 & E3).
  lets Hposv_neq: Int.eq_false E3.
  (* encrit *)
  hoare forward prim.
  hoare unfold.

  unfold EvtInv. 
  rename v'19 into vcspace.
  rename v'20 into v18. 
  rename v'21 into v19. 
  rename v'22 into v20. 
  
  unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'38.
  hoare_assert_pure (length v'28 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hlen_info.

  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto p).
  eapply backward_rule1.
  intros. 
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel ASeminfo.
  eauto.
  rewrite Hlen_info.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.
  (* transform_pre ASeminfo_unfold_any_idx ltac:(idtac). *)

  hoare unfold.
  rename H7 into HH7.
  rename H8 into HH8.
  rename H9 into H8.
  rename H10 into H9.
  rename H14 into H12.
  rename H16 into H14.
  rename H18 into H16.
  rename H6 into H7.
  rename H11 into H6.
  rename H13 into H11.
  rename H15 into H13.
  rename H17 into H15.
  rename H19 into H17.
  
  hoare normal pre.
  hoare_lifts_trms_pre Aop.
  rename v'40 into semvl.  
  hoare forward.
  eapply assign_rule_lvar with (v2:=nth_val' 7%nat semvl).
  split; introv Hsat.
  sep_lifts_trms_in Hsat (Alvarmapsto p).
  eauto.
  sep cancel (Alvarmapsto p).
  auto.
  sep_get_rv_array_struct. 
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split in H1; eauto.
  simpljoin. auto.
  apply eq_vptr; eauto.
  sep pauto. sep cancel p_local. sep pauto.

  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: semb_corr H7 H4 E1 Hlemu.
  destruct H00 as (eo & tp & sc & Hget & H').
  assert (Hcases: ((exists eid, eo = infotid eid /\ V_OSSINFOPevent semvl = Some (Vptr eid) /\ eid <> vhold_addr) \/ eo = infonull /\ V_OSSINFOPevent semvl = Some Vnull) \/ eo = infohold /\ V_OSSINFOPevent semvl = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  clear H'.
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    rewrite Habt1 in Hget.
    hoare_lifts_trms_pre (Aop, seminfoid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semtrywait_absimp_before_abt_hold; eauto.
    unfold aemp_isr_is.
    pure_auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  assert (Hcases: ((exists eid,  eo = infotid eid /\ v = Vptr eid) \/ eo = infonull /\ v = Vnull) \/ ( (exists eid,  eo = infotid eid /\ v <> Vptr eid) \/ eo = infonull /\ v <> Vnull)).
  {
    inv Hok. destruct H3 as (eid & H'). 
    assert (Hvcs: v = Vptr eid \/ v <> Vptr eid) by (apply Classical_Prop.classic).
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v = Vnull \/ v <> Vnull) by (apply Classical_Prop.classic).
    inv Hvcs.
    left. right. destructs H3. split; auto.
    right. right. destructs H3. split; auto.
  }
  inversion Hcases.
  2: {
    hoare_lifts_trms_pre (Aop, seminfoid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semtrywait_absimp_before_abt_out; eauto.
    unfold aemp_isr_is. 
    pure_auto.
    eapply absinfer_eq. 
    apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, seminfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_before_ok; eauto.
  unfold aemp_isr_is.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.

  (* excrit *) 
  eapply backward_rule1. 
  intros.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'38. exists (Z.to_nat (Int.unsigned i)). exists v'39.
  exists semvl. 
  sep pauto.

  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  unfold ASemEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel ASemCap.
  sep cancel CapabilityInv.
  eauto.
  auto.
  go.

  assert (H_prm_cases: (exists eid, v = Vptr eid /\  nth_val' 7 semvl = Vptr eid) \/ (v = Vnull /\ nth_val' 7 semvl = Vnull)). 
  {
    inversion Hok as [Heo1 | Heo2]; inversion H3 as [Heo1' | Heo2'].
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq).
    destruct Heo1' as (eid' & Heoeq1' & Hv'_).
    rewrite Heoeq1' in Heoeq1. inverts Heoeq1.
    unfold V_OSSINFOPevent in Hv_.
    apply nth_val_nth_val'_some_eq in Hv_.
    left. eexists. split; eauto.
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq);
    destruct Heo2' as (Heoeq2' & Hv_');
    tryfalse.
    destruct Heo2 as (Heoeq2 & Hv_);
    destruct Heo1' as (eid & Heoeq1' & Hv_');
    tryfalse.
    unfold V_OSSINFOPevent in Heo2.
    destruct Heo2. destruct Heo2'.
    right.
    split; auto. 
    apply nth_val_nth_val'_some_eq; auto.
  }
  assert (Heq: nth_val' 7 semvl = v).
  {
    inversion H_prm_cases.
    simpljoin1. congruence.
    simpljoin1. congruence.
  }
  rewrite Heq. clear Heq. 
  assert (Hvptr: isptr v).
  {
    inversion H_prm_cases.
    simpljoin1.
    apply ptr_isptr.
    simpljoin1.
    apply Vnull_is_ptr.
  }
  clear -E1 E2 E3 Hposv_neq H_prm_cases Hvptr Hrgn3 Hrgn4 Hdiveq.

  (* If p = NULL { RETURN -1; } *)
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  assert (Hvnull: v = Vnull) by pure_auto.
  subst v.
  assert (Hv1: v1 <> (Vint32 Int.mone) \/ v1 = (Vint32 Int.mone)) by tauto.
  (* ... <> -1 *)
  destruct Hv1.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_if_null_yes_abt; eauto.
  can_change_aop_solver.
  instantiate (1:=Afalse).
  eapply absinfer_eq.
  apply absabort_rule.
  (* ... = -1 *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_if_null_yes_end; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* the RETURN in case p = NULL *)
  hoare forward.

  (* p <> NULL *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  assert (exists eid, v = Vptr eid).
  {
    destruct v. 
    inversion H; tryfalse.
    inversion H; tryfalse.
    inversion H; tryfalse.
    eexists; eauto.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_if_null_no; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  clear H.
  destruct H0.
(* new code about part_pos_rgn *)
     hoare_lifts_trms_pre (Aop, os_code_defs.pos, temp_dom, temp_num, Aisr, Aie, Ais, Acs, Aier, p_local, A_dom_lenv).
    (*  fold init_lg. *)
     eapply part_pos_rgn_proof.
     introv Hsat; sep auto.
     pure_auto.
     can_change_aop_solver.
     simpl; auto.
     simpl; auto.
     simpl;auto.
     hoare normal pre.
     eapply ex_intro_rule; intro vtemp_num.
     eapply ex_intro_rule; intro vtemp_dom.
     (* clear v'6 v'7; rename v'8 into v'6. *)
     (* end of new code *)
  (* 2nd encrit *) 
  clear - E1 E2 E3 Hposv_neq Hrgn3 Hrgn4 Hdiveq.
  hoare_lifts_trms_pre (Aop, os_code_defs.pos, x, p, y, sem).

  hoare forward prim. 
  hoare unfold.

  unfold EvtInv. 
  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19.
  
  unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'35.
  hoare_assert_pure (length v'25 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hlen_info.
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto p).
  eapply backward_rule1.
  intros. 
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel ASeminfo.
  eauto.
  rewrite Hlen_info.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.
  (* transform_pre ASeminfo_unfold_any_idx ltac:(idtac). *)

  hoare unfold.
  rename H7 into HH7.
  rename H8 into HH8.
  rename H9 into H8.
  rename H10 into H9.
  rename H14 into H12.
  rename H16 into H14.
  rename H18 into H16.
  rename H6 into H7.
  rename H11 into H6.
  rename H13 into H11.
  rename H15 into H13.
  rename H17 into H15.
  rename H19 into H17.
  
  hoare normal pre.
  hoare_lifts_trms_pre Aop.
  rename v'37 into semvl.
  hoare forward.
  eapply assign_rule_lvar with (v2:=nth_val' 7%nat semvl).
  split; introv Hsat.
  sep cancel (Alvarmapsto p).
  eauto.
  sep cancel (Alvarmapsto p).
  auto.

  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split in H1; eauto.
  simpljoin. auto.
  apply eq_vptr; eauto.
  sep pauto. sep cancel p_local. sep pauto.
  (* OSTCBCur ′ → __OSTskSemPtr =ₑ p ′;ₛ *)
  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList, p_local).
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  assert (Hisptr: isptr (nth_val' 7 semvl)).
  {
    apply new_array_type_vallist_match_sem_getp in H1.
    clear -H1. simpljoin1.
    unfold V_OSSINFOPevent in H.
    do 8 (destruct semvl; simpl in H; tryfalse). 
    inverts H. simpl. auto. 
  }
  hoare_assign_evaux.
  {
    apply new_array_type_vallist_match_sem_getp in H1.
    clear -H1. simpljoin1.
    unfold V_OSSINFOPevent in H.
    do 8 (destruct semvl; simpl in H; tryfalse). 
    inverts H. pure_auto.
   }
  rename v'33 into locmp.
  rename v'34 into ptrmp.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).  
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_normal)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: semb_corr H7 H4 E1 Hlemu. 
  destruct H00 as (eo & tp & sc & Hget & H').
  assert (Hcases: ((exists eid, eo = infotid eid /\ V_OSSINFOPevent semvl = Some (Vptr eid) /\ eid <> vhold_addr) \/ eo = infonull /\ V_OSSINFOPevent semvl = Some Vnull) \/ eo = infohold /\ V_OSSINFOPevent semvl = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  clear H'.
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    rewrite Habt1 in Hget.
    hoare_lifts_trms_pre (Aop, seminfoid). 
    eapply abscsq_rule.
    apply noabs_oslinv. 
    eapply semtrywait_absimp_before_abt_hold2; eauto.
    unfold aemp_isr_is.
    unfold CurTid.
    pure_auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  inversion Hok.
  simpljoin1.

  (* p is argument for OSSemAccept *)
  (* p <> NULL *) 
  unfold V_OSSINFOPevent in H23.
  assert (Hnth: nth_val' 7 semvl = Vptr x).
  {
    eapply nth_val_nth_val'_some_eq; eauto.
  }
  rewrite Hnth in *.
  rename v'8 into els.
  rename v'28 into semeibs.
  rename v'29 into muxeibs.
  rename v'30 into mqeibs.
  assert (Hsem: is_sem els x).
  {
    unfold RH_SEM_EINFO_ECB_P in H8.
    apply H8 in Hget. simpljoin1.
    unfold is_sem. do 2 eexists; eauto.
  }
  assert (Hvvcs: vv = Vptr x \/ vv <> Vptr x) by tauto.
  destruct Hvvcs.
  2: {
    hoare_lifts_trms_pre (Aop, seminfoid, evptrid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semtrywait_absimp_before_abt_out2; eauto.
    unfold aemp_isr_is. unfold CurTid. go.
    eapply absinfer_eq.
    eapply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, seminfoid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_before_ok2_ptr; eauto.
  unfold aemp_isr_is. unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *)
  fold_evaux_sem (Vptr x).
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto.
  2: { splits; eauto. }
  sep cancel Aier.
  unfold EvtInv.
  unfold ASemEIBs.
  sep pauto.
  trycancel.
  eapply ASeminfo_select_sn_strong.
  eauto.
  sep cancel Sem_info.
  sep cancel Astruct. sep cancel Aarray_new. sep cancel Aarray_new.
  sep split; eauto.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel ASemCap.
  sep cancel CapabilityInv.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  eauto. eauto. eauto.

  eapply evdel_nodup_normal_semptr_preserve; eauto.
  eapply evcre_nodup_normal_semptr_preserve; eauto.
  3: { eapply sem_ecb_p_semptr_normal_preserve; eauto. }
  2: { eapply mux_ecb_p_semptr_normal_preserve; eauto. } 
  eapply mq_ecb_p_semptr_normal_preserve; eauto.
  auto. auto. auto. auto.
  go.

  subst vv.

  hoare forward.
  go.
  {
    unfold retpost.
    introv Hsat.
    unfold getasrt in Hsat. unfold OSSemAcceptPost in Hsat. unfold OSSemAcceptPost' in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    simpljoin1.
    pure_auto.
  }
  introv Hsat.
  sep pauto.
  sep cancel p_local.
  sep pauto.
  introv Hsat.
  sep pauto.
  sep cancel p_local.
  sep pauto.

  hoare unfold.
  (* ENTER_CRITICAL;ₛ *) 
  hoare forward prim. 
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  inverts H22. (* eq. on logic_val *)

  unfold EvtInv.
  rename v'55 into vcspace1.
  rename v'56 into v58. 
  rename v'57 into v59. 
  rename v'58 into v60. 
  
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList,p_local).
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.

  rename v'64 into semeibs_.
  rename v'65 into muxeibs_.
  rename v'66 into mqeibs_.
  rename v'69 into locmp_.
  rename v'70 into ptrmp_.
  rename v'47 into els_.
  subst.
  hoare_assign_evaux.

  rename v'29 into vy.
  destruct (Int.ltu Int.zero vy) eqn: EE.
  (* 0 < y *)
  casetac v1 (Vint32 Int.zero) Ht Hf.
  (* v1 = 0 *) 
  hoare_lifts_trms_pre (Aop, curtid, evptrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_afteracc1; eauto.
  unfold aemp_isr_is. unfold CurTid. go. 
  eapply absinfer_eq.
  
  (* EXIT_CRITICAL *)
  fold_evaux_sem Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto. 
  2: { splits; eauto. }
  unfold EvtInv.
  sep cancel Aier.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  eauto.

  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  3: { eapply sem_ecb_p_set_null3_preserve; eauto. }
  2: { eapply mux_ecb_p_set_null3_preserve; eauto. }
  eapply mq_ecb_p_set_null3_preserve; eauto.
  auto. go.

  lzh_hoare_if.
  pure_auto.
  destruct (Int.ltu ($ 0) vy); pure_auto.

  (* return 0 *) 
  hoare forward. 

  (* impossible case *)
  change ($0) with (Int.zero) in Hif_false.
  rewrite EE in Hif_false.
  simpl in Hif_false. destruct Hif_false; tryfalse.

  (* v1 <> 0 *)
  hoare_lifts_trms_pre (Aop, curtid, evptrid).  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply semtrywait_absimp_afteracc1_abt; eauto. 
  unfold aemp_isr_is. unfold CurTid. go.
  eapply absinfer_eq. 
  eapply absabort_rule.

  (* 0 >= y *)
  casetac v1 (Vint32 Int.mone) Ht Hf.
  (* v1 = -1 *) 
  hoare_lifts_trms_pre (Aop, curtid, evptrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_afteracc2; eauto. 
  unfold aemp_isr_is. unfold CurTid. go. 
  eapply absinfer_eq.
  
  (* EXIT_CRITICAL *)
  fold_evaux_sem Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto. 
  2: { splits; eauto. }
  unfold EvtInv.
  sep cancel Aier.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.

  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  3: { eapply sem_ecb_p_set_null3_preserve; eauto. }
  2: { eapply mux_ecb_p_set_null3_preserve; eauto. }
  eapply mq_ecb_p_set_null3_preserve; eauto.
  auto. go.

  lzh_hoare_if.
  pure_auto.
  destruct (Int.ltu ($ 0) vy); pure_auto.

  (* impossible case *)
  change ($0) with (Int.zero) in LHift_true.
  rewrite EE in LHift_true. tryfalse. 

  (* return -1 *)
  hoare forward.

  (* v1 <> -1 *)
  hoare_lifts_trms_pre (Aop, curtid, evptrid).  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply semtrywait_absimp_afteracc2_abt; eauto. 
  unfold aemp_isr_is. unfold CurTid. go.
  eapply absinfer_eq. 
  eapply absabort_rule.
  
  (* p is NULL *)
  simpljoin1.
  subst.
  assert (Hnth: nth_val' 7 semvl = Vnull).
  {
    unfold V_OSSINFOPevent in H23.
    clear -H23.
    apply nth_val_nth_val'_some_eq in H23.
    eauto.
  }
  rewrite Hnth in *.
  
  rename v'8 into els.
  rename v'28 into semeibs.
  rename v'29 into muxeibs.
  rename v'30 into mqeibs.
  assert (Hvvcs: vv = Vnull \/ vv <> Vnull) by tauto.
  destruct Hvvcs.
  2: {
    hoare_lifts_trms_pre (Aop, seminfoid, evptrid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semtrywait_absimp_before_abt_out2; eauto.
    unfold aemp_isr_is. unfold CurTid. go.
    eapply absinfer_eq.
    eapply absabort_rule.
  }
  hoare_lifts_trms_pre (Aop, seminfoid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_before_ok2_null; eauto.
  unfold aemp_isr_is. unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *)
  lets Hset_eq: EvAuxPtrMod.get_set_same Hevptr.
  fold_evaux_sem Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto.
  2: { splits; eauto. }
  unfold EvtInv. unfold ASemEIBs.
  sep cancel Aier.
  sep pauto; eauto.
  trycancel.
  eapply ASeminfo_select_sn_strong.
  eauto.
  sep cancel Sem_info.
  sep cancel Astruct. sep cancel Aarray_new. sep cancel Aarray_new.
  sep split; eauto.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  rewrite Hset_eq in *.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel ASemCap.
  eauto. 
  auto. auto. auto. go.
  subst vv.
  
  hoare forward.
  go.
  {
    unfold retpost.
    introv Hsat.
    unfold getasrt in Hsat. unfold OSSemAcceptPost in Hsat. unfold OSSemAcceptPost' in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    simpljoin1.
    pure_auto.
  }
  introv Hsat.
  sep pauto.
  sep cancel p_local.
  sep pauto.
  introv Hsat.
  sep pauto.
  sep cancel p_local.
  sep pauto.
  
  hoare unfold.
  simpl in H30. 
  specialize (H30 (eq_refl _)). subst v'29. 
  inverts H22.
  (* return value for OSSemAccept is 0 *)
  
  (* ENTER_CRITICAL;ₛ *) 
  hoare forward prim. 
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.

  unfold EvtInv.
  rename v'52 into vcspace1.
  rename v'53 into v55. 
  rename v'54 into v56. 
  rename v'55 into v57.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList,p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  rename v'63 into semeibs_.
  rename v'64 into muxeibs_.
  rename v'65 into mqeibs_.
  rename v'67 into locmp_.
  rename v'68 into ptrmp_.
  rename v'44 into els_.
  hoare_assign_evaux.

  casetac v1 (Vint32 Int.mone) Ht Hf.
  (* v1 = -1 *) 
  hoare_lifts_trms_pre (Aop, curtid, evptrid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_afteracc2; eauto. 
  unfold aemp_isr_is. unfold CurTid. go. 
  eapply absinfer_eq.
  
  (* EXIT_CRITICAL *)
  fold_evaux_sem Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep pauto.
  2: { splits; eauto. }
  unfold EvtInv.
  sep cancel Aier.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.

  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto. 
  3: { eapply sem_ecb_p_set_null3_preserve; eauto. }
  2: { eapply mux_ecb_p_set_null3_preserve; eauto. }
  eapply mq_ecb_p_set_null3_preserve; eauto.
  auto.
  go.

  lzh_hoare_if.

  (* impossible case *)
  change ($0) with (Int.zero) in LHift_true.
  rewrite sempend_ltu_ass1 in LHift_true.
  tryfalse.
  
  (* return -1 *)
  hoare forward. 

  (* v1 <> -1 *)
  hoare_lifts_trms_pre (Aop, curtid, evptrid).  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply semtrywait_absimp_afteracc2_abt; eauto. 
  unfold aemp_isr_is. unfold CurTid. go.
  eapply absinfer_eq. 
  eapply absabort_rule.

  Unshelve.
  exact 0%nat.
  exact 0%nat.
  trivial.
Qed.

Lemma OSSemTrywaitAProof:
  forall tid vl p r,
    Some p =
      BuildPreA' os_api sem_trywait semtrywaitapi vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api sem_trywait semtrywaitapi vl OSLInv tid init_lg -> 
    exists t d1 d2 s,
      os_api sem_trywait = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 10 (destruct v'; try apply absabort_rule).

  rename x into vsem.
  assert (Hptr: vsem = Vnull \/ (exists p, vsem = Vptr p)).
  {
    destruct vsem.
    unfold isptr in H1. inversion H1. tryfalse. mytac. 
    left. auto.
    right. eexists; eauto.
    unfold isptr in H1. inversion H1. tryfalse. mytac. tryfalse.
    right. eexists; eauto.
  }
  hoare forward.
  pure_auto.
  simpl.
  inversion Hptr. left; subst; auto. right. simpljoin; eexists; eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  do 2 destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
  do 2 destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
  pure_auto. 

  intros.
  destruct H.
  destruct H; try (sep pauto; sep cancel p_local; sep pauto).

  intros.
  sep pauto. sep cancel p_local. sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  hoare unfold.
  inverts H2.

  assert (Hv: v = Vint32 (Int.mone) \/ v <> Vint32 (Int.mone)) by tauto.
  destruct Hv.  
  2: {
    hoare abscsq.
    apply noabs_oslinv. 
    inversion Hptr.  
    subst.
    eapply semtrywait_absimp_semok_abt_null; eauto.
    can_change_aop_solver.
    destruct H2. subst. 
    eapply semtrywait_absimp_semerr_abt; eauto.
    inversion H; tryfalse.
    mytac. inverts H2. auto.
    can_change_aop_solver.
    apply absabort_rule.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply semtrywait_absimp_semerr_cont; eauto.
  inversion H.
  left. inverts H2; subst; auto.
  right.
  simpljoin. eexists; splits; eauto.  inverts H2; auto.
  can_change_aop_solver.
  subst v. 
  hoare forward.
  hoare forward.

  hoare unfold.
  assert (Heqf: Int.eq ($ 0) ($ 0) = true) by int auto.
  inversion H0.
  rewrite Heqf in H2. simpl in H2. tryfalse.
  rewrite Heqf in H2. simpl in H2. tryfalse.

  (* rearrange the pre-cond for the code starting with range check on pos *) 
  eapply hoare_disj_afalseP_r_pre.

  eapply backward_rule1; [idtac | eapply OSSemTrywaitPartProof ].
  sep pauto.

  (* ---------------------------------------------- *)
  (* second branch for conditional on x *)
  hoare unfold.
  inverts H2.
  rename x into vsem.

  assert (Hv00: ~(exists i, v = Vint32 i) \/ exists i, v = Vint32 i) by tauto.
  inversion Hv00 as [Hex | Hex].
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_sem_get_outtype_err_abt; eauto. 
  pure_auto.
  eapply absinfer_eq. 
  apply absabort_rule.
 
  lzh_hoare_if; try change (Int.eq ($ 1) ($ 0)) with false in *; tryfalse.
  (* second branch: encrit; pos = *sem; excrit *)
  (* encrit *)
  hoare forward prim.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  unfold EvtInv.
  rename v'23 into vcspace.
  rename v'24 into v22. 
  rename v'25 into v23. 
  rename v'26 into v24. 
  hoare normal pre.
  hoare_ex_intro.

  rename v'38 into pbls.
  assert (Hor: get pbls vsem = None \/ (exists posv, get pbls vsem = Some posv)).
  {
    destruct (get pbls vsem).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome]. 
  (* get pbls smadr = None *)
  hoare_ex_intro. 
  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply semtrywait_absimp_sem_get_none; eauto.
  unfold aemp_isr_is.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  (* exists posv, get pbls smadr = Some posv *)

  destruct Hsome as (posv & Hget). 
  eapply backward_rule1. 
  intros. 
  eapply pos_list_split_frm.
  sep cancel APosblkList.
  eauto.
  eauto.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).

  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_lvar with (v2:=Vint32 posv).
  split.
  instantiate (3:=long). instantiate (2:=v'0).
  intros.
  sep cancel os_code_defs.pos.
  eauto.
  introv Hsat. sep cancel os_code_defs.pos. auto.
  2: { instantiate (1:=long). eapply eq_int. split; ((do 2 right); auto). }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  unfold node.
  intros.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat Aexists. 
  apply astar_l_aexists_elim in Hsat.
  apply aexists_elim in Hsat.
  destruct Hsat.
  get_hsat Hsat. 
  sep normal in Hsat.
  apply astar_l_apure_elim in Hsat.
  destruct Hsat.
  destruct H.
  inverts H. 
  assert (Heqposv: nth_val' 0 v'44 = Vint32 posv).
  {
    get_hsat Hsat. 
    sep split in Hsat.
    unfold V_posblk_pos in H0. 
    eapply nth_val_nth_val'_some_eq; eauto. 
  }
  rewrite <- Heqposv. 
  eapply sem_rv; eauto.
  sep get rv.

  assert (Hv: v <> Vint32 posv \/ v = Vint32 posv) by tauto.
  destruct Hv.
  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_sem_get_pos_abt; eauto.
  unfold aemp_isr_is.
  pure_auto.
  go.
  eapply absinfer_eq.
  apply absabort_rule.

  hoare_lifts_trms_pre (Aop, pblsid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semtrywait_absimp_sem_get_pos_ok; eauto.
  unfold aemp_isr_is.
  pure_auto. 
  eapply absinfer_eq.
  
  (* preparation for excrit *)
  eapply backward_rule1. 
  introv Hsat.
  sep lifts (4::5::6::nil)%nat in Hsat.
  eapply pos_sllseg_merge.
  sep split; eauto.
  sep split in Hsat; simpljoin1; eauto.
  sep split in Hsat; simpljoin1; eauto.
  sep split in Hsat; simpljoin1; eauto.
  sep split in Hsat; simpljoin1; eauto.
  sep split in Hsat; simpljoin1; eauto.

  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep cancel Aier.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold APosblkList.
  sep pauto.
  auto.
  go.
  
  destruct Hex as (i & Hvi). 
  subst v.

  clear - tid i.

  eapply backward_rule1; [idtac | eapply OSSemTrywaitPartProof ].
  sep pauto.
  sep cancel Aop.
  sep_cancel_iers.
  auto.

  Unshelve.
  trivial.
  exact Afalse.
Qed.

