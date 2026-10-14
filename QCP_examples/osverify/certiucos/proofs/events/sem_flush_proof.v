
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import abs_op.

Require Import sem_flush_pure.

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
Require Import OSTimeTickPure.
Require Import OSQPostPure.
Require Import protect.
Require Import tcblist_setnode_lemmas.
Require Import sempost_pure.
Require Import sem_corecommu.

Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.

Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope int_scope.

Lemma semflush_absimp_iserr:
forall sch V_sem V_pos V_pevent P vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num',
    can_change_aop P -> 
    absinfer sch 
      (<|| semflush (V_sem :: V_pos :: V_pevent :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil) ||>  ** P)
      (<|| END (Some  (Vint32 (Int.mone))) ||> ** P).
Proof.
infer_solver 0%nat.
Qed. 

Lemma semflush_absimp_semerr:
  forall sch V_sem V_pos V_pevent P vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num',
    (V_sem = Vnull \/
 (exists a,
  V_sem = Vptr a /\
  (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true))) ->  
    can_change_aop P -> 
    absinfer sch 
      (<|| semflush (V_sem :: V_pos :: V_pevent :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil) ||>  **  P)
      (<|| END Some (Vint32 Int.mone) ||> ** P).
Proof.
infer_solver 1%nat.
Qed.

Lemma semflush_absimp_sem_get_none:
  forall sch vsm V_pos V_pevent pbls P vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num',
    cmpaddr Clt userAddrStart vsm = true ->
    cmpaddr Cle vsm userAddrEnd = true -> 
    get pbls vsm = None -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| semflush (Vptr vsm :: V_pos :: V_pevent :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil) ||>  **  Hpbls pbls ** P)
      (<|| ABORT ||> **  Hpbls pbls ** P).
Proof.
  introv Hrgn1 Hrgn2 Hnone Hcop.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) .
  can_change_aop_solver.
  do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  right.
  eexists; eauto. splits; eauto. 
  destruct H. simpljoin1. 
  simpl in H3. destruct H3.
  simpl in H2. subst x2.
  eapply join_sig_get; eauto.
Qed.

Lemma semflush_absimp_sem_get_outtype_err_abt:
  forall sch vsm V_pos V_pevent P vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num',
    cmpaddr Clt userAddrStart vsm = true ->
    cmpaddr Cle vsm userAddrEnd = true -> 
    ~(exists i, V_pos = Vint32 i) -> 
    can_change_aop P ->
    absinfer sch
     (<|| semflush (Vptr vsm :: V_pos :: V_pevent :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil) ||>  ** P)
     (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn1 Hrgn2 Hnone Hcop.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_abt; try eauto);
    try eauto.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  exact None. 
Qed. 

Lemma semflush_absimp_sem_get_pos_abt: 
  forall sch vsm V_pos V_pevent pbls posv P vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num', 
    cmpaddr Clt userAddrStart vsm = true ->
    cmpaddr Cle vsm userAddrEnd = true -> 
    get pbls vsm = Some posv ->
    V_pos <> Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<|| semflush (Vptr vsm :: V_pos :: V_pevent :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num':: nil) ||> ** Hpbls pbls ** P)
     (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_abt; try eauto);
    try eauto.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  right. eexists; splits; eauto.
  pure_auto.
  destruct H. simpljoin1. 
  simpl in s0. destruct s0.
  simpl in j0. subst x2.
  eapply join_sig_get; eauto.
  left. eexists; splits; eauto.
Qed.

Lemma semflush_absimp_sem_get_pos_ok: 
  forall sch vsm V_pos V_pevent pbls posv P vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num', 
   cmpaddr Clt userAddrStart vsm = true ->
    cmpaddr Cle vsm userAddrEnd = true -> 
    get pbls vsm = Some posv ->
    V_pos = Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<|| semflush (Vptr vsm :: V_pos :: V_pevent :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil) ||> ** Hpbls pbls ** P)
     (<|| (semflush_poserr (| V_pos :: nil |) ??
                (semflush_get_ecb_ptr (| V_pos :: V_pevent :: nil |) ;;
                  (semflush_if_null_yes (| V_pevent :: nil |) ?? 
                    (semflush_if_null_no (| V_pevent :: nil |) ;;
                       partition_pos_rgn (V_pos
            :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil)
                       ((semflush_get_not_hold (| V_pos :: nil |) ;; semflush_type_err (| V_pos :: nil|)) ??
                              (semflush_get_valid_ecb (| V_pos :: nil |) ;; 
                                ((* semflush_null (| V_pos :: nil |) ??  *)semflush_no_wl (| V_pos :: nil |) ??
                                   semflush_set_wl_all_rdy (| V_pos :: nil|)) ;; isched ;; (END (Some (Vint32 Int.zero))))))))) ||> ** Hpbls pbls ** P).
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
  infer_part1 2%nat.
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

Lemma semflush_absimp_poserr:
  forall posv P sch s,
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    can_change_aop P -> 
    absinfer sch
      ( <|| semflush_poserr (| Vint32 posv :: nil |) ?? s ||> ** P)
      ( <|| END (Some  (Vint32 (Int.mone))) ||> ** P ).
Proof.
  infer_solver 0%nat.  
Qed.

Lemma semflush_absimp_ecb_ptr_abt:
  forall posv V_pevent P sch s1 s2 sembls e tp sc,
    (posv = Int.zero \/ Int.ltu Int.zero posv = true) ->
    Int.ltu posv ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get sembls posv = Some (e,tp,sc) ->
    (~ (exists eid, e = infotid eid) /\ e <> infonull \/
  (exists eid, e = infotid eid /\ V_pevent <> Vptr eid) \/
  e = infonull /\ V_pevent <> Vnull) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_ecb_ptr (| Vint32 posv :: V_pevent :: nil |) ;; s2)  ||> ** HSEMInfo sembls ** P) 
      (<|| ABORT ||> ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  exact None.
Qed.

Lemma semflush_absimp_if_null_yes_end:
  forall posv V_pevent P sch s1 s2 sembls tp sc,
    (posv = Int.zero \/ Int.ltu Int.zero posv = true) ->
    Int.ltu posv ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get sembls posv = Some (infonull,tp,sc) ->
    V_pevent = Vnull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_ecb_ptr (| Vint32 posv :: V_pevent :: nil |) ;;
                            (semflush_if_null_yes (| V_pevent :: nil |) ?? 
                               (semflush_if_null_no (| V_pevent :: nil |) ;; s2)))  ||> ** HSEMInfo sembls ** P) 
      (<|| END Some (Vint32 Int.mone) ||> ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
  instantiate (1:= END None).
  infer_solver 0%nat.
  eapply absinfer_trans; try (eapply absinfer_seq_end; try eauto).
  infer_solver 0%nat.
Qed.

Lemma semflush_absimp_if_null_no:
  forall posv V_pevent P sch s1 s2 sembls tp sc e,
    (posv = Int.zero \/ Int.ltu Int.zero posv = true) ->
    Int.ltu posv ($ (OS_USER_MAX_EVENTS / 3)) = true -> 
    get sembls posv = Some (e,tp,sc) ->
    (exists eid, e = infotid eid /\ V_pevent = Vptr eid) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_ecb_ptr (| Vint32 posv :: V_pevent :: nil |) ;;
                            (semflush_if_null_yes (| V_pevent :: nil |) ?? 
                               (semflush_if_null_no (| V_pevent :: nil |) ;; s2)))  ||> ** HSEMInfo sembls ** P) 
      (<|| s2 ||> ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans; try (eapply absinfer_seq; try eauto).
  instantiate (1:= END None).
  infer_solver 0%nat.
  eapply absinfer_trans; try (eapply absinfer_seq_end; try eauto).
  infer_solver 1%nat.
  destruct H2 as (eid & He & Hp).
  subst.
  repeat eexists; eauto.
Qed.

Lemma semflush_absimp_ecb_hold_abt:
  forall posv P sch s1 s2 sembls e tp sc,
    get sembls posv = Some (e,tp,sc) ->
    ~ (exists eid, e = infotid eid) /\ e <> infonull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (semflush_get_not_hold (| Vint32 posv :: nil |) ;; s1) ?? s2  ||> ** HSEMInfo sembls ** P) 
      (<|| ABORT ||> ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice1; try eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma semflush_absimp_ecb_not_hold_cons:
  forall posv P sch s1 s2 sembls e tp sc,
    get sembls posv = Some (e,tp,sc) ->
    (exists eid, e = infotid eid) \/ e = infonull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| (semflush_get_not_hold (| Vint32 posv :: nil |) ;; s1) ?? s2  ||> ** HSEMInfo sembls ** P) 
      (<|| s1 ||> ** HSEMInfo sembls ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma semflush_absimp_ecb_hold_abt':
  forall posv P sch s1 s2 sembls e tp sc,
    get sembls posv = Some (e,tp,sc) ->
    ~ (exists eid, e = infotid eid) /\ e <> infonull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_not_hold (| Vint32 posv :: nil |) ;; s2) ||> ** HSEMInfo sembls ** P) 
      (<|| ABORT ||> ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma semflush_absimp_ecb_not_hold_cons':
  forall posv P sch s1 s2 sembls e tp sc,
    get sembls posv = Some (e,tp,sc) ->
    (exists eid, e = infotid eid) \/ e = infonull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_not_hold (| Vint32 posv :: nil |) ;; s2)  ||> ** HSEMInfo sembls ** P) 
      (<|| s2 ||> ** HSEMInfo sembls ** P). 
Proof.
  infer_solver 1%nat.
Qed.

Lemma semflush_absimp_type_err:
  forall posv P sch sembls eid tp sc els,
    get sembls posv = Some (infotid eid,tp,sc) ->
    ~(exists n wl, get els eid = Some (abssem n, wl)) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| semflush_type_err (| Vint32 posv :: nil |)  ||> ** HSEMInfo sembls ** HECBList els ** P) 
      (<|| END Some (Vint32 Int.mone) ||> ** HSEMInfo sembls ** HECBList els ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma semflush_absimp_valid_ecb_abt:
  forall posv P sch s1 s2 sembls e tp sc,
    get sembls posv = Some (e,tp,sc) ->
    ~ (exists eid, e = infotid eid) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_valid_ecb (| Vint32 posv :: nil |) ;; s2) ||> ** HSEMInfo sembls ** P) 
      (<|| ABORT ||> ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; try eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; try eauto).
  eapply absinfer_seq; try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma semflush_absimp_valid_ecb_cons:
  forall posv P sch s1 s2 sembls e tp sc,
    get sembls posv = Some (e,tp,sc) ->
    (exists eid, e = infotid eid) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? (semflush_get_valid_ecb (| Vint32 posv :: nil |) ;; s2)  ||> ** HSEMInfo sembls ** P) 
      (<|| s2 ||> ** HSEMInfo sembls ** P). 
Proof.
  infer_solver 1%nat.
Qed.

Lemma semflush_absimp_no_wl:
  forall posv P sch sembls tp sc (* s1  *)s2 s3 els n eid,
    get sembls posv = Some (infotid eid,tp,sc) ->
    get els eid = Some (abssem n, nil) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| ((* s1 ??  *)semflush_no_wl  (| Vint32 posv :: nil |) ?? s2) ;; s3  ||> ** HSEMInfo sembls ** HECBList els ** P) 
      (<|| s3 ||> ** HSEMInfo sembls ** HECBList els ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** HECBList els ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_end; try eauto).
  eapply absinfer_seq; try eauto.
  infer_solver 0%nat.
Qed.

Lemma semflush_absimp_set_wl_all_rdy:
  forall wl posv P sch sembls tp sc (* s1 *) s2 s3 eid els n tls ,
    get sembls posv = Some (infotid eid,tp,sc) ->
    get els eid = Some (abssem n, wl) ->
    wl <> nil ->
    can_change_aop P -> 
    absinfer sch 
      (<|| ((* s1 ?? *) s2 ?? semflush_set_wl_all_rdy  (| Vint32 posv :: nil |)) ;; s3  ||> 
         ** HSEMInfo sembls ** HECBList els ** HTCBList tls ** P) 
      (<|| s3 ||> 
        ** HSEMInfo sembls 
        ** HECBList (set els eid (abssem n, nil)) 
        ** HTCBList (set_tls_rdy wl tls) ** P). 
Proof.
  intros.
  assert (Hc: forall els tls, can_change_aop (HSEMInfo sembls ** HECBList els ** HTCBList tls ** P))
    by (intros; can_change_aop_solver).
  eapply absinfer_trans; 
  try eapply absinfer_seq_end; [idtac | idtac | idtac | eauto];
  eauto.
  eapply absinfer_seq; try eauto.
  infer_solver 1%nat.
  simpl eqtls.
  apply eqdomtls_set_tls_rdy.
Qed.

Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.

Local Open Scope code_scope.

(* copy form OSMutex_common.v *)
Goal forall x y, Int.eq x y = true  -> x=y.
intros.
int auto.
apply unsigned_inj.
auto.
Save inteqeq.
(* end of copy *)


Ltac sep_get_rv_array_struct' :=
  let Hsat := fresh in
  let Hf := fresh in
  let Ht'' := fresh in
  let Hn := fresh in
  match goal with
  | |- ?P ==> Rv efield (ederef (efield (?gident ′ [?ident ′]) ?id)) ?id2 @ ?tp1 == _ =>
        introv Hsat; eapply struct_member_e_rv;
         [ try eauto; try sep_get_rv_array_struct
         | try sep cancel Astruct; eauto
         | try
            (match goal with
             | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
             end; eauto)
         | try (simpl; auto)
         | try (simpl; auto)
         | try (intro Ht''; intro Hn; intro Hf; inv Hf)
         | try (intro Ht''; intro Hn; intro Hf; inv Hf)
         | try (unfold id_nth; simpl; auto)
         | try (simpl; auto with zarith)
         | try go
         | try (simpl; auto) ]
  | Hsat:?s |= ?P
    |- ?s |= Rv efield (ederef (efield (?gident ′ [?ident ′]) ?id)) ?id2 @ ?tp1 == _ =>
        eapply struct_member_e_rv;
         [ try eauto; try sep_get_rv_array_struct
         | try sep cancel Astruct; eauto
         | try
            (match goal with
             | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
             end; eauto)
         | try (simpl; auto)
         | try (simpl; auto)
         | try (intro Ht''; intro Hn; intro Hf; inv Hf)
         | try (intro Ht''; intro Hn; intro Hf; inv Hf)
         | try (unfold id_nth; simpl; auto)
         | try (simpl; auto with zarith)
         | try go
         | try (simpl; auto) ]
  end.


Lemma SemFlushProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api sem_flush
              (semflush, (Tint32, Tptr Tint32 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api sem_flush
              (semflush, (Tint32, Tptr Tint32 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api sem_flush = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 7 (destruct v'; try apply absabort_rule).

  rename x into V_sem.
  rename v into V_pos.
  rename v0 into V_pevent.
  rename H1 into Hptr.

  (*new add *)
  hoare forward prim.
  unfold AGVars.
  hoare unfold.
  rename v'21 into vpthattr.
  rename v'22 into vcspace.
  rename v'23 into v21. 
  rename v'24 into v22. 
  rename v'25 into v23. 

  rename v'26 into v'21. 
  rename v'27 into v'22. 
  rename v'28 into v'23. 
  rename v'29 into v'24. 
  rename v'30 into v'25.
  rename v'31 into v'26.
  rename v'32 into v'27. 
  rename v'33 into v'28. 
  rename v'34 into v'29. 
  rename v'35 into v'30. 
  rename v'36 into v'31. 
  rename v'37 into v'32. 
  assert (Hit: Int.ltu ($ 0) v'31 = true \/ Int.ltu ($ 0) v'31 = false) by int auto.
  destruct Hit as [Hit | Hit].
  hoare forward; rewrite Hit. simpl; pure_auto.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply semflush_absimp_iserr; try pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  simpl in H3. destruct H3; tryfalse.
  hoare forward; rewrite Hit. simpl; pure_auto.
  hoare unfold. simpl in H3; tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  auto.
  pure_auto.
  clear -Hptr.
  (* end add *)

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

  (* x ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 sem ′·);ₛ *)
  rename v'4 into er.
  hoare forward. 
  pure_auto.
  simpl.
  inverts Hptr; mytac; try pauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  pure_auto.

  intros.
  destruct H.
  destruct H; try (sep pauto; instantiate (1:=init_lg); sep pauto).

  intros.
  sep pauto. instantiate (1:=init_lg). sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  (* x = 0 *)
  hoare unfold.
  inverts H1.

  hoare forward.
  hoare forward.
  hoare unfold.
  change (Int.eq ($ 0) ($ 0)) with true in H0.
  simpl in H0.
  destruct H0; tryfalse.
  change (Int.eq ($ 0) ($ 0)) with true.
  simpl.
  instantiate (1 := Afalse).
  eapply hoare_disj_afalseP_r_pre.
  hoare unfold.
  (*hoare_lifts_trms_pre (Aop, os_code_defs.pos, x, p, err, sem).*) 
  
  lzh_hoare_if;
  try (rewrite Hchg);
  simpl;
  pure_auto.

  change (Int.eq ($ 3) Int.zero) with false in LHift_true; simpl in LHift_true.
  rewrite Hdiveq in LHift_true; simpl in LHift_true.
  rewrite int_min_neq_maxevents in LHift_true; simpl in LHift_true.
  destruct LHift_true as (Ha & Hb & Hc). clear Hb Hc.
  change (Int.ltu ($ -1) ($ 0)) with false in Ha.
  change ($ -1) with Int.mone in Ha.
  assert (Hmt: Int.ltu ($ OS_USER_MAX_EVENTS / 3) Int.mone = true).
  {clear - Hrgn3 Hrgn4. int auto. }
  rewrite Hmt in Ha.
  assert (Hmf: Int.eq Int.mone ($ OS_USER_MAX_EVENTS / 3) = false).
  { clear -Hrgn3 Hrgn4. int auto. }
  rewrite Hmf in Ha.
  repeat ( try simpl in Ha;
  try rewrite sempend_ltu_ass1 in Ha; try rewrite sempend_ltu_ass2 in Ha).
  tryfalse.
  hoare abscsq.
  apply noabs_oslinv.
  eapply semflush_absimp_semerr.
  can_change_aop_solver.
  destruct H. inverts H. pauto.
  do 2 destruct H. inverts H. pauto.
  can_change_aop_solver.
  hoare forward.
  change (Int.eq ($ 3) Int.zero) with false in Hif_false; simpl in Hif_false.
  change ($ -1) with Int.mone in Hif_false.
   rewrite Hdiveq in Hif_false; simpl in Hif_false.
  rewrite int_min_neq_maxevents in Hif_false; simpl in Hif_false.
  change (Int.ltu ($ -1) ($ 0)) with false in Hif_false.
  assert (Hmt: Int.ltu ($ OS_USER_MAX_EVENTS / 3) Int.mone = true).
  {clear - Hrgn3 Hrgn4. int auto. }
  rewrite Hmt in Hif_false.
  assert (Hmf: Int.eq Int.mone ($ OS_USER_MAX_EVENTS / 3) = false).
  { clear -Hrgn3 Hrgn4. int auto. }
  rewrite Hmf in Hif_false.
  repeat ( try simpl in Hif_false;
  try rewrite sempend_ltu_ass1 in Hif_false; try rewrite sempend_ltu_ass2 in Hif_false).
  destruct Hif_false; tryfalse.

  (*x != 0*)
  (* second branch for conditional on x *)
  hoare unfold.
  inverts H1.
  rename x into vsem.

  assert (Hv00: ~(exists i, V_pos = Vint32 i) \/ exists i, V_pos = Vint32 i) by tauto.
  inversion Hv00 as [Hex | Hex].
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_sem_get_outtype_err_abt; eauto. 
  pure_auto.
  eapply absinfer_eq. 
  apply absabort_rule.

  lzh_hoare_if.
 
  (* impossible case: x = 1 while first branch is taken *) 
  tryfalse.
  Focus 2. tryfalse.
  (* second branch: encrit; pos = *sem; excrit *)
  (* encrit *)
  hoare forward prim.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_lifts_trms_pre EvtInv.
  unfold EvtInv.
  rename v'21 into vpthattr.
  rename v'22 into vcspace.
  rename v'23 into v21. 
  rename v'24 into v22. 
  rename v'25 into v23. 
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).

  rename v'36 into pbls.
  assert (Hor: get pbls vsem = None \/ (exists posv, get pbls vsem = Some posv)).
  {
    destruct (get pbls vsem).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome].
  (* get pbls smadr = None *)
  hoare_lifts_trms_pre (Aabsdata pblsid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply semflush_absimp_sem_get_none; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  (* exists posv, get pbls smadr = Some posv *)
  destruct Hsome as (posv & Hget).
  hoare normal pre.
  eapply backward_rule1. 
  intros. 
  eapply pos_list_split_frm.
  sep cancel APosblkList.
  exact_s.
  eauto.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_lifts_trms_pre (Alvarmapsto (os_code_defs.pos)).
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_lvar with (v2:=Vint32 posv). 
  split.
  instantiate (3:=long). instantiate (2:=v'0).
  intros.
  (*sep cancel (Alvarmapsto os_code_defs.pos).*)
  sep cancel os_code_defs.pos.
  eauto.
  intro.
  sep pauto.
  auto.
  2: { instantiate (1:=long). eapply eq_int. split; ((do 2 right); auto). }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  unfold node.
  sep pauto.
  unfold V_posblk_pos in H4.
  eapply nth_val_nth_val'_some_eq in H4.
  rewrite <- H4.
 
  eapply sem_rv; eauto.
  inverts H0.
  sep get rv.
  assert (Hposv: V_pos <> Vint32 posv \/ V_pos = Vint32 posv) by tauto.
  destruct Hposv.
  hoare_lifts_trms_pre (Aabsdata pblsid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_sem_get_pos_abt; eauto. 
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  hoare_lifts_trms_pre (Aabsdata pblsid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_sem_get_pos_ok; eauto.
  pure_auto.
  eapply absinfer_eq.
  rewrite <- H.

  (* preparation for excrit *)
  hoare_lifts_trms_pre (pos_sllseg v'36, node, pos_sllseg v'43, 
   ev_aux_code.V_posblk_next,
   ev_aux_code.V_posblk_pos, v'36).
  hoare remember (1:: 2 :: 3 :: 4 :: 5 :: 6 :: nil)%nat pre.
  eapply backward_rule1. 
  introv Hsat.
  eapply pos_sllseg_merge
    with (vll1:=v'40) (hd:=v'36) (vsem:=vsem) (pbls1:=v'44) (vl:=v'42)
         (hd':=v'43) (vll2:=v'41) (pbls2:=v'46) (posv:=posv) (pbls':=v'45) (pbls:=pbls). 
  instantiate (1:= H0).
  clear -Hsat H Hget.
  sep pauto.
  auto.
  subst H0.

  (* EXIT_CRITICAL *) 
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold EvtInv.
  unfold APosblkList.
  sep pauto; eauto.
  trycancel.
  sep cancel pos_sllseg.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  exact_s.
  auto.
  go.
  clear Hv00.

  destruct Hex as (i & Hvi). 
  subst V_pos.
  rename i into posv.
  clear Hif_false.

  (* If (′ 0 >ₑ os_code_defs.pos ′
    ||ₑ os_code_defs.pos ′ ≥ ′ OS_USER_MAX_EVENTS ÷ ′ 3) *)
  hoare_lifts_trms_pre (Aop, os_code_defs.pos, x, p , y, sem).
  lzh_hoare_if;
  try (change (Int.eq ($ 3) Int.zero) with false; simpl;
  rewrite Hdiveq; simpl;
  rewrite int_min_neq_maxevents; simpl; pure_auto).
  pure_auto.

  change (Int.eq ($ 3) Int.zero) with false in LHift_true; simpl in LHift_true.
  rewrite Hdiveq in LHift_true; simpl in LHift_true.
  rewrite int_min_neq_maxevents in LHift_true; simpl in LHift_true.
  destruct LHift_true as (Ha & Hb & Hc). clear Hb Hc.
  destruct (Int.ltu posv ($ 0)) eqn: E1; 
    destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) posv) eqn: E2;
    destruct (Int.eq posv ($ OS_USER_MAX_EVENTS / 3)) eqn: E3;
  try
  (eapply abscsq_rule with (q:= Afalse);
  [ apply noabs_oslinv
     | eapply semflush_absimp_poserr; eauto;
        can_change_aop_solver
     | apply absinfer_eq |  hoare forward]).
    apply Inteq_true_is_Zeq in E3.
    right. right.
    apply unsigned_inj; auto.

  change (Int.eq ($ 3) Int.zero) with false in Hif_false; simpl in Hif_false. 
  rewrite Hdiveq in Hif_false; simpl in Hif_false.
  rewrite int_min_neq_maxevents in Hif_false; simpl in Hif_false.
  assert (Hif_cond: ~(Int.ltu posv ($ 0) = false /\ Int.ltu ($ OS_USER_MAX_EVENTS / 3) posv = false 
                       /\ Int.eq posv ($ OS_USER_MAX_EVENTS / 3) = false) 
                  \/ (Int.ltu posv ($ 0) = false /\ Int.ltu ($ OS_USER_MAX_EVENTS / 3) posv = false 
                        /\ Int.eq posv ($ OS_USER_MAX_EVENTS / 3) = false)) by tauto.
  destruct Hif_cond.
  destruct Hif_false as [Hy | Hf];
  destruct (Int.ltu posv ($ 0)) eqn: E1; 
  destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) posv) eqn: E2;
  destruct (Int.eq posv ($ OS_USER_MAX_EVENTS / 3)) eqn: E3;
  pure_auto_try_false.
  pure_auto.
   (* 0 <= posv < 20/3 *) 
  clear Hif_false. destruct H as (E1 & E2 & E3).
  change (Int.divs ($ 20) ($ 3)) with ($ 6) in *.
  eapply semacc_int_eq_false in E3.
  change ($ 0) with Int.zero in E1.

  (* encrit *)
  hoare_lifts_trms_pre (Aop, os_code_defs.pos, x, p, y, sem).
  hoare forward prim. 
  hoare unfold.
  rename v'21 into vpthattr.
  rename v'22 into vcspace.
  rename v'23 into v21. 
  rename v'24 into v22. 
  rename v'25 into v23. 
  unfold EvtInv. 
  unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'40.
  rename b into v'40.
  rename i into v'41.
  hoare_lifts_trms_pre (RH_SEM_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hs_nc.

  hoare_assert_pure (length v'30 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto. } 
  eapply pure_split_rule'; introv Hlen_info.
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto p).
  eapply backward_rule1.
  intros.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel ASeminfo.
  exact_s.
  rewrite Hlen_info.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  (* transform_pre ASeminfo_unfold_any_idx ltac:(idtac). *)
  hoare unfold.
  rename H9 into HH9.
  rename H10 into HH10.
  rename H8 into H9.
  rename H11 into H10.
  rename H12 into H8.
  rename H14 into H12.
  rename H16 into H14.
  rename H18 into H16.
  rename H15 into H13.
  rename H17 into H15.
  rename H19 into H17.
  rename H20 into H18.
  hoare normal pre.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  
  eapply assign_rule_lvar with (v2:=nth_val' 7%nat v'44).
  split; introv Hsat.
  sep_lifts_trms_in Hsat p.
  eauto.
  sep_lifts_trms p.
  auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply Int.eq_false; eauto.
  eapply new_array_type_vallist_match_split in H1; eauto.
  mytac. 
  { apply eq_vptr. do 2 eexists; splits; auto. }
  { sep pauto. sep cancel p_local. simpl; auto. }

  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: semb_corr H9 H6 E1 Hlemu.
  destruct H00 as (eo & tp & sc & Hget & H').
  assert (Hcases: 
           ((exists eid,
                eo = infotid eid /\ V_OSSINFOPevent v'44 = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = infonull /\ V_OSSINFOPevent v'44 = Some Vnull) \/
             eo = infohold /\ V_OSSINFOPevent v'44 = Some (Vptr vhold_addr) 
         ). 
  { clear -H'. intuition. }
  clear H'.
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget.
      hoare_lifts_trms_pre (Aop, seminfoid).
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply semflush_absimp_ecb_ptr_abt; eauto.
      eapply i_ge_z; eauto.
      eapply i_lt_user_max_event; eauto.
      left. split; pure_auto. destruct H5; tryfalse.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
    }
  assert (Hcases: 
      ((exists eid,  eo = infotid eid /\ V_pevent = Vptr eid) \/ eo = infonull /\ V_pevent = Vnull)
        \/ ( (exists eid,  eo = infotid eid /\ V_pevent <> Vptr eid) \/ eo = infonull /\ V_pevent <> Vnull)
    ).
  { inv Hok. destruct H5 as (eid & H'). 
    assert (Hvcs: V_pevent = Vptr eid \/ V_pevent <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: V_pevent = Vnull \/ V_pevent <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H5. split; auto.
    right. right. destructs H5. split; auto.
  }
  inversion Hcases.
  2: { hoare_lifts_trms_pre (Aop, seminfoid).
       eapply abscsq_rule.
       apply noabs_oslinv.
       eapply semflush_absimp_ecb_ptr_abt; eauto.
       eapply i_ge_z; eauto.
       eapply i_lt_user_max_event; eauto.
       pure_auto.
       eapply absinfer_eq. 
       apply absabort_rule.
     }
  hoare_lifts_trms_pre (Aop, seminfoid).
  destruct H5 as [(eid & Heo_eq & Hvp_eq) | (Heo_eq & Hvp_eq)].
  2:{ substs.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply semflush_absimp_if_null_yes_end; eauto.
      eapply i_ge_z; eauto.
      eapply i_lt_user_max_event; eauto.
      pure_auto.
      eapply absinfer_eq. 
      clear Hcases.
     (* excrit *) 
      eapply backward_rule1. 
      introv Hsat.
      eapply ASeminfo_select_sn_ex_strong.
      exists v'42 (Z.to_nat (Int.unsigned posv)) v'43 v'44.
      sep pauto.
      hoare forward prim.
      sep cancel tcbdllflag.
      sep cancel p_local.
      sep cancel Aier.
      unfold EvtInv.
      unfold ASemEIBs.
      sep pauto; eauto.
      sep cancel ASeminfo.
      sep cancel AMuxEIBs.
      sep cancel AMqEIBs.
      trycancel.
      sep cancel APthreadAttr.
      sep cancel CapabilityInv. 
      sep cancel ASemCap.
      eauto.
      pure_auto.
      pure_auto.
      destruct Hok as [(eid & Hfalse & _) | (_ & Hvp)].
      tryfalse.
      unfolds in Hvp.
      eapply nth_val_nth_val'_some_eq in Hvp.
      rewrite Hvp.
      hoare forward.
      hoare unfold.
      hoare forward.
      eapply hoare_disj_afalseP_l_pre.
      hoare unfold.
      destruct H5; tryfalse.
  }
  substs.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_if_null_no; eauto.
  eapply i_ge_z; eauto.
  eapply i_lt_user_max_event; eauto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.

   (* excrit *) 
  eapply backward_rule1. 
  introv Hsat.
  eapply ASeminfo_select_sn_ex_strong. 
  exists v'42 (Z.to_nat (Int.unsigned posv)) v'43 v'44.
  sep pauto.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep cancel Aier.
  unfold EvtInv.
  unfold ASemEIBs.
  sep pauto; eauto.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  trycancel.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel ASemCap.
  eauto.
  pure_auto.
  pure_auto.
  destruct Hok as [(eid' & Heo_eq & Hvp & Hvp_neq) | (Hfalse & _)].
  2 : { tryfalse. }
  inverts Heo_eq.
  unfolds in Hvp.
  eapply nth_val_nth_val'_some_eq in Hvp.
  rewrite Hvp.
  destruct eid' as (eid_b & eid_i).
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear H5.

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

  (* ENTER_CRITICAL;ₛ *)
  clear -E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
  hoare forward prim. 
  hoare unfold.
  rename v'16 into vpthattr.
  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20. 
  unfold EvtInv. unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'35.
  rename b into v'37.
  rename i into v'38.
  hoare_lifts_trms_pre (RH_SEM_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hs_nc.

  hoare_assert_pure (length v'25 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto. } 
  eapply pure_split_rule'; introv Hlen_info.
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto p).
  eapply backward_rule1.
  intros.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel ASeminfo.
  exact_s.
  rewrite Hlen_info.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  (* If (efield (Sem_info ′ [os_code_defs.pos ′]) pevent !=ₑ NULL) *)
  hoare unfold.
  rename H7 into HH7.
  rename H8 into HH8.
  rename H6 into H7.
  rename H9 into H8.
  rename H10 into H6.
  rename H12 into H10.
  rename H14 into H12.
  rename H16 into H14.
  rename H18 into H16.
  rename H13 into H11.
  rename H15 into H13.
  rename H17 into H15.
  hoare normal pre.
  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: semb_corr H7 H4 E1 Hlemu.
  destruct H00 as (eo & tp & sc & Hget & H').
  assert (Hcases: 
           ((exists eid,
                eo = infotid eid /\ V_OSSINFOPevent v'39 = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = infonull /\ V_OSSINFOPevent v'39 = Some Vnull) \/
             eo = infohold /\ V_OSSINFOPevent v'39 = Some (Vptr vhold_addr)
         ).
  { clear -H'. intuition. }
  clear H'.
  destruct Hcases as [ Hok | Habt ].
  2: { destruct Habt as (Habt1 & Habt2).
       rewrite Habt1 in Hget.
       hoare_lifts_trms_pre (Aop, seminfoid).
       eapply abscsq_rule.
       apply noabs_oslinv.
       eapply semflush_absimp_ecb_hold_abt; eauto.
       split; pure_auto. destruct H3; tryfalse.
       pure_auto.
       eapply absinfer_eq.
       apply absabort_rule.
  }
  unfold V_OSSINFOPevent in Hok.
  hoare_lifts_trms_pre (Aop, AECBList, os_code_defs.pos, A_dom_lenv).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: nil)%nat pre.
  protect HeqH3.
  eapply seq_rule.
  eapply lzh_if_then_rule.
  introv Hsat.
  sep_lift_context_in Hsat (Astruct).
  eapply uop_rv; eauto.
  eapply bop_rv; eauto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply Int.eq_false; eauto.
  eapply new_array_type_vallist_match_split in H1; eauto.
  mytac.
  sep get rv.
  destruct Hok as [((eid_b' & eid_i') & Heo & Hvp &Hvp_neq) | (Heo & Hvp)]; subst eo;
  eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp; simpl; pure_auto.
  simpl; eauto.
  destruct Hok as [((eid_b' & eid_i') & Heo & Hvp &Hvp_neq) | (Heo & Hvp)]; subst eo;
  eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp; go.
  go.

  hoare unfold.
  clear H17 H18.
  destruct Hok as [((eid_b' & eid_i') & Heo & Hvp &Hvp_neq) | (Heo & Hvp)]; subst eo;
  eapply nth_val_nth_val'_some_eq in Hvp; rewrite Hvp in H9; simpl in H9.
  2: { change ((Int.notbool Int.one)) with Int.zero in H9;tryfalse. }
  lets Hgete: H8 Hget.
  destruct Hgete as (n & wls & Hgete).

  unfold AECBList.
  hoare normal pre.
  hoare unfold.
  rename H17 into H_elp. (* ECBList_P ... *)
  lets Hctr: ECBList_P_get_ectr_some Hgete H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.
  hoare_assert_pure (length v'40 = length v'42).
  { get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg.
    eapply evsllseg_aux in Hsat.
    destruct Hsat.
    eauto.
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H_elp': H_elp.
  eapply ecblist_p_decompose in H_elp; eauto. 
  destruct H_elp as (els1 & els2 & x' & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).  

  hoare_assert_pure (x' = Vptr (v'49, Int.zero)).
  { get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 
  rename v'49 into eid_b'.
  hoare_assert_pure (i1 = ($ OS_EVENT_TYPE_SEM)).
  { get_hsat Hsat. 
    assert (Hcase: Int.eq i1 ($ OS_EVENT_TYPE_SEM) = false 
                                    \/ Int.eq i1 ($ OS_EVENT_TYPE_SEM) = true).
   clear; unfold OS_EVENT_TYPE_SEM; int auto.
   destruct Hcase as [Hf | Ht].
   sep_lifts_trms_in Hsat (AEventData).
   simpl in  Hecbl2.
   mytac.
   inverts H17.
   eapply sem_eventtype_neq_sem in Hsat; eauto.
   eapply EcbMod.join_sig_get in H40.
   eapply EcbMod.join_get_r in H40;eauto.
   unfold get in Hgete; unfold EcbMap in Hgete.
   rewrite Hgete in H40. inverts H40.
   sep split in Hsat.
   clear -H17. false. eapply H17; eauto.
   unfolds; simpl; auto.
   eapply semacc_int_eq_true; auto.
  }
  hoare_split_pure_all; subst.

  hoare_lifts_trms_pre (Aop).
  hoare unfold.
  eapply forward_rule1.
  2: { eapply lzh_if_then_rule.
       introv Hsat.
       eapply uop_rv; eauto.
       eapply bop_rv; eauto.
       (* sep_get_rv_array_struct'. *)
       eapply struct_member_e_rv.
       sep_get_rv_array_struct.
       rewrite Hdiveq; eauto.
       rewrite Hdiveq.
       eapply Int.eq_false; eauto.
       eapply new_array_type_vallist_match_split with (vl := v'39) in H1.
       mytac. eauto.
       mytac.
       sep cancel Astruct; eauto.
       pure_auto.
       pure_auto.
       pure_auto.
       simpl; auto.
       simpl; auto.
       simpl; auto.
       pure_auto.
       simpl; auto with zarith.
       go.
       simpl; auto.
       sep get rv.
       go.
       go.
       go.
       go.
       hoare unfold.
       simpl in H17; rewrite Int.eq_true in H17; simpl in H17.
       change ((Int.notbool Int.one)) with Int.zero in H17; tryfalse.
  }
  instantiate (2:= Afalse).
  introv Hsat.
  destruct Hsat as [Hsat | Hsat].
  sep pauto.
  clear -H17.
  simpl in H17; rewrite Int.eq_true in H17; simpl in H17.
  change ((Int.notbool Int.one)) with Int.zero in H17; tryfalse.
  instantiate (1:= fun v'12 => 
        ( <||
          semflush_get_not_hold (|Vint32 posv :: nil|);;
          semflush_type_err (|Vint32 posv :: nil|)
          ?? semflush_get_valid_ecb (|Vint32 posv :: nil|);;
             (semflush_no_wl (|Vint32 posv :: nil|)
                 ?? semflush_set_wl_all_rdy (|Vint32 posv :: nil|));;
             isched;; END Some (Vint32 Int.zero) ||>  **
         evsllseg v'12 Vnull v'18 v'21 **
          GV OSEventList @ OS_EVENT ∗ |-> v'12 **
          [|ECBList_P v'12 Vnull v'18 v'21 v'9 v'10 |] **
          LV os_code_defs.pos @ long |-> Vint32 posv **
          A_dom_lenv
            ((sem, (long) ∗)
             :: (os_code_defs.pos, long)
                :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
          GV Sem_info @ sem_info_t ∗ |-> Vptr (v'37, v'38) **
          Aarray_new (v'37, v'38)
            (Tarray sem_info_t (Z.to_nat (Int.unsigned posv))) v'35 **
          Astruct
            (v'37,
            v'38 +ᵢ
            $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
            sem_info_t v'39 **
          Aarray_new
            (v'37,
            v'38 +ᵢ
            $ Z.of_nat (S (Z.to_nat (Int.unsigned posv)) * typelen sem_info_t))
            (Tarray sem_info_t
               ∘ (OS_USER_MAX_EVENTS / 3 -
                  Z.of_nat (S (Z.to_nat (Int.unsigned posv))))) v'36 ** H3)).
  sep pauto.
  sep cancel Aop.
  eapply evsllseg_compose; eauto.
  unfolds; simpl; eauto.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  split; auto. go.
  
  (* EXIT_CRITICAL  *)
  eapply backward_rule1.
  introv Hsat.
  instantiate (1:= (
         <||
          semflush_get_not_hold (|Vint32 posv :: nil|);;
          semflush_type_err (|Vint32 posv :: nil|)
          ?? semflush_get_valid_ecb (|Vint32 posv :: nil|);;
             (semflush_no_wl (|Vint32 posv :: nil|)
                 ?? semflush_set_wl_all_rdy (|Vint32 posv :: nil|));;
             isched;; END Some (Vint32 Int.zero) ||>  **
          AECBList v'18 v'21 v'9 v'10 **
          LV os_code_defs.pos @ long |-> Vint32 posv **
          A_dom_lenv
            ((sem, (long) ∗)
             :: (os_code_defs.pos, long)
                :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
           GV Sem_info @ sem_info_t ∗ |-> Vptr (v'37, v'38) **
          Aarray_new (v'37, v'38)
            (Tarray sem_info_t (Z.to_nat (Int.unsigned posv))) v'35 **
          Astruct
            (v'37,
            v'38 +ᵢ
            $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
            sem_info_t v'39 **
          Aarray_new
            (v'37,
            v'38 +ᵢ
            $ Z.of_nat (S (Z.to_nat (Int.unsigned posv)) * typelen sem_info_t))
            (Tarray sem_info_t
               ∘ (OS_USER_MAX_EVENTS / 3 -
                  Z.of_nat (S (Z.to_nat (Int.unsigned posv))))) v'36 ** H3)).
  destruct Hsat as [Hsat | Hsat].
  unfold AECBList.
  sep pauto.
  sep pauto.
  
  (* real exit critical *)
  unprotect HeqH3.
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold ASemEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel Aier.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'35 (Z.to_nat (Int.unsigned posv)) v'36 v'39.
  sep pauto; eauto.
  pure_auto.
  pure_auto.

  (* ENTER_CRITICAL *)
  clear -E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
  hoare_lifts_trms_pre (Aop, os_code_defs.pos, x, p, y, sem).
  hoare forward prim. 
  hoare unfold.
  rename v'16 into vpthattr.
  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20.
  unfold EvtInv. unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'35.
  rename b into v'37.
  rename i into v'38.
  hoare_lifts_trms_pre (RH_SEM_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hs_nc.

  hoare_assert_pure (length v'25 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto. } 
  eapply pure_split_rule'; introv Hrqdata.
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos, Alvarmapsto p).
  eapply backward_rule1.
  intros.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel ASeminfo.
  exact_s.
  rewrite Hrqdata.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  rename H7 into HH7.
  rename H8 into HH8.
  rename H6 into H7.
  rename H9 into H8.
  rename H10 into H6.
  rename H12 into H10.
  rename H14 into H12.
  rename H16 into H14.
  rename H18 into H16.
  rename H13 into H11.
  rename H15 into H13.
  rename H17 into H15.
  hoare normal pre.
  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: semb_corr H7 H4 E1 Hlemu. 
  destruct H00 as (eo & tp & sc & Hget & H').
  assert (Hcases: 
           (exists eid,
                eo = infotid eid /\ V_OSSINFOPevent v'39 = Some (Vptr eid) /\ eid <> vhold_addr) \/
              eo = infonull /\ V_OSSINFOPevent v'39 = Some Vnull \/
             eo = infohold /\ V_OSSINFOPevent v'39 = Some (Vptr vhold_addr)
         ).
  { clear -H'. intuition. }
  clear H'.
  destruct Hcases as [ Hok | Habt ].
  2: { hoare_lifts_trms_pre (Aop, seminfoid).
       eapply abscsq_rule.
       apply noabs_oslinv.
       eapply semflush_absimp_valid_ecb_abt; eauto.
       destruct Habt as [(Heo & _)| (Heo & _)]; subst eo.
       pure_auto. destruct H3;tryfalse.
       pure_auto. destruct H3; tryfalse.
       pure_auto.
       eapply absinfer_eq.
       apply absabort_rule.
  }
  unfold V_OSSINFOPevent in Hok.
  destruct Hok as ((eid_b' & eid_i') & Heo & Hvp &Hvp_neq); subst eo;
  eapply nth_val_nth_val'_some_eq in Hvp.
  hoare_lifts_trms_pre (Aop, seminfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_valid_ecb_cons; eauto.
  pure_auto.
  eapply absinfer_eq.

  lets Hgete: H8 Hget.
  destruct Hgete as (n & wls & Hgete).

  unfold AECBList.
  hoare normal pre.
  hoare unfold.
  rename H3 into H_elp. (* ECBList_P ... *)
  lets Hctr: ECBList_P_get_ectr_some Hgete H_elp. 
  destruct Hctr as (evl & etbl & petbl & Hgetectr).
  
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.
  hoare_assert_pure (length v'40 = length v'42).
  { get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg.
    eapply evsllseg_aux in Hsat.
    destruct Hsat.
    eauto.
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H_elp': H_elp.
  eapply ecblist_p_decompose in H_elp; eauto. 
  destruct H_elp as (els1 & els2 & x' & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).  

  hoare_assert_pure (x' = Vptr (v'49, Int.zero)).
  { get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst. 
  rename v'49 into eid_b'.
   hoare_assert_pure (i1 = ($ OS_EVENT_TYPE_SEM)).
  { get_hsat Hsat. 
    assert (Hcase: Int.eq i1 ($ OS_EVENT_TYPE_SEM) = false 
                                    \/ Int.eq i1 ($ OS_EVENT_TYPE_SEM) = true).
   clear; unfold OS_EVENT_TYPE_SEM; int auto.
   destruct Hcase as [Hf | Ht].
   sep_lifts_trms_in Hsat (AEventData).
   simpl in  Hecbl2.
   mytac.
   inverts H3.
   eapply sem_eventtype_neq_sem in Hsat; eauto.
   eapply EcbMod.join_sig_get in H38.
   eapply EcbMod.join_get_r in H38;eauto.
   unfold get in Hgete; unfold EcbMap in Hgete.
   rewrite Hgete in H38. inverts H38.
   sep split in Hsat.
   clear -H3. false. eapply H3; eauto.
   unfolds; simpl; auto.
   eapply semacc_int_eq_true; auto.
   }
  hoare_split_pure_all; subst.

  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).

   (*WHILE (efield (Sem_info ′ [os_code_defs.pos ′]) pevent !=ₑ NULL &&ₑ
       (efield (Sem_info ′ [os_code_defs.pos ′]) pevent) → OSEventGrp !=ₑ ′ 0) *)

(*1: remember irrelevant sep-conjunctions*)
  hoare_lifts_trms_pre (Aop, os_code_defs.pos, (Alvarmapsto y),p_local, A_dom_lenv,
                                                AOSMapTbl,AOSUnMapTbl,AOSTCBPrioTbl,AOSTCBList,AOSRdyTblGrp,
                                              tcbdllflag,tcbllsegevaux).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: 11 :: 12 :: 
                  15 :: 16 :: 17 :: 18 :: 19 :: 20 :: 21 :: 22 :: 23 :: 24 :: 25 :: 26 :: nil)%nat pre.
  protect HeqH3.
  unfold AOSTCBList.
  hoare unfold.
  rename v'10 into tcbls.
  rename v'46 into tcbls_l.
  rename v'49 into tcbls_r.
  rename v'0 into tcb_head.
  rename v'3 into tcbvl_l.
  rename v'4 into tcbvl_ct.
  rename v'6 into tcbvl_r.
  rename v'7 into rtbl.
  rename v'8 into rgrp.
  hoare_assert_pure(v'44 = DSem i2).
  {  get_hsat Hsat.
    destruct v'44; simpl AEventData in Hsat;
   unfold V_OSEventType, V_OSEventCnt in Hsat; simpl nth_val in Hsat;
   sep split in Hsat; tryfalse.
   inverts H40. auto.
  }
  hoare_split_pure_all; subst.
  lets Hcp: Hecbl2.
  simpl in Hcp.
  mytac.
  inverts H39.
  unfolds in H42; simpl in H42; inverts H42.
  eapply EcbMod.join_sig_get in H43.
  eapply EcbMod.join_get_r in H43;eauto.
  unfold get in Hgete; unfold EcbMap in Hgete.
  rewrite Hgete in H43. inverts H43.
  rename H41 into Hpetbl.
  destruct H44 as (Hcnt_eq & Hrh_ecb).
  subst i2.
  simpl in Hrh_ecb.
  destruct Hrh_ecb as (Hcnt_wl_nil & Hcnt_wl_not_nil).
  rename v'9 into els.
   rename v'15 into ptls.

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)
  eapply backward_rule1 with (p := (*below is the loop inv*)
       (EX etbl' tcbvl_l' tcbvl_r' tcbvl_ct' rtbl' rgrp' egrp subwl vy tail tcbls_l' tcbls_r',
 <||
  (semflush_no_wl (|Vint32 posv :: nil|)
   ?? semflush_set_wl_all_rdy (|Vint32 posv :: nil|));;
  isched;; END Some (Vint32 Int.zero) ||>  **
  LV y @ Int16u |-> vy **
  LV os_code_defs.pos @ long |-> Vint32 posv **
  p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  A_dom_lenv
    ((sem, (long) ∗)
     :: (os_code_defs.pos, long)
        :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t):: nil) **
  AOSMapTbl **
  AOSUnMapTbl **
  AOSTCBPrioTbl v' rtbl' (set_tls_rdy subwl tcbls) ptls vhold_addr **
  GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
  tcbdllseg tcb_head Vnull tail (Vptr tid) tcbvl_l' **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
  tcbdllseg (Vptr tid) tail v'21 Vnull (tcbvl_ct' :: tcbvl_r') **
  [| TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy subwl tcbls) |] **
  [| TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l' |] **
  [| TCBList_P (Vptr tid) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r' |] **
  [| RH_TCBList_ECBList_P (set els (eid_b', Int.zero) (abssem n, (remove_wls subwl wls))) (set_tls_rdy subwl tcbls) tid |] **
  tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **
  tcbllsegevaux tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') v'33 v'34 **
  AOSRdyTblGrp rtbl' rgrp' **
  Astruct (eid_b', Int.zero) OS_EVENT
    (V$ OS_EVENT_TYPE_SEM :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil) **
  Aarray v'45 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
  AOSPostEventTbl v'47 petbl ** (* new add *)
  AEventData
    (V$ OS_EVENT_TYPE_SEM :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil)
    (DSem n) **
  evsllseg v'12 (Vptr (eid_b', Int.zero)) v'40 v'42 **
  evsllseg x5 Vnull v'41 v'43 **
  GV OSEventList @ OS_EVENT ∗ |-> v'12 **
  HSEMInfo v'28 **
  GV Sem_info @ sem_info_t ∗ |-> Vptr (v'37, v'38) **
  Aarray_new (v'37, v'38) (Tarray sem_info_t (Z.to_nat (Int.unsigned posv)))
    v'35 **
  Astruct
    (v'37,
    v'38 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
    sem_info_t v'39 **
  Aarray_new
    (v'37,
    v'38 +ᵢ
    $ Z.of_nat (S (Z.to_nat (Int.unsigned posv)) * typelen sem_info_t))
    (Tarray sem_info_t
       ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (Z.to_nat (Int.unsigned posv)))))
    v'36 ** H3 **
     [| (RL_Tbl_Grp_P etbl' (Vint32 Int.zero)  /\ array_type_vallist_match Tint8 etbl' /\
          egrp = Int.zero /\ ( ( subwl = nil \/ (forall t : Modules.tid, In t subwl -> In t wls)) /\ remove_wls subwl wls = nil) /\ length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp = 0, get out of the loop *)
         ECBList_P v'12 Vnull
           (v'40 ++
            ((V$ OS_EVENT_TYPE_SEM
              :: Vint32 Int.zero :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil, etbl',petbl) :: nil) ++
            v'41) (v'42 ++ (DSem n :: nil) ++ v'43) 
            (set els (eid_b', Int.zero) (abssem n, nil)) (set_tls_rdy wls tcbls)) \/
        (is_subl subwl wls /\
         RL_Tbl_Grp_P etbl' (Vint32 egrp)  /\ array_type_vallist_match Tint8 etbl' /\
         egrp <> Int.zero /\ Int.unsigned egrp <= 255 /\  length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp <> 0, still in the loop *)
         ECBList_P v'12 Vnull
           (v'40 ++
            ((V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil, etbl',petbl) :: nil) ++
            v'41) (v'42 ++ (DSem n :: nil) ++ v'43) 
                        (set els (eid_b', Int.zero) (abssem n, (remove_wls subwl wls))) 
                        (set_tls_rdy subwl tcbls)) |]
       )).
  introv Hsat.
  assert (Hegrp_case: i0 = Int.zero \/ i0 <> Int.zero) by tauto.
  destruct Hegrp_case as [Hegrp_zero | Hegrp_nzero].
  (* case1: egrp = 0*)
  subst.
  assert (Hwls: wls = nil).
  { eapply Grp_eq_zero_imp_wl_nil; eauto. }
  subst wls.
  assert(Hels: set els (eid_b', Int.zero) (abssem n, nil) = els ).
  { eapply EcbMod.get_set_same; eauto. }
  do 7 eexists.
  exists (nil: list Modules.tid).
  do 4 eexists.
  rewrite remove_wls_nil.
  rewrite Hels.
  rewrite set_tls_rdy_nil.
  sep pauto; eauto.
  sep cancel (tcbdllseg tcb_head).
  sep cancel tcbdllseg.
  sep cancel Aop.
  sep cancel A_dom_lenv.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp.
  sep cancel tcbdllflag.
  sep cancel tcbllsegevaux.
  left.
  splits; eauto.
  (* case2: egrp <> 0 *)
  assert (Hwls: wls <> nil).
  { eapply Grp_eq_nz_imp_wl_not_nil; eauto. }
  assert(Hels: set els (eid_b', Int.zero) (abssem n, (remove_wls nil wls)) = els ).
  { eapply EcbMod.get_set_same; eauto. }
  do 7 eexists.
  exists (nil: list Modules.tid).
  do 4 eexists.
  rewrite Hels.
  rewrite set_tls_rdy_nil.
  assert (His_subl_nil: is_subl nil wls).
  {  eapply nil_is_subl; eauto. }
  sep pauto; eauto.
  sep cancel (tcbdllseg tcb_head).
  sep cancel tcbdllseg.
  sep cancel Aop.
  sep cancel A_dom_lenv.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp.
  sep cancel tcbdllflag.
  sep cancel tcbllsegevaux.
  right.
  splits; eauto.

  (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
  eapply seq_rule.

  (*4: prove the condition expression of while is legal *)
  eapply while_rule with (tp := Int32u).
  (* prove  EX v : val,
  Rv efield (Sem_info ′ [os_code_defs.pos ′]) pevent !=ₑ NULL &&ₑ
   (efield (Sem_info ′ [os_code_defs.pos ′]) pevent) → OSEventGrp !=ₑ ′ 0 @
  long == v *)
  { introv Hsat.
    assert(Hrv_pevent: 
                    s |= Rv efield (Sem_info ′ [os_code_defs.pos ′]) pevent @ 
                                                                                            OS_EVENT ∗ == Vptr (eid_b', Int.zero)).
  {
     sep destruct Hsat;
     eapply struct_array_member_rv; auto;
     try sep get rv;
     try (fold sem_info_t; sep pauto);
     try go;
     auto;
     try (apply pos_rgn_comp'; auto;
             rewrite Hdiveq; eauto;
             eapply Int.eq_false; eauto;
             simpl; apply thirty_two_min_max);
     try (eapply new_array_type_vallist_match_split in H1; eauto;
              mytac);
     try (intro Hf; destruct Hf as (t'' & n' & Hf); inv Hf).
  }
  sep destruct Hsat.
  eexists.
  eapply bop_rv; eauto.
  eapply uop_rv; eauto.
  eapply bop_rv; eauto.
  sep get rv.
  go.
  go.
  go.
  go.
  eapply uop_rv; eauto.
  eapply bop_rv; eauto.
  (* sep_get_rv_array_struct' *)
  eapply struct_member_e_rv.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  eapply Int.eq_false; eauto.
  eapply new_array_type_vallist_match_split with (vl := v'39) in H1.
  mytac. eauto.
  mytac.
  sep cancel Astruct; eauto.
  pure_auto.
  pure_auto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  simpl; auto.
  pure_auto.
  simpl; auto with zarith.
  sep split in Hsat.
  mytac.
  auto.
  destruct H44 as [Hegrp_zero | Hegrp_nz]; mytac; tryfalse.
  go. go. go.
  sep get rv.
  clear; simpl; pure_auto.
  go.
  clear; simpl; pure_auto.
  go.
  clear; simpl; pure_auto.
  go.
}

  (*prove the condition expression of while is legal *)
  (*Aistrue
    (efield (Sem_info ′ [os_code_defs.pos ′]) pevent !=ₑ NULL &&ₑ
     (efield (Sem_info ′ [os_code_defs.pos ′]) pevent) → OSEventGrp !=ₑ ′ 0)*)

  (*5: the cond-expr of while hold implies the right part
    of the loop-inv*)
  eapply backward_rule1 with ( p:= (
     EX etbl' tcbvl_l' tcbvl_r' tcbvl_ct' rtbl' rgrp' egrp subwl vy tail (tcbls_l' tcbls_r': TcbMod.map),
 <||
  (semflush_no_wl (|Vint32 posv :: nil|)
   ?? semflush_set_wl_all_rdy (|Vint32 posv :: nil|));;
  isched;; END Some (Vint32 Int.zero) ||>  **
  LV y @ Int16u |-> vy **
  LV os_code_defs.pos @ long |-> Vint32 posv **
  p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  A_dom_lenv
    ((sem, (long) ∗)
     :: (os_code_defs.pos, long)
        :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t):: nil) **
  AOSMapTbl **
  AOSUnMapTbl **
  AOSTCBPrioTbl v' rtbl' (set_tls_rdy subwl  tcbls) ptls vhold_addr **
  GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
  tcbdllseg tcb_head Vnull tail (Vptr tid) tcbvl_l' **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
  tcbdllseg (Vptr tid) tail v'21 Vnull (tcbvl_ct' :: tcbvl_r') **
  [| TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy subwl tcbls) |] **
   [| TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l' |] **
   [| TCBList_P (Vptr tid) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r' |] **
   [| is_subl subwl wls |] **
   [| RH_TCBList_ECBList_P (set els (eid_b', Int.zero) (abssem n, (remove_wls subwl wls)))
                                                         (set_tls_rdy subwl tcbls) tid |] **
   tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **
  tcbllsegevaux tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') v'33 v'34 **
  AOSRdyTblGrp rtbl' rgrp' **
  Astruct (eid_b', Int.zero) OS_EVENT
    (V$ OS_EVENT_TYPE_SEM :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil) **
  Aarray v'45 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
  AOSPostEventTbl v'47 petbl ** (* new add *)
  AEventData
    (V$ OS_EVENT_TYPE_SEM :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil)
    (DSem n) **
  evsllseg v'12 (Vptr (eid_b', Int.zero)) v'40 v'42 **
  evsllseg x5 Vnull v'41 v'43 **
  GV OSEventList @ OS_EVENT ∗ |-> v'12 **
  HSEMInfo v'28 **
  GV Sem_info @ sem_info_t ∗ |-> Vptr (v'37, v'38) **
  Aarray_new (v'37, v'38) (Tarray sem_info_t (Z.to_nat (Int.unsigned posv)))
    v'35 **
  Astruct
    (v'37,
    v'38 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
    sem_info_t v'39 **
  Aarray_new
    (v'37,
    v'38 +ᵢ
    $ Z.of_nat (S (Z.to_nat (Int.unsigned posv)) * typelen sem_info_t))
    (Tarray sem_info_t
       ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (Z.to_nat (Int.unsigned posv)))))
    v'36 ** H3 **
     [| RL_Tbl_Grp_P etbl' (Vint32 egrp)  /\ array_type_vallist_match Tint8 etbl' /\
         egrp <> Int.zero /\ Int.unsigned egrp <= 255 /\  length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp <> 0, still in the loop *)
         ECBList_P v'12 Vnull
           (v'40 ++
            ((V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil, etbl',petbl) :: nil) ++
            v'41) (v'42 ++ (DSem n :: nil) ++ v'43) 
                        (set els (eid_b', Int.zero) (abssem n, (remove_wls subwl wls))) 
                        (set_tls_rdy subwl tcbls) |]
  )).
  introv Hsat.
  destruct Hsat as (Hsat & Histrue).
  sep destruct Hsat.
  lets Hcp: aconj_intro Hsat Histrue.
  eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
  2: {clear Hsat Hcp Histrue. introv Hsat.
  assert(Hrv_pevent: 
                    s0 |= Rv efield (Sem_info ′ [os_code_defs.pos ′]) pevent @ 
                                                                                            OS_EVENT ∗ == Vptr (eid_b', Int.zero)).
  { sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq.
     eapply Int.eq_false; eauto.
     eapply new_array_type_vallist_match_split in H1; eauto;
     mytac.
   }
  sep split in Hsat.
  mytac.
  assert (Hegrp_range: Int.unsigned x10 <= 255).
  { destruct H44 as [Hegrp_zero | Hegrp_nz]; mytac; auto. }
  eapply bop_rv; eauto.
  eapply uop_rv; eauto.
  eapply bop_rv; eauto.
  sep get rv.
  go.
  go.
  go.
  go.
  eapply uop_rv; eauto.
  eapply bop_rv; eauto.
  (* sep_get_rv_array_struct'. *)
  eapply struct_member_e_rv.
  eauto.
  sep cancel Astruct; eauto.
  pure_auto.
  pure_auto.
  pure_auto.
  simpl; auto.
  simpl; auto.
  simpl; auto.
  pure_auto.
  simpl; auto with zarith.
  sep split in Hsat.
  mytac.
  auto.
  destruct H44 as [Hegrp_zero | Hegrp_nz]; mytac; tryfalse.
  go. go. go.
  sep get rv.
  clear; simpl; pure_auto.
  go.
  clear; simpl; pure_auto.
  go.
  clear; simpl; pure_auto.
  go.
}
  clear -Hcp.
  sep_lifts_trms_in Hcp (RL_Tbl_Grp_P,bop_eval).
  eapply sep_pure_split in Hcp.
  destruct Hcp as (Hcases & Hcp).
  eapply sep_pure_split in Hcp.
  destruct Hcp as (Histrue & Hcp).
  destruct Hcases as [Hf | Ht].
  mytac.
  simpl in H.
  rewrite Int.eq_true in H;
  change (Int.notbool Int.zero) with Int.one in H;
  simpl in H;
  change (Int.notbool Int.one) with Int.zero in H;
  change (Int.ltu Int.zero Int.zero) with false in H;
  change (Int.ltu Int.zero Int.one) with true in H;
  simpl in H.
  tryfalse.
  sep pauto; eauto.
  splits; auto. (* new add *)

  (*y ′ =ₑ ′ OS_STAT_SEM;ₛ
  OS_EventTaskRdy (­efield (Sem_info ′ [os_code_defs.pos ′]) pevent, NULL, y ′­)*)
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  hoare forward.
  simpljoin.
  (* OS_EventTaskRdy (­efield (Sem_info ′ [os_code_defs.pos ′]) pevent, NULL, y ′­) *)
  unprotect HeqH3.
  subst H3.

  unfold AOSTCBPrioTbl.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  eapply conseq_rule; [eauto | idtac | idtac].

  Focus 2.
  Ltac hoare_call' :=
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} scall _ ?el {{ _ }} =>
      match find_aop P with 
        | some ?n =>  
              hoare lifts (n::nil)%nat pre; 
                eapply call_rule';
                [intuition eauto | 
                 intros; 
                    do 5 try (apply rvl_elim;[ try (eapply symbolic_lemmas.cast_rv_tnull; [sep get rv |  simpl; auto]); symbolic_execution | ]);
                     first [apply rvl_nil | simpl;auto] |
                 intros;  unfold_spec; sep normal; sep eexists; sep_cancel_iers(* ; sep pauto *) |
                 idtac |
                 sep_unfold_funpost |
                 sep_unfold_funpre |
                 simpl;eauto
                ] 
        | none _ => idtac
      end
  end.
  hoare_call'.

  2:{ instantiate (6:= (set_tls_rdy v'9 tcbls)). 
      sep cancel A_isr_is_prop.
      sep cancel AOSRdyTblGrp.
      sep cancel p_local.
      unfold AEventNode.
      unfold AOSEvent.
      unfold node.
      unfold AOSEventTbl.
      sep normal.
      sep eexists.
      sep cancel AOSPostEventTbl.
      sep cancel AEventData.
      sep cancel Aarray.
      sep split; eauto.
      sep cancel Astruct.
      sep cancel AOSUnMapTbl.
      sep cancel AOSMapTbl.
      sep_lifts_trms tcbdllseg.
      eapply tcbdllseg_compose. 
      sep cancel tcbdllseg.
      sep cancel (tcbdllseg (Vptr tid)). 
      sep cancel OSTCBPrioTbl.
      exact_s.
      unfold V_OSEventGrp; simpl; split; eauto.
      instantiate (2:= (Vptr (eid_b', Int.zero) :: Vnull :: V$ OS_STAT_SEM :: nil)).
      simpl; eauto.
      simpl; eauto.
      simpl; eauto.
      eapply TCBList_P_Combine; [idtac | idtac | eauto | eauto].
      eapply tcbdllseg_get_last_tcb_ptr.
      instantiate (4:=s).
      sep cancel (tcbdllseg tcb_head).
      eauto.
      eauto.
      lets H_elp: H51.
      eapply ecblist_p_decompose in H_elp; eauto.
      destruct H_elp as (els1' & els2' & x' & H'').
      destruct H'' as (Hecbl1' & Hecbl2' & Hjo').
      assert (Hx_eq: x' = Vptr (eid_b', Int.zero)).
      { get_hsat Hsat.
        sep_lifts_trms_in Hsat evsllseg.
        eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
      }
      subst x'. 
      simpl in Hecbl2'.
      mytac.
      inverts H57; auto.
      eapply tcbdllseg_combine_ptr_in_tcblist.
      instantiate (7:=s).
      sep cancel tcbdllseg.
      sep cancel tcbdllseg.
      eauto.
      auto.
      pure_auto.
  }
  { get_hsat Hsat.
    assert(Hrv_pevent: s |= Rv efield (Sem_info ′ [os_code_defs.pos ′]) pevent @ 
                                                                                           OS_EVENT ∗ == Vptr (eid_b', Int.zero)).
   { sep_get_rv_array_struct.
     rewrite Hdiveq; eauto.
     rewrite Hdiveq.
     eapply Int.eq_false; eauto.
     eapply new_array_type_vallist_match_split in H1; eauto;
     mytac.
   }
   sep_lifts_trms_in Hsat ((Alvarmapsto y), A_dom_lenv, Astruct (eid_b', Int.zero)).
   sep remember (1 :: 2 :: 3 :: nil)%nat in Hsat.
   lets Hcp: aconj_intro Hsat Hrv_pevent.
   clear -Hcp.
   destruct_s s.
   simpl in Hcp.
   simpl.
   simpljoin1.
   splits; auto.
   rewrite H61.
   splits; auto.
   eapply mapstoval_load in H62; eauto.
   change (Int.unsigned Int.zero) with 0 in H62.
   eapply load_local in H62; eauto.
   eapply join_emp_eq in H58; subst.
   eauto.
  }
  
  pure_auto.
  
  intros.
  sep auto.

  intros.
  sep auto.
  
  simpl. clear; pure_auto.
  introv Hsat.
  (* get_hsat Hsat. *)
  unfold OS_EventTaskRdyPost in Hsat.
  unfold OS_EventTaskRdyPost' in Hsat.
  unfold getasrt in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep_lifts_trms_in Hsat (Aop, A_dom_lenv, A_isr_is_prop).
  sep remember (1 :: 2 :: 3 :: nil)%nat in Hsat.
  (* lets Hsat': Hsat.
  protect Hsat'. *)
  subst H55.
  unfold AEventNode in Hsat.
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  unfold AOSEventTbl in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  inverts H93.
  simpl nth_val in *.
  inverts H84; inverts H85; inverts H86.
  substs.
  rename x14 into egrp.
  rename x15 into egrp'.
  simpl update_nth_val in *.
  mytac.
  inverts H55.
  rename x59 into eid_b'.
  inverts H58.
(*   unfold V_OSEventGrp in H54; simpl in H54; inverts H54. *)
  rewrite H19 in H57; inverts H57.
  inverts H61.
  rewrite H22 in H60; inverts H60.
  (* renameing *)
  rename tid into ctcb.
  rename x53 into htcb_addr. (* highest tcb in pevent waitlist *)
  rename H66 into Hhtcb.
  rename H87 into Hctcb_in_tcblist.
  rename x24 into tcblist_head.
  rename v'1 into tcblist_seg1.
  rename v'4 into ctcb_node.
  rename v'3 into tcblist_seg2.
  rename H70 into Hrel_et.

  (* ** ac: Print prio_in_tbl. *)
  rename x9 into ptbl'.
  rename x10 into rtbl'.
  rename v'9 into subwl.
  rename x16 into etbl'.
  (* ** ac: Print TCBList_P. *)

  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.

  (* ** ac: Print priority. *)
  (* ** ac: Print rel_edata_tcbstat. *)
  rename x48 into hprio.
  assert (exists hprio', hprio = Vint32 hprio').
  {
    clear - H78. (* struct_type_vallist_match *)
    (* ** ac: SearchAbout struct_type_vallist_match. *)
    (* ** ac: Print struct_type_vallist_match. *)
    rename H78 into H.
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
  destruct H55.
  subst hprio.
  rename x into hprio.
  
  rename x42 into hnext.
  rename x49 into htcbx.
  rename x50 into htcby.
  rename x51 into hbitx.
  rename x52 into hbity.

  (* ** ac: Check tcblist_get_TCBList_P_get. *)
  assert (Hhtcb_get: exists st m sus, get (set_tls_rdy subwl tcbls) (htcb_addr, Int.zero) = Some (hprio, st, m, sus)).
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }
  destruct Hhtcb_get as (st & msg & sus & Hhtcb_get).
  assert (Hs1: Int.unsigned x36 <= 7).
  {
    (* ** ac: Check osunmapvallist_prop. *)
    clear - H49 H71.
    apply osunmapvallist_prop in H49.
    mytac.
    rewrite H in H71.
    inverts H71.
    auto with zarith.
  }
  assert (Hs2: Int.unsigned x37 <= 255).
  {
    (* ** ac: Check array_int8u_nth_lt_len. *)
    clear - H72 Hs1 H83 H50.
    assert (Z.to_nat (Int.unsigned x36) < length etbl')%nat.
    {
      rewrite H50; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H83 H.
    mytac.
    rewrite H72 in H0.
    inverts H0.
    auto.
  }
  assert (Hs3: Int.unsigned x35 <= 7).
  {
    clear - H73 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H73; inverts H73.
    auto with zarith.
  }
  (* ** ac: Check post_exwt_succ_pre_sem. *)
  lets H_elp_subwl: H51.
  eapply ecblist_p_decompose in H51; eauto. 
  destruct H51 as (els1_new & els2_new & x' & H'').
  destruct H'' as (Hecbl1_new & Hecbl2_new & Hjo_new).
  assert (Hx': x' = Vptr (eid_b', Int.zero)).
  {
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'.
  lets Hcp: Hecbl2_new.
  simpl in Hcp.
  mytac.
  inverts H51.
  inverts H58.
  assert (Hx2: x2 = (abssem n, remove_wls subwl wls)).
  {
   eapply EcbMod.join_sig_get in H60.
   eapply EcbMod.join_get_r in H60; eauto.
   rewrite EcbMod.map_get_set in H60.
   inverts H60. auto. }
  subst x2.
  destruct H61 as (_ & Hrh_ecb_new).
  rename H60 into Hjo_sig_new.
  rename H66 into Hecb_right_new.
  clear H55.

  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  remember (remove_wls subwl wls) as pwls.
  assert (Hpre: pwls <> nil /\ GetHWait (set_tls_rdy subwl tcbls) pwls (htcb_addr, Int.zero) /\
                TcbMod.get (set_tls_rdy subwl tcbls) (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((x36<<ᵢ$ 3) +ᵢ  x35)).
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    eapply post_exwt_succ_pre_sem; eauto.
  }
  destruct Hpre as (Hpwls_not_nil & Hhwait & Hhtcb_get' & Hhprio_eq).
  subst hprio.

(* ** ac: Check sem_post_get_tcb_stat. *)
  rename H92 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get. 
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H51; inverts H55.

  rename H58 into Hh_tcbblk.
  rename H60 into Hh_tcbstat.
  unfolds in Hh_tcbblk.
  mytac.
  inverts H51.
  inverts H55; inverts H58; inverts H60; inverts H61; inverts H66; inverts H93.

  rename x36 into p1.
  rename x35 into p2.
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio. 
  assert (Hx: x10 = $ OS_STAT_SEM  \/ x10 = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }
  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  } 
  assert (Hs4: Int.unsigned x54 <= 255).
  { 
    clear - Hs1 H63 H69 H68. 
    assert (Z.to_nat (Int.unsigned p1) < length rtbl')%nat.
    {
      rewrite H69.
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H68 H. 
    mytac.
    rewrite H63 in H0. 
    inverts H0.
    auto.
  }
  (* ** ac: Check set_node_elim. *)
  assert (Htmp: x38 = $ 1 <<ᵢ p2).
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst x38.
  assert (Hno_dup: R_Prio_No_Dup (set_tls_rdy subwl tcbls)).
  {
    clear - H53.
    unfolds in H53.
    mytac.
  }

  sep_lifts_trms_in Hsat (tcbdllseg).
  (* eapply set_node_elim in Hsat; eauto. *)
  eapply set_node_elim_sus in Hsat; eauto.
  2: { eapply TCBNode_P_set_rdy_gen; eauto. 
       rewrite Hp1. 
       eapply nth_val'2nth_val; eauto.
       destruct Hx; subst x10.
       assert (Hsus: sus = false) by
       (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
       subst.
       rewrite Int.and_not_self; auto.
       assert (Hsus: sus = true) by
       (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
       subst.
       change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
       auto.
   }
   2:{ destruct sus eqn: eq1; auto.
       unfolds.
       rewrite Hp1. rewrite Hp2.
       do 2 eexists. splits; eauto. }
   2: {  unfolds. unfold V_OSTCBNext, V_OSTCBPrev. simpl. auto. }
   sep normal in Hsat.
   sep destruct Hsat.
   sep split in Hsat.
   rename H51 into Htcblist_new.
   rename H55 into Htcbjoin_new_set.
   rename H58 into Htcblist_p_new_left.
   rename H60 into Htcblist_p_new_right.
   assert (Htcbjoin_new_set': TcbMod.join x9 x14
                     (set_tls_rdy ((htcb_addr, Int.zero) :: nil)
                          (set_tls_rdy subwl tcbls) )).
  { clear -Htcbjoin_new_set Hhtcb_get.
    simpl set_tls_rdy.
    unfold get in *; unfold TcbMap in *.
    rewrite Hhtcb_get. auto.
  }
  clear Htcbjoin_new_set; rename Htcbjoin_new_set' into Htcbjoin_new_set.
  rewrite set_tls_rdy_succ_eq in Htcbjoin_new_set.
  assert (Hin_pwls: In (htcb_addr, Int.zero) (remove_wls subwl wls)).
  { clear -Hhwait. funfold Hhwait. mytac. }
  assert (Hst: exists xl,st = wait (os_stat_sem (eid_b', Int.zero)) xl).
  {  eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto. }
  destruct Hst as (st_t & Hst). 
  subst st.
  assert (Hr_ptbl_new: R_PrioTbl_P ptbl' (set_tls_rdy ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls) vhold_addr).
  { rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
    simpl set_tls_rdy at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.
    eapply r_priotbl_p_set_hold; eauto.
  }
  assert (Hrh_tls_els_new: RH_TCBList_ECBList_P (set els (eid_b', Int.zero) (abssem n, remove_wls ((htcb_addr, Int.zero) :: subwl) wls)) (set_tls_rdy ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls) ctcb).
  { rewrite <- remove_wls_succ_set_els_eq with (st':= (abssem n)).
    rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
    simpl set_tls_rdy at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.
    eapply rh_tcblist_ecblist_p_post_exwt_sem; eauto.
  }
  assert (H_elp_new: ECBList_P v'12 Vnull (v'40 ++ ((V$ OS_EVENT_TYPE_SEM :: Vint32 egrp' :: Vint32 n :: x0 :: x1 :: x7 :: Vint32 i :: x4 :: nil, (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl' (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))),x18) :: nil) ++  v'41) (v'42 ++ (DSem n :: nil) ++ v'43) (set els (eid_b', Int.zero) (abssem n, (remove_wls ((htcb_addr, Int.zero) :: subwl) wls))) (set_tls_rdy ((htcb_addr, Int.zero) :: subwl) tcbls) ).
  {
   rewrite <- remove_wls_succ_set_els_eq with (st':= (abssem n)).
   rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
   simpl set_tls_rdy at 1.
   rewrite Hhtcb_get'.
   eapply ecblist_p_post_exwt_hold_sem; eauto.
   eapply rl_etbl_ptbl_p; auto; eauto.
   subst hprio; auto.
   clear -Hs3. mauto.
   unfold RLH_ECBData_P.
   split; auto.
  }
  lets H_elp_cp: H_elp_new.
  eapply ecblist_p_decompose in H_elp_cp; eauto. 
  destruct H_elp_cp as (els1_new' & els2_new' & x' & H'').
  destruct H'' as (Hecbl1_new' & Hecbl2_new' & Hjo_new').
  assert (Hx': x' = Vptr (eid_b', Int.zero)).
  {
   sep_lifts_trms_in Hsat evsllseg.
   eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'.
  lets Hcp: Hecbl2_new'.
  remember ((htcb_addr, Int.zero) :: subwl) as subwl'.
  simpl in Hcp.
  mytac.
  inverts H51.
  inverts H60.
  assert (Hx0: x16 = (abssem n, remove_wls ((htcb_addr, Int.zero) :: subwl) wls)).
  {
   eapply EcbMod.join_sig_get in H61.
   eapply EcbMod.join_get_r in H61;eauto.
   rewrite EcbMod.map_get_set in H61.
   inverts H61. auto. }
  subst x16.
  destruct H66 as (_ & Hrh_ecb_new').
  rename H61 into Hjo_sig_new'.
  rename H85 into Hecb_right_new'.
  rename H55 into Hr_ecb_etbl_new'.
  rename H57 into Hr_ecb_petbl_new'.
  lets Hgete_new: EcbMod.join_sig_get Hjo_sig_new'.
  eapply EcbMod.join_get_r in Hgete_new; eauto.
  assert (His_subl_part: (forall t, In t ((htcb_addr,Int.zero) :: subwl) -> In t wls) 
/\ (forall t, ~(In t wls) -> ~ (In t ((htcb_addr,Int.zero) :: subwl))) /\ NoDup ((htcb_addr,Int.zero) :: subwl) ).
  { clear -H43 Hin_pwls.
    unfold is_subl in *.
    mytac.
    splits; intros.
    eapply in_remove_wls in Hin_pwls.
    simpl in H3.
    destruct H3; try subst; auto.
    rewrite not_in_cons.
    assert (t = (htcb_addr, Int.zero)  \/ t <> (htcb_addr, Int.zero) ) by tauto.
    eapply in_remove_wls in Hin_pwls.
    destruct H4. subst; tryfalse.
    split; auto.
    eapply NoDup_cons; eauto.
    eapply in_remove_wls_nin; eauto.
  }
  destruct His_subl_part as (His_subl_part1 & His_subl_part2 & His_subl_part3).
  (* change tcbdllflag *)
  sep_lifts_trms_in Hsat (tcbdllflag).
  eapply tcbdllflag_set_node in Hsat; eauto.
  2: { unfolds. unfold V_OSTCBNext; simpl. auto. }
  
  assert (Heq_sus: Int.eq (x10&ᵢInt.not ($ OS_STAT_SEM)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x10.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_SEM)) with ($ OS_STAT_SUSPEND).
    auto.
   }
   rewrite Heq_sus in *.
   rewrite negb_if in *.
  
  (* end of change tcbdllflag *)
  (* remain tcbllsegevaux *)
  sep_lifts_trms_in Hsat (tcbllsegevaux).
  unfold tcbllsegevaux in Hsat.
  eapply llsegevaux_set_node in Hsat; eauto.
  2: { unfolds. unfold V_OSTCBNext; simpl. auto. }
  (* end of tcbllsegevaux *)
  exists (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
               (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))).
  exists x x2 x5.
  exists (if sus
          then rtbl'
          else update_nth_val (Z.to_nat (Int.unsigned p1)) rtbl' 
               (Vint32 (Int.or x54 ($ 1<<ᵢp2)))). (* new rtbl *)
  exists x13. (* new rgrp *)
  exists egrp'. (* new egrp *)
  exists ((htcb_addr, Int.zero) :: subwl).
  exists (V$ OS_STAT_SEM).
  exists x8 x9 x14.
  sep auto.
  { assert (Hegrp'_case: egrp' = Int.zero \/ egrp' <> Int.zero) by tauto.
  destruct Hegrp'_case as [Hegrp'_eq | Hegrp'_neq];
  [left | right].
  (* case1 : after OS_EventTaskRdy, will get out of loop *)
  subst egrp'.
  assert (Hpwls'_eq: remove_wls ((htcb_addr, Int.zero) :: subwl) wls = nil).
  { eapply Grp_eq_zero_imp_wl_nil with (etbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
       (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.
    rewrite update_nth_val_len_eq; eauto.
  }
  assert (Hsubwl_eq':  set_tls_rdy ((htcb_addr,Int.zero) :: subwl) tcbls 
                                               = set_tls_rdy wls tcbls).
  { assert (Heq: ((htcb_addr,Int.zero) :: subwl) ++ remove_wls ((htcb_addr, Int.zero) :: subwl) wls = ((htcb_addr,Int.zero) :: subwl)).
     rewrite Hpwls'_eq. rewrite app_nil_end; auto.
     rewrite <- Heq.
     eapply set_tls_rdy_eq_alt_gen; eauto.
   }
  rewrite Hpwls'_eq in *.
  rewrite Hsubwl_eq' in *.
   splits; eauto.
  rewrite update_nth_val_len_eq; eauto.
   (* case 2 : after OS_EventTaskRdy, still in the loop *)
  assert (Hegrp'_range: Int.unsigned egrp' <= 255).
  {
   clear -H80.
   simpl in H80.
   destruct H80 as (_ & H & _).
   eapply int_true_le255; eauto.
  }
  splits; eauto.
  unfold is_subl.
  splits; auto.
  simpl length.
  eapply length_lt_succ; eauto.
  eapply Grp_eq_nz_imp_wl_not_nil with (etbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl' (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.
  rewrite update_nth_val_len_eq; eauto.
  rewrite update_nth_val_len_eq; eauto.
  }
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  (* end of OS_EventTaskRdy *)
  (* Aisfalse
    (efield (Sem_info ′ [os_code_defs.pos ′]) pevent !=ₑ NULL &&ₑ
     (efield (Sem_info ′ [os_code_defs.pos ′]) pevent) → OSEventGrp !=ₑ ′ 0 *)
  unprotect HeqH3.
  eapply backward_rule1 with ( p:= (
    EX etbl' tcbvl_l' tcbvl_r' tcbvl_ct' rtbl' rgrp' vy tail tcbls_l' tcbls_r',
 <||
  (semflush_no_wl (|Vint32 posv :: nil|)
   ?? semflush_set_wl_all_rdy (|Vint32 posv :: nil|));;
  isched;; END Some (Vint32 Int.zero) ||>  **
  LV y @ Int16u |-> vy **
  LV os_code_defs.pos @ long |-> Vint32 posv **
  p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  A_dom_lenv
    ((sem, (long) ∗)
     :: (os_code_defs.pos, long)
        :: (x, char_t) :: (y, Int16u) :: (p, OS_EVENT ∗) :: (temp_dom, char_t) :: (temp_num, char_t):: nil) **
  AOSMapTbl **
  AOSUnMapTbl **
  AOSTCBPrioTbl v' rtbl' (set_tls_rdy wls tcbls) ptls vhold_addr **
  GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
  tcbdllseg tcb_head Vnull tail (Vptr tid) tcbvl_l' **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
  tcbdllseg (Vptr tid) tail v'21 Vnull (tcbvl_ct' :: tcbvl_r') **
  [| TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy wls tcbls) |] **
  [| TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l' |] **
  [| TCBList_P (Vptr tid) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r' |] **
  [| RH_TCBList_ECBList_P (set els (eid_b', Int.zero) (abssem n, nil)) (set_tls_rdy wls tcbls) tid |] **
  tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **
  tcbllsegevaux tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') v'33 v'34 **
  AOSRdyTblGrp rtbl' rgrp' **
  Astruct (eid_b', Int.zero) OS_EVENT  (* egrp is zero, get out of loop *)
    (V$ OS_EVENT_TYPE_SEM :: Vint32 Int.zero :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil) **
  Aarray v'45 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
  AOSPostEventTbl v'47 petbl ** (* new add *)
  AEventData (V$ OS_EVENT_TYPE_SEM :: Vint32 Int.zero :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 ::  nil) (DSem n) **
  evsllseg v'12 (Vptr (eid_b', Int.zero)) v'40 v'42 **
  evsllseg x5 Vnull v'41 v'43 **
  GV OSEventList @ OS_EVENT ∗ |-> v'12 **
  HSEMInfo v'28 **
   GV Sem_info @ sem_info_t ∗ |-> Vptr (v'37, v'38) **
   Aarray_new (v'37, v'38) (Tarray sem_info_t (Z.to_nat (Int.unsigned posv))) v'35 **
   Astruct (v'37, v'38 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t)) sem_info_t v'39 **
   Aarray_new (v'37, v'38 +ᵢ  $ Z.of_nat (S (Z.to_nat (Int.unsigned posv)) * typelen sem_info_t)) (Tarray sem_info_t ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S (Z.to_nat (Int.unsigned posv))))) v'36 ** H3 **
   [| RL_Tbl_Grp_P etbl' (Vint32 Int.zero)  /\ 
      array_type_vallist_match Tint8 etbl' /\
      ECBList_P v'12 Vnull (v'40 ++ ((V$ OS_EVENT_TYPE_SEM :: Vint32 Int.zero :: Vint32 n ::  x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil, etbl', petbl) :: nil) ++ v'41) (v'42 ++ (DSem n :: nil) ++ v'43) (set els (eid_b', Int.zero) (abssem n, nil)) (set_tls_rdy wls tcbls) |] )). 
  introv Hsat.
  destruct Hsat as (Hsat & Hisfalse).
  sep destruct Hsat.
  lets Hcp: aconj_intro Hsat Hisfalse.
  eapply sep_aconj_r_aisfalse_to_astar in Hcp;eauto.
  2: { clear Hsat Hcp Hisfalse. introv Hsat.
       assert(Hrv_pevent: s0 |= Rv efield (Sem_info ′ [os_code_defs.pos ′]) pevent @ 
                                                                                           OS_EVENT ∗ == Vptr (eid_b', Int.zero)).
    { sep_get_rv_array_struct.
      rewrite Hdiveq; eauto.
      rewrite Hdiveq.
     eapply Int.eq_false; eauto.
     eapply new_array_type_vallist_match_split in H1; eauto;
     mytac.
   }
   sep split in Hsat.
   mytac.
   assert (Hegrp_range: Int.unsigned x10 <= 255).
   { destruct H44 as [Hegrp_zero | Hegrp_nz]; mytac; auto. }
   eapply bop_rv; eauto.
   eapply uop_rv; eauto.
   eapply bop_rv; eauto.
   sep get rv.
   go.
   go.
   go.
   go.
   eapply uop_rv; eauto.
   eapply bop_rv; eauto.
   (* sep_get_rv_array_struct'. *)
   eapply struct_member_e_rv.
   eauto.
   sep cancel Astruct; eauto.
   pure_auto.
   pure_auto.
   pure_auto.
   simpl; auto.
  simpl; auto.
  simpl; auto.
  pure_auto.
  simpl; auto with zarith.
  sep split in Hsat.
  mytac.
  auto.
  destruct H44 as [Hegrp_zero | Hegrp_nz]; mytac; tryfalse.
  go. go. go.
  sep get rv.
  clear; simpl; pure_auto.
  go.
  clear; simpl; pure_auto.
  go.
  clear; simpl; pure_auto.
  go.
  }
  clear -Hcp.
  sep_lifts_trms_in Hcp (RL_Tbl_Grp_P,bop_eval).
  eapply sep_pure_split in Hcp.
  destruct Hcp as (Hcases & Hcp).
  eapply sep_pure_split in Hcp.
  destruct Hcp as (Hisfalse & Hcp).
  destruct Hcases as [Ht | Hf].
  Focus 2.
  destruct Hf as (_ & _ & _ & Hegrp_neq & _).
  eapply Int.eq_false in Hegrp_neq.
  change ($ 0) with Int.zero in Hisfalse.
  simpl in Hisfalse.
  rewrite Hegrp_neq in Hisfalse;
  change (Int.notbool Int.zero) with Int.one in Hisfalse;
  simpl in Hisfalse;
  change (Int.notbool Int.zero) with Int.one in Hisfalse;
  change (Int.ltu Int.zero Int.zero) with false in Hisfalse;
  change (Int.ltu Int.zero Int.one) with true in Hisfalse;
  simpl in Hisfalse.
  destruct Hisfalse as [Hf | Hf];
  inverts Hf.
  mytac.
  rewrite H6 in *.
  assert (Hsubwl_eq':  set_tls_rdy x11 tcbls = set_tls_rdy wls tcbls).
  { assert (Heq: x11 ++ remove_wls x11 wls = x11).
    rewrite H6. rewrite app_nil_end; auto.
    assert (Hsubwl: x11 = nil \/ x11 <> nil) by tauto.
    destruct Hsubwl.
    subst. rewrite remove_wls_nil in H6.
    subst. auto.
    destruct H2. subst; tryfalse.
    rewrite <- Heq.
    eapply set_tls_rdy_eq_alt_gen; eauto.
  }
  rewrite Hsubwl_eq' in *.
  sep auto; eauto.
  (* end of while loop *)
  
  (* EXIT_CRITICAL;ₛ *)
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold_msg.
  sep normal.
  sep eexists.
  sep cancel AOSPostEventTbl.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  sep split; eauto.
  split; auto.
  go.
  unfolds; simpl; auto.
  (* unfolds; simpl; auto. *)
  eauto.
  eauto.
  eapply backward_rule1.
  introv Hsat.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'35 (Z.to_nat (Int.unsigned posv)) v'36 v'39.
  sep pauto; eauto.

  hoare_lifts_trms_pre (Aop, seminfoid,absecblsid,abtcblsid).
  assert (Hwls_case: wls = nil \/ wls <> nil) by tauto.
  destruct Hwls_case as [Hwls_eq | Hwls_neq].
  subst wls.
  (* case1: wls = nil *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_no_wl; eauto.
  pure_auto.
  eapply absinfer_eq.
  
  (* actual exit critical *)
  rewrite set_tls_rdy_nil in *.
  assert (Hels_eq: (set els (eid_b', Int.zero) (abssem n, nil)) = els).
  { eapply EcbMod.get_set_same; eauto. }
  rewrite Hels_eq in *.
  
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop  ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
  
  hoare forward prim.
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AECBList.
  sep pauto; try sep cancel evsllseg; eauto.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel ASeminfo.
  sep cancel tcbdllflag.
  sep cancel tcbllsegevaux.
  sep cancel p_local.
  unfold AOSTCBList.
  sep pauto; eauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  trycancel.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  pure_auto.
  pure_auto.
  (* end of exit critical *)
  
  (* OS_Sched (­);ₛ *)
  hoare forward.
  unfolds; auto.
  pure_auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare unfold.
  inverts H3.
  (* RETURN ′ 0 *)
  hoare forward.
  (* case2: wls <> nil *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semflush_absimp_set_wl_all_rdy; eauto.
  pure_auto.
  eapply absinfer_eq.
  (* actual exit critical *)
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop  ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  unfold AECBList.
  sep normal in H3.
  sep destruct H3.
  sep normal.
  do 23 eexists.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep cancel ASemCap.
  sep pauto; try sep cancel evsllseg; eauto.
  trycancel.
  sep cancel APthreadMutex.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel ASeminfo.
  sep cancel tcbdllflag.
  sep cancel tcbllsegevaux.
  sep cancel p_local.
  sep cancel Aier.
  unfold AOSTCBList.
  sep pauto; eauto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  cancel_corecommuinv.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  eapply mq_ecb_p_sem_set_wls'_preserve; eauto.
  eapply mux_ecb_p_sem_set_wls'_preserve; eauto.
  eapply sem_ecb_p_sem_set_wls'_preserve; eauto.
  eapply RH_SEM_EINFO_ECB_P_set_wls'; eauto.
  eapply RH_MUX_EIB_ECB_P_sem_set_wls'_preserve; eauto.
  eapply RH_EIB_ECB_Q_P_sem_set_wls'_preserve; eauto.
  (* RH_CurTCB tid (set_tls_rdy wls tcbls) *)
  clear -H0.
  unfold RH_CurTCB in *.
  mytac.
  eexists. 
  eapply set_tls_rdy_get_some in H.
  simpljoin1; eexists; eauto.
  eauto.
  (* end of RH_CurTCB *)
  pure_auto.
  (* end of exit critical *)

  (* OS_Sched (­);ₛ *)
  hoare forward.
  unfolds; auto.
  pure_auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  intros. sep pauto. sep cancel p_local. simpl; auto.
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  unfold getasrt.
  hoare unfold.
  inverts H3.
  (* RETURN ′ 0 *)
  hoare forward.
  Unshelve.
  exact Atrue.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 0%nat.
  exact 1%positive.
  exact Vnull.
  exact Vnull.
  exact nil.
  exact Int.zero.
  exact Vnull.
  exact 0%nat.
Qed. 
