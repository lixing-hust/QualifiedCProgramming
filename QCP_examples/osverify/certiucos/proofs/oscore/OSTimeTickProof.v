(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(********** Proof of Internal Fucntion: void OSTimeTick() ************)
(**************************** Code:***********************************)
(*
Definition OSTimeTick_impl := 
 Void ·OSTimeTick·(⌞ ⌟)··{
        ⌞ptcb @ OS_TCB∗;
         pevent @ OS_EVENT∗;
         ptbl @ Tptr Int8u⌟;
         
(*         ENTER_CRITICAL;ₛ *)
        ++OSTime′;ₛ
(*         EXIT_CRITICAL;ₛ *)

        ptcb′ =ₑ OSTCBList′;ₛ
        WHILE (ptcb′ !=ₑ NULL) {
(*           ENTER_CRITICAL;ₛ *)
          If (ptcb′→ OSTCBDly !=ₑ ′0){
               ptcb′→OSTCBDly =ₑ (ptcb′→OSTCBDly) − ′1;ₛ
               If (ptcb′→OSTCBDly ==ₑ ′0) {
                     IF ((ptcb′→OSTCBStat &ₑ ′OS_STAT_ILLEGAL) ==ₑ ′OS_STAT_RDY) {
                            OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ
                            OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX
                                    }
                      ELSE {
                                    ptcb′→OSTCBDly =ₑ ′1
                                  }
               }
           };ₛ
           ptcb′ =ₑ ptcb′→OSTCBNext
(*            EXIT_CRITICAL;ₛ *)
        };ₛ
        RETURN
 }·.
*)
Require Import ucos_include.
Require Import OSTimeTickPure.
Require Import OSTimeDlyPure.
Require Import ucos_common.
Require Import oscore_common.
Require Import os_ucos_h.
Require Import Lia.
Require Import seplog_trm_tacs.

Open Scope code_scope.

Lemma tcbls_recombine_imp_tcbnode:
  forall v'13 v'14 v'12 v v'4 rtbl v'3 v'5 v'6 v'15 v'16 vl,
    TcbMod.join v'13 v'14 v'12 ->
    TCBList_P v v'4 rtbl v'13 ->
    TCBList_P v'3 (v'5 :: v'6) rtbl v'14 ->
    v'4 ++ v'5 :: v'6 = v'15 ++ vl :: v'16 ->
    v'4 = nil /\ v'3 = v \/
    (exists vl, v'4 <> nil /\ last v'4 nil = vl /\ nth_val 0 vl = Some v'3) ->
    (exists abstcb, TCBNode_P vl rtbl abstcb).
Proof.
  intros.
  assert (Htls : TCBList_P v (v'4 ++ v'5 :: v'6) rtbl v'12).
  { destruct H3; simpljoin.
     simpl in H0.
     subst.
     apply TcbMod.join_emp_eq in H.
     subst.
     rewrite app_nil_l.
     auto.
     eapply TCBList_P_combine; eauto.
  }
  rewrite H2 in Htls.
  eapply OSQPostPure.TCBList_P_Split in Htls.
  simpljoin.
  simpl in H7.
  simpljoin.
  eauto.
Qed.

Lemma tcbls_recombine_imp_tcbnode':
  forall v'13 v'14 v'12 v v'4 rtbl v'3 v'5 v'6 v'15 v'16 vl (v'21 v'8 x7 x6 : val) (i6 i5 i4 i3 i2 i1 i0 : int32),
    TcbMod.join v'13 v'14 v'12 ->
    TCBList_P v v'4 rtbl v'13 ->
    TCBList_P v'3 (v'5 :: v'6) rtbl v'14 ->
    v'4 ++ v'5 :: v'6 = v'15 ++ vl :: v'16 ->
    v'4 = nil /\ v'3 = v \/
    (exists vl, v'4 <> nil /\ last v'4 nil = vl /\ nth_val 0 vl = Some v'3) ->
    vl = (v'21
        :: v'8
           :: x7
              :: x6
                 :: Vint32 i6
                    :: Vint32 i5
                       :: Vint32 i4
                          :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
    (exists st s, TCBNode_P (v'21
        :: v'8
           :: x7
              :: x6
                 :: Vint32 i6
                    :: Vint32 i5
                       :: Vint32 i4
                          :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) rtbl (i4,st,x6, s)).
Proof.
intros.
eapply tcbls_recombine_imp_tcbnode in H3; eauto.
subst.
simpljoin.
destruct x. destruct p. destruct p.
lets Hcp:H3.
funfold H3.
eauto.
Qed.

Lemma tcb_imp_eptr:
forall vl rtbl abstcb,
   TCBNode_P vl rtbl abstcb ->
   array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    exists stat, V_OSTCBStat vl = Some (Vint32 stat) /\
    (exists eptr, V_OSTCBEventPtr vl = Some eptr /\
                           (stat = $ OS_STAT_RDY -> eptr = Vnull) /\
                           ( ( stat = $ OS_STAT_SEM \/ stat = $ OS_STAT_Q \/ stat = $ OS_STAT_MBOX \/
                                     stat = $ OS_STAT_MUTEX \/ stat = $ OS_STAT_POSTQ \/ stat = $ OS_STAT_PORT) -> exists eid, eptr = Vptr eid) ).
Proof.
introv Htcb Hrtbl Hlen.
destruct abstcb.
destruct p.
destruct p.
funfold Htcb.
funfold H1.
exists x4.
split; auto.
exists x5.
splits; auto.
intros.
funfold H2.
rewrite H1 in H4; inverts H4.
lets Hcases: Hlen.
eapply prio_rtbl_dec in Hcases; eauto.
destruct t.
{
   destruct s.
   { destruct H14.
     specialize (H4 _ _ (eq_refl _ )) as [? ?].
     unfold V_OSTCBStat in  H19.
     rewrite H11 in H19.
     inverts H19.
     destruct H as [H | [H | [H | [ H | [H | H]]]]]; tryfalse.
   }
specialize (H2 _ _ (eq_refl _)).
destruct H2 as (_ & Hst & _).
unfold V_OSTCBStat in Hst.
rewrite Hst in H11; inverts H11.
destruct H as [H | [H | [H | [ H | [H | H]]]]]; tryfalse. }
destruct t;
[ destruct H18 as (_ & H18 & _ & _ & _ & _ & H18' & _ & _ & _ & _ & _ & _) (* sem *)
  | destruct H18 as (_ & _ & H18 & _  & _ & _ & _ & H18' & _ & _ & _ &_ & _) (* q *)
  | destruct H18 as (_ & _ & _ & _ & _ & H18 & _ & _ & H18' & _ & _& _ & _) (* postq *)
  | destruct H18 as (H18 & _) (* time *);destruct H14 as (_ & H18')
  | destruct H18 as (_ & _ & _ & H18 & _ & _ & _ & _ & _ & H18' & _ & _& _) (* mbox *)
  | destruct H18 as (_ & _ & _ & _ & H18 & _ & _ & _ & _ & _ & H18'& _& _ )(* mutex *)
  | destruct H18 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H18 & H18' )(* port *)
]. 
(*
destruct t.
unfold RHL_TCB_Status_Wait_P in H18.
destruct t;
[ destruct H18 as (_ & H18 & _ & _ & _ & _ & H18' & _ & _ & _ & _) (* sem *)
  | destruct H18 as (_ & _ & H18 & _  & _ & _ & _ & H18' & _ & _ & _) (* q *)
  | destruct H18 as (_ & _ & _ & _ & _ & H18 & _ & _ & H18' & _ & _) (* postq *)
  | destruct H18 as (H18 & _) (* time *);destruct H14 as (_ & H18')
  | destruct H18 as (_ & _ & _ & H18 & _ & _ & _ & _ & _ & H18' & _) (* mbox *)
  | destruct H18 as (_ & _ & _ & _ & H18 & _ & _ & _ & _ & _ & H18' )]. (* mutex *)
*)
all: destruct s;[ try specialize (H18' _ _ _ _ (eq_refl _ ));
                  try specialize (H18' _ _ _  (eq_refl _ ));
                  repeat match type of H18' with 
                  | _ /\ _ => destruct H18' as [? H18']
                  end;
                  try match goal with 
                  | H0 : V_OSTCBStat _ = Some _ |- _ =>
                     unfold  V_OSTCBStat in H0; rewrite H11 in H0;inverts H0;
                     destruct H as [H | [H | [H | [ H | [H | H]]]]]; tryfalse
                  end  | ].
all : try specialize (H18 _ _ _ _ (eq_refl _));
try specialize (H18 _ _ _ (eq_refl _));
try destruct H18 as ( _ & _ & Hptr & Hst);
try destruct H18 as ( _ & Hptr & Hst);
try (unfold V_OSTCBEventPtr in Hptr;
        unfold V_OSTCBStat in Hst;
        rewrite Hptr in H10; inverts H10;
        rewrite Hst in H11; inverts H11;
        pauto).
destruct H18' as (t' & _ & _ & _ & Hst).
unfold V_OSTCBStat in Hst.
rewrite Hst in H11; inverts H11.
destruct H as [H | [H | [H | [ H | [H | H]]]]]; tryfalse.
destruct H18 as (t' & _ & _ & _ & Hst).
unfold V_OSTCBStat in Hst.
rewrite Hst in H11; inverts H11.
destruct H as [H | [H | [H | [ H | [H | H]]]]]; tryfalse.
Qed.

Lemma tcb_imp_eptr':
forall vl rtbl abstcb stat eptr,
   TCBNode_P vl rtbl abstcb ->
   array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    V_OSTCBStat vl = Some (Vint32 stat) ->
    V_OSTCBEventPtr vl = Some eptr ->
     (stat = $ OS_STAT_RDY -> eptr = Vnull) /\
       ( ( stat = $ OS_STAT_SEM \/ stat = $ OS_STAT_Q \/ stat = $ OS_STAT_MBOX \/
            stat = $ OS_STAT_MUTEX \/ stat = $ OS_STAT_POSTQ \/ stat = $ OS_STAT_PORT) -> exists eid, eptr = Vptr eid) .
Proof.
introv Htcb Hrtbl Hlen Hst Hptr.
eapply tcb_imp_eptr in Hlen; eauto.
simpljoin.
rewrite Hst in H; inverts H.
rewrite Hptr in H0; inverts H0;
split; auto.
Qed.


Lemma tcbls_rtbl_timetci_update_hold_new:
  forall v'22 v'9 i v'17 v'26 v'27 v'31 v'10 x6 i6 i4 i3 i2 i1 i0 v'21 v'28 (* v'24 *) v'25 x7 i5 head rtbl tcbls
            vnext vprev vmsg vdly,
    TCBList_P head v'22 rtbl tcbls ->
    array_type_vallist_match Int8u v'9 ->
    length v'9 = ∘OS_RDY_TBL_SIZE ->
    Int.unsigned i <= 255 ->
    Int.eq i6 ($ 0) = false ->
    Int.eq (i6-ᵢ$ 1) ($ 0) = true ->
    os_stat_not_suspend i5 = true ->
    tcbls_rtbl_timetci_update v'22 v'9 (Vint32 i) v'21 v'17 = Some (v'25, v'26, Vint32 v'27, v'28) ->
    RL_TCBblk_P
      (vnext
         :: vprev
         :: x7
         :: vmsg
         :: vdly
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
    (i5 = $ OS_STAT_RDY -> x7 = Vnull) /\
       ( ( i5 = $ OS_STAT_SEM \/ i5 = $ OS_STAT_Q \/ i5 = $ OS_STAT_MBOX \/
            i5 = $ OS_STAT_MUTEX \/ i5 = $ OS_STAT_POSTQ \/ i5 = $ OS_STAT_PORT) -> exists eid, x7 = Vptr eid) ->
    RL_Tbl_Grp_P v'9 (Vint32 i) ->
    tcbls_rtbl_timetci_update
      (v'22 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil) v'9 (Vint32 i) v'21 v'17 =
    Some
      (v'25 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 (i6-ᵢ$ 1)
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil,
       update_nth_val (Z.to_nat (Int.unsigned i2)) v'26
                      (val_inj (or (nth_val' (Z.to_nat (Int.unsigned i2)) v'26) (Vint32 i1))),
       Vint32 (Int.or v'27 i0), v'28).
Proof.
  intros * H H0 H1 H2 H3 H4 H4'. intros.
  eapply tcbls_rtbl_timetci_update_compose;eauto.
  simpl.
  unfolds Int.zero.
  rewrite H3.
  unfold Int.one.
  rewrite H4, H4'.
  lets Hx:timetick_update_prop H H0 H1 H2 H8.
  lets Hx': Hx H5.
  clear Hx.
  simpljoin.
  funfold H6.
  lets Hx:n07_arr_len_ex H9 H10.
  instantiate (1:=Z.to_nat (Int.unsigned (Int.shru x ($ 3)))).
  eapply z_to_nat_shr3;eauto.
  simpljoin.
  rewrite H6.
  simpl.
  unfold val_inj.
  unfold or.
  rewrite nth_val'_and_nth_val.
  rewrite H6.
  simpl.
  destruct H24.
  subst.
  specialize (H7 (eq_refl _)).
  subst.
  auto.
  assert (
  x4 = $ OS_STAT_SEM \/
  x4 = $ OS_STAT_Q \/
  x4 = $ OS_STAT_MBOX \/
  x4 = $ OS_STAT_MUTEX \/
  x4 = $ OS_STAT_POSTQ \/
  x4 = $ OS_STAT_PORT).
  { repeat (destruct H15 as [? | H15]; try tauto). 
    all : rewrite H15 in H4'; unfold os_stat_not_suspend in H4'; clear - H4';mauto.  }
  lets Hptr_eq: H13 H16.
  destruct Hptr_eq as (eid & Hptr_eq).
  subst.
  auto.
Qed.

Lemma tcbls_rtbl_timetci_update_hold_new':
  forall v'22 v'9 i v'17 v'26 v'27 v'31 v'10 x6 i6 i4 i3 i2 i1 i0 v'21 v'28 (* v'24 *) v'25 x7 i5 head rtbl tcbls
            vnext vprev vmsg vdly,
    TCBList_P head v'22 rtbl tcbls ->
    array_type_vallist_match Int8u v'9 ->
    length v'9 = ∘OS_RDY_TBL_SIZE ->
    Int.unsigned i <= 255 ->
    Int.eq i6 ($ 0) = false ->
    Int.eq (i6-ᵢ$ 1) ($ 0) = true ->
    os_stat_not_suspend i5 = false ->
    tcbls_rtbl_timetci_update v'22 v'9 (Vint32 i) v'21 v'17 = Some (v'25, v'26, Vint32 v'27, v'28) ->
    RL_TCBblk_P
      (vnext
         :: vprev
         :: x7
         :: vmsg
         :: vdly
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3
         :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil) ->
    RL_Tbl_Grp_P v'9 (Vint32 i) ->
    tcbls_rtbl_timetci_update
      (v'22 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 i6
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil) v'9 (Vint32 i) v'21 v'17 =
    Some
      (v'25 ++
            (v'31
               :: v'10
               :: x7
               :: x6
               :: Vint32 Int.one
               :: Vint32 i5
               :: Vint32 i4
               :: Vint32 i3
               :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)
            :: nil,  v'26, Vint32 v'27, v'28).
Proof.
  intros * H H0 H1 H2 H3 H4 H4'. intros.
  eapply tcbls_rtbl_timetci_update_compose;eauto.
  simpl.
  unfolds Int.zero.
  rewrite H3.
  unfold Int.one.
  rewrite H4, H4'.
  auto.
Qed.

Lemma tcb_stat_and_prop :
  forall x4,
  x4 = $ OS_STAT_RDY \/
  x4 = $ OS_STAT_SUSPEND \/
  x4 = $ OS_STAT_SEM \/
  x4 = $ OS_STAT_Q \/
  x4 = $ OS_STAT_MBOX \/
  x4 = $ OS_STAT_MUTEX \/
  x4 = $ OS_STAT_POSTQ \/
  x4 = $ OS_STAT_PORT \/
  x4 = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
  x4 = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
  x4 = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
  x4 = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
  x4 = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) \/
  x4 = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND) ->
     (x4&ᵢ$ OS_STAT_ILLEGAL) = ($ OS_STAT_RDY).
Proof.
intros.
unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_Q, OS_STAT_MBOX , OS_STAT_PORT in *.
unfold OS_STAT_MUTEX, OS_STAT_POSTQ, OS_STAT_ILLEGAL in *.
destruct H; subst; mauto.
Qed.



Lemma OSTimeTick_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSTimeTick
                  vl logicl OSTimeTickPre ct ->
      Some r =
      BuildRetI os_internal OSTimeTick vl logicl OSTimeTickPost ct ->
      exists t d1 d2 s,
        os_internal OSTimeTick = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  (* unfold OSTimeTickPre'. *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AECBList.
  pure_intro'.
  rename v'21 into aop.
  rename v'24 into v'21.
  rename H10 into Hidle.
  rename H11 into H10.
  (* ++ OSTime ′;ₛ *)

  hoare forward.
  (* intro;tryfalse. *)
  (* ptcb ′ =ₑ OSTCBList ′;ₛ *)
  hoare forward.
  (* WHILE (ptcb ′ !=ₑ NULL) *)
  eapply backward_rule1.
  { intros.
  sep_lifts_trms_in H (tcbdllseg (Vptr v'5), tcbdllseg (Vptr v'22)).
(*   sep lifts (12::14::nil)%nat in H. *)

  eapply tcbdllseg_compose' in H.
  exact H. }
  pure_intro'.
  remember (v'6 ++ v'7 :: v'8) as tcbl.
  apply backward_rule1 with (p:=
  EX tail1 tcbl1 tcbl2 x tcbl1' rtbl' rgrp' ectrl' v'0 v'1,
     [| tcbl = tcbl1 ++ tcbl2|] **
     tcbdllseg (Vptr v'5) Vnull tail1 x tcbl1' **
     tcbdllseg x tail1 v'13 Vnull tcbl2 **
     evsllseg v'21 Vnull ectrl' v'18 **
     [| tcbls_rtbl_timetci_update tcbl1 v'9 (Vint32 i) v'21 v'17= Some (tcbl1',rtbl',Vint32 rgrp',ectrl')|] **
     <|| aop ||>  **
     LV ptcb @ OS_TCB ∗ |-> x **
     LV pevent @ OS_EVENT ∗ |-> v'0 **
     LV ptbl @ (Int8u) ∗ |-> v'1 **
     A_dom_lenv ((ptcb, OS_TCB ∗) :: (pevent, OS_EVENT ∗) ::  (ptbl, (Int8u) ∗) :: nil)  **
     GV OSEventList @ OS_EVENT ∗ |-> v'21 **
     GV OSTime @ Int32u |-> Vint32 (Int.add v'11 Int.one) **
     Aisr (isrupd v'2 4%nat false) **
     Aier (ierupd v'4 4%nat true) **
     Aie false **
     Ais (4%nat :: v'3) **
     Acs nil **
     GV OSTCBList @ OS_TCB ∗ |-> Vptr v'5 **
     GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
     GAarray OSRdyTbl (Tarray Int8u ∘OS_RDY_TBL_SIZE) rtbl' **
     GV OSRdyGrp @ Int8u |-> Vint32 rgrp' ** p_local OSLInv ct (logic_val v'23 :: nil)).
  { intros.
  exists Vnull (nil:list vallist) tcbl (Vptr v'5) (nil:list vallist).
  exists v'9 i v'17 v'0 v'1.

  sep semiauto.
  unfold tcbdllseg at 1.
  unfold dllseg.
  sep auto. }
  
  eapply seq_rule.
  eapply while_rule.
  { intros.

  sep normal in H11.
  sep destruct H11.
  sep lift 3%nat in H11.
  unfold tcbdllseg in H11.
  lets Hisptr: dllseg_head_isptr H11.

  symbolic execution;pauto. }
  2:{ 
  pure_intro'.
  eapply backward_rule1.
  { intros.
  destruct H11.

  sep lift 6%nat in H11.
  lets Hx:neq_null_false_elim H11 H12.
  lets Hsat: astar_l_apure_intro H11 Hx.
  exact Hsat. }
  eapply pure_split_rule'; introv Heq.
  subst v'26.
  unfold OSTimeTickPost'.
  unfold tcbdllseg at 3.

  eapply backward_rule1.
  { intros.
  sep lift 3%nat in H11.
  lets Hx:dllseg_head_null_elim H11.
  lets Hsat: astar_l_apure_intro H11 Hx.
  exact Hsat. }
  eapply pure_split_rule'; introv Hx.
  destruct Hx;subst.
  simpl dllseg.
  hoare normal pre.
  eapply pure_split_rule'; introv Heq; clear Heq.
  eapply pure_split_rule'; introv Heq; clear Heq.
  pure_intro'.
  rewrite List.app_nil_r in H12;subst.
  apply ret_rule'.
  intros.
  sep normal.
  sep eexists.
  sep normal in H12.
  sep split in H12.
  sep split.
  22: auto.
  sep semiauto.
  sep lift 2%nat;eauto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  eapply timetick_idle_in_rtbl;eauto.
  eapply TCBList_P_imp_RL;eauto.
  eapply OSQPostPure.TCBList_P_Combine;eauto.
  clear -H.
  destruct H.
  Import DeprecatedTactic.
  mytac;subst;simpl;auto.
  inverts H0.
  auto.
  mytac.
  unfolds.
  destruct v'6;tryfalse;simpl;auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  eauto.
  auto.
  auto.
  auto. }
  (* while body *)
  remember (
    logic_isr v'2
   :: logic_is v'3
      :: logic_ier v'4
         :: logic_val (Vint32 v'11)
            :: logic_val (Vptr v'5)
               :: logic_val (Vptr v'5)
                  :: logic_llv v'6
                     :: logic_lv v'7
                        :: logic_llv v'8
                           :: logic_lv v'9
                              :: logic_val (Vint32 i)
                                 :: logic_val v'12
                                    :: logic_val v'13
                                       :: logic_abstcb v'14
                                          :: logic_abstcb v'15
                                             :: logic_abstcb v'16
                                                :: logic_leventc v'17
                                                   :: logic_leventd v'18
                                                      :: 
                                                      logic_absecb v'19
                                                      :: 
                                                      logic_code aop
                                                      :: 
                                                      logic_val (Vptr v'22)
                                                      :: 
                                                      logic_val v'23 :: nil) as ll.
  clear Heqll.
  
  pure_intro'.

  eapply backward_rule1.
  { intros.
  destruct H11.
  sep lift 6%nat in H11.
  lets Hx:neq_null_true_elim H11 H12.
  lets Hsat: astar_l_apure_intro H11 Hx.
  exact Hsat. }
  eapply pure_split_rule'; introv Hneq.
  rename Hneq into H13.
  (* instantiate (1:=LV ptcb @ OS_TCB ∗ |-> v'25 **
           tcbdllseg (Vptr v'4) Vnull v'9 v'25 v'26 **
           tcbdllseg v'25 v'9 v'12 Vnull v'24 **
           evsllseg v'20 Vnull v'29 v'17 **
           [|tcbls_rtbl_timetci_update v'23 v'8 (Vint32 i) v'20 v'16 =
             Some (v'26, v'27, Vint32 v'28, v'29)|] **
            <|| vcode ||>  **
           LV pevent @ OS_EVENT ∗ |-> v'30 **
           LV ptbl @ (Int8u) ∗ |-> v'31 **
           A_dom_lenv
             ((ptcb, OS_TCB ∗)
              :: (pevent, OS_EVENT ∗) :: (ptbl, (Int8u) ∗) :: nil) **
           GV OSEventList @ OS_EVENT ∗ |-> v'20 **
           GV OSTime @ Int32u |-> Vint32 (v'10 +ᵢ  Int.one) **
           Aisr (isrupd v'2 0%nat false) **
           Aie false **
           Ais (0%nat :: v'3) **
           Acs nil **
           GV OSTCBList @ OS_TCB ∗ |-> Vptr v'4 **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
           GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'27 **
           GV OSRdyGrp @ Int8u |-> Vint32 v'28 **
           p_local OSLInv ct (logic_val v'22 :: nil) **
           [|v'5 ++ v'6 :: v'7 = v'23 ++ v'24|] ** [| v'25 <> Vnull |]).
  clear H12.
  sep semiauto. *)
  pure_intro'.
  destruct v'25.
  unfold tcbdllseg at 3.
  unfold dllseg.
  pure_intro'.
  tryfalse.
  hoare lift 3%nat pre.
  unfold tcbdllseg at 2.
  unfold dllseg;fold dllseg.
  unfold node.

  pure_intro'.
   hoare forward.
  (* intro;tryfalse. *)
  go.
  destruct (Int.eq i6 ($ 0));simpl;intro;tryfalse.
  destruct (Int.eq i6 ($ 0));simpl;intro;tryfalse.

  hoare forward.
  (* intro;tryfalse. *)
  go.
  (* intro;tryfalse. *)
  hoare forward.
  destruct H16 as (Hif_dly_0 & _).
  destruct (Int.eq i6  ($ 0)) eqn: eq1; simpl in Hif_dly_0.
  change (Int.notbool Int.one) with Int.zero in Hif_dly_0; tryfalse.
  lets Hsub: ne_0_minus_1_in_range H21 eq1.
  go.
   pauto.
   hoare_split_pure_all.
   destruct H15 as (Hif1 & _).
   destruct H16 as (Hif2 & _).
  destruct (Int.eq i6 ($ 0)) eqn: eq1;
  simpl in Hif1; try change (Int.notbool Int.one) with Int.zero in Hif1; tryfalse.
  destruct (Int.eq (i6 -ᵢ $ 1) ($ 0)) eqn: eq2; 
  simpl in Hif2; tryfalse.

  lets Hx: tcblist_p_recombine H0 H1 H2 H12;auto.
  mytac.
  lets Hx:timetick_update_prop H6 H10 H7 H8 H11.
  exact H15.

  eapply Inteq_true_is_Zeq in eq2; eapply unsigned_inj in eq2.
  rewrite eq2 in *.
  mytac.
  hoare forward.
  go.
  pauto.
  go.
  pauto.
  pauto.
  lets Hrltcbblk: tcbnode_rl_prop H0 H1 H2 H12.
  lets Hi2:rl_tcbblk_tcby_range Hrltcbblk.
  assert(Hi2':  (Z.to_nat(Int.unsigned i2) < ∘ OS_RDY_TBL_SIZE)%nat) by
  (unfold OS_RDY_TBL_SIZE; unfold nat_of_Z;
  clear -Hi2; auto with zarith).
  lets Hnth: nthval'_has_value H16 H28 Hi2'.
  destruct Hnth as (rtbl_vy & Hnth & Hmat).
  (* assign rdygrp *)
  hoare forward.
  pauto.
  go.
  (* assign rdytbl *)
  hoare forward.
  go.
  rewrite Hnth. rewrite <- Hmat; auto.
  go.
  rewrite Hnth. pauto.
  go.
  (* stat isn't rdy, assign dly = 1 *)
  hoare forward.

  (* pre conditions *)
  lets Hx: tcblist_p_recombine H0 H1 H2 H12;auto.
  destruct Hx as (rtbl' & tcbls' & Hx).
  lets Hnode: tcbls_recombine_imp_tcbnode' H0 H1 H2 H12 H.
  specialize (Hnode (eq_refl _)).
  destruct Hnode as (st & Hnode).
  lets Hrltcbblk: tcbnode_rl_prop H0 H1 H2 H12.
  (* discuss cases: Int.eq i6 ($ 0) *)
  hoare forward.
 { hoare unfold.
  clear H29 H28. rename H15 into Hif1.
  destruct (Int.eq i6 ($ 0)) eqn: eq1;
  simpl in Hif1; try change (Int.notbool Int.one) with Int.zero in Hif1; tryfalse.
  lets Hdly_sub: ne_0_minus_1_in_range H21 eq1.
  (* discuss case : Int.eq (i6 -ᵢ $ 1) ($ 0) *)
  hoare forward.
  { hoare unfold.
  clear H29 H28. rename H15 into Hif2.
  destruct (Int.eq (i6 -ᵢ $ 1) ($ 0)) eqn: eq2; 
  simpl in Hif2; tryfalse.
  assert (eq3: (i5&ᵢ$ OS_STAT_ILLEGAL) = ($ OS_STAT_RDY)).
  { clear - Hrltcbblk. eapply tcb_stat_and_prop.
     funfold Hrltcbblk. auto.
   }
  rewrite eq3; rewrite Int.eq_true.
  simpl val_inj.
 (* discuss case : Int.eq (i5&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY)*)
  hoare forward.
  { hoare unfold.
    clear H31 H32 H29 H30 H28. rename H15 into Hif3.
    destruct (Int.eq (i5&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY)) eqn: eq4;
    simpl in Hif3;
    try change ( Int.ltu Int.zero Int.one) with (true) in Hif3;
    try change ( Int.ltu Int.zero Int.zero) with (false) in Hif3;simpl in Hif3;tryfalse.
   hoare_split_pure_all.
  (* case: Int.eq i6 ($ 0) = false /\ Int.eq (i6 -ᵢ $ 1) ($ 0) = true /\
                Int.eq (i5&ᵢ$ OS_STAT_ILLEGAL) ($ OS_STAT_RDY) = true /\ 
               Int.eq (i5&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = true *)
(*   lets Htcbls_up: H11. *)
  rename H11 into Htcbls_up.
  eapply tcbls_rtbl_timetci_update_hold_new in Htcbls_up; eauto.
  2: { unfold os_stat_not_suspend.  rewrite eq3, eq4.  rewrite Int.eq_true. auto.  }
  2: { eapply tcb_imp_eptr'; eauto.  }
  eapply forward_rule2.
  { hoare forward.
  go. }
  introv Hsat.
  exists (Vptr (v'34, Int.zero))
         ( v'24 ++
                (v'33
                   :: v'10
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'25
         v'33
         (v'27 ++( (v'33
                      :: v'10
                      :: x7
                      :: x6
                      :: Vint32 (i6 -ᵢ $ 1)
                      :: Vint32 i5
                      :: Vint32 i4
                      :: Vint32 i3
                      :: Vint32 i2
                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.
  apply tcbdllseg_compose_tail;auto.
  go.
  eapply Inteq_true_is_Zeq in eq2; eapply unsigned_inj in eq2.
  rewrite eq2 in *.
  sep cancel Astruct.
  sep cancel tcbdllseg.
  rewrite Htcbls_up; eauto.
  rewrite List.app_assoc_reverse.
  auto. }
  (* case: Int.eq i6 ($ 0) = false /\ Int.eq (i6 -ᵢ $ 1) ($ 0) = true /\
                Int.eq (i5&ᵢ$ OS_STAT_ILLEGAL) ($ OS_STAT_RDY) = true /\ 
                Int.eq (i5&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = false *)
  hoare unfold.
  clear H28. rename H15 into Hif3.
  destruct (Int.eq (i5&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY)) eqn: eq4;
  simpl in Hif3;
  try change ( Int.ltu Int.zero Int.one) with (true) in Hif3;
  try change ( Int.ltu Int.zero Int.zero) with (false) in Hif3;simpl in Hif3;
  destruct Hif3;tryfalse.
  rename H11 into Htcbls_up.
  eapply (tcbls_rtbl_timetci_update_hold_new') with (i6 := i6) in Htcbls_up; eauto.
  2: { unfold os_stat_not_suspend.  rewrite eq3, eq4.  rewrite Int.eq_true. auto.  }
  eapply forward_rule2.
  { hoare forward.
  go. }
  introv Hsat.
  exists (Vptr (v'34, Int.zero))
         ( v'24 ++
                (v'33
                   :: v'10
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'25
         v'33
         (v'27 ++( (v'33
                      :: v'10
                      :: x7
                      :: x6
                      :: Vint32 Int.one
                      :: Vint32 i5
                      :: Vint32 i4
                      :: Vint32 i3
                      :: Vint32 i2
                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.
  apply tcbdllseg_compose_tail;auto.
  go.
  rewrite Htcbls_up; eauto.
  rewrite List.app_assoc_reverse.
  auto. }

  hoare unfold.
  clear H15 H29 H30. rename H28 into Hif2.
  destruct (Int.eq (i6 -ᵢ $ 1) ($ 0)) eqn: eq2; 
  simpl in Hif2; destruct Hif2; tryfalse.
  (* case: Int.eq i6 ($ 0) = false /\ Int.eq (i6 -ᵢ $ 1) ($ 0) = false *)
   rename H11 into Htcbls_up.
  eapply tcbls_rtbl_timetci_update_hold' with (i6:= i6) in Htcbls_up; eauto.
  eapply forward_rule2.
  { hoare forward.
  go. }
  introv Hsat.
  exists (Vptr (v'34, Int.zero))
         ( v'24 ++
                (v'33
                   :: v'10
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'25
         v'33
         (v'27 ++( (v'33
                      :: v'10
                      :: x7
                      :: x6
                      :: Vint32 (i6 -ᵢ $ 1)
                      :: Vint32 i5
                      :: Vint32 i4
                      :: Vint32 i3
                      :: Vint32 i2
                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.
  apply tcbdllseg_compose_tail;auto.
  go.
  rewrite Htcbls_up; eauto.
  rewrite List.app_assoc_reverse.
  auto. }

  hoare unfold.
  rename H15 into Hif1.
  destruct (Int.eq i6 ($ 0)) eqn: eq1; 
  simpl in Hif1; destruct Hif1; tryfalse.
  (* case: Int.eq i6 ($ 0) = true *)
  rename H11 into Htcbls_up.
  eapply tcbls_rtbl_timetci_update_hold'' with (i6:= i6) in Htcbls_up; eauto.
  eapply forward_rule2.
  hoare forward.
  go.
  introv Hsat.
  exists (Vptr (v'34, Int.zero))
         ( v'24 ++
                (v'33
                   :: v'10
                   :: x7
                   :: x6
                   :: Vint32 i6
                   :: Vint32 i5
                   :: Vint32 i4
                   :: Vint32 i3
                   :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: nil)::nil)
         v'25
         v'33
         (v'27 ++( (v'33
                      :: v'10
                      :: x7
                      :: x6
                      :: Vint32 i6
                      :: Vint32 i5
                      :: Vint32 i4
                      :: Vint32 i3
                      :: Vint32 i2
                      :: Vint32 i1 :: Vint32 i0 :: nil)::nil)).
  sep semiauto.
  sep cancel evsllseg.
  unfold tcbdllseg at 2.
  sep cancel dllseg.
  apply tcbdllseg_compose_tail;auto.
  go.
  rewrite Htcbls_up; eauto.
  rewrite List.app_assoc_reverse.
  auto.
Qed.
