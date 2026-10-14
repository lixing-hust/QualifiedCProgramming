(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(**Proof of Internal Fucntion: 
 Int8u OS_EventTaskRdy(OS_EVENT* pevent; void* message; int8u  msk) **)
(**************************** Code:***********************************)
(***
Int8u ·OS_EventTaskRdy·(⌞pevent @ OS_EVENT∗; message @ Void∗ ;  msk @ Int16u⌟)··{
       ⌞
        ptcb @ OS_TCB∗;
        x @ Int8u;
        y @ Int8u;
        bitx @ Int8u;
        bity @ Int8u;
        prio @ Int8u
       ⌟;

1       y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ
2       bity′ =ₑ OSMapTbl′[y′];ₛ
3       x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ
4       bitx′ =ₑ OSMapTbl′[x′];ₛ
5       prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ
6       pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] &ₑ (∼bitx′);ₛ
7       If (pevent′→OSEventTbl[y′] ==ₑ ′0)
        {
8           pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼bity′)
        };ₛ
9       ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
10      ptcb′→OSTCBDly =ₑ ′0;ₛ
11      ptcb′→OSTCBEventPtr =ₑ  NULL;ₛ
12      ptcb′→OSTCBMsg =ₑ message′;ₛ
13      ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼msk′);ₛ
14      OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ bity′;ₛ
15      OSRdyTbl′[y′] =ₑ OSRdyTbl′[y′] |ₑ bitx′;ₛ
16      RETURN prio′
 }·.
*********)                                                             
(*Require Import ucert.
Require Import mathlib.
Require Import OSEventTaskRdyPure.
Require Import lab.
Require Import new_inv.
Require Import oscore_common.
 *)

Require Import ucos_include.
Require Import OSTimeDlyPure.
Require Import go.
Require Import Lia.
Require Import symbolic_lemmas.
(* Require Import OS_EventTaskPostRdy_spec. *)
Require Import ifun_spec.
Require Import OS_EventTaskPostRdy_pure.
Require Import sem_lab. 
Require Import seplog_trm_tacs.
Require Import new_inv.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

Lemma RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat :
  forall x13 x12 x11 x10 i7 i6 i5 i4 i3 i2 i prio st m sus eid d rtbl,
    RHL_TCB_Status_Wait_P
      (x13
         :: x12
         :: x11
         :: x10
         :: Vint32 i7
         :: Vint32 i6
         :: Vint32 i5
         :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2 :: Vint32 i :: nil)
      rtbl (prio, st, m, sus) ->
    rel_edata_stat eid d st ->
    rel_edata_tcbstat_postrdy d i6.
Proof.
  intros.
  unfolds in H; simp join.
  destruct d.
  clear - H5 H0 H8; unfolds in H5.
  simpl in H0; simp join.
  destruct sus.
  specialize (H8 _ _ _ _ (eq_refl _)).
  simpljoin.
  inverts H2.
  simpl; auto.
  pose proof H5 prio eid x m; clear H5.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H1 H; unfolds in H1.
  simpl in H; simp join.
  destruct H; auto.
  destruct H3 as (Hw & Hptr & Hst). inverts Hst. auto.
(*   pose proof H prio eid x m; clear H.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto. *)

  clear - H1 H0 H6; unfolds in H1.
  simpl in H0; simp join.
  destruct sus.
  specialize (H6 _ _ _ _ (eq_refl _)).
  simpljoin.
  inverts H2.
  simpl; auto.
  pose proof H1 prio eid x m; clear H1.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H3 H0 H9; unfolds in H3.
  simpl in H0; simp join.
  destruct sus.
  specialize (H9 _ _ _ _ (eq_refl _)).
  simpljoin.
  inverts H1.
  simpl; auto.
  pose proof H3 prio eid x m; clear H3.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H4 H0 H10; unfolds in H4.
  simpl in H0; simp join.
  destruct sus.
  specialize (H10 _ _ _ _ (eq_refl _)).
  simpljoin.
  inverts H1.
  simpl; auto.
  pose proof H4 prio eid x m; clear H4.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H11 H0 H12; unfolds in H11.
  simpl in H0; simp join.
  destruct sus.
  specialize (H12 _ _ _ _ (eq_refl _)).
  simpljoin.
  inverts H1.
  simpl; auto.
  pose proof H11 prio eid x m; clear H11.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.
Qed.

Lemma OSEventTaskPostRdy_proof:
  forall vl p r ll ct, 
    Some p =
    BuildPreI os_internal OS_EventTaskPostRdy vl ll OS_EventTaskPostRdyPre ct ->
    Some r =
    BuildRetI os_internal OS_EventTaskPostRdy vl ll OS_EventTaskPostRdyPost ct ->
    exists t d1 d2 s,
      os_internal OS_EventTaskPostRdy = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  hoare_split_pure_all.
  rename H14 into Hlt_size; rename H15 into H14. (* new add *)
  rename H10 into Htype.
  rename H11 into HR_ECB_PETbl_P.
  rename H12 into Hlh_ecbdata.
  rename H14 into H10.
  rename H13 into Hx''.
  simpl in H7, H8; inverts H7; inverts H8.
  rename v'26 into absmsq.
(*   rename v'18 into dd1. *)
  rename v'28 into d2.
  rename v'29 into d3.
  rename v'30 into d4.
  rename v'31 into d5.
  rename v'32 into d6.
  rename v'33 into d7.
  rename v'34 into d8.
  rename v'35 into d9.
  rename v'19 into dd3.
  rename v'20 into dd4.
  rename v'21 into v'19.
  rename v'22 into v'20.
  rename v'23 into v'21.
  rename v'24 into v'22.
  rename v'25 into v'23.
  rename v'27 into dd2'.
  rename v'36 into lg'.
  hoare unfold.
  unfold AOSPostEventTbl.
  hoare_split_pure_all.

  hoare unfold.
  rename v'13 into pegrp.
  rename v'16 into etbl.
  inverts H9.
  inverts H15.
  rename i0 into egrp.
  rename v'17 into petbl.

(*get the conditions used by following reasoning steps first*)
  assert (
      exists x y erow bitx bity,
        nth_val' (Z.to_nat (Int.unsigned pegrp)) OSUnMapVallist = Vint32 y /\
        Int.unsigned y < 8 /\
        nth_val' (Z.to_nat (Int.unsigned y)) petbl = Vint32 erow /\
        Int.unsigned erow < 256 /\ erow <> $ 0 /\
        nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist = Vint32 x /\
        Int.unsigned x < 8 /\
        nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity /\
        Int.unsigned bity <= 128 /\
        nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx /\
        Int.unsigned bitx <= 128
    ).
  lets Hx1: osunmapvallist_prop H24; simpljoin.
  apply Zle_bool_imp_le in H15.
  pose proof z_le_7_imp_n x H15.
  lets Hx2: array_int8u_nth_lt_len H7.
  rewrite H12 in Hx2.
  unfold OS_EVENT_TBL_SIZE in Hx2.
  lets Hx2': Hx2 H25; clear Hx2; simpljoin.
  lets Hx3: osunmapvallist_prop H27; simpljoin.
  apply Zle_bool_imp_le in H29.
  lets Hx4: osmapvallist_prop H15.
  lets Hx5: osmapvallist_prop H29.
  simp join.
  exists x5 x x3 x6 x7.
  splits; eauto.
  clear - H15; int auto.
  clear - H27; int auto.
  clear H27 H28 H30 H32.

  eapply rl_tbl_grp_neq_zero; eauto.
  clear - H15.
  int auto.
  clear - H29; int auto.
  
  destruct H9 as [x [y [erow [bitx [bity H9]]]]].
  destruct H9 as
      [unmap_pegrp [y_lt8 [nth_val_etbl [erow_lt256 [erow_ne0 [unmap_erow [x_lt8 [map_y
       [bity_le128 [map_x bitx_le128]]]]]]]]]].
  simp join.
  pose proof lt_8_le_byte_max_unsigned_true y y_lt8 as y_ble_max.
  pose proof lt_8_le_byte_max_unsigned_true x x_lt8 as x_ble_max.
  pose proof lt_256_le_byte_max_unsigned_true erow as erow_ble_max.
  pose proof le_128_le_byte_max_unsigned_true bity bity_le128 as bity_ble_max.
  pose proof le_128_le_byte_max_unsigned_true bitx bitx_le128 as bitx_ble_max.
(**)

  (* y′ =ₑ OSUnMapTbl′[pevent′→OSEventPostGrp];ₛ *)
  hoare unfold.
  unfold AOSUnMapTbl at 2.
  hoare forward; pure_auto.
  rewrite unmap_pegrp.
  rtmatch_solve.

  (*bity′ =ₑ OSMapTbl′[y′];ₛ*)
  unfold AOSMapTbl at 2.
  hoare forward.
  rewrite unmap_pegrp. rtmatch_solve; rewrite y_ble_max; auto.
  eauto.
  auto.
  auto.
  simpl; rewrite map_y; rewrite bity_ble_max; auto.
  
  (*x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ*)
  rewrite unmap_pegrp.
  rewrite map_y.
  hoare forward.
  4: eauto.
  rewrite y_ble_max; auto.
  rewrite H12; simpl; auto.
  simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
  auto.
  auto.
  simpl; rewrite unmap_erow; rewrite x_ble_max; auto.

  (*bitx′ =ₑ OSMapTbl′[x′];ₛ*)
  hoare forward.
  2: eauto.
  simpl; rewrite unmap_erow; rewrite x_ble_max; auto.
  auto.
  auto.
  simpl; rewrite map_x; rewrite bitx_ble_max; auto.
  
  (*prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ*)
  hoare forward.
  rewrite y_ble_max; auto.
  (* rewrite int_ltu_3_iwordsize.
  simpl; intro; tryfalse. *)
  rewrite unmap_erow; rewrite x_ble_max; auto.
  rewrite int_ltu_3_iwordsize.
  simpl val_inj.
  rewrite unmap_erow.
  simpl; intro; tryfalse.

  (*(pevent ′ → OSEventTbl) [y ′] &= ∼ bitx*)
  hoare forward.
  rewrite y_ble_max; auto.
  rewrite H12; simpl; auto.
  simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
  rewrite map_x; rewrite bitx_ble_max; auto.
  rewrite map_x; simpl; intro; tryfalse.
  rewrite nth_val_etbl; rewrite map_x; simpl; intro; tryfalse.
  rewrite y_ble_max; auto.
  apply eq_int; auto.
  rewrite H12; simpl; auto.

  (*If((pevent ′ → OSEventTbl) [y ′] ==ₑ ′0)*)
  hoare forward.
  rewrite y_ble_max; auto.
  rewrite update_nth_val_len_eq; rewrite H12; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  rewrite unsigned_int_and_not_range; auto.
  lia.
  lia.
  rewrite H12; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)); simpl; intro; tryfalse.
  rewrite H12; simpl; auto.
 
  (*pevent ′ → OSEventGrp &= ∼ os_code_defs.bity ′*)
  hoare forward; pure_auto.
  
  (*combine the 2 cases after the IF stmt into one case*)
  rewrite nth_val_etbl; rewrite map_x.
  apply disj_combine with (S:=(
   EX pegrp',
     [| RL_Tbl_Grp_P (update_nth_val (Z.to_nat (Int.unsigned y)) petbl
                                     (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) (Vint32 pegrp')  /\ Int.unsigned pegrp' <= 255|] **
      <|| v'19 ||>  **
      Aarray v'24 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
      LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'28, Int.zero) **
      Astruct (v'28, Int.zero) os_ucos_h.OS_EVENT
        (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i2 :: x0 :: x1 :: x2 :: Vint32 pegrp' :: x4 :: nil)  **
      Aarray v'26 (Tarray char_t ∘OS_EVENT_TBL_SIZE)
        (update_nth_val (Z.to_nat (Int.unsigned y)) petbl
           (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) **
      LV prio @ char_t
      |-> val_inj
            (add
               (val_inj
                  (if Int.ltu ($ 3) Int.iwordsize
                   then Some (Vint32 (y<<ᵢ$ 3))
                   else None))
               (nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist)
               Int32u char_t) **
      LV os_code_defs.bitx @ char_t |-> Vint32 bitx **
      LV os_code_defs.x @ char_t
      |-> nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist **
      LV os_code_defs.bity @ char_t |-> Vint32 bity **
      LV os_code_defs.y @ char_t |-> Vint32 y **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aisr empisr **
      A_isr_is_prop **
      Aier v'37 **
      AEventData
        (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i2 :: x0 :: x1 :: x2 :: Vint32 pegrp' :: x4 :: nil) (DMsgQ v'18 (d2
         :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 (d8 -ᵢ $ 1) :: Vptr (d9, Int.zero) :: nil) dd3 dd4) **
      GAarray OSUnMapTbl (Tarray char_t 256) OSUnMapVallist **
      GAarray OSMapTbl (Tarray char_t 8) OSMapVallist **
      AOSRdyTblGrp v'10 v'11 **
      GAarray OSTCBPrioTbl (Tarray os_ucos_h.OS_TCB ∗ 64) v'9 **
      tcbdllseg v'20 v'21 v'22 v'23 v'12 **
      p_local OSLInv ct (logic_val (V$ 1) :: lg') **
      LV pq @ os_ucos_h.OS_Q ∗ |-> v'5 **
      LV ptcb @ os_ucos_h.OS_TCB ∗ |-> v' **
      LV msk @ Int16u |-> Vint32 v'6 **
      A_dom_lenv
        ((msk, Int16u)
          :: (pevent, os_ucos_h.OS_EVENT ∗)
             :: (ptcb, os_ucos_h.OS_TCB ∗)
               :: (os_code_defs.x, char_t)
                  :: (os_code_defs.y, char_t)
                     :: (os_code_defs.bitx, char_t)
                         :: (os_code_defs.bity, char_t) :: (prio, char_t) :: (pq, os_ucos_h.OS_Q ∗) :: nil))
  ). 
  (*if true*)
  intros.
  sep pauto.
  simpl val_inj.

  split.
  eapply rl_tbl_grp_p_set_hold1 with (v'12:= pegrp) ; eauto.
  clear - y_lt8; int auto.
  clear - erow_lt256; int auto.
  clear - x_lt8; int auto.
  clear - H25 H26 H27 H12 y_lt8.
  simpl val_inj in *.
  assert(Int.unsigned y < Z.of_nat (length petbl)).
  rewrite H12; int auto.
  rewrite len_lt_update_get_eq in *; auto.
  simpl val_eq in *.
  destruct(Int.eq (erow&ᵢInt.not bitx) ($ 0)) eqn: eq1; auto.
  eapply not_and_p; eauto.
  
  (*if false*)
  intros.
  sep auto.
  simpl val_inj.
  
  split; auto.
  eapply rl_tbl_grp_p_set_hold2; eauto.
  clear - y_lt8; int auto.
  clear - erow_lt256; int auto.
  clear - x_lt8; int auto.
  clear - H27 y_lt8 H12.
  simpl val_inj in H27.
  rewrite len_lt_update_get_eq in *.
  simpl val_eq in H27.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)) eqn : eq1; auto.
  destruct H27; simpl in H; tryfalse.
  rewrite H12; unfold OS_EVENT_TBL_SIZE; simpl; auto.

  (*ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ*)
  rewrite int_ltu_3_iwordsize.
  rewrite unmap_erow.
  simpl val_inj.

  (*get the relation between event data and event type*)
  hoare_split_pure_all.
  hoare_lifts_trms_pre AEventData.

  apply hoare_pure_gen with (p:=(rel_edata_etype (DMsgQ v'18 (d2
         :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 (d8 -ᵢ $ 1) :: Vptr (d9, Int.zero) :: nil) dd3 dd4) ($ OS_EVENT_TYPE_Q))).
  intros.
  clear - H15.
  unfold AEventData in H15.
  destruct v'18; sep split in H15; unfolds in H; simpl in H; inverts H; simpl; auto.
(*   unfolds in H0; simpl in H0; inverts H0; simpl; auto. *)
  hoare_split_pure_all.
  rename H15 into rel_ed_et.
  rename v'8 into tcbls.
  rename v'9 into ptbl.  

  (*prove prio lt 64*)
  assert(Int.unsigned ((y<<ᵢ$ 3)+ᵢx) < 64) as prio_lt64.
  clear - y_lt8 x_lt8.
  mauto.

  (*prio ble max byte*)
  pose proof lt_64_le_byte_max_unsigned_true ((y<<ᵢ$ 3)+ᵢx) prio_lt64 as prio_ble_max.

  (*prove exist a tid coresponding to prio in tcbls*)
  assert(exists tid st m sus, get tcbls tid = Some ((y<<ᵢ$ 3)+ᵢx, st, m, sus) /\ rel_edata_stat (v'28, Int.zero) (DMsgQ v'18 (d2
         :: d3 :: Vptr d4 :: d5 :: d6 :: Vint32 d7 :: Vint32 (d8 -ᵢ $ 1) :: Vptr (d9, Int.zero) :: nil) dd3 dd4) st) as ex_tid_prio_rel.
  
  assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)>>ᵢ$ 3) = y) as y_shl3_shr3.
  clear - x_lt8 y_lt8.
  mauto.

  assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)&ᵢ$ 7) = x) as y_shl3_and7.
  clear - x_lt8 y_lt8.
  mauto.

  unfold R_ECB_ETbl_P in H5; simp join.
  eapply PrioWaitInQ_RLH_ECB_PETbl_P_tcbls_ex; eauto.

  
  2: { 
    instantiate (1:=(V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i2 :: x0 :: x1 :: x2 :: Vint32 pegrp :: x4 :: nil
 ) ).
   simpl; auto.
   }
  2: { eapply HR_ECB_PETbl_P. }
  
  unfolds.
  clear - prio_lt64 y_lt8 x_lt8 H7 H12 nth_val_etbl unmap_erow erow_lt256 erow_ne0 y_shl3_shr3 y_shl3_and7.
  unfold Int.add in prio_lt64.
  rewrite Int.unsigned_repr in prio_lt64.
  do 3 eexists.
  splits; eauto.
  clear - x_lt8 y_lt8.
  mauto.
  apply nth_val'_imp_nth_val_int.
  rewrite y_shl3_shr3.
  eauto.
  rewrite y_shl3_and7.
  eapply math_8_255_eq; auto.
  clear - erow_lt256.
  int auto.
  clear - y_lt8 x_lt8.
  mauto.
  destruct ex_tid_prio_rel as [tid [st [m [sus [tcbls_tid_prio rel_ed_st]]]]].

  (*prove vptr tid indexed by prio in prio table*)
  rename v'7 into vhold.
  assert (
        nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl = Vptr tid /\ tid <> vhold
    ) as nth_val_ptbl_vhold.
  clear - H4 tcbls_tid_prio.
  unfolds in H4; destruct H4; destruct H0.
  eapply H0 in tcbls_tid_prio; simp join; split;  auto.
  
  apply nth_val_nth_val'_some_eq; auto.
  destruct nth_val_ptbl_vhold as [nth_val_ptbl tid_neq_vhold].
  
  (*do the statement*)
  hoare forward.
  rewrite prio_ble_max; auto.
  rewrite nth_val_ptbl.
  simpl; auto.
  
  (*key step: prove tid in tcbdllseg*)
  rename v'20 into head; rename v'21 into headprev;
  rename v'22 into tail; rename v'23 into tailnext;
  rename v'12 into vltcb.

  assert (ptr_in_tcblist (Vptr tid) head vltcb).
  eapply tcbls_get_some_TCBList_P_ptr_in_tcblist; eauto.

  (*get the tcb node pointed by tid*)
  hoare_lifts_trms_pre tcbdllseg.
  apply tcbdllseg1_init_pre.
  hoare_split_pure_all.
  apply tcbdllseg1_split_pre with (p:=Vptr tid).
  apply ptr_in_tcblist1_init; auto.
  hoare unfold.
  
  (*ptcb ′ → OSTCBDly =ₑ ′0;ₛ*)
  rewrite nth_val_ptbl.
  hoare forward.

  (*ptcb ′ → OSTCBEventPtr =ₑ NULL;ₛ*)
  hoare forward.

  (*pq ′ =ₑ pevent ′ .. OSEventPtr;ₛ*)
  hoare forward.
  pure_auto.

  (*∗ pq ′ .. OSQIn =ₑ ptcb ′ .. OSTCBMsg;ₛ*)
  rename v'18 into v.
(*   rename dd2 into v0. *)
  rename dd3 into v1.
  rename dd4 into v2.
(*   destruct (DMsgQ v'18 dd2 dd3 dd4).
  2:{
    simpl AEventData.
    hoare_split_pure_all.
    unfold V_OSEventType in H27.
    simpl in H27. tryfalse.
    }
    
  2:{
    simpl AEventData.
    hoare_split_pure_all.
    unfold V_OSEventType in H27.
    simpl in H27. tryfalse.
  }
    
  2:{
    simpl AEventData.
    hoare_split_pure_all.
    unfold V_OSEventType in H27.
    simpl in H27. tryfalse.
  } *)
  simpl AEventData.
  hoare_unfold.
  
  lets Hx: osq_same_blk_st_in' H45; simpljoin.
  simpl in H43; inverts H43.
  lets Hy: wellq_in_props' H47 Hlh_ecbdata H45;eauto.
  simpljoin.
(*   lets Hy: wellq_in_props H47 H4 H45;eauto.
  simpljoin. *)
  
(*   unfold WellformedOSQ in H45.
  destruct H45.
  do 6 destruct H27.
  destruct H27 as (H271 & H272 & H273 & H274 & H275 & H276 & H277 & H278 & H279 & H2710 & H2712 & H2713).
  unfold V_OSQIn in H273.
  simpl in H273.
  inverts H273.
  simpl in H43.
  Search (v'14).
  
   inverts H43. *)
(*   hoare lift 4%nat pre. *)
  hoare forward; eauto.
  pure_auto.
  pure_auto.

  (*++ pq ′ .. OSQIn;ₛ*)

  hoare forward.
  go.
  (*pq ′ → OSQEntries =ₑ pq ′ → OSQEntries +ₑ ′ 1;ₛ*)
  hoare unfold.
  eapply seq_rule.
  eapply assign_rule_struct_aop_typeneq. 
  split.
  introv Hsat.
  sep cancel pq.
  sep cancel (Astruct (v'9, Int.zero)).
  eauto.
  introv Hsat.
  auto. 
  go. go. go. go. go. go. go. go. go. 
  introv Hsat.
  eapply cast_rv_tint32_tint16; eauto. 
  eapply bop_rv.
  eapply struct_member_rv''.
  sep cancel pq.
  sep cancel (Astruct (v'9, Int.zero)).
  eauto.
  go. go. go. go. go. go. go. simpl. eauto. go.
  clear -H48. simpl in H48. simpljoin. auto.
  sep get rv.
  pure_auto.
  pure_auto.
  go.
  go.
  apply eq_int. auto.
  simpl. clear. mauto.
  simpl. eauto.
  introv Hsat. sep pauto. sep cancel p_local. sep auto.
  assert (Heq: (Int.modu ((d8 -ᵢ $ 1) +ᵢ  $ 1) ($ Int16.modulus)) = ((d8 -ᵢ $ 1) +ᵢ  $ 1)).
  { eapply ecast_intlemma1; eauto.  }
  rewrite Heq in *.
  clear Heq.
(*   hoare forward. *)
(*   go. *)

  rename d2 into x15.
  rename d3 into x10.
  rename x3 into x16.
  rename x5 into x17.
  rename d4 into x3.
  rename d6 into x6.
  rename d7 into i8.
  rename d8 into i7.

  (* If(pq ′ → OSQIn ==ₑ pq ′ → OSQEnd)*)
  pure intro.
(*   lets Hx: wellformedosq_ens_add_1 H47 Hlh_ecbdata H45. *)
  rename Hx'' into Hx.
  hoare forward.
  clear -H48 Hx.
  simpl in *. 
  destruct H48 as (H & H0 & H1 & H2 & H3 & H4 & H5).
  splits; eauto. 
  eapply Zle_imp_le_bool in Hx. rewrite Hx. simpl; auto.

  clear -H48 Hx.
  simpl in *. 
  destruct H48 as (H & H0 & H1 & H2 & H3 & H4 & H5).
  splits; eauto. 
  eapply Zle_imp_le_bool in Hx. rewrite Hx. simpl; auto.
  
  clear -H45.
  
  destruct x3.
  destruct (peq v'14 b);
    destruct (Int.eq (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i); simpl; intro; tryfalse.

  (* pq ′ → OSQIn =ₑ pq ′ → OSQStart*)
  hoare forward.
  clear -H48 Hx.
  simpl in *. 
  destruct H48 as (H & H0 & H1 & H2 & H3 & H4 & H5).
  splits; eauto. 
  eapply Zle_imp_le_bool in Hx. rewrite Hx. simpl; auto.

(*   assert (exists a, x3 = Vptr a).
  clear - H45.
  unfolds in H45; simpl in H45; simpljoin.
  unfolds in H0; simpl in H0; inverts H0.
  eauto.
  simpljoin. *)
  
  eapply backward_rule1 with
  (p:= (EX new_qin,
        [| ((v'14, x0 +ᵢ  Int.mul ($ 1) ($ 4)) = x3 /\ new_qin = x10) \/
         ((v'14, x0 +ᵢ  Int.mul ($ 1) ($ 4)) <> x3 /\ new_qin = (Vptr (v'14, x0 +ᵢ  Int.mul ($ 1) ($ 4)))) |] **
         <|| v'19 ||>  **
   LV pq @ os_ucos_h.OS_Q ∗ |-> Vptr (v'9, Int.zero) **
   Astruct (v'9, Int.zero) os_ucos_h.OS_Q
     (x15 :: x10 :: Vptr x3 :: new_qin :: x6 :: Vint32 i8 :: Vint32 ((i7 -ᵢ $ 1) +ᵢ  $ 1) :: Vptr (v'14, Int.zero) :: nil) **
   Aarray (v'14, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero)) (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE)
     (update_nth_val (Z.to_nat ((Int.unsigned x0 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) v2 x11) **
   Astruct (v'14, Int.zero) os_ucos_h.OS_Q_FREEBLK (x16 :: x17 :: nil) **
   LV ptcb @ os_ucos_h.OS_TCB ∗ |-> Vptr (v'8, Int.zero) **
   Astruct (v'8, Int.zero) OS_TCB_flag
     (x14
      :: x13
         :: Vnull :: x11 :: V$ 0 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) **
   tcbdllseg1 head headprev tail tailnext vltcb
     ((Vptr (v'8, Int.zero),
      x14
      :: x13
         :: x12
            :: x11 :: Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
      :: nil) **
   Aarray v'24 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
   LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'28, Int.zero) **
   Astruct (v'28, Int.zero) os_ucos_h.OS_EVENT
     (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i2 :: Vptr (v'9, Int.zero) :: x1 :: x2 :: Vint32 v'13 :: x4 :: nil) **
   Aarray v'26 (Tarray char_t ∘ OS_EVENT_TBL_SIZE)
     (update_nth_val (Z.to_nat (Int.unsigned y)) petbl (Vint32 (erow&ᵢInt.not bitx))) **
   LV prio @ char_t |-> Vint32 ((y<<ᵢ$ 3) +ᵢ  x) **
   LV os_code_defs.bitx @ char_t |-> Vint32 bitx **
   LV os_code_defs.x @ char_t |-> Vint32 x **
   LV os_code_defs.bity @ char_t |-> Vint32 bity **
   LV os_code_defs.y @ char_t |-> Vint32 y **
   Aie false **
   Ais nil **
   Acs (true :: nil) **
   Aisr empisr **
   A_isr_is_prop **
   Aier v'37 **
   GAarray OSUnMapTbl (Tarray char_t 256) OSUnMapVallist **
   GAarray OSMapTbl (Tarray char_t 8) OSMapVallist **
   AOSRdyTblGrp v'10 v'11 **
   GAarray OSTCBPrioTbl (Tarray os_ucos_h.OS_TCB ∗ 64) ptbl **
   p_local OSLInv ct (logic_val (V$ 1) :: lg') **
   LV msk @ Int16u |-> Vint32 v'6 **
   A_dom_lenv
     ((msk, Int16u)
      :: (pevent, os_ucos_h.OS_EVENT ∗)
         :: (ptcb, os_ucos_h.OS_TCB ∗)
            :: (os_code_defs.x, char_t)
               :: (os_code_defs.y, char_t)
                  :: (os_code_defs.bitx, char_t)
                     :: (os_code_defs.bity, char_t) :: (prio, char_t) :: (pq, os_ucos_h.OS_Q ∗) :: nil) )).
  
  intros.
  destruct H49.
  
  (*if true*)
  sep auto.
  left.
  split; auto.
  simpljoin.
  clear - H53.
  destruct x3.
  destruct (peq v'14 b) eqn : eq1;
    destruct (Int.eq (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H53; tryfalse.
  substs.
  pose proof Int.eq_spec (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i.
  rewrite eq2 in H.
  substs; auto.

  (*if false*)
  sep auto.
  right.
  split; auto.
  simpljoin.
  clear - H53.
  destruct x3.
  destruct (peq v'14 b) eqn : eq1;
    destruct (Int.eq (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H53; destruct H53; tryfalse.
  substs.
  intro.
  inverts H0.
  pose proof Int.eq_spec (x0 +ᵢ  Int.mul ($ 1) ($ 4)) (x0 +ᵢ  Int.mul ($ 1) ($ 4)).
  rewrite eq2 in H0.
  tryfalse.

  intro; inverts H0.
  tryfalse.

  intro; inverts H0.
  tryfalse.
  
  pure intro.
  
(*   (*ptcb ′ → OSTCBMsg =ₑ message ′;ₛ*)
  hoare forward.
  apply isptr_match; auto. *)

  (*ptcb ′ → OSTCBStat &= ∼ msk ′;ₛ*)
  hoare forward; pure_auto.

  (* If (ptcb ′ .. OSTCBStat ==ₑ ′ OS_STAT_RDY) *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyGrp.
  hoare unfold.
  rename v'10 into rtbl.
  rename i9 into rgrp.
  rename H27 into rgrp_le255.
  hoare_assert_pure (array_type_vallist_match char_t rtbl /\ length rtbl = ∘ OS_RDY_TBL_SIZE).
  { unfold AOSRdyTbl in H27.
    seplog_trm_tacs.sep_lifts_trms_in H27 array_type_vallist_match.
    eapply sep_pure_split in H27; destruct H27 as (Hmat & _).
    auto.
  }
  seplog_trm_tacs.hoare_lifts_trms_pre (array_type_vallist_match).
  eapply pure_split_rule'; introv Hmat.
  destruct Hmat as (Hmat & Hlen).
  assert (exists i, nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 i /\
                    Int.unsigned i <= 255) as nth_val_rtbl.
  assert(Hvy: Int.unsigned y <= 7).
  clear - y_lt8.
  lia.
  pose proof z_le_7_imp_n y Hvy.
  eapply array_int8u_nth_lt_len; eauto.
  rewrite Hlen.
  unfold OS_RDY_TBL_SIZE.
  auto with zarith.
  destruct nth_val_rtbl as [rrow [nth_val_rtbl rrow_le_255]].
   assert(y_le7: Int.unsigned y <= 7).
  clear - y_lt8.
  lia.
  assert(xle7: Int.unsigned x <= 7).
  clear - x_lt8.
  lia.
  assert(Herow: Int.unsigned erow <= 255).
  clear - erow_lt256.
  lia.
  assert (RL_Tbl_Grp_P (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl
         (Vint32 (Int.or rrow bitx))) (Vint32 (Int.or rgrp bity))) as rl_tbl_grp_new.
  lets Hx1: nth_val_etbl.
  eapply rl_tbl_grp_p_set_hold' with (v'12:= pegrp) in Hx1; eauto.
  rewrite nth_val_rtbl in Hx1; simpl val_inj in Hx1.
  auto.

  assert (forall x, prio_in_tbl x rtbl -> prio_in_tbl x (update_nth_val (Z.to_nat (Int.unsigned y)) rtbl (Vint32 (Int.or rrow bitx)))) as prio_in_tbl_preserv.
  intros.
  eapply prio_in_tbl_preserv; eauto.
  clear - y_lt8 x_lt8.
  mauto.
  assert(((y<<ᵢ$ 3)+ᵢx)&ᵢ$ 7 = x).
  clear - y_lt8 x_lt8.
  mauto.
  rewrite H53.
  clear - map_x x_lt8.
  apply math_mapval_core_prop; auto.

  assert(Hor_prop: Int.unsigned (i5&ᵢInt.not v'6) <= 65535).
  {eapply Z.le_trans. apply Int.and_le. eauto. }
  hoare forward.
  go.
  pure_auto.
  hoare_split_pure_all.
  destruct (Int.eq (i5&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H27; destruct H27 as (Hif & _); tryfalse.
  clear Hif.

  (**)
  (*key step: put the tcb node back into the tcblist*)
  hoare lifts (3::8::nil)%nat pre.
  apply tcbdllseg1_node_join_pre1; auto.
  go.

  unfolds; simpl; auto.
  simpl; auto.

  apply tcbdllseg1_to_tcbdllseg_pre1.
  (**)
  
  (*OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ os_code_defs.bity ′;ₛ*)
  hoare unfold.
  hoare forward; pure_auto.

  (*OSRdyTbl ′ [os_code_defs.y ′] =ₑ
   OSRdyTbl ′ [os_code_defs.y ′] |ₑ os_code_defs.bitx ′;ₛ*)
  unfold AOSRdyTbl.
  hoare_split_pure_all.
  destruct H27.

  hoare unfold.
  hoare forward.
  pure_auto.
  rewrite H53; unfold OS_RDY_TBL_SIZE; simpl; auto.
  simpl; rewrite nth_val_rtbl; pure_auto.
  pure_auto.
  rewrite nth_val_rtbl; simpl; intro; tryfalse.
  pure_auto.
  unfold OS_RDY_TBL_SIZE; simpl; auto.
  rewrite H53; unfold OS_RDY_TBL_SIZE; simpl; auto.

  assert (Hwell: WellformedOSQ
  (x15
   :: x10
      :: Vptr x3
         :: v'7
            :: x6
               :: Vint32 i8
                  :: Vint32 ((i7 -ᵢ $ 1) +ᵢ  $ 1)
                     :: Vptr (v'14, Int.zero) :: nil)).
  { destruct H49; simpljoin; substs.
     eapply get_wellformedosq_in_setst; eauto.
     rewrite Int.eq_true.
     rewrite peq_true.
     pure_auto.
     eapply get_wellformedosq_in_setst'; eauto.
     introv Hf; inverts Hf; tryfalse.
   }
  assert(Hqmat: struct_type_vallist_match OS_Q
  (x15
   :: x10
      :: Vptr x3
         :: v'7
            :: x6
               :: Vint32 i8
                  :: Vint32 ((i7 -ᵢ $ 1) +ᵢ  $ 1)
                     :: Vptr (v'14, Int.zero) :: nil)).
  { destruct H49; simpljoin; substs.
     clear -H48 Hx.
     simpl in *.
     simpljoin.
     splits; eauto. 
     eapply Zle_imp_le_bool in Hx. rewrite Hx. simpl; auto.
     clear -H48 H27 Hx.
     simpl in *. 
     simpljoin.
     splits; eauto. 
     eapply Zle_imp_le_bool in Hx. rewrite Hx. simpl; auto.
  }
  hoare forward.
  Focus 2.
  hoare_split_pure_all.
  destruct (Int.eq (i5&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H27; destruct H27 as [Hif1 |  Hif2]; tryfalse.
  clear Hif1.
  hoare lifts (3::8::nil)%nat pre.
  apply tcbdllseg1_node_join_pre1; auto.
  go.
  unfolds; simpl; auto.
  simpl; auto.
  apply tcbdllseg1_to_tcbdllseg_pre1.
  hoare forward; try  rewrite Hifrdy; try eauto.
  (*side conditions*)
{
  rewrite prio_ble_max; auto.
}
{
  simpl update_nth_val.
  unfold AOSUnMapTbl, AOSMapTbl.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr,AOSQBlk.
  unfold node.
  sep auto.
  unfolds; simpl; eauto.
  split;auto.
  split;auto.
  go.
}
{
  clear - H H26.
  eapply ptr_in_tcbdllseg1_set_node; eauto.
  unfolds; simpl; auto.
}
(* split; auto. *)
rtmatch_solve.
(* unfolds; *) simpl; auto.
{
  eapply array_type_vallist_match_int8u_update_hold; eauto.
}
split; auto.
go.
rtmatch_solve.
{clear Hx.
  lets Hx: TCBList_P_get_node_TCBNode_P H6 H26 tcbls_tid_prio.
  clear - Hx rel_ed_st.
  unfold TCBNode_P in Hx; simp join.
  clear - H2 rel_ed_st.
  unfolds in H2; simp join.
  eapply RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat; eauto.
}
split.
eauto.
go.

  (* case: OS_STAT_RDY *)
  hoare_split_pure_all.
  destruct (Int.eq (i5&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H27; destruct H27 as (Hif & _); tryfalse.
  clear Hif.
  rewrite nth_val_rtbl.
  simpl val_inj.

  (*RETURN prio ′*)
(*   hoare_split_pure_all. *)

  hoare forward; try rewrite Hifrdy.
  (*side conditions*)
{
  rewrite prio_ble_max; auto.
}
{
  simpl update_nth_val.
  unfold AOSUnMapTbl, AOSMapTbl.
  unfold AEventData.
  unfold AMsgData.
  unfold AOSQCtr,AOSQBlk.
  unfold node.
  sep auto.
  split.
  eapply array_type_vallist_match_hold; eauto.
  rewrite Hlen.
  unfold OS_RDY_TBL_SIZE.
  clear - y_lt8.
  mauto.
  clear - bitx_le128 rrow_le_255.
  rtmatch_solve.
  apply int_unsigned_or_prop'; int auto.
  rewrite update_nth_val_len_eq; auto.
  unfolds; simpl; eauto.
  eauto.
  split;auto.
  go.
  }
  eauto.
{
  clear Hx.
  lets Hx: rl_rtbl_priotbl_p_hold tid_neq_vhold H3 H19 H24 H7.
  lets Hx': nth_val_etbl.
  eapply Hx in Hx'; eauto.
  rewrite nth_val_rtbl in Hx'; simpl val_inj in Hx'.
  auto.
}
{
  clear - H H26.
  eapply ptr_in_tcbdllseg1_set_node; eauto.
  unfolds; simpl; auto.
}
{
  clear - H52  rl_tbl_grp_new prio_in_tbl_preserv y_lt8 x_lt8 map_x x_lt8 nth_val_rtbl.
  split; eauto.
}
{
(*   clear - rgrp_le255 bity_le128. *)
  rtmatch_solve.
  apply int_unsigned_or_prop; auto.
}
eauto.
simpl; auto.
auto.
{
  eapply array_type_vallist_match_int8u_update_hold; eauto.
}
  eauto.
  simpl.
  auto.
  auto.
  split; auto.
  simpl update_nth_val; pure_auto.
  pure_auto.
  auto.
  eauto.
  auto.
  auto.
  eauto.
{
  clear Hx.
  lets Hx: TCBList_P_get_node_TCBNode_P H6 H26 tcbls_tid_prio.
  clear - Hx rel_ed_st.
  unfold TCBNode_P in Hx; simp join.
  clear - H2 rel_ed_st.
  unfolds in H2; simp join.
  eapply RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat; eauto.
}
  auto.
  split.
  eauto.
  go.
  auto.
  auto.
Qed.

Close Scope code_scope.
