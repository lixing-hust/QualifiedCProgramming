Require Import ucos_include.
Require Import os_ucos_h.
Require Import sep_lemmas_ext.
Require Import sem_common.
Require Import new_inv.
Require Import linv_solver.
Require Import inline_definitions.
Require Import inline_bittblfunctions.
Require Import inline_tactics.
Require Import symbolic_lemmas.
Require Import Lia.
Require Import protect.
Require Import OSTimeDlyPure.
Require Import tasksuspend.
Require Export include_frm.
Require Export Integers.
(* Require Import taskpure.v. *)
Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

(* Definition OSTaskResume_impl := 
  Int8u ·OSTaskResume·(⌞prio @ Int8u⌟)··{
    ⌞ ptcb @ OS_TCB∗⌟;
    If (prio′ ≥ ′OS_LOWEST_PRIO) {
      RETURN ′OS_PRIO_INVALID
    };ₛ
    ENTER_CRITICAL;ₛ
    ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
    If (ptcb′ ==ₑ NULL){
      EXIT_CRITICAL;ₛ
      RETURN ′OS_TASK_RESUME_PRIO
    };ₛ
    If ((ptcb′→OSTCBStat &ₑ ′OS_STAT_SUSPEND) !=ₑ ′OS_STAT_RDY){
      ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼′OS_STAT_SUSPEND);ₛ
      If(ptcb′→OSTCBStat ==ₑ ′OS_STAT_RDY){
        If(ptcb′→OSTCBDly ==ₑ ′ 0){
          OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ
          OSRdyTbl′[y′] =ₑ OSRdyTbl′[y′] |ₑ ptcb′→OSTCBBitX;ₛ
          EXIT_CRITICAL;ₛ
          OS_Sched(­)
        }
      };ₛ
      EXIT_CRITICAL;ₛ
      RETURN ′OS_NO_ERR
    };ₛ
    EXIT_CRITICAL;ₛ
    RETURN ′OS_TASK_NOT_SUSPENDED
}·. *)
Lemma absimp_taskres_prio_idle:
  forall P v1 sch,
    can_change_aop P ->
    (Int.ltu (Int.repr OS_LOWEST_PRIO) v1 = true \/ Int.eq (Int.repr OS_LOWEST_PRIO) v1 = true)->
    absinfer sch ( <|| taskresumecode ((Vint32 v1) :: nil) ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma absimp_taskres_no_such_tcb:
  forall P v1 sch (ecbls : EcbMod.map) (tcbls : TcbMod.map),
    can_change_aop P ->
    (~exists tid st msg sus, TcbMod.get tcbls tid = Some (v1, st, msg, sus)) ->
    absinfer sch ( <|| taskresumecode ((Vint32 v1) :: nil) ||> **
                       HECBList ecbls **
                       HTCBList tcbls ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_TASK_RESUME_PRIO))) ||> **
                       HECBList ecbls **
                       HTCBList tcbls ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma abs_imp_taskres_succ:
  forall P v1 sch (ecbls : EcbMod.map) (tcbls : TcbMod.map) tid st msg sus,
    can_change_aop P ->
    TcbMod.get tcbls tid = Some (v1, st, msg, sus) ->
    absinfer sch
      ( <|| taskresumecode ((Vint32 v1) :: nil) ||> **
            HECBList ecbls ** HTCBList tcbls ** P )
      ( <|| isched;; END (Some (Vint32 (Int.repr OS_NO_ERR))) ||> **
            HECBList ecbls ** HTCBList (TcbMod.set tcbls tid (v1, st, msg, false)) ** P).
Proof.
  infer_solver 3%nat.
Qed.

Lemma or_true_ltrue_rtrue: forall x y, val_inj (bool_or (val_inj (Some x)) (val_inj (Some y))) <> Vint32 Int.zero -> x <> Vint32 Int.zero \/  y <> Vint32 Int.zero.
Proof.
  intros.
  unfold bool_or in H.
  destruct x; destruct y; tryfalse;
  simpl in H;try solve[left; intro; tryfalse].
  right; intro; tryfalse.
  right; intro; tryfalse.
  unfold Int.ltu in H.
  2: right; intro; tryfalse.
  destruct ( zlt (Int.unsigned Int.zero) (Int.unsigned i)).
  left.
  intro.
  inverts H0.
  tryfalse.
  destruct ( zlt (Int.unsigned Int.zero) (Int.unsigned i0)).
  right; intro.
  inverts H0.
  try false.
  simpl in H.
  tryfalse.
Qed.

Lemma OSTCBflag_des:
forall v'11,
  struct_type_vallist_match OS_TCB_flag v'11 ->
  exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10,
    exists a11,
    v'11 = (a1::a2::a3::a4::a5::a6::Vint32 a7::a8::a9::a10::a11::nil).
Proof.
  intros.
  destruct v'11; simpl in H; tryfalse.
  destruct v'11; simpl in H; simpljoin; tryfalse.
  destruct v'11; simpl in H; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v'11; simpl in *; simpljoin; tryfalse.
  destruct v5; tryfalse.
  repeat tri_exists_and_solver1.
Qed.

Lemma nv'2nv:
  forall vl n x,
    nth_val' n vl = x ->
    x <> Vundef ->
    nth_val n vl = Some x.
Proof.
  induction vl.
  induction n.
  intros.
  simpl in H.
  tryfalse.
  intros.
  simpl in H.
  tryfalse.

  induction n.
  intros.
  simpl in H.
  simpl.
  inverts H.
  auto.
  intros.
  simpl.
  simpl in H.
  apply IHvl.
  auto.
  auto.
Qed.

Ltac sep_get_rv1:=
  match goal with
  | H: ?s |= ?P |- ?s |= Rv (evar ?x) @ _ == _ =>
  match find_lvarmapsto P x with
    | some ?m =>
      eapply lvar_rv;
        [ sep lift m in H; exact H
        (*| auto*)
        | simpl; auto ]
    | none _ =>
      match find_dom_lenv P with
        | (none _, _) => fail 1
        | (some ?m, Some ?l) =>
          let ret1 := constr:(var_notin_dom x l) in
          let ret2 := (eval compute in ret1) in
          match ret2 with
            | true =>
              match find_gvarmapsto P x with
                | none _ => fail 2
                | some ?n =>
                  eapply gvar_rv;
                    [ sep lifts (m::n::nil)%list in H; exact H
                    | simpl; auto
                    (*| auto*)
                    | simpl; auto ]
              end
            | false => fail 3
          end
      end
  end
end.

  (* In taskdelete.v *)
Lemma valinjbopevallemma:
forall x v'19, val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
    Vint32 Int.zero \/
    val_inj (bop_eval (Vptr x) (Vptr v'19) OS_TCB ∗ (Int8u) ∗ oeq) =
    Vnull -> x <> v'19.
  Proof.
    intros.
    destruct H.
    simpl in H.
    destruct x; destruct v'19.
    intro.
    inverts H0.
    rewrite peq_true in H.
    rewrite Int.eq_true in H.
    inverts H.
    simpl in H.
    destruct x; destruct v'19.
    destruct (peq b b0); destruct (Int.eq i i0); tryfalse.
Qed.

Lemma val_inj_iftrue_impl_eqtrue :  
  forall i, val_inj (if Int.eq i ($ 0)
                      then Some (Vint32 Int.one)
                                else Some (Vint32 Int.zero)) <> 
            Vint32 Int.zero ->   Int.eq i ($ 0) = true.
  Proof.
    intros.
    assert (Int.eq i ($ 0) = true \/ Int.eq i ($ 0) = false).
    destruct (Int.eq i ($ 0)); auto.
    destruct H0; auto.
    rewrite H0 in H.
    simpl in H.
    auto.
Qed.

Lemma int_eq_true_impl_eq:
  forall i j,
    Int.eq i j = true ->
    i = j.
  intros.
  assert (Hif: if Int.eq i j then i = j else i <> j).
    eapply Int.eq_spec.
  rewrite H in Hif.
  auto.
Qed.

(* In tasksuspend.v *)
Lemma prio_rtbl_dec':
forall x rtbl,
  0 <= Int.unsigned x < 64 ->
  array_type_vallist_match Int8u rtbl ->
  length rtbl = ∘OS_RDY_TBL_SIZE ->
  prio_in_tbl x rtbl -> prio_not_in_tbl x rtbl -> False.
Proof.
  intros.
  unfolds in H2. unfolds in H3.
  assert (exists z, nth_val ∘ (Int.unsigned (x >>ᵢ $ 3)) rtbl =
  Some (Vint32 z)). {
    apply array_type_match_get_value.
    mauto. auto. auto.
  }
  destruct H4.
  assert (x0 &ᵢ($ 1<<ᵢ (x&ᵢ$ 7)) = $ 1<<ᵢ (x&ᵢ$ 7)). {
    eapply H2; auto.
  }
  assert (x0&ᵢ($ 1<<ᵢ(x&ᵢ$ 7)) = $0). {
    eapply H3; auto.
  }
  rewrite H5 in H6.
  assert ($ 1<<ᵢ(x&ᵢ$ 7) <> $ 0). {
    apply math_prop_neq_zero2; auto.
  }
  auto.
Qed.

(* In OSQPostPure.v *)
Lemma prio_in_tbl_orself :
forall prio v'37 vx,
  prio_in_tbl prio
              (update_nth_val (Z.to_nat (Int.unsigned (Int.shru prio ($ 3)))) v'37
                              (Vint32 (Int.or vx ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  intros.
  unfolds.
  intros.
  subst.
  apply nth_upd_eq in H1.
  inverts H1.
  rewrite Int.and_commut.
  rewrite Int.or_commut.
  rewrite Int.and_or_absorb.
  auto.
Qed.

(* In task_pure.v *)
Lemma Z_and_onebitmask:
  forall a b,
    0<=b ->
    Z.land a (Z.shiftl 1 b) = Z.shiftl 1 b \/ Z.land a (Z.shiftl 1 b) = 0.
Proof.
  intros.
  
  assert (Z.testbit a b = true \/ Z.testbit a b= false).
  destruct (Z.testbit a b); tauto.
  destruct H0.

  left.
  eapply Byte.equal_same_bits.
  intros.
  rewrite Z.land_spec.

  assert ( b = i \/ b <> i).
  tauto.
  destruct H2.
  subst.
  rewrite H0.
  simpl.
  auto.
  assert (i = (i-b)+b).
  lia.
  rewrite H3 at 2 3.
  rewrite Z.shiftl_spec_alt.
  rewrite Byte.Ztestbit_1.
  assert (i - b <> 0).
  lia.
  remember ( zeq (i - b) 0 ).
  destruct s.
  tryfalse.
  simpl.
  rewrite andb_false_r.
  reflexivity.
  auto.
  
  right.

  eapply Byte.equal_same_bits.
  intros.
  assert (i = (i-b)+b).
  lia.
  rewrite Z.land_spec.
  rewrite H2 at 2 .
  rewrite Z.shiftl_spec_alt.
  rewrite Byte.Ztestbit_1.
  rewrite Byte.Ztestbit_0.
  assert ( i = b \/ i <> b).
  tauto.
  destruct H3.
  subst.
  rewrite H0.
  simpl.
  reflexivity.

  remember ( zeq (i - b) 0 ).
  destruct s.
  assert (i = b).
  lia.
  tryfalse.
  simpl.
  rewrite andb_false_r.
  reflexivity.
  auto.
 
Qed.

Lemma and_onebitmask:
  forall z x ,
    Int.unsigned x <= 7 ->
    z&ᵢ($ 1 <<ᵢ x) = $ 1 <<ᵢ x \/ z&ᵢ($ 1 <<ᵢ x) = $ 0.
Proof.
  intros.
  unfold Int.and.
  unfold Int.shl.
  repeat ur_rewriter.
  Focus 2.
  mauto.
  assert (0 <= Int.unsigned x).
  int auto.

  lets bb: Z_and_onebitmask (Int.unsigned z) (Int.unsigned x) H0.
  destruct bb.
  left.
  rewrite H1.
  auto.
  right.
  rewrite H1.
  auto.
Qed.

Lemma not_prio_in_tbl_is_prio_not_in_tbl:
  forall p rtbl,
    ~prio_in_tbl p rtbl ->
    prio_not_in_tbl p rtbl.
Proof.
  intros.
  unfold prio_in_tbl in H.
  unfold prio_not_in_tbl.
  intros.
  assert (z&ᵢ($ 1 <<ᵢ x) = $ 1 <<ᵢ x \/ z&ᵢ($ 1 <<ᵢ x) = $ 0).
  apply and_onebitmask.
  subst.
  rewrite Int.and_commut.
  eapply Z.le_trans.

  apply Int.and_le. 
  clear.
  int auto.

  destruct H3.

  false.
  apply H.
  intros.
  rewrite <- H4 in H0.
  subst.
  rewrite H6 in H2.
  inverts H2.
  auto.
  auto.
Qed.

(* In taskdelete.v *)
Lemma tcbget_ptr_in_tcblist:
  forall tcblst head rtbl tcbmap x xx,
  TCBList_P head tcblst rtbl tcbmap ->
  get tcbmap x = Some xx ->
  ptr_in_tcbdllseg (Vptr x) head tcblst.
  Proof.
  induction tcblst.
  intros.
  simpl in H.
  subst tcbmap.
  rewrite map_emp_get in H0.
  inverts H0.
  intros.
  unfold1 ptr_in_tcbdllseg.
  remember (beq_val (Vptr x) head).
  destruct b.
  auto.
  unfold1 TCBList_P in H.
  simpljoin.
  rewrite H1.
  eapply IHtcblst.
  exact H4.
  assert ( x <> x0).
  intro.
  subst x0.
  rewrite beq_val_true in Heqb.
  tryfalse.
  unfold join,get,sig in *; simpl in *.
  eapply TcbMod.join_get_or in H2.
  destruct H2; eauto.
  rewrite TcbMod.get_a_sig_a' in H2.
  inverts H2.
  go.
  eauto.
Qed.

Lemma stat_resume_rdy_imp_rdy :  
  forall stat , stat &ᵢ Int.not ($ OS_STAT_SUSPEND) = $ 0 ->
                stat = $ OS_STAT_RDY \/
                stat = $ OS_STAT_SUSPEND \/
                stat = $ OS_STAT_SEM \/
                stat = $ OS_STAT_Q \/
                stat = $ OS_STAT_MBOX \/
                stat = $ OS_STAT_MUTEX \/
                stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
                stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
                stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
                stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) ->
                stat = $ 0 \/ stat = $ 8.
  Proof.
    intros.
    int auto.
    unfold OS_STAT_SUSPEND in *;unfold OS_STAT_RDY in *;unfold OS_STAT_SEM  in *;
    unfold OS_STAT_Q in *;unfold OS_STAT_MBOX in *;unfold OS_STAT_MUTEX in *.
    unfold Int.not in H.
    int auto.
    2: mauto.
    assert ((Z.lxor 8 4294967295)=  4294967287). {
      unfold Z.lxor.
      unfold Pos.lxor.
      simpl.
      auto.
    }
    rewrite H1 in H.
    clear H1.
    unfold Z.lor in H0;simpl in H0.
    destruct H0.
    auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    destruct H0.
    rewrite H0 in H;int_auto.
    rewrite H0 in H;int_auto.
    unfold OS_STAT_MUTEX;lia.
    unfold OS_STAT_MBOX;lia.
    unfold OS_STAT_Q;lia.
    unfold OS_STAT_SUSPEND;lia.
    unfold OS_STAT_SEM;lia.
Qed.

Lemma low_stat_rdy_or_sus_imp_high_rdy:
  forall a b c d e f g h i j k l st rtbl p t m sus,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    RL_TCBblk_P  (a
                    :: b
                    :: c
                    :: d
                    :: Vint32 e
                    :: Vint32 st
                    :: Vint32 f
                    :: g
                    :: h :: i :: j :: k :: l :: nil)
    ->
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: Vint32 f
         :: g
         :: h :: i :: j :: k :: l :: nil)
      rtbl (p, t, m, sus) -> Int.eq st ($ OS_STAT_RDY) = true \/ Int.eq st ($ OS_STAT_SUSPEND) = true ->
    Int.eq e ($ 0) = true ->
    t = rdy .
    Proof.
      introv Hz Hlen  Ht  Hr Heq Heqq.
      funfold Ht.
      unfolds in Hr.
      destruct Hr as (RLH_rdy & RHL_rdy & RLH_sus & RHL_sus & RLH_wait & RHL_wait).
      destruct Heq.
      + unfolds in RLH_wait.
        simpljoin;try splits.
        unfolds in H0.
        unfold V_OSTCBStat in *; simpl in *.
        unfold WaitTCBblk in *; simpl in *.
        unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *.
        assert (Some (Vint32 x) = Some (Vint32 x)).
        auto.
        unfold Pos.to_nat in Hlen.
        simpl in Hlen.
        assert ( 0 <= Int.unsigned x < 64 ) by lia.
        lets Hdis : prio_rtbl_dec  Hz Hlen; eauto.
        assert (if Int.eq x4 ($ OS_STAT_RDY) then  x4  =($ OS_STAT_RDY)
                else x4 <> ($ OS_STAT_RDY)).
        apply Int.eq_spec.
        rewrite H in H15.
        subst.
        destruct Hdis as [Hd1 | Hd2].
        assert (Some (Vint32 x) = Some (Vint32 x) /\
                prio_in_tbl x rtbl). 
        split;eauto.
        eapply RLH_rdy in H15.
        destruct H15 as ( _ & Had & Hzd).
        (* destruct Hzd. inverts H9. *)
        destruct Hzd as (m0 & H15).
        (* eapply H3 in H9. *)
        inverts H15; auto.
        assert (Some (Vint32 e) = Some (Vint32 e)).
        auto.
        assert (Some (Vint32 x) = Some (Vint32 x) /\
                prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 e)).   
        splits; auto.
        eapply H0 in H16;auto.
        simpljoin;try splits.
        eapply ltu_eq_false in H16.
        unfold Int.zero in H16.
        rewrite Heqq in H16.
        tryfalse.
      + unfolds in RLH_sus.
        simpljoin;try splits.
        unfold V_OSTCBStat in *; simpl in *.
        unfold WaitTCBblk in *; simpl in *.
        unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *.
        assert (Some (Vint32 x) = Some (Vint32 x)).
        auto.
        unfold Pos.to_nat in Hlen.
        simpl in Hlen.
        assert ( 0 <= Int.unsigned x < 64 ) by lia.
        lets Hdis : prio_rtbl_dec  Hz Hlen; eauto.
        assert (if Int.eq x4 ($ OS_STAT_SUSPEND) then  x4  =($ OS_STAT_SUSPEND)
                else x4 <> ($ OS_STAT_SUSPEND)).
        apply Int.eq_spec.
        rewrite H in H4.
        subst.
        destruct Hdis as [Hd1 | Hd2].
        assert (Some (Vint32 x) = Some (Vint32 x) /\
                prio_in_tbl x rtbl). 
        split;eauto.
        eapply RLH_rdy in H4.
        destruct H4 as ( _ & Had & Hzd).
        (* destruct Hzd. inverts H9. *)
        destruct Hzd as (m0 & H4).
        (* eapply H3 in H9. *)
        inverts H4; auto.
        apply int_eq_true_impl_eq in Heqq.
        assert (Some (Vint32 e) = Some (Vint32 Int.zero)). {
          rewrite Heqq.
          eauto.
        }
        assert (Some (Vint32 x) = Some (Vint32 x) /\
                prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 Int.zero)).   
        splits; auto.
        eapply H0 in H6;auto.
        simpljoin;try splits.
    Qed.

Lemma low_stat_rdy_imp_high_susFalse:
  forall a b c d e f g h i j k l st rtbl p t m sus,
    array_type_vallist_match Int8u rtbl ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    RL_TCBblk_P  (a
                    :: b
                    :: c
                    :: d
                    :: Vint32 e
                    :: Vint32 st
                    :: Vint32 f
                    :: g
                    :: h :: i :: j :: k :: l :: nil)
    ->
    R_TCB_Status_P
      (a
         :: b
         :: c
         :: d
         :: Vint32 e
         :: Vint32 st
         :: Vint32 f
         :: g
         :: h :: i :: j :: k :: l :: nil)
      rtbl (p, t, m, sus) -> Int.eq st ($ OS_STAT_RDY) = true ->
    Int.eq e ($ 0) = true ->
    sus = false.
Proof.
  introv Hz Hlen  Ht  Hr Heq Heqq.
  funfold Ht.
  unfolds in Hr.
  simpljoin;try splits.
  clear H0 H1 H2 H4.
  unfolds in H.
  unfolds in H3.
  simpljoin;try splits.
  unfolds in H0.
  unfolds in H1.
  unfolds in H2.
  unfolds in H3.
  unfolds in H4.
  unfold RdyTCBblk in *.
  unfold V_OSTCBStat in *; simpl in *.
  unfold WaitTCBblk in *; simpl in *.
  unfold V_OSTCBPrio,  V_OSTCBDly , V_OSTCBEventPtr in *; simpl in *.
  assert (Some (Vint32 x) = Some (Vint32 x)).
  auto.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  assert ( 0 <= Int.unsigned x < 64 ) by lia.
  lets Hdis : prio_rtbl_dec  Hz Hlen; eauto.
  assert (if Int.eq x4 ($ OS_STAT_RDY) then  x4  =($ OS_STAT_RDY)
          else x4 <> ($ OS_STAT_RDY)).
  apply Int.eq_spec.
  rewrite Heq in H15.
  subst.
  destruct Hdis as [Hd1 | Hd2].
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_in_tbl x rtbl). 
  split;eauto.
  eapply H in H15.
  destruct H15 as ( _ & Had & Hzd).
  (* destruct Hzd. inverts H9. *)
  destruct Hzd as (m0 & H15).
  (* eapply H3 in H9. *)
  inverts H15; auto.
  assert (Some (Vint32 e) = Some (Vint32 e)).
  auto.
  assert (Some (Vint32 x) = Some (Vint32 x) /\
          prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 e)).   
  splits; auto.
  eapply H0 in H16;auto.
  simpljoin;try splits.
Qed.

Lemma option2Vint32val:
forall x y,
  Some (Vint32 x) = Some (Vint32 y) -> x = y.
Proof.
  intros x y Hinteq.
  inversion Hinteq.
  trivial.
Qed.

Lemma RL_TCBblk_P_resume:
  forall next prev eptr msg dly stat prio x y bitx bity,
  RL_TCBblk_P
    (next :: prev :: eptr :: msg :: dly :: Vint32 stat
    :: prio :: x :: y :: bitx :: bity :: nil) ->
    RL_TCBblk_P
    (next :: prev :: eptr :: msg :: dly
    :: Vint32 (Int.and stat (Int.not ($ OS_STAT_SUSPEND)))
    :: prio :: x :: y :: bitx :: bity :: nil). {
      intros. unfold RL_TCBblk_P in *.
      simpljoin; inverts H; inverts H0; inverts H1; inverts H2;
      inverts H3; inverts H4; inverts H11.
      do 6 eexists. splits.
      unfolds; simpl; eauto.
      unfolds; simpl; eauto.
      unfolds; simpl; eauto.
      unfolds; simpl; eauto.
      unfolds; simpl; eauto.
      unfolds; simpl; eauto.
      auto.
      splits; auto.
      unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q,
      OS_STAT_MBOX, OS_STAT_MUTEX in *.
      destruct H10. rewrite H; auto.
      destruct H. rewrite H; auto.
      destruct H. rewrite H; do 2 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 3 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 4 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 5 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 2 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 3 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 4 apply or_intror; apply or_introl; reflexivity.
      rewrite H. do 5 apply or_intror. apply or_introl. reflexivity.
      unfold V_OSTCBEventPtr. simpl. exists x6.
      split. auto. unfold OS_STAT_SUSPEND, OS_STAT_RDY.
      intro pred. unfold OS_STAT_RDY in *.
      eapply H12.
      rename H10 into H.
      (* repeat destruct H; try solve [left;auto|right;auto|rewrite H in pred; destruct pred; tryfalse]. *)
      destruct H. {left;auto. }
      destruct H. {right;auto. }
      (* destruct H; [rewrite H in pred; destruct pred; tryfalse ]. *)
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      destruct H. {rewrite H in pred; destruct pred; tryfalse. }
      {rewrite H in pred; destruct pred; tryfalse. }
    }
Qed.

Lemma R_TCB_Status_P_resume:
  forall rtbl x y row bitx bity prio rtbl' next prev eptr msg stat p m0 i,
    0 <= Int.unsigned prio < 64 ->
    length rtbl' = ∘OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned y)) rtbl = Vint32 row ->
    (* (prio_in_tbl prio rtbl -> prio_in_tbl prio rtbl') -> *)
    prio_in_tbl prio rtbl' ->
    RL_TCBblk_P
    (next :: prev :: eptr :: msg :: V$ 0 :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) ->
    R_TCB_Status_P
    (next :: prev :: eptr  :: msg :: V$ 0 :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) rtbl (p, rdy, m0, i) ->
    array_type_vallist_match Int8u rtbl' ->
    stat = $ OS_STAT_RDY \/ stat = $ OS_STAT_SUSPEND ->
    prio_in_tbl prio rtbl \/ prio_not_in_tbl prio rtbl ->
    R_TCB_Status_P
    (next :: prev :: eptr  :: msg :: V$ 0 :: Vint32 (stat &ᵢInt.not ($ OS_STAT_SUSPEND))
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) rtbl' (p, rdy, m0, false). 
Proof.
        intros.
        rename H3 into RLtcbblk.
        rename H4 into H3.
        rename H7 into Hpdec.
        lets HTCB_P_Backup : H3.
        unfold R_TCB_Status_P in H3.
        destruct H3 as [RLHrdy [RHLrdy [RLHsus [RHLsus [RLHstwait RHLstwait]]]]].
        destruct RLtcbblk;simpljoin.
        unfold OS_STAT_RDY,OS_STAT_SUSPEND in H6.
        assert (stat &ᵢInt.not ($ OS_STAT_SUSPEND) = $0) as Heqstat'. {
          destruct H6.
          rewrite H6;eauto.
          rewrite H6;eauto.
        }
        rewrite Heqstat'.
        destruct H6.
        inverts H3;inverts H6;inverts H10.
        clear H3.
        (* stat = $ 0 *)
        { 
          unfold R_TCB_Status_P.
          splits.
          + unfold RLH_RdyI_P in *.
            intros;splits;eauto.
            destruct H7.
            destruct Hpdec as [Hpin|Hpnin].
            - unfold RdyTCBblk in H3;simpljoin.
              inverts H3.
              pose proof (RLHrdy prio);simpljoin.
              assert (RdyTCBblk
              (next
               :: prev
                  :: eptr
                     :: msg :: V$ 0 :: V$ 0 :: Vint32 prio :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
              rtbl prio). {
                unfolds.
                splits;auto.
              }
              apply H3 in H7;simpljoin.
              eexists x0;auto.
            - unfold RHL_Suspend_P in RHLsus.
              destruct RHLsus as (RHLsus1 & RHLsus2).
              destruct i.
              {
                pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true)));simpljoin.
                tryfalse.
              }
              {
                unfold RHL_RdyI_P in RHLrdy.
                pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false)));simpljoin.
                unfold RdyTCBblk in H6;simpljoin.
                inverts H6.
                unfold RdyTCBblk in H3;simpljoin.
                inverts H3.
                eexists m0;eauto.
              }
          + unfold RHL_RdyI_P in *.
            intros.
            inverts H3.
            splits;eauto.
            unfolds;splits.
            destruct i.
            - unfold RHL_Suspend_P in RHLsus.
              destruct RHLsus as (RHLsus1 & RHLsus2).
              pose proof (RHLsus1 prio m (eq_refl (prio, rdy, m, true))).
              unfold WaitTCBblk in H3;simpljoin;eauto.
            - pose proof (RHLrdy prio m (eq_refl (prio, rdy, m, false))).
              unfold RdyTCBblk in H3;simpljoin;eauto.
            - destruct i.
              {
                unfold RHL_Suspend_P in RHLsus.
                destruct RHLsus as (RHLsus1 & RHLsus2).
                pose proof (RHLsus1 prio m (eq_refl (prio, rdy, m, true))).
                unfold WaitTCBblk in H3;simpljoin.
                inverts H3.
                apply H2.
              }
              {
                pose proof (RHLrdy prio m (eq_refl (prio, rdy, m, false))).
                simpljoin.
                unfolds in H3;simpljoin.
                inverts H3.
                auto.
              }
          + unfold RLH_Suspend_P in *.
            splits.
            intros.
            tryfalse.
            intros.
            tryfalse.
          + unfold RHL_Suspend_P in *.
            splits.
            intros.
            tryfalse.
            intros.
            tryfalse.
          + unfold RLH_TCB_Status_Wait_P in *.
            destruct RLHstwait as (RLHwait & RLHwaitS & RLHwaitQ & 
            RLHwaitMB & RLHwaitMS & RLHwaitSsus & RLHwaitQsus & RLHwaitMBsus & RLHwaitMSsus).
            splits.
            - unfold RLH_Wait_P in *.
              intros.
              unfold WaitTCBblk in H3;simpljoin.
              inverts H3;inverts H12.
              pose proof (RLHwait prio Int.zero).
              destruct Hpdec as [Hpin|Hpnin].
              {
                assert (WaitTCBblk
                (next
                :: prev
                    :: eptr
                      :: msg :: V$ 0 :: V$ 0 :: Vint32 prio :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
                rtbl prio Int.zero). {
                  unfolds.
                  splits;eauto.
                  apply not_prio_in_tbl_is_prio_not_in_tbl.
                  assert (0 <= Int.unsigned prio < 64) as Hprange by auto.
                  false.
                  eapply prio_rtbl_dec';eauto.
                }
                apply H3 in H12.
                simpljoin.
                eauto.
              }
              {
                assert (WaitTCBblk
                (next
                :: prev
                    :: eptr
                      :: msg :: V$ 0 :: V$ 0 :: Vint32 prio :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
                rtbl prio Int.zero). {
                  unfolds.
                  splits;eauto.
                }
                apply H3 in H12.
                simpljoin.
                eauto.
              }
            - unfold RLH_WaitS_P in *.
              intros.
              tryfalse.
            - unfold RLH_WaitQ_P in *.
              intros.
              tryfalse.
            - unfold RLH_WaitMB_P in *.
              intros.
              tryfalse.
            - unfold RLH_WaitMS_P in *.
              intros.
              tryfalse.
            - unfold RLH_WaitS_Suspend_P in *.
              intros.
              tryfalse.
            - unfold RLH_WaitQ_Suspend_P in *.
              intros.
              tryfalse.
            - splits.
              unfold RLH_WaitMB_Suspend_P in *.
              intros.
              tryfalse.
              unfold RLH_WaitMS_Suspend_P in *.
              intros.
              tryfalse.
          + unfold RHL_TCB_Status_Wait_P in *.
            destruct RHLstwait as (RHLwait & RHLwaitS & RHLwaitQ & 
            RHLwaitMB & RHLwaitMS & RHLwaitSsus & RHLwaitQsus & RHLwaitMBsus & RHLwaitMSsus).
            splits.
            - unfold RHL_Wait_P in *.
              intros.
              tryfalse.
            - unfold RHL_WaitS_P in *.
              intros.
              tryfalse.
            - unfold RHL_WaitQ_P in *.
              intros.
              tryfalse.
            - unfold RHL_WaitMB_P in *.
              intros.
              tryfalse.
            - unfold RHL_WaitMS_P in *.
              intros.
              tryfalse.
            - unfold RHL_WaitS_Suspend_P in *.
              intros.
              tryfalse.
            - unfold RHL_WaitQ_Suspend_P in *.
              intros.
              tryfalse.
            - splits.
              unfold RHL_WaitMB_Suspend_P in *.
              intros.
              tryfalse.
              unfold RHL_WaitMS_Suspend_P in *.
              intros.
              tryfalse.
        }
        (* stat = $ 8 *)
        {
          unfold R_TCB_Status_P.
          splits.
          * unfold RLH_RdyI_P in *.
            intros;splits;eauto.
            destruct Hpdec as [Hpin|Hpnin].
            +
              unfolds in H12;simpljoin.
              inverts H3;inverts H10;inverts H12.
              pose proof (RLHrdy prio0).
              assert (RdyTCBblk
              (next
              :: prev
                  :: eptr
                    :: msg :: V$ 0 :: V$ 8 :: Vint32 prio0 :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
              rtbl prio0). {
                unfolds.
                splits;eauto.
              }
              apply H3 in H6.
              simpljoin.
              tryfalse.
            + unfolds in H12.
              simpljoin.
              inverts H12.
              destruct i.
              - unfold RHL_Suspend_P in RHLsus.
                destruct RHLsus as (RHLsus1 & RHLsus2).
                pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true)));simpljoin.
                inverts H12.
                unfolds in H6.
                simpljoin.
                inverts H6.
                eexists m0.
                auto.
              - 
                unfold RHL_RdyI_P in RHLrdy.
                pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false)));simpljoin.
                unfold RdyTCBblk in H6;simpljoin.
                inverts H6.
                unfold RdyTCBblk in H3;simpljoin.
                inverts H3.
                eexists m0;eauto.
          * unfold RHL_RdyI_P in *.
            intros.
            inverts H3.
            splits;eauto.
            unfolds;splits.
            inverts H12.
            destruct i.
            + unfold RHL_Suspend_P in RHLsus.
              destruct RHLsus as (RHLsus1 & RHLsus2).
              pose proof (RHLsus1 prio0 m (eq_refl (prio0, rdy, m, true))).
              unfold WaitTCBblk in H3;simpljoin;eauto.
            + pose proof (RHLrdy prio0 m (eq_refl (prio0, rdy, m, false))).
              unfold RdyTCBblk in H3;simpljoin;eauto.
            + destruct i.
              2: {
                pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))).
                inverts H12.
                simpljoin.
                tryfalse.
              }
              {
                inverts H12.
                inverts H6.
                - destruct Hpdec.
                  {
                    unfold RLH_RdyI_P in RLHrdy.
                    pose proof (RLHrdy x0).
                    assert (
                      RdyTCBblk
                      (next
                        :: prev
                          :: eptr :: msg :: V$ 0 :: V$ 8 :: Vint32 x0 :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
                      rtbl x0
                    ). {
                      unfolds.
                      splits;eauto.
                    }
                    apply H12 in H13.
                    simpljoin.
                  }
                  {
                    destruct RLHsus as (RLHsus1 & RLHsus2).
                    pose proof (RLHsus1 x0).
                    assert (WaitTCBblk
                    (next
                    :: prev
                        :: eptr
                          :: msg :: V$ 0 :: V$ 8 :: Vint32 x0 :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
                    rtbl x0 Int.zero). {
                      unfolds;splits;eauto.
                    }
                    apply H12 in H13.
                    simpljoin.
                    auto.
                    auto.
                  }
              }
          * unfold RLH_Suspend_P in *.
            splits.
            intros.
            tryfalse.
            intros.
            tryfalse.
          * unfold RHL_Suspend_P in *.
            splits.
            intros.
            tryfalse.
            intros.
            tryfalse.
          * unfold RLH_TCB_Status_Wait_P in *.
            destruct RLHstwait as (RLHwait & RLHwaitS & RLHwaitQ & 
            RLHwaitMB & RLHwaitMS & RLHwaitSsus & RLHwaitQsus & RLHwaitMBsus & RLHwaitMSsus).
            splits.
            {
              unfold RLH_Wait_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
              eapply prio_rtbl_dec';eauto.
            }
            {
              unfold RLH_WaitS_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitQ_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitMB_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitMS_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitS_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitQ_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            split.
            {
              unfold RLH_WaitMB_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitMS_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
          * unfold RHL_TCB_Status_Wait_P in *.
            unfold RHL_Wait_P, RHL_WaitS_P, RHL_WaitQ_P, RHL_WaitMB_P, RHL_WaitMS_P,
            RHL_WaitS_Suspend_P, RHL_WaitQ_Suspend_P, RHL_WaitMB_Suspend_P, RHL_WaitMS_Suspend_P.
            splits;intros;tryfalse.
            splits;intros;tryfalse.
        }
Qed.

(* In OSQPostPure.v *)
Lemma prio_set_rdy_in_tbl:
forall prio0 prio rtbl grp,
  0 <= Int.unsigned prio0 < 64 ->
  0 <= Int.unsigned prio < 64 ->
  prio0 <> prio ->
  nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
  prio_in_tbl prio0 rtbl ->
  prio_in_tbl prio0
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                              (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
introv Fd1 Fd2 Fneq Fnth Fpit.
unfold prio_in_tbl in *.
introv Fx Fy Fnth'.
assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
        ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
destruct H.
assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
        Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
eapply update_nth.
eauto.
subst.
rewrite <- H in Fnth'.
rewrite H0 in Fnth'.
inverts Fnth'.
eapply or_and_combine; eauto.
eapply Fpit; trivial.
rewrite <- H; trivial.
unfolds in H.
eapply prio_bit_and_zero; eauto.
subst.

assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) rtbl = Some (Vint32 z)).
eapply nth_upd_neq.
eapply neq_comm.
eapply H.
eapply Fnth'.
eapply Fpit; auto.
Qed.

(* In OSQPostPure.v *)
Lemma prio_set_rdy_in_tbl_rev:
  forall prio0 prio rtbl grp,
    0 <= Int.unsigned prio0 < 64 ->
    0 <= Int.unsigned prio < 64 ->
    prio0 <> prio ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    prio_in_tbl prio0
                (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
    prio_in_tbl prio0 rtbl.
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
          ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  inverts Fnth'.
  rewrite H in H0.
  rewrite H in Fpit.
  lets Hzz: Fpit H0; eauto.
  rewrite -> Fnth in H2.
  inverts H2.
  eapply or_and_distrib; eauto.
  eapply prio_bit_and_zero; eauto.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) 
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = Some (Vint32 z)). 
  eapply nth_upd_neqrev; eauto.
  rewrite Fy in Fnth'. trivial.
  eapply Fpit; auto.
Qed.

(* In OSQPostPure.v *)
Lemma prio_set_rdy_not_in_tbl:
forall prio0 prio rtbl grp,
  0 <= Int.unsigned prio0 < 64 ->
  0 <= Int.unsigned prio < 64 ->
  prio0 <> prio ->
  nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
  prio_not_in_tbl prio0 rtbl ->
  prio_not_in_tbl prio0
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_not_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
          ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  rewrite H0 in Fnth'.
  inverts Fnth'.
  eapply or_and_combine_zero; eauto.
  eapply Fpit; trivial.
  rewrite <- H; trivial.
  unfolds in H.
  eapply prio_bit_and_zero; eauto.
  subst.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) rtbl = Some (Vint32 z)).
  eapply nth_upd_neq.
  eapply neq_comm.
  eapply H.
  eapply Fnth'.
  eapply Fpit; auto.
Qed.

(* In OSQPostPure.v *)
Lemma prio_set_rdy_not_in_tbl_rev:
forall prio0 prio rtbl grp,
  0 <= Int.unsigned prio0 < 64 ->
  0 <= Int.unsigned prio < 64 ->
  prio0 <> prio ->
  nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
  prio_not_in_tbl prio0
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) ->
  prio_not_in_tbl prio0 rtbl.
Proof.
  introv Fd1 Fd2 Fneq Fnth Fpit.
  unfold prio_in_tbl in *.
  introv Fx Fy Fnth'.
  assert ( ∘(Int.unsigned (Int.shru prio ($ 3))) =  ∘(Int.unsigned (Int.shru prio0 ($ 3))) \/
          ∘(Int.unsigned (Int.shru prio ($ 3))) <>  ∘(Int.unsigned (Int.shru prio0 ($ 3)))) by tauto.
  destruct H.
  assert (nth_val ∘(Int.unsigned  (Int.shru prio ($ 3)))
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = 
          Some (Vint32  (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))).
  eapply update_nth.
  eauto.
  subst.
  rewrite <- H in Fnth'.
  inverts Fnth'.
  rewrite H in H0.
  rewrite H in Fpit.
  lets Hzz: Fpit H0; eauto.
  rewrite -> Fnth in H2.
  inverts H2.
  eapply or_and_distrib_zero; eauto.
  eapply prio_bit_and_zero; eauto.

  assert (nth_val ∘(Int.unsigned  (Int.shru prio0 ($ 3))) 
                  (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                                  (Vint32 (Int.or grp ($ 1<<ᵢ(prio&ᵢ$ 7))))) = Some (Vint32 z)). 
  eapply nth_upd_neqrev; eauto.
  rewrite Fy in Fnth'. trivial.
  eapply Fpit; auto.
Qed.

Lemma RLH_Rdy_prioneq_setrdy_prop_hold:
forall p s prio a rtbl t m grp,
  p <> prio ->
  0 <= Int.unsigned prio < 64 ->
  0 <= Int.unsigned p < 64 ->
  V_OSTCBPrio a = Some (Vint32 p) ->
  nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
  RLH_RdyI_P a rtbl (p, t, m, s)  ->
  RLH_RdyI_P a
            (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                            (Vint32 (Int.or(grp) ($ 1<<ᵢ(prio &ᵢ$ 7))))) (p, t, m, s).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  intros.
  eapply Hrl; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Rdy_prioneq_setrdy_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_RdyI_P a rtbl (p, t, m, sus)  ->
    RHL_RdyI_P a
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                              (Vint32 (Int.or(grp) (($ 1<<ᵢ(prio &ᵢ$ 7)))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  intros.
  lets Hs : Hrl H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_set_rdy_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RLH_Suspend_prioneq_setrdy_prop_hold:
forall p prio a rtbl t m grp sus,
  p <> prio ->
  0 <= Int.unsigned prio < 64 ->
  0 <= Int.unsigned p < 64 ->
  V_OSTCBPrio a = Some (Vint32 p) ->
  nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
  RLH_Suspend_P  a rtbl (p, t, m, sus)  ->
  RLH_Suspend_P  a
            (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
            (Vint32 (Int.or (grp) (($ 1<<ᵢ(prio &ᵢ$ 7)))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  destruct Hrl as (Hrl1 & Hrl2).
  unfolds.
  split.
  intros.
  eapply Hrl1; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  intros.
  eapply Hrl2; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Suspend_prioneq_setrdy_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_Suspend_P a rtbl (p, t, m, sus)  ->
    RHL_Suspend_P a
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
              (Vint32 (Int.or (grp) (($ 1<<ᵢ(prio &ᵢ$ 7)))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  destruct Hrl as (Hrl1 & Hrl2).
  unfolds.
  splits.
  intros.
  lets Hs : Hrl1 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  intros.
  lets Hs : Hrl2 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  inverts Hvp.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RLH_Wait_prioneq_setrdy_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RLH_TCB_Status_Wait_P a rtbl (p, t, m, sus) ->
    RLH_TCB_Status_Wait_P a
                          (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                          (Vint32 (Int.or (grp) (($ 1<<ᵢ(prio &ᵢ$ 7)))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  destruct Hrl as (Hrl1 & Hrl2 & Hrl3 & Hrl4 & Hrl5 & Hrl6 & Hrl7 & Hrl8 & Hrl9).
  splits.
  unfolds in Hrl1.
  unfolds.
  intros.
  eapply Hrl1; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl2.
  unfolds.
  intros.
  eapply Hrl2; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl3.
  unfolds.
  intros.
  eapply Hrl3; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl4.
  unfolds.
  intros.
  eapply Hrl4; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl5.
  unfolds.
  intros.
  eapply Hrl5; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl6.
  unfolds.
  intros.
  eapply Hrl6; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl7.
  unfolds.
  intros.
  eapply Hrl7; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  split.

  unfolds in Hrl8.
  unfolds.
  intros.
  eapply Hrl8; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl9.
  unfolds.
  intros.
  eapply Hrl9; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma RHL_Wait_prioneq_setrdy_prop_hold:
  forall p prio a rtbl t m grp sus,
    p <> prio ->
    0 <= Int.unsigned prio < 64 ->
    0 <= Int.unsigned p < 64 ->
    V_OSTCBPrio a = Some (Vint32 p) ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    RHL_TCB_Status_Wait_P a rtbl (p, t, m, sus) ->
    RHL_TCB_Status_Wait_P a
                          (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                          (Vint32 (Int.or (grp) (($ 1<<ᵢ(prio &ᵢ$ 7)))))) (p, t, m, sus).
Proof.
  introv Hpneq Hr1 Hr2 Hvp  Hnth Hrl.
  unfolds in Hrl.
  unfolds.
  destruct Hrl as (Hrl1 & Hrl2 & Hrl3 & Hrl4 & Hrl5 & Hrl6 & Hrl7 & Hrl8 & Hrl9).
  splits.
  unfolds in Hrl1.
  unfolds.
  intros.
  lets Hex : Hrl1 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl2.
  unfolds.
  intros.
  lets Hex : Hrl2 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl3.
  unfolds.
  intros.
  lets Hex : Hrl3 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl4.
  unfolds.
  intros.
  lets Hex : Hrl4 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl5.
  unfolds.
  intros.
  lets Hex : Hrl5 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl6.
  unfolds.
  intros.
  lets Hex : Hrl6 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl7.
  unfolds.
  intros.
  lets Hex : Hrl7 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl8.
  split.
  unfolds.
  intros.
  lets Hex : Hrl8 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in Hrl9.
  unfolds.
  intros.
  lets Hex : Hrl9 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
Qed.

Lemma update_rtbl_setrdy_tcblist_hold:
  forall vl vptr rtbl tcbls prio grp,
    0<= Int.unsigned prio < 64 ->
    nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl = Some (Vint32 grp) ->
    (forall tid a b c sus , TcbMod.get tcbls tid  = Some (a,b,c,sus) -> a <> prio
    ) ->
    TCBList_P vptr vl rtbl tcbls ->
    TCBList_P vptr vl
              (update_nth_val ∘(Int.unsigned (Int.shru prio ($ 3))) rtbl
                              (Vint32 (Int.or (grp) ($ 1<<ᵢ(prio &ᵢ$ 7))))) tcbls.
Proof.
  inductions vl.
  intros; simpl in *.
  auto.
  intros.
  unfold TCBList_P in *; fold TCBList_P in *.
  simpljoin;try splits.
  exists x x0 x1 x2.
  splits; auto.
  unfolds in H5.
  unfolds.
  destruct x2.
  destruct p.
  destruct p.
  simpljoin;try splits; auto.
  lets Hds : tcbjoin_get_a H4. 
  apply H1 in Hds.
  unfolds in H7.
  unfolds.
  lets Hran : tcbblk_prio_range H8 H5.
  unfolds in H9.
  simpljoin;try splits.
  eapply RLH_Rdy_prioneq_setrdy_prop_hold; eauto.
  eapply  RHL_Rdy_prioneq_setrdy_prop_hold; eauto.
  eapply RLH_Suspend_prioneq_setrdy_prop_hold;eauto.
  eapply RHL_Suspend_prioneq_setrdy_prop_hold;eauto.
  eapply RLH_Wait_prioneq_setrdy_prop_hold; eauto.
  eapply  RHL_Wait_prioneq_setrdy_prop_hold; eauto.
  eauto.
  eapply IHvl; auto.
  intros; eapply H1.  
  eapply tcbjoin_get_get; eauto.
Qed.

Lemma ECBList_P_preserve_resume:
  forall ls x mqls ecbls tcbls prio b st0 m0,
    ECBList_P x Vnull ls mqls ecbls tcbls ->
    (exists sus0, TcbMod.get tcbls (b, Int.zero) = Some (prio, st0, m0, sus0)) -> 
    ECBList_P x Vnull ls mqls ecbls
      (TcbMod.set tcbls (b, Int.zero) (prio, st0, m0, false)).
Proof.
  induction ls.
  * intros. unfolds. unfolds in H. auto.
  * intros. unfold1 ECBList_P. unfold1 ECBList_P in H.
    simpljoin. exists x1. split. auto. split.
    unfolds R_ECB_ETbl_P. destruct H1. destruct H1.
    split. unfold RLH_ECB_ETbl_P in *.
    destruct H as [Q_P [SEM_P [MBOX_P MUTEX_P]]].

    split. {
      unfold RLH_ECB_ETbl_Q_P in *.
      destruct a. intros. lets temp: Q_P prio0 H H4.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H6.
        rewrite H0 in H5. inverts H5.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }
    
    split. {
      unfold RLH_ECB_ETbl_SEM_P in *.
      destruct a. intros. lets temp: SEM_P prio0 H H4.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H6.
        rewrite H0 in H5. inverts H5.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    split. {
      unfold RLH_ECB_ETbl_MBOX_P in *.
      destruct a. intros. lets temp: MBOX_P prio0 H H4.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H6.
        rewrite H0 in H5. inverts H5.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    {
      unfold RLH_ECB_ETbl_MUTEX_P.
      destruct a. intros. lets temp: MUTEX_P prio0 H H4.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H6.
        rewrite H0 in H5. inverts H5.
        rewrite TcbMod.map_get_set. eauto.
      + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    unfold RHL_ECB_ETbl_P in *.
    split. 2: auto.
    destruct H1 as [Q_P [SEM_P [MBOX_P MUTEX_P]]].

    split. {
      unfold RHL_ECB_ETbl_Q_P in *.
      destruct a. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply Q_P. inverts H4.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply Q_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_SEM_P in *.
      destruct a. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply SEM_P. inverts H4.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply SEM_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_MBOX_P in *.
      destruct a. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply MBOX_P. inverts H4.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply MBOX_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    {
      unfold RHL_ECB_ETbl_MUTEX_P in *.
      destruct a. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply MUTEX_P. inverts H4.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply MUTEX_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    destruct mqls. tryfalse.
    destruct a. destruct H2 as [x [mqls' [v' [P1 [P2 [P3]]]]]].
    eexists x. eexists mqls'. eexists v'.
    repeat split; auto.
    apply IHls.
    auto. eauto.
Qed.
Lemma RH_TCBList_ECBList_P_suspend:
  forall ecbls tcb tid prio st msg tid' sus,
    RH_TCBList_ECBList_P ecbls tcb tid' ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcb tid (prio, st, msg, true)) tid'.
Proof.
  intros.
  unfold RH_TCBList_ECBList_P in *. simpljoin. splits.
  * unfold RH_TCBList_ECBList_Q_P in *.
    destruct H. split.
    + intros.
      pose proof (H eid x y qwaitset tid0 H5) as H.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H7. rewrite TcbMod.map_get_set.
        unfold get in H; simpl in H. rewrite H7 in H0.
        rewrite H in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
  * unfold RH_TCBList_ECBList_SEM_P in *.
    destruct H1. split.
    + intros.
      pose proof (H1 eid n wls tid0 H5) as H1.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H7. rewrite TcbMod.map_get_set.
        unfold get in H1; simpl in H1. rewrite H7 in H0.
        rewrite H1 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
  * unfold RH_TCBList_ECBList_MBOX_P in *.
    destruct H2. split.
    + intros.
      pose proof (H2 eid n wls tid0 H5) as H2.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H7. rewrite TcbMod.map_get_set.
        unfold get in H2; simpl in H2. rewrite H7 in H0.
        rewrite H2 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
  * unfold RH_TCBList_ECBList_MUTEX_P in *.
    destruct H3. split.
    + intros.
      pose proof (H3 eid n1 n2 wls tid0 H5) as H3.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H8. rewrite TcbMod.map_get_set.
        unfold get in H3; simpl in H3. rewrite H8 in H0.
        rewrite H3 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + split. intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice. destruct H4.
      - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
        inverts H5. unfold get in H0; simpl in H0.
        rewrite H6 in H0. eauto.
      - eapply H4. rewrite TcbMod.map_get_set' in H5.
        unfold get; simpl. eauto. auto.
    - destruct H4. unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
      intros.
      pose proof (H5 eid pr wls opr tid0 H6) as H5.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice. rewrite H7. rewrite TcbMod.map_get_set.
      eauto. rewrite TcbMod.map_get_set'. eauto. auto.
Qed.

Lemma TaskResumeProof:
    forall  vl p r tid, 
      Some p =
      BuildPreA' os_internal OSTaskResume taskresumeapi vl OSLInv tid init_lg->
      Some r =
      BuildRetA' os_internal OSTaskResume taskresumeapi vl OSLInv tid init_lg->
      exists t d1 d2 s,
        os_api OSTaskResume = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|- tid {{p}}s {{Afalse}}.
Proof.
    init_spec.
    (* If (prio′ ≥ ′OS_LOWEST_PRIO) { *)
    lzh_hoare_if; pure_auto.
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_prio_idle.
    can_change_aop_solver.
    pure_auto.
    right.
    symmetry in HeqH0.
    rewrite Int.eq_sym.
    eauto.
    hoare forward.

    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    unfold AOSTCBList.
    hoare_split_pure_all.
    
    hoare unfold.
    (* ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ *)
    rename v'5 into ptbl.
    rename v'11 into rtbl.
    rename v'13 into ecbls.
    rename v'14 into tcbls.
    rename v'16 into vhold.

    assert (Int.unsigned i < 64)%Z. {
      destruct Hif_false; 
      repeat match goal with
      | H : context [if ?x then _ else _ ] |- _ =>
        let y := fresh in  remember x as y ; destruct y; simpl in H; tryfalse
      end.
      clear - HeqH11.
      unfold OS_LOWEST_PRIO in HeqH11.
      int auto.
    }
    assert (rule_type_val_match OS_TCB ∗
    (nth_val' (Z.to_nat (Int.unsigned i)) ptbl) = true). {
      apply array_type_vallist_match_imp_rule_type_val_match.
      rewrite H9.
      clear - H10; handle_z2n_lt_nat.
      auto.
    }
    clear Hif_false.
    hoare forward.
    pure_auto.
    auto.

    unfold1 tcbdllseg.
    unfold1 dllseg.
    unfold node.
    hoare normal pre.
    hoare_split_pure_all.
    simpljoin.
    inverts H12.
    
    lets bb: OSTCBflag_des H16.
    simpljoin.

    assert (
    exists t sus, TcbMod.get tcbls (v'7, Int.zero) =
      Some (x5, t, x2, sus)
    ). {
      unfold1 TCBList_P in H3.
      simpljoin.
      unfolds in H18.
      destruct x13. destruct p. destruct p.
      simpljoin.
      inverts H20.
      unfolds in H22. simpl in H22.
      inverts H18.
      inverts H3.
      eexists. eexists.
      unfold join,sig,get in *; simpl in *.
      unfold join,sig,get in *; simpl in *.
      go.
    }

    destruct H12 as (st & sus & tcbmod_get).

    (* If (ptcb ′ ==ₑ NULL) *)
    hoare forward.
    destruct (nth_val' (Z.to_nat (Int.unsigned i)) ptbl); auto.
    simpl val_eq.
    destruct a.
    simpl val_inj.
    auto.

    hoare unfold.
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_no_such_tcb.
    can_change_aop_solver.
    {
      intro.
      apply H12.
      destruct H11.
      2: {
        simpljoin.
        rewrite H11.
        simpl.
        destruct x12.
        reflexivity.
      }
      false.
      simpljoin.
      unfolds in H8.
      simpljoin.
      lets bb: H14 H13.
      simpljoin.
      unfold nat_of_Z in H21.
      apply nv'2nv in H11.
      rewrite H11 in H21.
      inverts H21.
      intro; tryfalse.
    }
    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    unfold AOSTCBList.
    sep pauto; eauto.
    sep cancel tcbdllflag.
    unfold tcbdllseg.
    unfold1 dllseg.
    sep pauto.
    sep cancel dllseg.
    sep cancel dllseg.
    unfold node.
    sep pauto.
    sep cancel Astruct.
    unfold AOSTCBPrioTbl.
    sep pauto.
    instantiate (1:=
    LV ptcb @ OS_TCB ∗ |-> nth_val' (Z.to_nat (Int.unsigned i)) ptbl **
      LV prio @ Int8u |-> Vint32 i **
      A_dom_lenv
        ((prio, Int8u)
        :: (ptcb, OS_TCB ∗) :: nil)).
    sep auto.
    pauto.
    go.
    go.
    go.
    go.

    (* RETURN ′OS_TASK_RESUME_PRIO *)
    hoare forward.
    hoare forward.
    hoare_split_pure_all.

    hoare unfold.
    assert (exists p, nth_val' (Z.to_nat (Int.unsigned i)) ptbl = Vptr p). {
      destruct (nth_val' (Z.to_nat (Int.unsigned i)) ptbl); eauto.
      destruct H12. discriminate.
      discriminate.
      destruct H12. discriminate.
      simpl in H11. destruct H11.
      discriminate. discriminate.
    }
    clear H11 H12.
    simpljoin.
    rewrite H11.

    eapply seq_rule. {
      eapply ift_rule''.
      intros.
      eapply symbolic_lemmas.bop_rv.
      sep_get_rv1.
      eapply symbolic_lemmas.addrof_gvar_rv.
      gen_notin_lenv H12 OSPlaceHolder.
      eapply symbolic_lemmas.dom_lenv_imp_notin_lenv.
      eauto.
      sep cancel A_dom_lenv.
      sep cancel Agvarenv'.
      eauto.
      eauto.
      simpl.
      destruct x10. destruct vhold.
      destruct ( Int.eq i0 i1 ); destruct (peq b b0); simpl; intro; tryfalse.
      simpl.
      eauto.
      hoare unfold.
      instantiate (1:=Afalse).
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskres_no_such_tcb.
      go.
      {
        intro.
        apply H12.
        assert (x10 <> vhold \/ x10 = vhold).
        tauto.
        destruct H14.
        simpl.
        destruct x10; destruct vhold.
        remember (peq b b0).
        destruct s.
        subst.
        rewrite Int.eq_false.
        reflexivity.
        intro; tryfalse.
        reflexivity.
        subst x10.
        simpl.
        false.
        simpljoin.
        unfolds in H8.
        simpljoin.
        lets bb: H14 H13.
        simpljoin.
        unfold nat_of_Z in H21.
        apply nv'2nv in H11.
        rewrite H11 in H21.
        inverts H21.
        apply H22; reflexivity.
        intro; tryfalse.
      }
      hoare forward prim.
      unfold AOSTCBPrioTbl.
      unfold AOSTCBList.
      sep pauto.
      sep cancel tcbdllflag.
      unfold tcbdllseg.
      sep cancel 5%nat 1%nat.
      
      unfold1 dllseg.
      unfold node.
      sep pauto.
      sep cancel Astruct.
      sep cancel dllseg.
      sep cancel 2%nat 1%nat .
      sep cancel 2%nat 1%nat.
      eauto.
      go.
      go.
      go.
      go.
      go.
      go.
      go.
      hoare forward.
    }

    hoare forward.
    unfold AOSRdyTblGrp.
    hoare unfold.
    apply valinjbopevallemma in H17.
    (* check whether the tbl exists *)
    
    
    rename v'7 into cur_tcb_blk.
    rename x10 into toresptr.
    assert (exists st0 m sus0, TcbMod.get tcbls toresptr = Some (i, st0, m, sus0)). 
    {
        unfolds in H8.
        simpljoin.
        apply H8.
        splits.
        clear; int auto.
        lia.
        unfold nat_of_Z.
        eapply nv'2nv.
        assumption.
        intro; tryfalse.
        assumption.
    }
    simpljoin.
    rename x into st0.
    rename x0 into m0.
    rename x10 into sus0.
    rename v'8 into l1.
    rename v'10 into l2.
    remember (v'5 :: v'19 :: x1 :: x2 :: x3 :: x4 :: Vint32 x5 :: x6 :: x7 :: x8 :: x9 :: nil) as tcbcur.
    protect Heqtcbcur.
    eapply backward_rule1.
    intros.
    instantiate (1 := (
      [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'6 (l1++tcbcur::l2)|] **
      tcbdllseg v'6 Vnull v'20 Vnull (l1++tcbcur::l2) **
      [|TCBList_P v'6 (l1++tcbcur::l2) rtbl tcbls|] **

      <|| taskresumecode (Vint32 i :: nil) ||>  **
      LV ptcb @ OS_TCB ∗ |-> Vptr toresptr **
      PV vhold @ Int8u |-> v'23 **
      GV OSTCBList @ OS_TCB ∗ |-> v'6 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
      AOSEventFreeList v'0 **
      AOSQFreeList v'1 **
      AOSQFreeBlk v'2 **
      AECBList v'4 v'3 ecbls tcbls **
      AOSMapTbl **
      AOSUnMapTbl **
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      AOSRdyTbl rtbl **
      AOSRdyGrp v'12 **
      G& OSPlaceHolder @ Int8u == vhold **
      AOSIntNesting **
      AOSTCBFreeList v'17 v'18 **
      (* AOSRdyTblGrp rtbl v'12 ** *)
      AOSTime (Vint32 v'15) **
      HECBList ecbls **
      HTCBList tcbls **
      HTime v'15 **
      HCurTCB (cur_tcb_blk, Int.zero) **
      AGVars **
      A_isr_is_prop **
      tcbdllflag v'6
        (l1 ++ tcbcur :: l2) **
      p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
      Aisr empisr **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      atoy_inv' **
      LV prio @ Int8u |-> Vint32 i **
      A_dom_lenv
        ((prio, Int8u)
            :: (ptcb, OS_TCB ∗) :: nil)    
    )).
    eapply tcbdllseg_combine.
    unfold tcbdllseg.
    unfold1 dllseg.
    unfold node.
    (* unfold AOSRdyTblGrp. *)
    sep pauto.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 2%nat.
    sep cancel 1%nat 1%nat.
    sep pauto.
    go.
    go.
    go.
    unprotect Heqtcbcur; rewrite Heqtcbcur; eauto.
    unprotect Heqtcbcur; rewrite Heqtcbcur; eauto.

    hoare_split_pure_all.
    assert (ptr_in_tcbdllseg (Vptr toresptr) v'6 (l1++tcbcur ::l2)).
    eapply tcbget_ptr_in_tcblist.
    eauto.
    eauto.

    eapply backward_rule1.
    intros.
    eapply tcbdllseg_split' in H20.
    eauto.
    exact H21.
    eauto.
    clear Heqtcbcur.
    remember (l1  ++ tcbcur :: l2) as tcblst.
    protect Heqtcblst.
    hoare unfold.

    (* Remove the original splitting *)
    clear dependent v'21.
    clear dependent v'22.

    destruct v'8.
    {
      unfold tcbdllseg.
      simpl.
      hoare unfold.
      inverts H0.
    }

    unfold tcbdllseg.
    unfold1 dllseg.
    unfold node.
    hoare_split_pure_all.
    simpljoin.
    inverts H0.
    rename v'14 into toresblock.
    hoare unfold.
    lets backup : H25.
    unfold1 TCBList_P in H25.
    simpljoin.
    unfold TCBNode_P in H47.
    destruct x11; destruct p; destruct p.
    simpljoin.
    unfold RL_TCBblk_P in H50.
    simpljoin.
    inverts H50; inverts H52; inverts H53; inverts H54;
    inverts H55; inverts H56; inverts H63.
    (* If ((ptcb ′ → OSTCBStat &ₑ ′ OS_STAT_SUSPEND) !=ₑ ′ OS_STAT_RDY) *)
    hoare forward.
    go.
    (* in taskdelete.v *)
    Local Ltac sifs := 
      match goal with
        | |- context[if ?e then _ else _] => destruct e; sifs
        | |- _ <> _ => try solve [simpl; intro; tryfalse]
        | _ => idtac
      end.
    sifs.
    sifs.
    {
      hoare unfold.
      hoare forward.
      go.
      (* If (ptcb ′ → OSTCBStat ==ₑ ′ OS_STAT_RDY) *)
      hoare forward.
      go.
      sifs.
      hoare unfold.
      {
        (* If (ptcb ′ → OSTCBDly ==ₑ ′ 0) *)
        hoare unfold.
        hoare forward.
        go.
        sifs.
        change ((OSRdyGrp ′ =ₑ OSRdyGrp ′ |ₑ ptcb ′ → OSTCBBitY;ₛ
        OSRdyTbl ′ [ptcb ′ → OSTCBY] =ₑ OSRdyTbl ′ [ptcb ′ → OSTCBY] |ₑ ptcb ′ → OSTCBBitX)) with (
          inline_call inline_bittbl_setbit
          ((OSRdyGrp ′) :: (OSRdyTbl ′) :: (ptcb ′ → OSTCBBitX) ::
          (ptcb ′ → OSTCBBitY) :: (ptcb ′ → OSTCBY) :: nil)).
        unfold GAarray.  
        unfold AOSRdyGrp.
        unfold Agvarmapsto at 3.
        unfold AOSRdyTbl.
        unfold GAarray.  
        hoare unfold.
        eapply seq_rule.
        Ltac inline_forward :=
          match goal with
            | |- {| _ , _ , _, _, _, _|} |- _ {{ _ }} inline_call ?inline_record _ {{ _ }} => eapply backward_rule2; [eapply (inl_proof inline_record)  | intro;intros;inline_pre_unfolder inline_record |idtac..]
          end.
        inline_forward.
        2:{
          sep pauto.
          sep cancel Aop.
          sep cancel (2%nat) (1%nat).
          sep cancel (3%nat) (1%nat).
          eauto.
      
          instantiate (1 := p).
          lia.
          go.
          math simpls.
          go.
          go.
          clear - H65.
          mauto.
      
          2: go.
      
          intros.
          lrv_solver.
          go.
          go.
          go.
        }
        {
          intros.
          linv_solver.
        }
        inline_post_unfolder inline_bittbl_setbit.
        hoare unfold.
        rename H61 into Hlogic_var.
        inverts Hlogic_var.
        eapply backward_rule1.
        intros.
        sep lift 2%nat in H61.
        sep lift 5%nat in H61.
        eapply GrefArray in H61.
        sep lift 3%nat in H61.
        sep lift 4%nat in H61.
        apply GrefPV in H61.      
        sep lift 5%nat in H61.
        sep lift 5%nat in H61.
        eapply GrefArray in H61.
        eauto.
        hoare unfold.
        remember (
          Vint32 p
          :: Vint32 (p&ᵢ$ 7)
              :: Vint32 (p >>ᵢ $ 3)
                  :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7))
                    :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) as resblk.
        rename v'7 into l1'.
        rename v'8 into l2'.
        rename v'24 into rtbl.

        assert (array_type_vallist_match Int8u (update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) rtbl
        (val_inj (or (Vint32 v'35) (Vint32 ($ 1<<ᵢ(p&ᵢ$ 7))))))) as typematch'. {
          lets Hprange : prio_prop H57 H65.
          rewrite Int.repr_unsigned in Hprange.
          rewrite <- H66.
          eapply array_type_vallist_match_int8u_update_hold';eauto.
          lia.
          clear -H65.
          mauto.
        }

        remember (update_nth_val (Z.to_nat (Int.unsigned (p >>ᵢ $ 3))) rtbl
        (val_inj (or (Vint32 v'35) (Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)))))) as rtbl'.
        protect Heqrtbl'.

        (* assert (rule_type_val_match Int8u (Vint32 v'34) = true). *)

        remember (TcbMod.set tcbls (toresblock,Int.zero) (i, st0 , m0, false)) as tcbls'.
        protect Heqtcbls'.

        assert ((p, t, m, s)=(i, st0, m0, sus0))as abstcbeq. {
          clear - H13 H23 H25.
          assert(TcbMod.get v'11 (toresblock, Int.zero) = Some (p, t, m, s)). {
            unfolds in H25.
            unfold join, sig in H25.
            simpl in H25.
            apply TcbMod.join_sig_get in H25;eauto.
          }
          assert (TcbMod.get tcbls (toresblock, Int.zero) = Some (p, t, m, s)). {
            eapply TcbMod.join_get_get_r;eauto.
          }
          rewrite H0 in H13.
          inverts H13.
          reflexivity.
        }

        assert (prio_neq_cur tcbls (toresblock, Int.zero) p) as Hprio. {
          eapply R_PrioTbl_P_impl_prio_neq_cur.
          auto. eauto.
          inverts abstcbeq. eauto.
        }

        assert (prio_neq_cur v'11 (toresblock, Int.zero) p) as Hprio1. {
          unfolds. unfolds in Hprio.
          intros. eapply Hprio; eauto.
          clear - H67 H25.
          eapply TcbMod.join_get_r; eauto. 
        }

        assert (prio_neq_cur v'10 (toresblock, Int.zero) p) as Hprio2. {
          unfolds. unfolds in Hprio.
          intros. eapply Hprio; eauto.
          clear - H67 H25.
          eapply TcbMod.join_get_l; eauto.
        }
        
        assert (TCBList_P (Vptr (toresblock, Int.zero))
        ((x0 :: v'9 :: x23 :: m :: Vint32 i13 :: Vint32 (x22 &ᵢ Int.not ($ OS_STAT_SUSPEND)) :: resblk) :: l2') rtbl'
            (TcbMod.set v'11 (toresblock, Int.zero) (i, st0, m0, false))).
        {
          unfold1 TCBList_P.
          do 4 eexists. splits. auto.
          unfolds. simpl. eauto.
          eapply tcbjoin_set. eauto.
          rewrite Heqresblk.
          unfolds.
          unfold1 TCBList_P in backup.
          (* unfold1 TCBList_P in H20. *)
          simpljoin.
          unfolds in H74. destruct x13. destruct p. destruct p.
          destruct H74 as (Holdmsg & Holdprio & HoldblkP & HoldtcbP).
          splits; auto.
          apply RL_TCBblk_P_resume; auto.
          remember (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) as resstat.
          inverts Holdmsg;inverts Holdprio.
          lets HoldtcbBackup : HoldtcbP.
          unfold R_TCB_Status_P in HoldtcbP.
          destruct HoldtcbP as (_ & HRHLrdy & _).
          unfold RHL_RdyI_P in HRHLrdy;unfold V_OSTCBStat,V_OSTCBDly in HRHLrdy;simpl in HRHLrdy.
          
          apply val_inj_iftrue_impl_eqtrue in H2.
          apply int_eq_true_impl_eq in H2.
          apply val_inj_iftrue_impl_eqtrue in H55.
          apply int_eq_true_impl_eq in H55 as Hdly0.
          apply eq_sym in Heqresstat.
          rewrite <- Heqresstat.
          rewrite H2 in Heqresstat.
          apply stat_resume_rdy_imp_rdy in Heqresstat.
          2: auto.
          assert (Int.eq x22 ($ OS_STAT_RDY) = true \/ Int.eq x22 ($ OS_STAT_SUSPEND) = true). {
            unfold OS_STAT_RDY;unfold OS_STAT_SUSPEND.
            destruct Heqresstat.
            left;rewrite H74;eapply eq_refl.
            right;rewrite H74;eapply eq_refl.
          }
          lets Hprerdy : low_stat_rdy_or_sus_imp_high_rdy H49 H56 HoldblkP H51 H74.
          eapply Hprerdy in H55.
          inverts H55.
          clear H76 Hprerdy.
          rewrite Hdly0;rewrite Hdly0 in H51.
          assert (0 <= Int.unsigned p < 64)as Hprange by auto.
          rename H49 into typematch.
          assert (prio_in_tbl p rtbl'). {
            rewrite Heqrtbl'.
            eapply prio_in_tbl_orself.
          }
          lets Hpdec : prio_rtbl_dec Hprange typematch H56.
          eapply R_TCB_Status_P_resume;eauto.
          rewrite Heqrtbl'.
          inverts abstcbeq.
          eapply update_rtbl_setrdy_tcblist_hold; eauto.
          apply nv'2nv; auto.
          unfolds in Hprio1.
          intros.
          lets Has : tcbjoin_get_getneq H25 H61.
          destruct Has.
          eapply Hprio1; eauto.
        }

        assert (TCBList_P v'6 l1' rtbl' v'10). {
          rewrite Heqrtbl'.
          apply update_rtbl_setrdy_tcblist_hold; eauto.
          apply nv'2nv; auto.
          intros.
          unfolds in Hprio2.
          eapply Hprio2. 2: apply H67.
          eapply tcbjoin_join_get_neq; eauto.
        }  

        assert (TcbMod.join v'10 (TcbMod.set v'11 (toresblock, Int.zero) (i, st0, m0, false))
          tcbls'). {
          unprotect Heqtcbls'.
          rewrite Heqtcbls'.
          eapply TcbMod.join_set_r. auto.
          clear - H25.
          unfold TcbMod.indom. eexists.
          unfolds in H25.
          unfold join, sig in H25; simpl in H25.
          apply TcbMod.join_sig_get in H25. eauto.
        }
        
        (* Recombine the tcbdllseg *)
        eapply backward_rule1.
        intros.
        instantiate (1 := (
          [|ptr_in_tcbdllseg (Vptr (toresblock, Int.zero)) v'6 
          (l1' ++ (x0 :: v'9 :: x23 :: m :: Vint32 i13 ::
           Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) :: resblk)::l2')|] 
           **
          tcbdllseg v'6 Vnull v'20 Vnull 
          (l1' ++ (x0 :: v'9 :: x23 :: m :: Vint32 i13 ::
           Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) :: resblk)::l2')
          **
          [|TCBList_P v'6 
          (l1' ++ (x0 :: v'9 :: x23 :: m :: Vint32 i13 ::
           Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) :: resblk)::l2')
          rtbl' tcbls'|] 
          **
          <|| taskresumecode (Vint32 i :: nil) ||>  **
          LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) **
          GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
          GV OSRdyGrp @ Int8u |-> Vint32 v'34 **
          GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) rtbl'
          **
          PV vhold @ Int8u |-> v'23
          **
          GV OSTCBList @ OS_TCB ∗ |-> v'6 **
          GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
          AOSEventFreeList v'0 **
          AOSQFreeList v'1 **
          AOSQFreeBlk v'2 **
          AECBList v'4 v'3 ecbls tcbls' **
          AOSMapTbl **
          AOSUnMapTbl **
          G& OSPlaceHolder @ Int8u == vhold **
          AOSIntNesting **
          AOSTCBFreeList v'17 v'18 **
          AOSTime (Vint32 v'15) **
          HECBList ecbls **
          HTCBList tcbls **
          HTime v'15 **
          HCurTCB (cur_tcb_blk, Int.zero) **
          AGVars **
          A_isr_is_prop **
          tcbdllflag v'6 (l1' ++ (x0 :: v'9 :: x23 :: m :: Vint32 i13 :: Vint32 x22 :: resblk) :: l2') **
          p_local OSLInv (cur_tcb_blk, Int.zero) init_lg **
          Aisr empisr **
          Aie false **
          Ais nil **
          Acs (true :: nil) **
          atoy_inv' **
          (* LV x @ OS_TCB ∗ |-> v' **
          LV pevent @ OS_EVENT ∗ |-> v'
           ** *)
          LV prio @ Int8u |-> Vint32 i
           **
          A_dom_lenv
            ((prio, Int8u)
             :: (ptcb, OS_TCB ∗) :: nil)  
            )).

        eapply tcbdllseg_combine.
        sep pauto.
        sep cancel tcbdllflag.
        sep cancel Aop.
        unfold tcbdllseg.
        unfold1 dllseg.
        unfold node.
        sep pauto.
        sep cancel Astruct.
        sep cancel dllseg.
        sep cancel dllseg.
        unfold AECBList.
        unfold AECBList in H74.
        sep pauto.
        {
          unprotect Heqtcbls'. rewrite Heqtcbls'.
          apply ECBList_P_preserve_resume; eauto.
        }
        auto.
        auto.

        Open Scope Z_scope.
        Open Scope int_scope.
        assert ((Int.unsigned (x22&ᵢInt.not ($ OS_STAT_SUSPEND))) <= 255). {
          apply not_and_p'.
          auto. unfold OS_STAT_SUSPEND; clear; int auto.
        }
        go.
      
        eauto.
        eauto.
        auto. 

        protect Heqresblk.
        hoare unfold.

        (* tcbcur is still in the new array *)
        assert (ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'6
        (l1' ++
         (x0 :: v'9 :: x23 :: m0 :: Vint32 i13 :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
          :: resblk) :: l2')).
        eapply ptr_in_tcbdllseg_preserve.
        apply H14.
        unfolds; simpl; auto.
        
        eapply backward_rule1.
        intros.
        eapply tcbdllseg_split' in H77.
        eauto.
        eauto.
        instantiate (1 := tcbls').
        instantiate (1 := rtbl').
        assumption.

        hoare unfold.
        destruct v'8.
        {
          unfold tcbdllseg.
          simpl.
          hoare unfold.
          inverts H81.
        }
        (* Fix abstract operation *)
        hoare abscsq.
        apply noabs_oslinv.
        eapply abs_imp_taskres_succ.
        go.
        eauto.

        (* EXIT_CRITICAL;ₛ *)
        hoare forward prim.

        unfold AOSTCBPrioTbl.
        sep pauto.
        unfold AOSTCBList.
        sep pauto.
        sep cancel tcbdllseg.
        sep cancel tcbdllseg.
        sep cancel (4%nat) (1%nat).
        sep cancel (5%nat) (2%nat).
        unfold AOSRdyTblGrp.
        sep pauto.
        unfold AOSRdyTbl.
        unfold AOSRdyGrp.
        (* instantiate (2:=nth_val' (Z.to_nat (Int.unsigned (i >>ᵢ $ 3))) rtbl). *)
        sep pauto.
        unfold AECBList.
        unfold AECBList in H81.
        sep pauto.
        sep cancel evsllseg.

        instantiate (1 := 
          LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) **
                LV prio @ Int8u |-> Vint32 i **
                A_dom_lenv
                  ((prio, Int8u) :: (ptcb, OS_TCB ∗) :: nil)).
          sep pauto.
          {
            eapply tcbdllflag_hold.
            2: eauto.
            rewrite <- H77. rewrite Heqresblk.
            apply eq_dllflag_set.
            unfold V_OSTCBNext; simpl; auto.
            unfold V_OSTCBflag; simpl; auto.
          }

          {
            unprotect Heqtcbls'.
            rewrite Heqtcbls' in H82.
            auto.
          }
          Set Nested Proofs Allowed.
          Lemma rule_type_val_match_int8_intro :
            forall i,
              Int.unsigned i <= 255 -> rule_type_val_match Int8u (Vint32 i) = true.
          Proof.
            intros.
            simpl.
            unfold Byte.max_unsigned; simpl.
            apply Z.leb_le in H.
            rewrite H; auto.
          Qed.
          Lemma rl_tbl_grp_p_set_hold':
  forall v'12 v'38 v'37 v'57 v'69 v'39 v'36 v'13 v'58 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 =  ∘OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
    RL_Tbl_Grp_P  (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                  (val_inj
                                     (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
                  (Vint32 (Int.or v'57 v'41)).
      Proof.
        intros.
        unfold Int.zero in *.
        unfolds in H16.
        unfolds in H17.
        unfolds.
        intros.
        inverts H20.
        assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
        tauto.
        destruct Hdisj.
        subst n.
        apply nth_upd_eq in H19.
        unfolds in H19.
        remember (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40)) as vo.
        destruct vo; tryfalse.
        subst v0.
        assert ((Z.to_nat (Int.unsigned v'38)) < length v'37)%nat.
        rewrite H4.
        simpl.
        clear -H6.
        mauto.
        lets Hrs : array_int8u_nth_lt_len H19 ; eauto.
        destruct Hrs as (i & Hnth & Hr).
        rewrite Hnth in Heqvo.
        simpl in Heqvo.
        inverts Heqvo.
        assert (Int.unsigned v'38 < 8) as Ha by lia.
        assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
        clear - Ha.
        mauto.
        rewrite H20 in *.
        clear H20.
        split.
        split.
        intros.
        rewrite Int.and_commut in H20.
        rewrite  Int.and_or_distrib in H20.
        apply int_or_zero_split in H20.
        lets Hneq : math_nth_8_neq_zero  Ha H14.
        destruct H20.
        tryfalse.
        intros.
        apply int_or_zero_split in H20.
        destruct H20. subst.
        lets Hnz : math_nth_8_neq_zero' H12.
        lia.
        tryfalse.
        splits.
        assert (Int.unsigned v'40 <= Int.unsigned (Int.or i v'40)) .
        rewrite Int.or_commut.
        apply Int.or_le.
        lets Hgs : math_nth_8_gt_zero  H10 H12.
        assert (0 < Int.unsigned (Int.or i v'40)) by lia.
        intros.
        unfolds.
        rewrite zlt_true; auto.
        intros.
        rewrite Int.and_commut.
        rewrite Int.and_or_distrib.
        lets Has :   math_nth_8_eq_shl Ha H14.
        rewrite Has.
        rewrite Int.or_commut.
        rewrite Int.or_and_absorb.
        auto.
        apply nth_upd_neq in H19.
        assert ( Vint32 v'57 = Vint32 v'57) by auto.
        lets Hrs : H17 H18 H19 H21.
        destruct Hrs.
        splits.
        split;intros.
        apply H22.
        rewrite Int.and_commut in H24.
        rewrite Int.and_or_distrib in H24.
        apply int_or_zero_split in H24.
        destruct H24.
        rewrite Int.and_commut; auto.
        apply H22 in H24.
        rewrite Int.and_commut.
        rewrite Int.and_or_distrib .
        rewrite Int.and_commut in H24.
        rewrite H24.
        rewrite Int.and_commut.
        assert ($ 0 = Int.zero) by auto.
        rewrite H25.
        rewrite Int.or_commut.
        rewrite Int.or_zero.
        lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
        intros.
        split; intros.
        apply H23.
        lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
        rewrite Int.and_commut in H24.
        rewrite Int.and_or_distrib in H24.
        rewrite Int.and_commut in Hbc.
        rewrite Hbc in H24.
        rewrite Int.or_zero in H24.
        rewrite Int.and_commut.
        auto.
        apply H23 in H24.
        lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
        rewrite Int.and_commut .
        rewrite Int.and_or_distrib.
        rewrite Int.and_commut in Hbc.
        rewrite Hbc .
        rewrite Int.or_zero.
        rewrite Int.and_commut.
        auto.
        auto.
      Qed.
Lemma array_type_vallist_match_vptr_update_nth_val :
  forall l n t a,
         array_type_vallist_match (Tptr t ) l -> (n < (length l))%nat ->
        (* (Int.unsigned x) <= Byte.max_unsigned -> *)
         array_type_vallist_match (Tptr t) (update_nth_val n l (Vptr a)).
Proof.
  inductions l; intros.
  simpl; auto.

  destruct n.
  simpl.
  simpl in H; simpljoin.
  auto.

  simpl in H.
  simpl.
  simpljoin; split.
  auto.
  simpl in H0.
  assert(n < length l)%nat by lia.
  eapply IHl; eauto.
Qed.
Lemma mund_int_a2:
  forall i,
    Int.unsigned i <= 255 ->
    (if Int.unsigned i <=? Byte.max_unsigned then true else false) = true.
  intros.
  apply leb_bytemax_true_intro in H.
  rewrite H.
  auto.
Qed.

        assert ( (Z.to_nat (Int.unsigned  (i>>ᵢ$ 3) )) <  length rtbl )%nat.
        {
          rewrite H56.
          clear -H65.
          mauto.
        }
        lets fff: array_int8u_nth_lt_len H49 H83.
        simpljoin.
        eapply rule_type_val_match_int8_intro.
        unfold RL_Tbl_Grp_P in  H70.
        pose proof (H70 )
        unprotect Heqrtbl'.
        rewrite Heqrtbl' in typematch'.
        eapply array_type_vallist_match_vptr_update_nth_val.
          eapply rl_tbl_grp_p_set_hold' in H70;eauto.
          rewrite  in  H70.
          eapply rule_type_val_match_int8_intro.
          eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
          split.
          auto.
          apply H57; auto.
          rewrite Int.eq_sym. assumption.
          eauto.
          eauto.
      }
    }
Qed.