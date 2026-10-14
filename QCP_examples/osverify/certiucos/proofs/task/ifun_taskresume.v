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
Require Import abs_op.
Require Import init_spec.

Require Export include_frm.

Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import sep_cancel_ext.
Require Import sep_combine_lemmas.
Require Import sep_combine.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Require Import evauxvar_lemmas.
Require Import ifun_taskres_spec.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.

Set Nested Proofs Allowed.

(* 
Definition OSTaskResume_impl := 
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
    If (ptcb′ ==ₑ PlaceHolder){
      EXIT_CRITICAL;ₛ
      RETURN ′OS_TASK_RESUME_PRIO
    };ₛ
    If ((ptcb′→OSTCBStat &ₑ ′OS_STAT_SUSPEND) ==ₑ ′OS_STAT_RDY){
      EXIT_CRITICAL;ₛ
      RETURN ′OS_TASK_NOT_SUSPENDED
    };ₛ      

    If(ptcb′→OSTCBStat &ₑ (∼′OS_STAT_SUSPEND) !=ₑ ′OS_STAT_RDY &&ₑ ptcb′→OSTCBDly <>ₑ ′ 0){
      ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼′OS_STAT_SUSPEND);ₛ
      EXIT_CRITICAL;ₛ
      RETURN ′OS_NO_ERR
    };ₛ        
    If(ptcb′→OSTCBStat &ₑ (∼′OS_STAT_SUSPEND) ==ₑ ′OS_STAT_RDY &&ₑ ptcb′→OSTCBDly ==ₑ ′ 0){
      ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼′OS_STAT_SUSPEND);ₛ
      inline_call inline_bittbl_setbit ((OSRdyGrp′):: (OSRdyTbl′)::(ptcb′→OSTCBBitX)::(ptcb′→OSTCBBitY)::(ptcb′→OSTCBY)::nil);ₛ
      (* OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ *)
      (* OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX *)

      EXIT_CRITICAL;ₛ
      OS_Sched(­);ₛ
      RETURN ′OS_NO_ERR
    };ₛ
    EXIT_CRITICAL;ₛ
    RETURN ′OS_NO_ERR
}·.
*)


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

Lemma Some_Vint32_invert:
  forall a b, Some (Vint32 a) = Some (Vint32 b) -> a = b.
Proof.
  intros. invert H. auto.
Qed.

Lemma eq_dllflag_set:
  forall l1 l2 x x',
    V_OSTCBNext x = V_OSTCBNext x' ->
    V_OSTCBflag x = V_OSTCBflag x' ->
    eq_dllflag (l1 ++ x :: l2) (l1 ++ x' :: l2).
Proof.
  intros. induction l1.
  simpl. splits; auto. apply eq_dllflag_refl.
  simpl. splits; auto.
Qed.

Lemma tcbllsegevaux_hold: 
  forall (l1 : list vallist) (P : asrt) (head : val) (l2 : list vallist) locmp ptrmp,
    eq_dllflag l1 l2 ->
    tcbllsegevaux head l1  locmp ptrmp ** P ==> tcbllsegevaux head l2 locmp ptrmp ** P.
Proof.
  induction l1.
  - 
    introv Heqnil.
    simpl in Heqnil.
    destruct l2.
    + intros; auto.
    + false.
  -
    introv Heqdf.
    simpl in Heqdf.
    destruct l2.
    +
      false.
    +
      destruct Heqdf as (Heqn & Heqf & Heqdf).
      introv Haux1.
      unfold tcbllsegevaux in *.
      unfold llsegevaux in Haux1; fold llsegevaux in Haux1.
      unfold llsegevaux; fold llsegevaux.
      sep normal in Haux1.
      sep destruct Haux1.
      sep split in Haux1.
      sep normal.
      sep eexists. 
      sep cancel evaux_node.
      sep split; eauto.
      congruence. 
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

(*
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
*)

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
      rtbl (p, t, m, sus) -> Int.eq st ($ OS_STAT_SUSPEND) = true ->
    Int.eq e ($ 0) = true ->
    t = rdy .
    Proof.

      introv Hz Hlen  Ht  Hr Heq Heqq.
      protect Heq.

      funfold Ht.
      unfolds in Hr.
      destruct Hr as (RLH_rdy & RHL_rdy & RLH_sus & RHL_sus & RLH_wait & RHL_wait).
  
       unfolds in RLH_sus.
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
        rewrite Heq in H3.
        subst.
  
        destruct Hdis as [Hd1 | Hd2].
        assert (Some (Vint32 x) = Some (Vint32 x) /\
                prio_in_tbl x rtbl). 
        split;eauto.
        eapply RLH_rdy in H3.
        destruct H3.
        rename H3 into Had.
        destruct H4 as [H3 | H3].

        destruct H3.
        rename H4 into Hzd.

        destruct Hzd as (m0 & H4).
        (* eapply H3 in H9. *)
        inverts H4; auto.

        destruct H3.
        destruct H3.
        unfold V_OSTCBStat in H3; simpl in H3.
        invert H3.

        destruct H3.
        destruct H3.
        unfold V_OSTCBStat in H3; simpl in H3.
        invert H3.

        destruct H3.
        destruct H3.
        unfold V_OSTCBStat in H3; simpl in H3.
        invert H3.    
        
        destruct H3.
        unfold V_OSTCBStat in H3; simpl in H3.
        invert H3.  

        apply int_eq_true_impl_eq in Heqq.
        assert (Some (Vint32 e) = Some (Vint32 Int.zero)). {
          rewrite Heqq.
          eauto.
        }
        assert (Some (Vint32 x) = Some (Vint32 x) /\
                prio_not_in_tbl x  rtbl/\Some (Vint32 e) = Some (Vint32 Int.zero)).   
        splits; auto.
        eapply H in H4;auto.
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
      simpljoin. inverts H; inverts H0; inverts H1; inverts H2;
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
      unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q, OS_STAT_POSTQ, OS_STAT_PORT,
      OS_STAT_MBOX, OS_STAT_MUTEX in *.
      destruct H10. rewrite H; auto.
      destruct H. rewrite H; auto.
      destruct H. rewrite H; do 2 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 3 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 4 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 5 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 6 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 7 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 2 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 3 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 6 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 4 apply or_intror; apply or_introl; reflexivity.
      destruct H. rewrite H; do 5 apply or_intror; apply or_introl; reflexivity.
      rewrite H. do 7 apply or_intror. apply or_introl. reflexivity.
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
    stat = $ OS_STAT_SUSPEND ->
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
        rename H into HH.
        rename H0 into HH0.
        rename H1 into HH1.
        rename H5 into HH5.
        lets H: H2.
        lets H0: H2.
        lets H1: H2.
        lets H5: H2.
        lets HTCB_P_Backup : H3.
        unfold R_TCB_Status_P in H3.
        assert (stat &ᵢInt.not ($ OS_STAT_SUSPEND) = $0) as Heqstat'. {
          rewrite H6;eauto.
        }
        destruct H3 as [RLHrdy [RHLrdy [RLHsus [RHLsus [RLHstwait RHLstwait]]]]].
        destruct RLtcbblk;simpljoin.


        rewrite Heqstat'.
        lets H6: H2.


        (* stat = $ 8 *)
        
          unfold R_TCB_Status_P.
          splits.
          * unfold RLH_RdyI_P in *.
            intros;splits;eauto.
            destruct Hpdec as [Hpin|Hpnin].
            +
              unfolds in H12;simpljoin.
              clear H6.
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

              destruct H6.
              destruct H10.
              unfold V_OSTCBStat in H10; simpl in H10.
              destruct H10.
              tryfalse.

              destruct H10.
              unfold V_OSTCBStat in H10; simpl in H10.
              destruct H10.
              tryfalse.

              destruct H10.
              unfold V_OSTCBStat in H10; simpl in H10.
              destruct H10.
              tryfalse.

              destruct H10.
              unfold V_OSTCBStat in H10; simpl in H10.
              destruct H10.
              tryfalse.  

              destruct H10.
              unfold V_OSTCBStat in H10; simpl in H10.
              tryfalse.  

            + unfolds in H12.
              simpljoin.
              clear H6.
              inverts H12.
              left.
              splits; auto.
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


                - destruct Hpdec.
                  clear H6.
                  rename H3 into H6.
                  lets H3: H2.
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
                    destruct H13.
                    destruct H14.

                    destruct H14.
                    unfold V_OSTCBStat in H14; simpl in H14.
                    tryfalse.

                    destruct H14.
                    destruct H14.
                    unfold V_OSTCBStat in H14; simpl in H14.
                    tryfalse.   
                    
                    destruct H14.
                    destruct H14.
                    unfold V_OSTCBStat in H14; simpl in H14.
                    tryfalse. 

                    destruct H14.
                    destruct H14.
                    unfold V_OSTCBStat in H14; simpl in H14.
                    tryfalse. 

                    destruct H14.
                    unfold V_OSTCBStat in H14; simpl in H14.
                    tryfalse. 
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
  Optimize Proof.
  Optimize Heap.
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
            destruct RLHstwait as (RLHwait & RLHwaitS & RLHwaitSTo & RLHwaitQ & RLHwaitQTo &
            RLHwaitMB & RLHwaitMBTo & RLHwaitMS & RLHwaitMSTo & RLHWaitPostQ & RLHwaitSsus & RLHwaitQsus & RLHwaitPostQsus & RLHwaitMBsus & RLHwaitMSsus & RLHWaitPort & RLHWaitPortTo & RLHWaitPortsus).

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
              unfold RLH_WaitS_TO_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
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
              unfold RLH_WaitQ_TO_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
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
              unfold RLH_WaitMB_TO_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
              false.
            }
            splits.
            {
              unfold RLH_WaitMS_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitMS_TO_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
              false.
            }
            {
              unfold RLH_WaitPostQ_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
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
            {
              unfold RLH_WaitPostQ_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitMB_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            splits.
            {
              unfold RLH_WaitMS_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }
            {
              unfold RLH_WaitPort_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
              false.
            }
            {
              unfold RLH_WaitPort_TO_P in *.
              intros.
              unfold V_OSTCBStat in H13; simpl in H13.
              false.
            }
            {
              unfold RLH_WaitPort_Suspend_P in *.
              intros.
              unfold WaitTCBblk in H12;simpljoin.
              inverts H3;inverts H12.
              false.
            }

          * unfold RHL_TCB_Status_Wait_P in *.
            unfold RHL_Wait_P, RHL_WaitS_P, RHL_WaitQ_P, RHL_WaitMB_P, RHL_WaitMS_P, RHL_WaitPostQ_P,
            RHL_WaitS_Suspend_P, RHL_WaitQ_Suspend_P, RHL_WaitPostQ_Suspend_P, RHL_WaitMB_Suspend_P, RHL_WaitMS_Suspend_P, RHL_WaitPort_P, RHL_WaitPort_Suspend_P.
            splits;intros;tryfalse.
            splits;intros;tryfalse.        
Qed.




Lemma R_TCB_Status_P_resume':
  forall rtbl x y bitx bity prio next prev eptr msg dly stat p t0 m0 i time, 
  0 <= Int.unsigned prio < 64 ->
  length rtbl = ∘OS_RDY_TBL_SIZE ->
  array_type_vallist_match Int8u rtbl ->   
  ((
    stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
    stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
    stat = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
    stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/ 
    stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)  \/ 
    stat = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND)
    ) \/
  (stat = $ OS_STAT_SUSPEND /\
    (V_OSTCBDly
    (next :: prev :: eptr :: msg :: dly :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) = Some (Vint32 time) /\
    Int.ltu Int.zero time = true))) ->
    RL_TCBblk_P
    (next :: prev :: eptr :: msg :: dly :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) ->
    R_TCB_Status_P
    (next :: prev :: eptr  :: msg :: dly :: Vint32 stat
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) rtbl (p, t0, m0, i) ->
    (forall eid time0, i = true /\ (t0 = wait (os_stat_sem eid) (Some time0) \/
    t0 = wait (os_stat_q eid) (Some time0) \/
    t0 = wait (os_stat_mbox eid) (Some time0) \/
    t0 = wait (os_stat_mutexsem eid) (Some time0) \/ t0 = wait (os_stat_port eid) (Some time0)) ->
    time0 <> Int.zero) ->
    R_TCB_Status_P
    (next :: prev :: eptr  :: msg :: dly :: Vint32 (stat &ᵢInt.not ($ OS_STAT_SUSPEND))
      :: Vint32 prio :: Vint32 x :: Vint32 y
      :: Vint32 bitx :: Vint32 bity :: nil) rtbl (p, t0, m0, false). 
Proof.
intros.


rename H3 into RLtcbblk.
rename H into HH.
rename H2 into H.
rename H5 into Hsus_tnzero.


assert(Hstatall: stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/ 
stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)  \/ 
stat = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND) \/
stat = $ OS_STAT_SUSPEND).
{
  destruct H.
  destruct H. 
  left. auto.
  destruct H.
  right. left. auto. 
  destruct H.
  right. right. left. auto. 
  destruct H.
  right. right. right. left. auto. 
  destruct H.
  right. right. right. right. left. auto. 
  right. right. right. right. right. left. auto. 
  destruct H.
  right. right. right. right. right. right. auto. 
}


assert(Hnrdy: stat <> ($ OS_STAT_RDY)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnsem: stat <> ($ OS_STAT_SEM)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnmbox: stat <> ($ OS_STAT_MBOX)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnmutex: stat <> ($ OS_STAT_MUTEX)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnq: stat <> ($ OS_STAT_Q)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnpostq: stat <> ($ OS_STAT_POSTQ)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnport: stat <> ($ OS_STAT_PORT)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.
  

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}

assert(Hnnsus: stat&ᵢInt.not ($ OS_STAT_SUSPEND) <> ($ OS_STAT_SUSPEND)).
{
  clear -H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.

  destruct H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 

  destruct H.
  rewrite H.
  mauto.
}



assert(Hnnrdy: (
  stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/ 
  stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND)
  ) -> stat&ᵢInt.not ($ OS_STAT_SUSPEND) <> ($ OS_STAT_RDY)).
{
  intros.
  clear -H2.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.
  rename H2 into H.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.
    
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto.  
}


assert(Hnsus: (
  stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/ 
  stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) \/
  stat = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND)
  ) ->stat <> ($ OS_STAT_SUSPEND)).
{
  intros.
  clear -H2.
  rename H2 into H.
  unfold OS_STAT_RDY, OS_STAT_SEM, OS_STAT_SUSPEND, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_PORT, OS_STAT_POSTQ in *.
  destruct H.
  rewrite H.
  mauto.
  
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.
    
  destruct H.
  rewrite H.
  mauto.

  destruct H.
  rewrite H.
  mauto.

  rewrite H.
  mauto. 
}

assert(Hdlytime: 
(V_OSTCBDly
(next :: prev :: eptr :: msg :: dly :: Vint32 stat
  :: Vint32 prio :: Vint32 x :: Vint32 y
  :: Vint32 bitx :: Vint32 bity :: nil) = Some (Vint32 time) ) -> dly = Vint32 time).
{
  intros.
  unfold V_OSTCBDly in H2; simpl in H2.
  invert H2. 
  intros.
  auto.
  Optimize Proof.
  Optimize Heap.
}

rename H into H3.
rename HH into H.

lets H2: Hnrdy.



unfold R_TCB_Status_P in H4.
destruct H4 as [RLHrdy [RHLrdy [RLHsus [RHLsus [RLHstwait RHLstwait]]]]].
unfold R_TCB_Status_P.
splits.

* unfold RLH_RdyI_P in *.
  intros. unfold RdyTCBblk in H4. simpljoin.

(*   rename H5 into Hsus_tnzero.
  rename H6 into H5.
  rename H7 into H6. *)


  pose proof RLHrdy prio0 as RLHrdy.
  unfold V_OSTCBPrio in H4. simpl in H4.

  assert(RdyTCBblk
           (next
            :: prev
               :: eptr
                  :: msg :: Vint32 time :: V$ OS_STAT_SUSPEND :: Vint32 prio :: Vint32 x :: Vint32 y :: Vint32 bitx :: Vint32 bity :: nil)
           rtbl prio0).
  {
    unfold RdyTCBblk.
    split.
    unfold V_OSTCBPrio.
    simpl.
    assumption.
    auto.
  }


  lets bb: RLHrdy H7.
  destruct bb.
  destruct H9.
  destruct H9.
  unfold V_OSTCBStat in H9.
  simpl in H9.
  tryfalse.

  destruct H9.  
  destruct H9.
  unfold V_OSTCBStat in H9.
  simpl in H9.
  tryfalse.

  destruct H9.  
  destruct H9.
  unfold V_OSTCBStat in H9.
  simpl in H9.
  tryfalse.
  
  destruct H9.  
  destruct H9.
  unfold V_OSTCBStat in H9.
  simpl in H9.
  tryfalse.
  
  destruct H9.
  unfold V_OSTCBStat in H9.
  simpl in H9.
  tryfalse.

* unfold RHL_RdyI_P in *.
{
  intros.
  destruct t0.
  {
    destruct i.
    2: {
      unfold RHL_RdyI_P in RHLrdy.
      pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.

      simpljoin.
      unfold V_OSTCBStat in H6.
      simpl in H6.
      tryfalse.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
      destruct RHLsus1 as [Hblk Hstat].
      {
        destruct H3.
      (* wait suspend*)
        apply Hnsus in H3.
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.

      (* only suspend *) 
       destruct H3 as (Hx22stat & Hdlyt & Htnz). 
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        unfold V_OSTCBDly in Hdly; simpl in Hdly.        
        apply Hdlytime in Hdlyt.
        rewrite Hdlyt in Hdly.
        apply Some_Vint32_invert in Hdly.
        rewrite Hdly in Htnz.
        invert Htnz.
      }
    }
  }
  discriminate H4.
}

* unfold RLH_Suspend_P in *.
  split.
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    tryfalse.
  }
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    tryfalse.
  }
* unfold RHL_Suspend_P.
  split.
  {
    intros. inverts H4.
  }
  {
    intros. inverts H4.
  }

* unfold RLH_TCB_Status_Wait_P.
  lets H6: Hnrdy.
  splits.

  + unfolds RLH_Wait_P.

  destruct H3.
  (* wait suspend*)
  intros. unfolds in H5. simpl in H5.  
  apply Hnnrdy in H3.
  tryfalse.
  (* only suspend*)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfolds in Hblk. destruct Hblk as [Hprio [_ Hdly]].
        unfold V_OSTCBDly in Hdly; simpl in Hdly.
        
        apply Hdlytime in Hdlyt.
        rewrite Hdlyt in Hdly.
        apply Some_Vint32_invert in Hdly.
        rewrite Hdly in Htnz.
        invert Htnz.
      }      
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        destruct Hstat.
        tryfalse.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        destruct Hstat.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfolds in H4. unfolds in Hwait. simpljoin.
        unfolds in H4; simpl in H4; apply Some_Vint32_invert in H4.
        unfolds in H9; simpl in H9; apply Some_Vint32_invert in H9.
        rewrite H9 in H4. rewrite H4.
        unfolds in H8; simpl in H8. 
        unfolds in H11; simpl in H11.
        unfolds in Hdlyt; simpl in Hdlyt.
        rewrite Hdlyt in H8.
        apply Some_Vint32_invert in H8.
        rewrite Hdlyt in H11.
        apply Some_Vint32_invert in H11.
        rewrite H11 in H8. rewrite <- H8.
        split.
        auto.
  Optimize Proof.
  Optimize Heap.
        eauto.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfolds in H4. unfolds in Hwait. simpljoin.
        unfolds in H4; simpl in H4; apply Some_Vint32_invert in H4.
        unfolds in H9; simpl in H9; apply Some_Vint32_invert in H9.
        rewrite H9 in H4. rewrite H4.
        unfolds in H8; simpl in H8. 
        unfolds in H11; simpl in H11.
        unfolds in Hdlyt; simpl in Hdlyt.
        rewrite Hdlyt in H8.
        apply Some_Vint32_invert in H8.
        rewrite Hdlyt in H11.
        apply Some_Vint32_invert in H11.
        rewrite H11 in H8. rewrite <- H8.
        split.
        auto.
        eauto.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        rewrite Hx22stat in Hstat.
        tryfalse.
      }
    }
  }
 
  + unfolds RLH_WaitS_P. 
  destruct H3.
  (* wait suspend *)
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        apply Hnsus in H3.
        tryfalse.
      }
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        inverts Heptr. unfolds in H4.
        destructs H4. inverts H4. inverts H7. 
        destruct Hwait.
        destruct H4.
        * destruct H4 as [Ho Hwrd].
          destruct Hwrd.
          ** destruct H4 as [Hneq Hwait].
             unfolds in Hwait.
             destructs Hwait. inverts H4. inverts H9. inverts H10.
             rewrite Ho.
             eexists.
             eauto.
          ** destruct H4 as [Heq [Hrdy Hdly]].
             inverts Heq. inverts Ho. inverts Hstat.
             inverts H9.
             unfolds in Hrdy.
             destruct Hrdy as [Hprio Hpintbl].
             inverts Hprio. inverts Hdly.
             eexists.
             eauto.
        * destruct H4 as [Ho Hwait].
          unfolds in Hwait.
          destruct Hwait as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H9.
          rewrite Ho.
          eexists.
          eauto.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].

        destruct Hwait.
        
        * destruct H8 as [t0 H8].
          assert(Ht0: (t0 = Int.zero)\/(t0 <> Int.zero)) by tauto.
          destruct Ht0. subst.
          (* t0 = Int.zero *)
          destruct H8 as (Ho & H8).

          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].          

          subst o.
          lets bb: Hsus_tnzero e Int.zero.
          destruct bb. 
          splits; auto. 
          auto.

          (* t0 <> Int.zero *)

          destruct H8 as (Ho & H8).

          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H7.
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H8.
          inverts Ho.
          eexists.
          eauto.

        * destruct H8 as [Ho Hwt].
          unfolds in Hwt.
          destruct Hwt as (Hprio & Htbl & Hdly).
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H7. inverts H9.
          inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
          eexists.
          eauto.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
  }
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.

  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    rewrite Hx22stat in H5.
    tryfalse.
  }
  + unfolds RLH_WaitS_TO_P.
  intros.
  destruct t0.
  - unfold RHL_RdyI_P in RHLrdy.
  {
    destruct i.
    2: {
      unfold RHL_RdyI_P in RHLrdy.
      pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
      destruct RHLrdy as [Hblk [Hstat Hdly]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      tryfalse.
    }    
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
      destruct RHLsus1 as [Hblk Hstat].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      unfold V_OSTCBStat in H5; simpl in H5.
      inverts Hstat.
      tryfalse.
    }
  }
  - unfold RHL_TCB_Status_Wait_P in RHLstwait.
  destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
  [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
  destruct t.
  {
    destruct i.
    2: {
      unfold RHL_WaitS_P in RHLwaits.
      pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
      destruct RHLwaits as [Hwait [Heptr Hstat]].
      inverts Heptr. unfolds in H4.
      destructs H4. inverts H4. inverts H7. 
      destruct Hwait.
      destruct H4.
      * destruct H4 as [Ho Hwrd].
        destruct Hwrd.
        ** destruct H4 as [Hneq Hwait].
           unfolds in Hwait.
           destructs Hwait. 
           inverts H4. 
           false.
           eapply prio_rtbl_dec';eauto.
        ** destruct H4 as [Heq [Hrdy Hdly]].
           unfolds in Hrdy. destruct Hrdy as [Hprio Hpintbl].
           inverts Heq. inverts Ho. inverts Hstat.
           inverts Hdly. inverts Hprio.
           eexists.
           eauto.
      * destruct H4 as [Ho Hwait].
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. 
        false.
        eapply prio_rtbl_dec';eauto.
    }
    {
      unfold RHL_WaitS_Suspend_P in RHLwaitssus.
      pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
      destruct RHLwaitssus as [Hwait [Heptr Hstat]].

      destruct Hwait.
      
      * destruct H8 as [t0 H8].

      destruct H8 as (Ho & H8).

      unfolds in H8.
      destruct H8 as [Hprio [Hpintbl Hdly]].
      inverts Hprio. inverts Hdly. inverts H7.
      inverts Heptr. unfolds in H4.
      destructs H4.
      inverts H4. 
      false.
      eapply prio_rtbl_dec';eauto.

      * destruct H8 as [Ho Hwt].

        inverts Heptr. unfolds in H4.
        destructs H4.
        inverts H4. 
        unfolds in Hwt.
        destruct Hwt as (Hprio & Hnpintbl & Hdly).
        inverts Hprio.
        false.
        eapply prio_rtbl_dec';eauto.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitQ_P in RHLwaitq.
      pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
      destruct RHLwaitq as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
      pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
      destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPostQ_P in RHLwaitpostq.
      pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
      destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
      pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
      destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_Wait_P in RHLwait.
      pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
      destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
      destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMB_P in RHLwaitmb.
      pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
      destruct RHLwaitmb as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
      pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
      destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMS_P in RHLwaitms.
      pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
      destruct RHLwaitms as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
      pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
      destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPort_P in RHLwaitport.
      pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
      destruct RHLwaitport as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
      pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
      destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  
  + unfolds RLH_WaitQ_P.
  destruct H3.
  (* wait suspend *)
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        apply Hnsus in H3.
        tryfalse.
      }
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        inverts Heptr. unfolds in H4.
        destructs H4. inverts H4. inverts H7. 
        destruct Hwait.
        destruct H4.
        * destruct H4 as [Ho Hwrd].
          destruct Hwrd.
          ** destruct H4 as [Hneq Hwait].
             unfolds in Hwait.
             destructs Hwait. inverts H4. inverts H9. inverts H10.
             rewrite Ho.
             eexists.
             eauto.
          ** destruct H4 as [Heq [Hrdy Hdly]].
             inverts Heq. inverts Ho. inverts Hstat.
             inverts H9.
             unfolds in Hrdy.
             destruct Hrdy as [Hprio Hpintbl].
             inverts Hprio. inverts Hdly.
             eexists.
             eauto.
        * destruct H4 as [Ho Hwait].
          unfolds in Hwait.
          destruct Hwait as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H9.
          rewrite Ho.
          eexists.
          eauto.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        destruct Hwait.        
        * destruct H8 as [t0 H8].
          assert(Ht0: (t0 = Int.zero)\/(t0 <> Int.zero)) by tauto.
          destruct Ht0. subst.
          (* t0 = Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          subst o.
          lets bb: Hsus_tnzero e Int.zero.
          destruct bb. 
          splits; auto. 
          auto.
  Optimize Proof.
  Optimize Heap.

          (* t0 <> Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H7.
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H8.
          inverts Ho.
          eexists.
          eauto.
        * destruct H8 as [Ho Hwt].
          unfolds in Hwt.
          destruct Hwt as (Hprio & Htbl & Hdly).
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H7. inverts H9.
          inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
          eexists.
          eauto.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
  }
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy. 
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    rewrite Hx22stat in H5.
    tryfalse.
  }

  + unfolds RLH_WaitQ_TO_P.
  intros.
  destruct t0.
  - unfold RHL_RdyI_P in RHLrdy.
  {
    destruct i.
    2: {
      unfold RHL_RdyI_P in RHLrdy.
      pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
      destruct RHLrdy as [Hblk [Hstat Hdly]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      tryfalse.
    }    
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
      destruct RHLsus1 as [Hblk Hstat].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      unfold V_OSTCBStat in H5; simpl in H5.
      inverts Hstat.
      tryfalse.
    }
  }
  - unfold RHL_TCB_Status_Wait_P in RHLstwait.
  destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
  [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
  destruct t.
  {
    destruct i.
    2: {
      unfold RHL_WaitS_P in RHLwaits.
      pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
      destruct RHLwaits as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitS_Suspend_P in RHLwaitssus.
      pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
      destruct RHLwaitssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitQ_P in RHLwaitq.
      pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
      destruct RHLwaitq as [Hwait [Heptr Hstat]].
      inverts Heptr. unfolds in H4.
      destructs H4. inverts H4. inverts H7. 
      destruct Hwait.
      destruct H4.
      * destruct H4 as [Ho Hwrd].
        destruct Hwrd.
        ** destruct H4 as [Hneq Hwait].
           unfolds in Hwait.
           destructs Hwait. 
           inverts H4. 
           false.
           eapply prio_rtbl_dec';eauto.
        ** destruct H4 as [Heq [Hrdy Hdly]].
           unfolds in Hrdy. destruct Hrdy as [Hprio Hpintbl].
           inverts Heq. inverts Ho. inverts Hstat.
           inverts Hdly. inverts Hprio.
           eexists.
           eauto.
      * destruct H4 as [Ho Hwait].
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. 
        false.
        eapply prio_rtbl_dec';eauto.
    }
    {
      unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
      pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
      destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
      destruct Hwait.      
      * destruct H8 as [t0 H8].
      destruct H8 as (Ho & H8).
      unfolds in H8.
      destruct H8 as [Hprio [Hpintbl Hdly]].
      inverts Hprio. inverts Hdly. inverts H7.
      inverts Heptr. unfolds in H4.
      destructs H4.
      inverts H4. 
      false.
      eapply prio_rtbl_dec';eauto.
      * destruct H8 as [Ho Hwt].
        inverts Heptr. unfolds in H4.
        destructs H4.
        inverts H4. 
        unfolds in Hwt.
        destruct Hwt as (Hprio & Hnpintbl & Hdly).
        inverts Hprio.
        false.
        eapply prio_rtbl_dec';eauto.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPostQ_P in RHLwaitpostq.
      pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
      destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
      pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
      destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_Wait_P in RHLwait.
      pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
      destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
      destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMB_P in RHLwaitmb.
      pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
      destruct RHLwaitmb as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
      pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
      destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMS_P in RHLwaitms.
      pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
      destruct RHLwaitms as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
      pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
      destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPort_P in RHLwaitport.
      pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
      destruct RHLwaitport as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
      pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
      destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }  
  + unfolds RLH_WaitMB_P. 
  destruct H3.
  (* wait suspend *)
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        apply Hnsus in H3.
        tryfalse.
      }
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        inverts Heptr. unfolds in H4.
        destructs H4. inverts H4. inverts H7. 
        destruct Hwait.
        destruct H4.
        * destruct H4 as [Ho Hwrd].
          destruct Hwrd.
          ** destruct H4 as [Hneq Hwait].
             unfolds in Hwait.
             destructs Hwait. inverts H4. inverts H9. inverts H10.
             rewrite Ho.
             eexists.
             eauto.
          ** destruct H4 as [Heq [Hrdy Hdly]].
             inverts Heq. inverts Ho. inverts Hstat.
             inverts H9.
             unfolds in Hrdy.
             destruct Hrdy as [Hprio Hpintbl].
             inverts Hprio. inverts Hdly.
             eexists.
             eauto.
        * destruct H4 as [Ho Hwait].
          unfolds in Hwait.
          destruct Hwait as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H9.
          rewrite Ho.
          eexists.
          eauto.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        destruct Hwait.        
        * destruct H8 as [t0 H8].
          assert(Ht0: (t0 = Int.zero)\/(t0 <> Int.zero)) by tauto.
          destruct Ht0. subst.
          (* t0 = Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          subst o.
          lets bb: Hsus_tnzero e Int.zero.
          destruct bb. 
          splits; auto. 
          auto.
  Optimize Proof.
  Optimize Heap.
          (* t0 <> Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H7.
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H8.
          inverts Ho.
          eexists.
          eauto.
        * destruct H8 as [Ho Hwt].
          unfolds in Hwt.
          destruct Hwt as (Hprio & Htbl & Hdly).
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H7. inverts H9.
          inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
          eexists.
          eauto.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
  }
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy. 
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    rewrite Hx22stat in H5.
    tryfalse.
  }

  + unfolds RLH_WaitMB_TO_P.
  intros.
  destruct t0.
  - unfold RHL_RdyI_P in RHLrdy.
  {
    destruct i.
    2: {
      unfold RHL_RdyI_P in RHLrdy.
      pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
      destruct RHLrdy as [Hblk [Hstat Hdly]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      tryfalse.
    }    
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
      destruct RHLsus1 as [Hblk Hstat].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      unfold V_OSTCBStat in H5; simpl in H5.
      inverts Hstat.
      tryfalse.
    }
  }
  - unfold RHL_TCB_Status_Wait_P in RHLstwait.
  destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
  [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
  destruct t.
  {
    destruct i.
    2: {
      unfold RHL_WaitS_P in RHLwaits.
      pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
      destruct RHLwaits as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitS_Suspend_P in RHLwaitssus.
      pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
      destruct RHLwaitssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitQ_P in RHLwaitq.
      pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
      destruct RHLwaitq as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
      pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
      destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPostQ_P in RHLwaitpostq.
      pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
      destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
      pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
      destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_Wait_P in RHLwait.
      pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
      destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
      destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMB_P in RHLwaitmb.
      pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
      destruct RHLwaitmb as [Hwait [Heptr Hstat]].
      inverts Heptr. unfolds in H4.
      destructs H4. inverts H4. inverts H7. 
      destruct Hwait.
      destruct H4.
      * destruct H4 as [Ho Hwrd].
        destruct Hwrd.
        ** destruct H4 as [Hneq Hwait].
           unfolds in Hwait.
           destructs Hwait. 
           inverts H4. 
           false.
           eapply prio_rtbl_dec';eauto.
        ** destruct H4 as [Heq [Hrdy Hdly]].
           unfolds in Hrdy. destruct Hrdy as [Hprio Hpintbl].
           inverts Heq. inverts Ho. inverts Hstat.
           inverts Hdly. inverts Hprio.
           eexists.
           eauto.
      * destruct H4 as [Ho Hwait].
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. 
        false.
        eapply prio_rtbl_dec';eauto.
    }
    {
      unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
      pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
      destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
      destruct Hwait.      
      * destruct H8 as [t0 H8].
      destruct H8 as (Ho & H8).
      unfolds in H8.
      destruct H8 as [Hprio [Hpintbl Hdly]].
      inverts Hprio. inverts Hdly. inverts H7.
      inverts Heptr. unfolds in H4.
      destructs H4.
      inverts H4. 
      false.
      eapply prio_rtbl_dec';eauto.
      * destruct H8 as [Ho Hwt].
        inverts Heptr. unfolds in H4.
        destructs H4.
        inverts H4. 
        unfolds in Hwt.
        destruct Hwt as (Hprio & Hnpintbl & Hdly).
        inverts Hprio.
        false.
        eapply prio_rtbl_dec';eauto.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMS_P in RHLwaitms.
      pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
      destruct RHLwaitms as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
      pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
      destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPort_P in RHLwaitport.
      pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
      destruct RHLwaitport as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
      pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
      destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  } 
  
  + splits. 

  unfolds RLH_WaitMS_P.
  destruct H3.
  (* wait suspend *)
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        apply Hnsus in H3.
        tryfalse.
      }
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        inverts Heptr. unfolds in H4.
        destructs H4. inverts H4. inverts H7. 
        destruct Hwait.
        destruct H4.
        * destruct H4 as [Ho Hwrd].
          destruct Hwrd.
          ** destruct H4 as [Hneq Hwait].
             unfolds in Hwait.
             destructs Hwait. inverts H4. inverts H9. inverts H10.
             rewrite Ho.
             eexists.
             eauto.
          ** destruct H4 as [Heq [Hrdy Hdly]].
             inverts Heq. inverts Ho. inverts Hstat.
             inverts H9.
             unfolds in Hrdy.
             destruct Hrdy as [Hprio Hpintbl].
             inverts Hprio. inverts Hdly.
             eexists.
             eauto.
        * destruct H4 as [Ho Hwait].
          unfolds in Hwait.
          destruct Hwait as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H9.
          rewrite Ho.
          eexists.
          eauto.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        destruct Hwait.        
        * destruct H8 as [t0 H8].
          assert(Ht0: (t0 = Int.zero)\/(t0 <> Int.zero)) by tauto.
          destruct Ht0. subst.
          (* t0 = Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          subst o.
          lets bb: Hsus_tnzero e Int.zero.
          destruct bb. 
          splits; auto. 
          auto.
  Optimize Proof.
  Optimize Heap.
          (* t0 <> Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H7.
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H8.
          inverts Ho.
          eexists.
          eauto.
        * destruct H8 as [Ho Hwt].
          unfolds in Hwt.
          destruct Hwt as (Hprio & Htbl & Hdly).
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H7. inverts H9.
          inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
          eexists.
          eauto.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
  }
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy. 
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    rewrite Hx22stat in H5.
    tryfalse.
  }

  unfolds RLH_WaitMS_TO_P.
  intros.
  destruct t0.
  - unfold RHL_RdyI_P in RHLrdy.
  {
    destruct i.
    2: {
      unfold RHL_RdyI_P in RHLrdy.
      pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
      destruct RHLrdy as [Hblk [Hstat Hdly]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      tryfalse.
    }    
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
      destruct RHLsus1 as [Hblk Hstat].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      unfold V_OSTCBStat in H5; simpl in H5.
      inverts Hstat.
      tryfalse.
    }
  }
  - unfold RHL_TCB_Status_Wait_P in RHLstwait.
  destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
  [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
  destruct t.
  {
    destruct i.
    2: {
      unfold RHL_WaitS_P in RHLwaits.
      pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
      destruct RHLwaits as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitS_Suspend_P in RHLwaitssus.
      pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
      destruct RHLwaitssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitQ_P in RHLwaitq.
      pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
      destruct RHLwaitq as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
      pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
      destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPostQ_P in RHLwaitpostq.
      pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
      destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
      pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
      destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_Wait_P in RHLwait.
      pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
      destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
      destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMB_P in RHLwaitmb.
      pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
      destruct RHLwaitmb as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
      pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
      destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMS_P in RHLwaitms.
      pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
      destruct RHLwaitms as [Hwait [Heptr Hstat]].
      inverts Heptr. unfolds in H4.
      destructs H4. inverts H4. inverts H7. 
      destruct Hwait.
      destruct H4.
      * destruct H4 as [Ho Hwrd].
        destruct Hwrd.
        ** destruct H4 as [Hneq Hwait].
           unfolds in Hwait.
           destructs Hwait. 
           inverts H4. 
           false.
           eapply prio_rtbl_dec';eauto.
        ** destruct H4 as [Heq [Hrdy Hdly]].
           unfolds in Hrdy. destruct Hrdy as [Hprio Hpintbl].
           inverts Heq. inverts Ho. inverts Hstat.
           inverts Hdly. inverts Hprio.
           eexists.
           eauto.
      * destruct H4 as [Ho Hwait].
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. 
        false.
        eapply prio_rtbl_dec';eauto.
    }
    {
      unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
      pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
      destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
      destruct Hwait.      
      * destruct H8 as [t0 H8].
      destruct H8 as (Ho & H8).
      unfolds in H8.
      destruct H8 as [Hprio [Hpintbl Hdly]].
      inverts Hprio. inverts Hdly. inverts H7.
      inverts Heptr. unfolds in H4.
      destructs H4.
      inverts H4. 
      false.
      eapply prio_rtbl_dec';eauto.
      * destruct H8 as [Ho Hwt].
        inverts Heptr. unfolds in H4.
        destructs H4.
        inverts H4. 
        unfolds in Hwt.
        destruct Hwt as (Hprio & Hnpintbl & Hdly).
        inverts Hprio.
        false.
        eapply prio_rtbl_dec';eauto.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPort_P in RHLwaitport.
      pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
      destruct RHLwaitport as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
      pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
      destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  - unfolds RLH_WaitPostQ_P.
  destruct H3.
  (* wait suspend *)
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        apply Hnsus in H3.
        tryfalse.
      }
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
        inverts Heptr. 
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. inverts Hdly. 
        unfolds in H4.
        destructs H4. inverts H4. inverts H9. inverts H7.
        rewrite Ho.
        splits; eauto.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
        inverts Heptr. 
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. inverts Hdly. 
        unfolds in H4.
        destructs H4. inverts H4. inverts H9. inverts H7.
        rewrite Ho.
        splits; eauto.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
  }
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy. 
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    rewrite Hx22stat in H5.
    tryfalse.
  }



  - unfolds RLH_WaitS_Suspend_P. 
  destruct H3.
  (* wait suspend *)
  intros.
  unfolds in H5. simpl in H5.    
  apply Some_Vint32_invert in H5.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  rewrite H3 in H5.
  tryfalse.
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.  
  intros.
  unfold V_OSTCBStat in H5; simpl in H5.
  rewrite Hx22stat in H5.
  tryfalse.

  - unfolds RLH_WaitQ_Suspend_P. 
  destruct H3.
  (* wait suspend *)
  intros.
  unfolds in H5. simpl in H5.    
  apply Some_Vint32_invert in H5.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  rewrite H3 in H5.
  tryfalse.
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.  
  intros.
  unfold V_OSTCBStat in H5; simpl in H5.
  rewrite Hx22stat in H5.
  tryfalse.

  - unfolds RLH_WaitPostQ_Suspend_P.
  destruct H3.
  (* wait suspend *)
  intros.
  unfolds in H5. simpl in H5.    
  apply Some_Vint32_invert in H5.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  rewrite H3 in H5.
  tryfalse.
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.  
  intros.
  unfold V_OSTCBStat in H5; simpl in H5.
  rewrite Hx22stat in H5.
  tryfalse.

  - unfolds RLH_WaitMB_Suspend_P. 
  destruct H3.
  (* wait suspend *)
  intros.
  unfolds in H5. simpl in H5.    
  apply Some_Vint32_invert in H5.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  rewrite H3 in H5.
  tryfalse.
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.  
  intros.
  unfold V_OSTCBStat in H5; simpl in H5.
  rewrite Hx22stat in H5.
  tryfalse.

  - splits.

  unfolds RLH_WaitMS_Suspend_P. 
  destruct H3.
  (* wait suspend *)
  intros.
  unfolds in H5. simpl in H5.    
  apply Some_Vint32_invert in H5.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  rewrite H3 in H5.
  tryfalse.
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.  
  intros.
  unfold V_OSTCBStat in H5; simpl in H5.
  rewrite Hx22stat in H5.
  tryfalse.

  unfolds RLH_WaitPort_P.
  destruct H3.
  (* wait suspend *)
  {
    intros.
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_RdyI_P in RHLrdy.
        pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
        destruct RHLrdy as [Hblk [Hstat Hdly]].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        tryfalse.
      }
      
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
        destruct RHLsus1 as [Hblk Hstat].
        unfold V_OSTCBStat in Hstat.
        simpl in Hstat.
        apply Hnsus in H3.
        tryfalse.
      }
    }
    unfold RHL_TCB_Status_Wait_P in RHLstwait.
    destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
    [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
    destruct t0.
    {
      destruct i.
      2: {
        unfold RHL_WaitS_P in RHLwaits.
        pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
        destruct RHLwaits as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
        destruct RHLwaitssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitQ_P in RHLwaitq.
        pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
        destruct RHLwaitq as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
        destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPostQ_P in RHLwaitpostq.
        pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
        destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
        pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
        destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_Wait_P in RHLwait.
        pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
        destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_Suspend_P in RHLsus.
        destruct RHLsus as [RHLsus1 RHLsus2].
        pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
        destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMB_P in RHLwaitmb.
        pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
        destruct RHLwaitmb as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
        destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitMS_P in RHLwaitms.
        pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
        destruct RHLwaitms as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
      {
        unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
        destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
        unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
        unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
        clear - Hstat H5.
        rewrite Hstat in H5.
        tryfalse.
      }
    }
    {
      destruct i.
      2: {
        unfold RHL_WaitPort_P in RHLwaitport.
        pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
        destruct RHLwaitport as [Hwait [Heptr Hstat]].
        inverts Heptr. unfolds in H4.
        destructs H4. inverts H4. inverts H7. 
        destruct Hwait.
        destruct H4.
        * destruct H4 as [Ho Hwrd].
          destruct Hwrd.
          ** destruct H4 as [Hneq Hwait].
             unfolds in Hwait.
             destructs Hwait. inverts H4. inverts H9. inverts H10.
             rewrite Ho.
             eexists.
             eauto.
          ** destruct H4 as [Heq [Hrdy Hdly]].
             inverts Heq. inverts Ho. inverts Hstat.
             inverts H9.
             unfolds in Hrdy.
             destruct Hrdy as [Hprio Hpintbl].
             inverts Hprio. inverts Hdly.
             eexists.
             eauto.
        * destruct H4 as [Ho Hwait].
          unfolds in Hwait.
          destruct Hwait as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H9.
          rewrite Ho.
          eexists.
          eauto.
      }
      {
        unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
        destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
        destruct Hwait.        
        * destruct H8 as [t0 H8].
          assert(Ht0: (t0 = Int.zero)\/(t0 <> Int.zero)) by tauto.
          destruct Ht0. subst.
          (* t0 = Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          subst o.
          lets bb: Hsus_tnzero e Int.zero.
          destruct bb. 
          splits; auto. 
          auto.
  Optimize Proof.
  Optimize Heap.
          (* t0 <> Int.zero *)
          destruct H8 as (Ho & H8).
          unfolds in H8.
          destruct H8 as [Hprio [Hpintbl Hdly]].
          inverts Hprio. inverts Hdly. inverts H7.
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H8.
          inverts Ho.
          eexists.
          eauto.
        * destruct H8 as [Ho Hwt].
          unfolds in Hwt.
          destruct Hwt as (Hprio & Htbl & Hdly).
          inverts Heptr. unfolds in H4.
          destructs H4.
          inverts H4. inverts H7. inverts H9.
          inverts Ho. inverts Hprio. inverts Hdly. inverts Hstat.
          eexists.
          eauto.
      }
    }
  }
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy. 
  {
    intros.
    unfold V_OSTCBStat in H5; simpl in H5.
    rewrite Hx22stat in H5.
    tryfalse.
  }

  unfolds RLH_WaitPort_TO_P.
  intros.
  destruct t0.
  ** unfold RHL_RdyI_P in RHLrdy.
  {
    destruct i.
    2: {
      unfold RHL_RdyI_P in RHLrdy.
      pose proof (RHLrdy p m0 (eq_refl (p, rdy, m0, false))) as RHLrdy.
      destruct RHLrdy as [Hblk [Hstat Hdly]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      tryfalse.
    }    
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus1 p m0 (eq_refl (p, rdy, m0, true))) as RHLsus1.
      destruct RHLsus1 as [Hblk Hstat].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      unfold V_OSTCBStat in H5; simpl in H5.
      inverts Hstat.
      tryfalse.
    }
  }
  ** unfold RHL_TCB_Status_Wait_P in RHLstwait.
  destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
  [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
  destruct t.
  {
    destruct i.
    2: {
      unfold RHL_WaitS_P in RHLwaits.
      pose proof (RHLwaits p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, false))) as RHLwaits. 
      destruct RHLwaits as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitS_Suspend_P in RHLwaitssus.
      pose proof (RHLwaitssus p e o m0 (eq_refl (p, wait (os_stat_sem e) o, m0, true))) as RHLwaitssus. 
      destruct RHLwaitssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitQ_P in RHLwaitq.
      pose proof (RHLwaitq p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, false))) as RHLwaitq. 
      destruct RHLwaitq as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
      pose proof (RHLwaitqsus p e o m0 (eq_refl (p, wait (os_stat_q e) o, m0, true))) as RHLwaitqsus. 
      destruct RHLwaitqsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPostQ_P in RHLwaitpostq.
      pose proof (RHLwaitpostq p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, false))) as RHLwaitpostq. 
      destruct RHLwaitpostq as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
      pose proof (RHLpostqsus p e o m0 (eq_refl (p, wait (os_stat_postq e) o, m0, true))) as RHLpostqsus. 
      destruct RHLpostqsus as [Ho [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_Wait_P in RHLwait.
      pose proof (RHLwait p o m0 (eq_refl (p, wait os_stat_time o, m0, false))) as RHLwait. 
      destruct RHLwait as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus2 p o m0 (eq_refl (p, wait os_stat_time o, m0, true))) as RHLsus2. 
      destruct RHLsus2 as [t0 [Ho [Hwait [Hdly Hstat]]]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMB_P in RHLwaitmb.
      pose proof (RHLwaitmb p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, false))) as RHLwaitmb. 
      destruct RHLwaitmb as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
      pose proof (RHLwaitmbsus p e o m0 (eq_refl (p, wait (os_stat_mbox e) o, m0, true))) as RHLwaitmbsus. 
      destruct RHLwaitmbsus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitMS_P in RHLwaitms.
      pose proof (RHLwaitms p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, false))) as RHLwaitms. 
      destruct RHLwaitms as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
    {
      unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
      pose proof (RHLwaitmssus p e o m0 (eq_refl (p, wait (os_stat_mutexsem e) o, m0, true))) as RHLwaitmssus. 
      destruct RHLwaitmssus as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in H5. simpl in H5. apply Some_Vint32_invert in H5.
      unfold V_OSTCBStat in Hstat. simpl in Hstat. apply Some_Vint32_invert in Hstat.
      clear - Hstat H5.
      rewrite Hstat in H5.
      tryfalse.
    }
  }
  {
    destruct i.
    2: {
      unfold RHL_WaitPort_P in RHLwaitport.
      pose proof (RHLwaitport p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, false))) as RHLwaitport. 
      destruct RHLwaitport as [Hwait [Heptr Hstat]].
      inverts Heptr. unfolds in H4.
      destructs H4. inverts H4. inverts H7. 
      destruct Hwait.
      destruct H4.
      * destruct H4 as [Ho Hwrd].
        destruct Hwrd.
        ** destruct H4 as [Hneq Hwait].
           unfolds in Hwait.
           destructs Hwait. 
           inverts H4. 
           false.
           eapply prio_rtbl_dec';eauto.
        ** destruct H4 as [Heq [Hrdy Hdly]].
           unfolds in Hrdy. destruct Hrdy as [Hprio Hpintbl].
           inverts Heq. inverts Ho. inverts Hstat.
           inverts Hdly. inverts Hprio.
           eexists.
           eauto.
      * destruct H4 as [Ho Hwait].
        unfolds in Hwait.
        destruct Hwait as [Hprio [Hpintbl Hdly]].
        inverts Hprio. 
        false.
        eapply prio_rtbl_dec';eauto.
    }
    {
      unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
      pose proof (RHLwaitportsus p e o m0 (eq_refl (p, wait (os_stat_port e) o, m0, true))) as RHLwaitportsus. 
      destruct RHLwaitportsus as [Hwait [Heptr Hstat]].
      destruct Hwait.      
      * destruct H8 as [t0 H8].
      destruct H8 as (Ho & H8).
      unfolds in H8.
      destruct H8 as [Hprio [Hpintbl Hdly]].
      inverts Hprio. inverts Hdly. inverts H7.
      inverts Heptr. unfolds in H4.
      destructs H4.
      inverts H4. 
      false.
      eapply prio_rtbl_dec';eauto.
      * destruct H8 as [Ho Hwt].
        inverts Heptr. unfolds in H4.
        destructs H4.
        inverts H4. 
        unfolds in Hwt.
        destruct Hwt as (Hprio & Hnpintbl & Hdly).
        inverts Hprio.
        false.
        eapply prio_rtbl_dec';eauto.
    }
  } 

  **   unfolds RLH_WaitPort_Suspend_P. 
  destruct H3.
  (* wait suspend *)
  intros.
  unfolds in H5. simpl in H5.    
  apply Some_Vint32_invert in H5.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  destruct H3. rewrite H3 in H5.
  tryfalse.
  rewrite H3 in H5.
  tryfalse.
  (* only suspend *)
  destruct H3 as (Hx22stat & Hdlyt & Htnz).
  lets H3: Hnrdy.  
  intros.
  unfold V_OSTCBStat in H5; simpl in H5.
  rewrite Hx22stat in H5.
  tryfalse.

* unfold RHL_TCB_Status_Wait_P in *.
destruct RHLstwait as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
[RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].
  splits.
  
  + unfolds RHL_Wait_P. intros.  inverts H4.
  {

    destruct i.
    2: {
      pose proof (RHLwait prio0 t_opt m (eq_refl (prio0, wait os_stat_time t_opt, m, false))) as RHLwait. 
      destruct RHLwait as [x0 [Htopt [Hwait [Hdly Hstat]]]].
      destruct H3.
      (* wait suspend *)
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      tryfalse.
      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      eexists x0.
      splits; auto. 
      unfold V_OSTCBStat; simpl.
      rewrite Hx22stat.
      unfold OS_STAT_SUSPEND, OS_STAT_RDY.
      clear -H2.
      mauto.
    }
    {
      unfold RHL_Suspend_P in RHLsus.
      destruct RHLsus as [RHLsus1 RHLsus2].
      pose proof (RHLsus2 prio0 t_opt m (eq_refl (prio0, wait os_stat_time t_opt, m, true))) as RHLsus2. 
      destruct RHLsus2 as [x0 [Htopt [Hwait [Hdly Hstat]]]].
      destruct H3.
      (* wait suspend *)
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Hnsus in H3.
      tryfalse.
      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      eexists x0.
      splits; auto. 
      unfold V_OSTCBStat; simpl.
      rewrite Hx22stat.
      unfold OS_STAT_SUSPEND, OS_STAT_RDY.
      clear -H2.
      mauto.
    }
  }

  + unfolds RHL_WaitS_P. intros. inverts H4.
  {
    destruct i.
    2: {
      pose proof (RHLwaits prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_sem eid) t_opt, m, false))) as RHLwaits. 
      destruct RHLwaits as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Some_Vint32_invert in Hstat.
      tryfalse.
    }
    {
      unfold RHL_WaitS_Suspend_P in RHLwaitssus.
      pose proof (RHLwaitssus prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_sem eid) t_opt, m, true))) as RHLwaitssus. 
      destruct RHLwaitssus as [Hblk [Heptr Hstat]].
      destruct H3.
      (* wait suspend *)
      destruct Hblk as [Hblk | Hblk].
      destruct Hblk as [x0 [Htopt [Hprio [Hpnit Hdly]]]].
      assert(x0 = Int.zero \/ x0 <> Int.zero) by tauto.
      destruct H4. subst.
      
      lets bb: Hsus_tnzero eid Int.zero.
      destruct bb. 
      splits; auto. 
      auto.
  Optimize Proof.
  Optimize Heap.

      inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
      splits; auto.
      eexists x0.
      left.
      splits; auto. 
      left.
      splits; auto. 
      unfold WaitTCBblk.
      splits; auto. 

      destruct Hblk as [Hnopt Hwait].
      unfolds in Hwait.
      destruct Hwait as [Hprio [Hpnit Hdly]].
      splits; auto.
      eexists.
      right.
      splits; eauto. 
      inverts Hprio; inverts Hdly.
      unfold WaitTCBblk.
      splits; auto. 
      inverts Hstat.
      eauto.
      
      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }
  }

  + unfolds RHL_WaitQ_P. intros. inverts H4.
  {
    destruct i.
    2: {
      unfold RHL_WaitQ_P in RHLwaitq.
      pose proof (RHLwaitq prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_q eid) t_opt, m, false))) as RHLwaitq. 
      destruct RHLwaitq as [Hwait [Heptr Hstat]].
      destruct H3.
      (* wait suspend *)
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Some_Vint32_invert in Hstat.
      false.

      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }

    {
      unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
      pose proof (RHLwaitqsus prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_q eid) t_opt, m, true))) as RHLwaitqsus. 
      destruct RHLwaitqsus as [Hblk [Heptr Hstat]].
      destruct H3.
      (* wait suspend *)
      destruct Hblk as [Hblk | Hblk].
      destruct Hblk as [x0 [Htopt [Hprio [Hpnit Hdly]]]].
      assert(x0 = Int.zero \/ x0 <> Int.zero) by tauto.
      destruct H4. subst.

      lets bb: Hsus_tnzero eid Int.zero.
      destruct bb. 
      splits; auto. 
      auto.

      inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
      splits; auto.
      eexists x0.
      left.
      splits; auto. 
      left.
      splits; auto. 
      unfold WaitTCBblk.
      splits; auto. 

      destruct Hblk as [Hnopt Hwait].
      unfolds in Hwait.
      destruct Hwait as [Hprio [Hpnit Hdly]].
      splits; auto.
      eexists.
      right.
      splits; eauto. 
      inverts Hprio; inverts Hdly.
      unfold WaitTCBblk.
      splits; auto. 
      inverts Hstat.
      eauto.

      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }
  }

  + unfolds RHL_WaitMB_P. intros. inverts H4.  
  {
    destruct i.
    2: {
      unfold RHL_WaitMB_P in RHLwaitmb.
      pose proof (RHLwaitmb prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_mbox eid) t_opt, m, false))) as RHLwaitmb. 
      destruct RHLwaitmb as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Some_Vint32_invert in Hstat.
      false.
    }
    {
      unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
      pose proof (RHLwaitmbsus prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_mbox eid) t_opt, m, true))) as RHLwaitmbsus. 
      destruct RHLwaitmbsus as [Hblk [Heptr Hstat]].
      destruct H3.
      (* wait suspend *)
      destruct Hblk as [Hblk | Hblk].
      destruct Hblk as [x0 [Htopt [Hprio [Hpnit Hdly]]]].
      assert(x0 = Int.zero \/ x0 <> Int.zero) by tauto.
      destruct H4. subst.

      lets bb: Hsus_tnzero eid Int.zero.
      destruct bb. 
      splits; auto. 
      auto.

      inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
      splits; auto.
      eexists x0.
      left.
      splits; auto. 
      left.
      splits; auto. 
      unfold WaitTCBblk.
      splits; auto. 

      destruct Hblk as [Hnopt Hwait].
      unfolds in Hwait.
      destruct Hwait as [Hprio [Hpnit Hdly]].
      splits; auto.
      eexists.
      right.
      splits; eauto. 
      inverts Hprio; inverts Hdly.
      unfold WaitTCBblk.
      splits; auto. 
      inverts Hstat.
      eauto.

      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }
  }

  + unfolds RHL_WaitMS_P. intros. inverts H4.  
  {
    destruct i.
    2: {
      unfold RHL_WaitMS_P in RHLwaitms.
      pose proof (RHLwaitms prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_mutexsem eid) t_opt, m, false))) as RHLwaitms. 
      destruct RHLwaitms as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Some_Vint32_invert in Hstat.
      false.
    }
    {
      unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
      pose proof (RHLwaitmssus prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_mutexsem eid) t_opt, m, true))) as RHLwaitmssus. 
      destruct RHLwaitmssus as [Hblk [Heptr Hstat]].
      destruct H3.
      (* wait suspend *)
      destruct Hblk as [Hblk | Hblk].
      destruct Hblk as [x0 [Htopt [Hprio [Hpnit Hdly]]]].
      assert(x0 = Int.zero \/ x0 <> Int.zero) by tauto.
      destruct H4. subst.

      lets bb: Hsus_tnzero eid Int.zero.
      destruct bb. 
      splits; auto. 
      auto.
  Optimize Proof.
  Optimize Heap.
      inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
      splits; auto.
      eexists x0.
      left.
      splits; auto. 
      left.
      splits; auto. 
      unfold WaitTCBblk.
      splits; auto. 

      destruct Hblk as [Hnopt Hwait].
      unfolds in Hwait.
      destruct Hwait as [Hprio [Hpnit Hdly]].
      splits; auto.
      eexists.
      right.
      splits; eauto. 
      inverts Hprio; inverts Hdly.
      unfold WaitTCBblk.
      splits; auto. 
      inverts Hstat.
      eauto.

      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }
  }

  + unfolds RHL_WaitPostQ_P. intros. inverts H4.  
  {
    destruct i.
    2: {
      unfold RHL_WaitPostQ_P in RHLwaitpostq.
      pose proof (RHLwaitpostq prio0 eid t m (eq_refl (prio0, wait (os_stat_postq eid) t, m, false))) as RHLwaitpostq. 
      destruct RHLwaitpostq as [Htnone [Hwait [Heptr Hstat]]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Some_Vint32_invert in Hstat.
      false.
    }
    {
      unfold RHL_WaitPostQ_Suspend_P in RHLpostqsus.
      pose proof (RHLpostqsus prio0 eid t m (eq_refl (prio0, wait (os_stat_postq eid) t, m, true))) as RHLpostqsus. 
      destruct RHLpostqsus as [Htnone [Hwait [Heptr Hstat]]].
      destruct H3.
      (* wait suspend *)
      splits; auto.
      inverts Hstat.
      eauto.

      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }
  }

  + unfolds RHL_WaitS_Suspend_P. intros. inverts H4.

  + splits.

  - unfolds RHL_WaitQ_Suspend_P. intros. inverts H4.

  - unfolds RHL_WaitPostQ_Suspend_P. intros. inverts H4.

  - unfolds RHL_WaitMB_Suspend_P. intros. inverts H4.

  - unfolds RHL_WaitMS_Suspend_P. intros. inverts H4.

  - unfolds RHL_WaitPort_P. intros. inverts H4.
  {
    destruct i.
    2: {
      unfold RHL_WaitPort_P in RHLwaitport.
      pose proof (RHLwaitport prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_port eid) t_opt, m, false))) as RHLwaitport. 
      destruct RHLwaitport as [Hwait [Heptr Hstat]].
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      apply Some_Vint32_invert in Hstat.
      false.
    }
    {
      unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
      pose proof (RHLwaitportsus prio0 eid t_opt m (eq_refl (prio0, wait (os_stat_port eid) t_opt, m, true))) as RHLwaitportsus. 
      destruct RHLwaitportsus as [Hblk [Heptr Hstat]].
      destruct H3.
      (* wait suspend *)
      destruct Hblk as [Hblk | Hblk].
      destruct Hblk as [x0 [Htopt [Hprio [Hpnit Hdly]]]].
      assert(x0 = Int.zero \/ x0 <> Int.zero) by tauto.
      destruct H4. subst.

      lets bb: Hsus_tnzero eid Int.zero.
      destruct bb. 
      splits; auto. 
      auto.

      inverts Hprio; inverts Hdly; inverts Heptr; inverts Hstat.
      splits; auto.
      left.
      eexists x0.
      splits; auto. 
      left.
      splits; auto. 
      unfold WaitTCBblk.
      splits; auto. 

      destruct Hblk as [Hnopt Hwait].
      unfolds in Hwait.
      destruct Hwait as [Hprio [Hpnit Hdly]].
      splits; auto.
      right.
      splits; eauto. 
      inverts Hprio; inverts Hdly.
      unfold WaitTCBblk.
      splits; auto. 
      inverts Hstat.
      eauto.

      (* only suspend *)
      destruct H3 as (Hx22stat & Hdlyt & Htnz).
      unfold V_OSTCBStat in Hstat.
      simpl in Hstat.
      rewrite Hx22stat in Hstat.
      tryfalse.
    }
  }
  - unfolds RHL_WaitPort_Suspend_P. intros. inverts H4.

  Unshelve.
  auto. 
  auto. 
  auto. 
  auto.
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
  unfolds in H0.
  eexists x.
  splits; auto.
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
  destruct Hrl as (Hrl1 & Hrl2 & Hrl2t & Hrl3 & Hrl3t & Hrl4 & Hrl4t & Hrl5 & Hrl5t & Hrlpq & Hrl6 & Hrl7 & Hrlpqs & Hrl8 & Hrl9 & Hrlp & Hrlpt & Hrlps).
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

  unfolds in Hrl2t.
  unfolds.
  intros.
  eapply Hrl2t; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

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

  unfolds in Hrl3t.
  unfolds.
  intros.
  eapply Hrl3t; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.  

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

  unfolds in Hrl4t.
  unfolds.
  intros.
  eapply Hrl4t; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.  

  splits.

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
  
  unfolds in Hrl5t.
  unfolds.
  intros.
  eapply Hrl5t; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.  

  unfolds in Hrlpq.
  unfolds.
  intros.
  eapply Hrlpq; eauto.
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

  unfolds in Hrlpqs.
  unfolds.
  intros.
  eapply Hrlpqs; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

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

  splits.

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

  unfolds in Hrlp.
  unfolds.
  intros.
  eapply Hrlp; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_not_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrlpt.
  unfolds.
  intros.
  eapply Hrlpt; eauto.
  unfolds.
  unfolds in H.
  simpljoin;try splits;auto.
  rewrite Hvp in H.
  inverts H.
  eapply prio_set_rdy_in_tbl_rev with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrlps.
  unfolds.
  intros.
  eapply Hrlps; eauto.
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
  destruct Hrl as (Hrl1 & Hrl2 & Hrl3 & Hrl4 & Hrl5 & Hrlpq & Hrl6 & Hrl7 & Hrlpqs & Hrl8 & Hrl9 & Hrlp & Hrlps).
  splits.

  unfolds in Hrl1.
  unfolds.
  intros.
  lets Hex : Hrl1 H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H0.
  exists x.
  splits; auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl2.
  unfolds.
  intros.
  lets Hex : Hrl2 H.
  inverts H.
  simpljoin;try splits; auto.

  destruct H as [H | H].
  destruct H.
  destruct H6.
  destruct H6.
  unfolds in H7.
  exists x.
  left.
  split; auto.
  left.
  splits; auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  left. 
  splits. eauto.
  right.
  simpljoin.
  unfolds in H7.
  simpljoin.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  right.
  simpljoin. 
  splits. eauto.
  unfolds.
  splits; eauto.
  unfolds in H6.
  simpljoin; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in H6.
  simpljoin; eauto. 

  unfolds in Hrl3.
  unfolds.
  intros.
  lets Hex : Hrl3 H.
  inverts H.
  simpljoin;try splits; auto.

  destruct H as [H | H].
  destruct H.
  destruct H6.
  destruct H6.
  unfolds in H7.
  exists x.
  left.
  split; auto.
  left.
  splits; auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  left. 
  splits. eauto.
  right.
  simpljoin.
  unfolds in H7.
  simpljoin.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  right.
  simpljoin. 
  splits. eauto.
  unfolds.
  splits; eauto.
  unfolds in H6.
  simpljoin; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in H6.
  simpljoin; eauto. 


  unfolds in Hrl4.
  unfolds.
  intros.
  lets Hex : Hrl4 H.
  inverts H.
  simpljoin;try splits; auto.
  destruct H as [H | H].
  destruct H.
  destruct H6.
  destruct H6.
  unfolds in H7.
  exists x.
  left.
  split; auto.
  left.
  splits; auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  left. 
  splits. eauto.
  right.
  simpljoin.
  unfolds in H7.
  simpljoin.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  right.
  simpljoin. 
  splits. eauto.
  unfolds.
  splits; eauto.
  unfolds in H6.
  simpljoin; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in H6.
  simpljoin; eauto. 

  unfolds in Hrl5.
  unfolds.
  intros.
  lets Hex : Hrl5 H.
  inverts H.
  simpljoin;try splits; auto.
  destruct H as [H | H].
  destruct H.
  destruct H6.
  destruct H6.
  unfolds in H7.
  exists x.
  left.
  split; auto.
  left.
  splits; auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  left. 
  splits. eauto.
  right.
  simpljoin.
  unfolds in H7.
  simpljoin.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  eexists.
  right.
  simpljoin. 
  splits. eauto.
  unfolds.
  splits; eauto.
  unfolds in H6.
  simpljoin; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.
  unfolds in H6.
  simpljoin; eauto. 

  
  unfolds in Hrlpq.
  unfolds.
  intros.
  lets Hex : Hrlpq H.
  inverts H.
  simpljoin;try splits; auto.
  unfolds in H0.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.



  unfolds in Hrl6.
  unfolds.
  intros.
  lets Hex : Hrl6 H.
  inverts H.
  simpljoin;try splits; auto.

  destruct H as [H | H].
  destruct H.
  destruct H.
  unfolds in H6.
  left.
  simpljoin;try splits; auto.
  eexists x.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  destruct H.
  unfolds in H6.
  right.
  simpljoin;try splits; auto.
  unfolds.
  splits; eauto. 
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  splits.

  unfolds in Hrl7.
  unfolds.
  intros.
  lets Hex : Hrl7 H.
  inverts H.
  simpljoin;try splits; auto.
  
  destruct H as [H | H].
  destruct H.
  destruct H.
  unfolds in H6.
  left.
  simpljoin;try splits; auto.
  eexists x.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  destruct H.
  unfolds in H6.
  right.
  simpljoin;try splits; auto.
  unfolds.
  splits; eauto. 
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrlpqs.
  unfolds.
  intros.
  lets Hex : Hrlpqs H.
  inverts H.
  simpljoin;try splits; auto.
  
  unfolds in H0.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl8.
  unfolds.
  intros.
  lets Hex : Hrl8 H.
  inverts H.
  simpljoin;try splits; auto.
  
  destruct H as [H | H].
  destruct H.
  destruct H.
  unfolds in H6.
  left.
  simpljoin;try splits; auto.
  eexists x.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  destruct H.
  unfolds in H6.
  right.
  simpljoin;try splits; auto.
  unfolds.
  splits; eauto. 
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrl9.
  unfolds.
  intros.
  lets Hex : Hrl9 H.
  inverts H.
  simpljoin;try splits; auto.
  
  destruct H as [H | H].
  destruct H.
  destruct H.
  unfolds in H6.
  left.
  simpljoin;try splits; auto.
  eexists x.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  destruct H.
  unfolds in H6.
  right.
  simpljoin;try splits; auto.
  unfolds.
  splits; eauto. 
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  
  unfolds in Hrlp.
  unfolds.
  intros.
  lets Hex : Hrlp H.
  inverts H.
  simpljoin;try splits; auto.

  destruct H as [H | H].
  destruct H.
  destruct H.
  destruct H6.
  destruct H6.
  unfolds in H7.
  left.
  exists x.
  splits; eauto.
  left.
  split; auto.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  left.
  exists x.
  splits; eauto.
  right.
  simpljoin;try splits; auto.
  unfolds in H7.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  
  right.
  simpljoin;try splits; auto.
  unfolds in H6.
  unfolds.
  simpljoin;try splits; auto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  unfolds in Hrlps.
  unfolds.
  intros.
  lets Hex : Hrlps H.
  inverts H.
  simpljoin;try splits; auto.

    
  destruct H as [H | H].
  destruct H.
  destruct H.
  unfolds in H6.
  left.
  simpljoin;try splits; auto.
  eexists x.
  splits; eauto.
  unfolds.
  splits; eauto.
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  destruct H.
  unfolds in H6.
  right.
  simpljoin;try splits; auto.
  unfolds.
  splits; eauto. 
  eapply prio_set_rdy_not_in_tbl with (prio0 := prio0) (prio := prio); eauto.

  Unshelve.
  auto. auto. auto. auto. 
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
    destruct H as [Q_P [SEM_P [MBOX_P [MUTEX_P PORT_P]]]].

    rename H2 into HH2.
    rename H3 into H2.
    rename H4 into H3.

    split. {
      unfold RLH_ECB_ETbl_Q_P in *.
      destruct a. destruct p. intros. lets temp: Q_P prio0 H H4.
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
      destruct a. destruct p. intros. lets temp: SEM_P prio0 H H4.
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
      destruct a. destruct p. intros. lets temp: MBOX_P prio0 H H4.
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
      unfold RLH_ECB_ETbl_MUTEX_P.
      destruct a. destruct p. intros. lets temp: MUTEX_P prio0 H H4.
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
      unfold RLH_ECB_ETbl_PORT_P.
      destruct a. destruct p. intros. lets temp: PORT_P prio0 H H4.
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
    destruct H1 as [Q_P [SEM_P [MBOX_P [MUTEX_P PORT_P]]]].

    split. {
      unfold RHL_ECB_ETbl_Q_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply Q_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply Q_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_SEM_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply SEM_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply SEM_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_MBOX_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply MBOX_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply MBOX_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split. {
      unfold RHL_ECB_ETbl_MUTEX_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply MUTEX_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply MUTEX_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    {
      unfold RHL_ECB_ETbl_PORT_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply PORT_P. inverts H5.
        rewrite TcbMod.map_get_set in H1.
        inverts H1. eauto.
      + eapply PORT_P. rewrite TcbMod.map_get_set' in H1.
        eauto. auto.
    }

    split.
    unfold R_ECB_PETbl_P in *.
    simpljoin.
    split.


    {
      unfold RLH_ECB_PETbl_Q_P.
      destruct a. destruct p. intros.
      unfolds in H.
      lets temp: H prio0 H4 H5.
      simpljoin.
      eexists x.
      unfold join,get,sig in *; simpl in *.
      assert (x = (b, Int.zero) \/ x <> (b, Int.zero)) as choice by tauto.
      destruct choice.
      + inverts H7.
      rewrite H0 in H6. inverts H6.
      rewrite TcbMod.map_get_set. eauto.
    + simpl. rewrite TcbMod.map_get_set'. eauto. auto.
    }

    {
      unfold RHL_ECB_PETbl_Q_P in *.
      destruct a. destruct p. intros.
      assert (tid = (b, Int.zero) \/ tid <> (b, Int.zero)) as choice by tauto.
      unfold join,get,sig in *; simpl in *.
      destruct choice.
      + eapply H2. inverts H5.
        rewrite TcbMod.map_get_set in H4.
        inverts H4. eauto.
      + eapply H2. rewrite TcbMod.map_get_set' in H4.
        eauto. auto.
    }

    destruct mqls. tryfalse.
    destruct a. destruct p. 
    destruct H3 as [x [mqls' [v' [P1 [P2 [P3]]]]]].
    eexists x. eexists mqls'. eexists v'.
    repeat split; auto.
    apply IHls.
    auto. eauto.
Qed.

Lemma RH_TCBList_ECBList_P_resume:
  forall ecbls tcb tid prio st msg tid' sus,
    RH_TCBList_ECBList_P ecbls tcb tid' ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    RH_TCBList_ECBList_P ecbls (TcbMod.set tcb tid (prio, st, msg, false)) tid'.
Proof.
intros.
unfold RH_TCBList_ECBList_P in *. simpljoin. splits.
rename H4 into Hport.
* unfold RH_TCBList_ECBList_Q_P in *.
  simpljoin. 
  rename H4 into HH4.
  rename H5 into H4.
  rename H6 into HH6.
  splits.
  + intros.
    pose proof (H eid x y pqwaitset qwaitset tid0 H5) as H.
    assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
    simpljoin.
    destruct choice.
    - rewrite H7. rewrite TcbMod.map_get_set.
      unfold get in H; simpl in H. rewrite H7 in H0.
      rewrite H in H0. inverts H0. eauto.
    - rewrite TcbMod.map_get_set'. eauto. auto.
  + intros.
    pose proof (HH4 eid x y pqwaitset qwaitset tid0 H5) as HH4.
    assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
    simpljoin.
    destruct choice.
    - rewrite H8. rewrite TcbMod.map_get_set.
      unfold get in H6; simpl in H6. rewrite H8 in H0.
      rewrite H6 in H0. inverts H0. eauto.
    - rewrite TcbMod.map_get_set'. eauto. auto.
  + intros.
    assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
    destruct choice.
    - eapply H4. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
      inverts H5. unfold get in H0; simpl in H0.
      rewrite H6 in H0. eauto.
    - eapply H4. rewrite TcbMod.map_get_set' in H5.
      unfold get; simpl. eauto. auto.
  + intros.
    assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
    destruct choice.
    - eapply HH6. rewrite H6 in H5. rewrite TcbMod.map_get_set in H5.
      inverts H5. unfold get in H0; simpl in H0.
      rewrite H6 in H0. eauto.
    - eapply HH6. rewrite TcbMod.map_get_set' in H5.
      unfold get; simpl. eauto. auto.
* unfold RH_TCBList_ECBList_SEM_P in *.
  rename H4 into Hport.
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
  rename H4 into Hport.
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
  rename H4 into Hport.
  destruct H3. split.
  + intros.
    pose proof (H3 eid n1 n2 wls tid0 H5) as H3.
    simpljoin.
    rename H8 into HH8.
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
  - split.
    destruct H4. destruct H5. rename H6 into HH6.
    unfold RH_TCBList_ECBList_MUTEX_OWNER in *.
    intros.
    pose proof (H5 eid pr wls opr tid0 H6) as H5.
    simpljoin.
    assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
    destruct choice. rewrite H8. rewrite TcbMod.map_get_set.
    split; auto.
    eauto.
    split; auto.  
    rewrite TcbMod.map_get_set'. eauto. auto.

    destruct H4. destruct H5. 
    unfold RH_TCBList_ECBList_MUTEX_OWNER_P in *.
    unfolds in H5.
    simpljoin.
    rename H6 into HH6.
    rename H7 into HH7.
    rename H8 into HH8.
    splits.
    {
      intros.
      pose proof (HH6 eid pip wls H6) as HH6.
      unfold os_inv.prio_available in *.
      intros.
      assert (tid = t \/ tid <> t) as choice by tauto.
      destruct choice.
      eapply HH6. rewrite H8 in H7.
      rewrite TcbMod.map_get_set in H7.
      inverts H7. unfold get in H0; simpl in H0.
      unfold get; simpl. eauto.
      eapply HH6.
      rewrite TcbMod.map_get_set' in H7. 
      unfold get; simpl. eauto. auto.
    }
    {

      Set Nested Proofs Allowed.
      Lemma prio_avail_preserve:
        forall tls tls' tid prio st msg sus els, 
          get tls tid = Some (prio, st, msg, sus) ->
          tls' = TcbMod.set tls tid (prio, st, msg, false) ->
          (
            forall eid pip wls tid0 pt st m prio sus,
              get els eid = Some (absmutexsem pip (Some (tid0, pt)), wls) ->
              get tls tid0 = Some (prio, st, m, sus) ->
              ~In tid0 wls ->
              prio <> pip ->
              os_inv.prio_available pip tls
          ) -> 
          (forall eid pip wls tid0 pt st m prio sus,
              get els eid = Some (absmutexsem pip (Some (tid0, pt)), wls) ->
              get tls' tid0 = Some (prio, st, m, sus) ->
              ~In tid0 wls ->
              prio <> pip ->
              os_inv.prio_available pip tls'
          ).
      Proof.
        introv Hgt Ht' Hpa.
        introv He Hgt't0 Hnin0 Hne0.
        subst tls'.
        casetac tid tid0 Ht Hf.
        - subst.
          rewrite set_a_get_a in Hgt't0.
          inverts Hgt't0.
          unfold os_inv.prio_available in *.
          introv Hgt_.
          casetac tid0 t Ht_ Hf_.
          + subst.
            rewrite set_a_get_a in Hgt_.
            inverts Hgt_.
            eapply Hpa; eauto.
          + rewrite set_a_get_a' in Hgt_; eauto.
        - rewrite set_a_get_a' in Hgt't0; eauto.
          unfold os_inv.prio_available in *.
          introv Hgt_.
          casetac tid t Ht_ Hf_.
          + subst.
            rewrite set_a_get_a in Hgt_.
            inverts Hgt_.
            eapply Hpa; eauto.
          + rewrite set_a_get_a' in Hgt_; eauto.
      Qed. 
      eapply prio_avail_preserve; eauto. 
    }
    {
      intros.
      pose proof (HH8 eid1 eid2 pip1 pip2 ow1 ow2 wls1 wls2 H6 H7 H8) as HH8.
      auto.
    }
    * rename H4 into HH4.
    unfold RH_TCBList_ECBList_PORT_P in *.
    destruct HH4. split.
    + intros.
      pose proof (H4 eid wls tid0 H6) as H4.
      simpljoin.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - rewrite H8. rewrite TcbMod.map_get_set.
        unfold get in H4; simpl in H4. rewrite H8 in H0.
        rewrite H4 in H0. inverts H0. eauto.
      - rewrite TcbMod.map_get_set'. eauto. auto.
    + intros.
      assert (tid = tid0 \/ tid <> tid0) as choice by tauto.
      destruct choice.
      - eapply H5. rewrite H7 in H6. rewrite TcbMod.map_get_set in H6.
        inverts H6. unfold get in H0; simpl in H0.
        rewrite H7 in H0. eauto.
      - eapply H5. rewrite TcbMod.map_get_set' in H6.
        unfold get; simpl. eauto. auto.
Qed.


Lemma R_PrioTbl_P_resume:
  forall vl tcb tid prio st msg adrv sus,
    R_PrioTbl_P vl tcb adrv ->
    TcbMod.get tcb tid = Some (prio, st, msg, sus) ->
    R_PrioTbl_P vl (TcbMod.set tcb tid (prio, st, msg, false)) adrv.
Proof.
  intros.
  unfold R_PrioTbl_P in *.
  simpljoin. splits.
  * clear - H H0.
    intros. pose proof (H prio0 tcbid H1 H2 H3) as H.
    do 3 destruct H.
    assert (tid = tcbid \/ tid <> tcbid) as choice by tauto.
    destruct choice.
    + rewrite H4. rewrite TcbMod.map_get_set.
      rewrite <- H4 in H. unfold get in H; simpl in H.
      rewrite H in H0. inverts H0. eauto.
    + rewrite TcbMod.map_get_set'.
      unfold get in H; simpl in H. eauto. auto.
  * clear - H H0 H1.
    intros.
    assert (tid = tcbid \/ tid <> tcbid) as choice by tauto.
    destruct choice.
    + eapply H1. rewrite H3 in H0.
      unfold get; simpl. rewrite H3 in H2. rewrite TcbMod.map_get_set in H2.
      inverts H2. eauto.
    + eapply H1. rewrite TcbMod.map_get_set' in H2.
      unfold get; simpl. eauto. auto.
  * eapply R_Prio_NoChange_Prio_hold; eauto.
Qed.

(* In OSTimeTickPure.v*)
Lemma rl_rtbl_priotbl_p_set_hold:
  forall next pre eptr msg stat dly i1 i2 i3 i4 i5  v1 v3 ptbl x rtbl vhold,
    x <> vhold ->
    RL_TCBblk_P
      (next
         :: pre
         :: eptr
         :: msg
         :: stat
         :: dly
         :: Vint32 i1
         :: Vint32 i2
         :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: nil) ->
    nth_val (Z.to_nat (Int.unsigned i3)) rtbl = Some v1  ->
    or v1 (Vint32 i4) = Some v3 ->
    RL_RTbl_PrioTbl_P rtbl ptbl vhold ->
    nth_val (nat_of_Z (Int.unsigned i1)) ptbl = Some (Vptr x) ->
    RL_RTbl_PrioTbl_P (update_nth_val (Z.to_nat (Int.unsigned i3)) rtbl v3) ptbl vhold.
Proof.
  introv Hnvhold Hrl Hnth Hor Hrb Htn.
  unfolds in Hrl.
  mytac.
  simpl_hyp.
  remember ((Int.shru x0 ($ 3))) as py.
  remember ((x0&ᵢ$ 7)) as px.
  unfolds in Hor.
  destruct v1; tryfalse.
  inverts Hor.
  unfolds in Hrb.
  unfolds.
  introv Hra Hpr.
  assert (p = x0 \/ p <> x0) by tauto.
  destruct H.
  subst.
  eauto.
  eapply Hrb; eauto.
  subst py.
  eapply prio_set_rdy_in_tbl_rev with (prio:= x0); eauto.
  subst px.
  auto.
Qed.


Lemma int_eq_true_eq : forall i1 i2, Int.eq i1 i2 = true -> i1 = i2.
Proof.
  intros.
  pose proof Int.eq_spec i1 i2.
  rewrite H in H0.
  auto.
Qed.

Lemma int_eq_false_eq : forall i1 i2, Int.eq i1 i2 = false -> i1 <> i2.
Proof.
  intros.
  pose proof Int.eq_spec i1 i2.
  rewrite H in H0.
  auto.
Qed.

Lemma statsus_and_not_statsus_eq_rdy : $ OS_STAT_SUSPEND&ᵢInt.not ($ OS_STAT_SUSPEND) = $ OS_STAT_RDY.
Proof.
  unfold OS_STAT_SUSPEND, OS_STAT_RDY.
  unfold Int.not.
  unfold Int.xor.
  unfold Z.lxor.
  int auto.
  compute.
  int auto.
Qed.

Lemma stat_imp_or_not_sus_eq_stat: forall stat,
    stat = ($ OS_STAT_SEM) \/ stat = ($ OS_STAT_Q) \/ 
    stat = ($ OS_STAT_MBOX) \/ stat = ($ OS_STAT_MUTEX) ->
    Int.or stat ($ OS_STAT_SUSPEND) &ᵢ Int.not ($ OS_STAT_SUSPEND) = stat.
Proof.
  unfold OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_RDY.
  unfold Int.not.
  unfold Int.xor.
  unfold Z.lxor.
  unfold Int.or.
  unfold Z.lor.
  unfold Pos.lor.
  intros.
  destruct H.
  inverts H.
  int auto.
  compute.
  int auto.
  destruct H.
  inverts H.
  int auto.
  compute.
  int auto.
  destruct H.
  inverts H.
  int auto.
  compute.
  int auto.
  inverts H.
  int auto.
  compute.
  int auto.
Qed.

Lemma stat_andsus_notrdy_imp_not_sus: forall stat,
stat = $ OS_STAT_RDY \/
stat = $ OS_STAT_SUSPEND \/
stat = $ OS_STAT_SEM \/
stat = $ OS_STAT_Q \/
stat = $ OS_STAT_MBOX \/
stat = $ OS_STAT_MUTEX \/
stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/ stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND)
-> 
stat&ᵢ$ OS_STAT_SUSPEND <> $ OS_STAT_RDY
-> 
stat = $ OS_STAT_SUSPEND \/ stat = ($ OS_STAT_SEM) \/ stat = ($ OS_STAT_Q) \/ 
stat = ($ OS_STAT_MBOX) \/ stat = ($ OS_STAT_MUTEX) \/
stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND).
Proof.
  intros.
  unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX in *.
  destruct H.
  inverts H.
  destruct H0.
  eauto.
  destruct H.
  inverts H.
  eauto.
  destruct H.
  inverts H.
  eauto.
  destruct H.
  inverts H.
  eauto.
  destruct H.
  inverts H.
  eauto.
  destruct H.
  inverts H.
  do 4 apply or_intror.
  eauto.
  destruct H.
  inverts H.
  do 5 apply or_intror.
  eauto.
  destruct H.
  inverts H.
  do 6 apply or_intror.
  eauto.
  destruct H.
  inverts H.
  do 7 apply or_intror.
  eauto.
  inverts H.
  do 8 apply or_intror.
  eauto.
Qed.

(*
Lemma TCBNode_P_imp_notsus_preserve:
forall x1 x2 x3 x4 x5 (stat:int32) (x7:int32) (rtbl:vallist) (abstcb:(priority * taskstatus * msg * susstatus)),
  TCBNode_P(x1 :: x2 :: x3 :: x4 :: Vint32 x5 :: Vint32 (stat) :: Vint32 x7 :: 
  Vint32 (x7&ᵢ$ 7) :: Vint32 (x7 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(x7&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(x7 >>ᵢ $ 3)) :: nil) rtbl abstcb
/\
(stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SUSPEND) \/
stat = ($ OS_STAT_SEM) \/ stat = ($ OS_STAT_Q) \/ 
stat = ($ OS_STAT_MBOX) \/ stat = ($ OS_STAT_MUTEX) \/
stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))
->
Int.eq (stat&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = false
->
exists stat',
(stat' = ($ OS_STAT_SUSPEND) \/
stat' = ($ OS_STAT_SEM) \/ stat' = ($ OS_STAT_Q) \/ 
stat' = ($ OS_STAT_MBOX) \/ stat' = ($ OS_STAT_MUTEX) \/
stat' = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat' = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat' = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
stat' = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))
/\
TCBNode_P(x1 :: x2 :: x3 :: x4 :: Vint32 x5 :: Vint32 (stat'&ᵢ$ OS_STAT_SUSPEND) :: Vint32 x7 :: 
Vint32 (x7&ᵢ$ 7) :: Vint32 (x7 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(x7&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(x7 >>ᵢ $ 3)) :: nil) rtbl abstcb.
Proof.
  intros.
  destruct H as (HP & Hstat).
  apply stat_andsus_notrdy_imp_not_sus in Hstat.
  destruct Hstat as [Hsus | [Hsem | [Hq | [Hmbox | [Hmutex | Hstat]]]]].

  eapply int_eq_false_eq in H0.

  exists ($ OS_STAT_SUSPEND).
  rewrite Hsus in HP.
  split.
  auto.
  auto.

  exists (Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)).
  rewrite Hsem in HP.
  split.
  right. right. right. right. right. left.
  auto.
  assert(Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND)&ᵢ$ OS_STAT_SUSPEND = $ OS_STAT_SEM).
  {
    unfold OS_STAT_SEM, OS_STAT_SUSPEND.
    mauto.
  }
  rewrite H.
  auto.

  
  exists ($ OS_STAT_Q).
  rewrite Hq in HP.
  split.
  auto.
  auto.

    
  exists ($ OS_STAT_MBOX).
  rewrite Hmbox in HP.
  split.
  auto.
  auto.
    
  exists ($ OS_STAT_MUTEX).
  rewrite Hmutex in HP.
  split.
  right. right. right. right. left.
  auto.
  auto.

  destruct Hstat as  [Hsem | [Hq | [Hmbox | Hmutex]]].
      
  exists ($ OS_STAT_MUTEX).
  rewrite Hmutex in HP.
  split.
  right. right. right. right. left.
  auto.
  auto.

  unfold TCBNode_P in *.
  destruct abstcb. destruct p. destruct p.
  simpljoin.
  splits;eauto.
  
  destruct H0.
  
  * inverts Hsem.
    auto.
  * inverts Hsus.
    auto.
Qed. 
*)

(* Lemma TCBNode_P_imp_notsus_preserve:
forall x1 x2 x3 x4 x5 (stat:int32) (stat':int32) (x7:int32) (rtbl:vallist) (abstcb:(priority * taskstatus * msg * susstatus)),
  TCBNode_P(x1 :: x2 :: x3 :: x4 :: Vint32 x5 :: Vint32 (stat) :: Vint32 x7 :: 
  Vint32 (x7&ᵢ$ 7) :: Vint32 (x7 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(x7&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(x7 >>ᵢ $ 3)) :: nil) rtbl abstcb
/\
(stat = ($ OS_STAT_RDY) \/ stat = ($ OS_STAT_SUSPEND) \/
stat = ($ OS_STAT_SEM) \/ stat = ($ OS_STAT_Q) \/ 
stat = ($ OS_STAT_MBOX) \/ stat = ($ OS_STAT_MUTEX) \/
stat = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
stat = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))
->
Int.eq (stat&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = false
->
(stat' = ($ OS_STAT_SUSPEND) \/
stat' = ($ OS_STAT_SEM) \/ stat' = ($ OS_STAT_Q) \/ 
stat' = ($ OS_STAT_MBOX) \/ stat' = ($ OS_STAT_MUTEX) \/
stat' = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
stat' = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
stat' = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/
stat' = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND))
->
TCBNode_P(x1 :: x2 :: x3 :: x4 :: Vint32 x5 :: Vint32 (stat') :: Vint32 x7 :: 
Vint32 (x7&ᵢ$ 7) :: Vint32 (x7 >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(x7&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(x7 >>ᵢ $ 3)) :: nil) rtbl abstcb.
Proof.
  intros.
  destruct H as (HP & Hstat).
  apply stat_andsus_notrdy_imp_not_sus in Hstat.
  destruct Hstat as [Hsem | [Hsus | [Hmbox | Hmutex]]].

  eapply int_eq_false_eq in H0.
  

  unfold TCBNode_P in *.
  destruct abstcb. destruct p. destruct p.
  simpljoin.
  splits;eauto.
  
  destruct H0.
  
  * inverts Hsem.
    auto.
  * inverts Hsus.
    auto.
Qed. *)



Lemma OSTaskResume_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI new_os_internal OSTaskResume
                vl logicl OSTaskResumePre ct->
    Some r =
    BuildRetI new_os_internal OSTaskResume vl logicl OSTaskResumePost ct->
    exists t d1 d2 s,
      new_os_internal OSTaskResume = Some (t, d1, d2, s) /\
      {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
    init_spec.
    rename v'2 into vier.
    rename v'1 into opv.
    (* If (prio′ ≥ ′OS_LOWEST_PRIO) { *)
    lzh_hoare_if; pure_auto.

    change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
    assert (Hopv: opv = Vint32 (Int.repr OS_PRIO_INVALID) \/ opv <>Vint32 (Int.repr OS_PRIO_INVALID)) by tauto.
    destruct Hopv. 
    subst.
    (* opv = Vint32 (Int.repr OS_PRIO_INVALID) *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_prio_invalid'.
    auto.
    can_change_aop_solver.
    pure_auto.
    right.
    symmetry in HeqH0.
    rewrite Int.eq_sym.
    eauto.

    hoare forward.
    unfold OS_PRIO_INVALID.
    splits; eauto.
    mauto.
    mauto.

    (* opv <> Vint32 (Int.repr OS_PRIO_INVALID) *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_prio_invalid_abt'.
    auto.
    can_change_aop_solver.
    pure_auto.
    right.
    symmetry in HeqH3.
    rewrite Int.eq_sym.
    eauto.
    eapply absabort_rule.

    rename H into HH.


    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    unfold AOSTCBList.
    hoare_split_pure_all.

    rename v'16 into vpthattr.
    rename v'17 into vcspace.
    rename v'18 into v18. 
    rename v'19 into v19. 
    rename v'20 into v20. 

    rename v'21 into v'19.
    rename v'22 into v'20.
    rename v'23 into v'21.
    rename v'24 into v'22.

    rename v'15 into v15.
    rename v'11 into v'15.
    rename v'12 into v'16.
    rename v'13 into v'17.
    rename v'14 into v'18.

       
    rename v'10 into v'14.
    rename v'9 into v'13.
    rename v'8 into v'12.
    rename v'7 into v'11.
    rename v'6 into v'10.
    rename v'5 into v'9.
    rename v'4 into v'8.
    rename v'3 into v'7.
    rename v'2 into v'6.
    rename v'1 into v'5.

    lets v'1 : v'.
    lets v'2 : v'.
    lets v'3 : v'.
    lets v'4 : v'.
    
    hoare unfold.

    rename H9 into HH9.
    rename H10 into H9.


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

    assert(~
    (exists tid st0 msg sus0,
     TcbMod.get tcbls tid = Some (i, st0, msg, sus0))) as Hnotcb.
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

    change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
    assert (Hopv: opv = Vint32 (Int.repr OS_TASK_RESUME_PRIO) \/ opv <>Vint32 (Int.repr OS_TASK_RESUME_PRIO)) by tauto.
    destruct Hopv. 
    subst.

   (* opv = Vint32 (Int.repr OS_TASK_RESUME_PRIO) *)
    hoare lifts (3::17::nil)%nat pre.
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_no_such_tcb'.
    auto.
  Optimize Proof.
  Optimize Heap.
    can_change_aop_solver.
    auto.

    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.

    sep cancel APthreadAttr.
    sep cancel EvtInv .
    sep cancel CoreCommuInv .
    sep cancel PartitionInv .
    sep cancel CapabilityInv .
    sep cancel p_local.
    sep cancel Aier.

    unfold AOSTCBList.
    sep pauto; eauto.
    
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
    auto.
    auto.
    eauto.
    go.

    (* RETURN ′OS_TASK_RESUME_PRIO *)
    hoare forward.
    unfold OS_TASK_RESUME_PRIO.
    splits; eauto.
    int auto.
    int auto.
    change Byte.max_unsigned with 255. lia.

    (* opv <> Vint32 (Int.repr OS_TASK_RESUME_PRIO) *)
    hoare lifts (3::17::nil)%nat pre.
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_no_such_tcb_abt'.
    auto.

    can_change_aop_solver.    
    auto.
    eapply absabort_rule.



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
      assert(~
      (exists tid st0 msg sus0,
       TcbMod.get tcbls tid = Some (i, st0, msg, sus0))) as Hnotcb.
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

      change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
      assert (Hopv: opv = Vint32 (Int.repr OS_TASK_RESUME_PRIO) \/ opv <>Vint32 (Int.repr OS_TASK_RESUME_PRIO)) by tauto.
      destruct Hopv. 
      subst.

      (* opv <> Vint32 (Int.repr OS_TASK_RESUME_PRIO) *)
      hoare lifts (3::17::nil)%nat pre.
      hoare abscsq.
      apply noabs_oslinv.
      eapply absimp_taskres_no_such_tcb'.
      auto.
      go.
      auto.

      hoare forward prim.

      sep cancel APthreadAttr.
      sep cancel EvtInv .
      sep cancel CoreCommuInv .
      sep cancel PartitionInv .
      sep cancel CapabilityInv .
      sep cancel p_local.
      sep cancel Aier.

      unfold AOSTCBPrioTbl.
      unfold AOSTCBList.
      sep pauto.

      unfold tcbdllseg.
      sep cancel 4%nat 1%nat.
      
      unfold1 dllseg.
      unfold node.
      sep pauto.
      eauto.
      eauto.
      auto.
      auto.
      go.

      hoare forward.
      unfold OS_TASK_RESUME_PRIO.
      splits; eauto.
      int auto.
      int auto.
      change Byte.max_unsigned with 255.
      lia.

    (* opv <> Vint32 (Int.repr OS_TASK_RESUME_PRIO) *)
    hoare lifts (3::17::nil)%nat pre.
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_no_such_tcb_abt'.
    auto.

    can_change_aop_solver.    
    auto.
  Optimize Proof.
  Optimize Heap.
    eapply absabort_rule.
    }


    (* If ((ptcb ′ → OSTCBStat &ₑ ′ OS_STAT_SUSPEND) ==ₑ ′ OS_STAT_RDY) *)
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
    instantiate(1 := (
      [|ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'6 (l1++tcbcur::l2)|] **
      tcbdllseg v'6 Vnull v'20 Vnull (l1++tcbcur::l2) **
      [|TCBList_P v'6 (l1++tcbcur::l2) rtbl tcbls|] **

      (* Astruct (cur_tcb_blk, Int.zero) OS_TCB_flag tcbcur **
      dllseg v'5 (Vptr (cur_tcb_blk, Int.zero)) v'20 Vnull l2 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
        (fun vl : vallist => nth_val 0 vl) ** *)
       <|| ifun_tasksus_spec.spec_code_cons (taskresumecode ((Vint32 i :: nil) ++ opv :: nil)) v'0 ||>  **
      LV ptcb @ OS_TCB ∗ |-> Vptr toresptr **
      PV vhold @ char_t |-> v'23 **
      GV OSTCBList @ OS_TCB ∗ |-> v'6 **
      (* dllseg v'6 Vnull v'19 (Vptr (cur_tcb_blk, Int.zero)) l1 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
        (fun vl : vallist => nth_val 0 vl) ** *)
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
      AOSMapTbl **
      AOSUnMapTbl **
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      G& OSPlaceHolder @ char_t == vhold **
      HPriotls v15 **
      AOSTCBFreeList v'17 v'18 **
      AOSRdyTbl rtbl **
      AOSRdyGrp v'12 **
      AOSTime (Vint32 v'15) **
      HTCBList tcbls **
      HTime v'15 **
      HCurTCB (cur_tcb_blk, Int.zero) **
      AGVars **
      APthreadAttr vpthattr **
      EvtInv ecbls v'6 (l1 ++ tcbcur :: l2) tcbls vhold v18 v19 v20 **
      A_isr_is_prop **
      IntInv **
      TmrInv **
      CoreCommuInv ecbls **
      PartitionInv ecbls **
      CapabilityInv vcspace **
      tcbdllflag v'6 (l1 ++ tcbcur :: l2) **
      p_local OSLInv (cur_tcb_blk, Int.zero)
        (logic_val (V$ 1)
         :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
      Aisr empisr **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Aier vier **
      aemp_isr_is ** LV prio @ char_t |-> Vint32 i ** A_dom_lenv ((prio, char_t) :: (ptcb, OS_TCB ∗) :: nil)
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
    lets RL_TCBblk_P_backup: H50.
    unfold RL_TCBblk_P in H50.
    simpljoin.
    inverts H50; inverts H52; inverts H53; inverts H54;
    inverts H55; inverts H56; inverts H63.



    (* If ((ptcb ′ → OSTCBStat &ₑ ′ OS_STAT_SUSPEND) ==ₑ ′ OS_STAT_RDY) *)
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


    hoare unfold.
    instantiate (1:=Afalse).

    assert(Hx22: x22&ᵢ$ OS_STAT_SUSPEND = $ OS_STAT_RDY).
    {
      clear - H50.
      assert (Int.eq (x22&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = true \/ Int.eq (x22&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = false).
      destruct (Int.eq (x22&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY));eauto.
      destruct H.
      apply int_eq_true_eq in H;auto.
      simpl in H50.
      rewrite H in H50.
      simpl in H50; tryfalse.
    }
  
    assert(Hx22stat: x22 = $ OS_STAT_RDY \/ x22 = $ OS_STAT_SEM \/
        x22 = $ OS_STAT_Q \/ x22 = $ OS_STAT_MBOX \/ x22 = $ OS_STAT_MUTEX \/
        x22 = $ OS_STAT_POSTQ \/ x22 = $ OS_STAT_PORT).
    {
      clear - H62 Hx22.
      destruct H62.
      left; auto.

      destruct H.
      rewrite H in Hx22.
      inversion Hx22.
      destruct H. 
      right. left. auto.
      destruct H. 
      right. right. left. auto.
      destruct H.
      right. right. right. left. auto.
      destruct H. 
      right. right. right. right. auto.
      destruct H.
      right. right. right. right. right. auto.
      destruct H.
      right. right. right. right. right. right. auto.

      destruct H.
      rewrite H in Hx22.
      inversion Hx22.

      destruct H.
      rewrite H in Hx22.
      inversion Hx22.
      
      destruct H.
      rewrite H in Hx22.
      inversion Hx22.

      destruct H.
      rewrite H in Hx22.
      inversion Hx22.

      destruct H.
      rewrite H in Hx22.
      inversion Hx22.

      rewrite H in Hx22.
      inversion Hx22.
    }

    (* assert (TcbMod.get tcbls (toresblock, Int.zero) = Some (i, t, m, false)).  *)
    assert (TcbMod.get tcbls (toresblock, Int.zero) = Some (i, st0, m0, false)) as Hextcb. 
    {
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
      inverts abstcbeq.
      
      destruct sus0.
      Focus 2. eauto.

      unfold R_TCB_Status_P in H51.
      simpljoin.

      
      destruct st0.
      unfold RHL_Suspend_P in H49.
      simpljoin.
      pose proof (H49 i m0 (eq_refl(i,rdy,m0,true))).
      simpljoin.
      inverts H58.
      tryfalse.
      
      unfold RHL_TCB_Status_Wait_P in H54.
      destruct H54 as [RHLwait [RHLwaits [RHLwaitq [RHLwaitmb
      [RHLwaitms [RHLwaitpostq [RHLwaitssus [RHLwaitqsus [RHLwaitpostqsus [RHLwaitmbsus [RHLwaitmssus [RHLwaitport RHLwaitportsus]]]]]]]]]]]].

      destruct t.
      - unfold RHL_WaitS_Suspend_P in RHLwaitssus.
        pose proof (RHLwaitssus i e o m0 (eq_refl((i, wait (os_stat_sem e) o, m0, true)))).
        simpljoin.
        inverts H56.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.
      - unfold RHL_WaitQ_Suspend_P in RHLwaitqsus.
        pose proof (RHLwaitqsus i e o m0 (eq_refl((i, wait (os_stat_q e) o, m0, true)))).
        simpljoin.
        inverts H56.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.
      - unfold RHL_WaitPostQ_Suspend_P in RHLwaitpostqsus.
        pose proof (RHLwaitpostqsus i e o m0 (eq_refl((i, wait (os_stat_postq e) o, m0, true)))).
        simpljoin.
        inverts H58.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.        
      - unfold RHL_Suspend_P in H49.
        simpljoin.
        pose proof (H54 i o m0 (eq_refl((i, wait os_stat_time o, m0, true)))).
        simpljoin.
        inverts H59.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.
      - unfold RHL_WaitMB_Suspend_P in RHLwaitmbsus.
        pose proof (RHLwaitmbsus i e o m0 (eq_refl((i, wait (os_stat_mbox e) o, m0, true)))).
        simpljoin.
        inverts H56.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.
      - unfold RHL_WaitMS_Suspend_P in RHLwaitmssus.
        pose proof (RHLwaitmssus i e o m0 (eq_refl((i, wait (os_stat_mutexsem e) o, m0, true)))).
        simpljoin.
        inverts H56.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.
      - unfold RHL_WaitPort_Suspend_P in RHLwaitportsus.
        pose proof (RHLwaitportsus i e o m0 (eq_refl((i, wait (os_stat_port e) o, m0, true)))).
        simpljoin.
        inverts H56.
        destruct Hx22stat as [Hrdy | [Hsem | [Hq | [Hmbox | [Hmutex | [Hpostq | Hport]]]]]].
        inverts Hrdy.
        inverts Hsem.
        inverts Hq.
        inverts Hmbox.
        inverts Hmutex.
        inverts Hpostq.
        inverts Hport.
    }
    
    (*
    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_not_suspended.
    go.
    eauto.
*)

  (* Recombine the tcbdllseg *)
  eapply backward_rule1.
  intros.


  instantiate(1:= (
    [|ptr_in_tcbdllseg (Vptr (toresblock, Int.zero)) v'6
    (v'7 ++
     (x0
      :: v'9
         :: x23
            :: m
               :: Vint32 i13
                  :: Vint32 x22
                     :: Vint32 p
                        :: Vint32 (p&ᵢ$ 7)
                           :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
     :: v'8)|] **
    tcbdllseg v'6 Vnull v'20 Vnull (v'7 ++
    (x0
     :: v'9
        :: x23
           :: m
              :: Vint32 i13
                 :: Vint32 x22
                    :: Vint32 p
                       :: Vint32 (p&ᵢ$ 7)
                          :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
    :: v'8) **
    [|TCBList_P v'6
    (v'7 ++
     (x0
      :: v'9
         :: x23
            :: m
               :: Vint32 i13
                  :: Vint32 x22
                     :: Vint32 p
                        :: Vint32 (p&ᵢ$ 7)
                           :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
     :: v'8) rtbl tcbls|] **

    (* Astruct (toresblock, Int.zero) OS_TCB_flag
          (x0
           :: v'9
              :: x23
                 :: m
                    :: Vint32 i13
                       :: Vint32 x22
                          :: Vint32 p
                             :: Vint32 (p&ᵢ$ 7)
                                :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) **
        dllseg x0 (Vptr (toresblock, Int.zero)) v'20 Vnull v'8 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
          (fun vl : vallist => nth_val 0 vl) **
        dllseg v'6 Vnull v'9 (Vptr (toresblock, Int.zero)) v'7 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
          (fun vl : vallist => nth_val 0 vl) ** *)
         <|| ifun_tasksus_spec.spec_code_cons (taskresumecode ((Vint32 i :: nil) ++ opv :: nil)) v'0 ||>  ** 
        LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) **
        PV vhold @ char_t |-> v'23 **
        GV OSTCBList @ OS_TCB ∗ |-> v'6 **
        GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
        AOSMapTbl **
        AOSUnMapTbl **
        GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
        G& OSPlaceHolder @ char_t == vhold **
        HPriotls v15 **
        AOSTCBFreeList v'17 v'18 **
        AOSRdyTbl rtbl **
        AOSRdyGrp v'12 ** AOSTime (Vint32 v'15) ** HTCBList tcbls ** HTime v'15 ** HCurTCB (cur_tcb_blk, Int.zero) **
        AGVars **
        APthreadAttr vpthattr **
        EvtInv ecbls v'6
          (v'7 ++
           (x0
            :: v'9
               :: x23
                  :: m
                     :: Vint32 i13
                        :: Vint32 x22
                           :: Vint32 p
                              :: Vint32 (p&ᵢ$ 7)
                                 :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
           :: v'8) tcbls vhold v18 v19 v20 **
        A_isr_is_prop **
        IntInv **
        TmrInv **
        CoreCommuInv ecbls **
        PartitionInv ecbls **
        CapabilityInv vcspace **
        tcbdllflag v'6
          (v'7 ++
           (x0
            :: v'9
               :: x23
                  :: m
                     :: Vint32 i13
                        :: Vint32 x22
                           :: Vint32 p
                              :: Vint32 (p&ᵢ$ 7)
                                 :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
           :: v'8) **
        p_local OSLInv (cur_tcb_blk, Int.zero)
          (logic_val (V$ 1)
           :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
        Aisr empisr **
        Aie false **
        Ais nil **
        Acs (true :: nil) **
        Aier vier **
        aemp_isr_is ** LV prio @ char_t |-> Vint32 i ** A_dom_lenv ((prio, char_t) :: (ptcb, OS_TCB ∗) :: nil)
  )).

  eapply tcbdllseg_combine.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel Aop.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep pauto.
  split; auto.
  go.
  eauto.
  eauto.
  auto.
  Optimize Proof.
  Optimize Heap.

  hoare unfold.

  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H47.
  eauto.

  instantiate (1 := Vptr (cur_tcb_blk, Int.zero)).
  auto.
  
  instantiate (1 := tcbls).
  instantiate (1 := rtbl).
  assumption.

  hoare unfold.

  destruct v'14.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H56.
  }

  change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
  assert (Hopv: opv = Vint32 (Int.repr OS_TASK_NOT_SUSPENDED) \/ opv <>Vint32 (Int.repr OS_TASK_NOT_SUSPENDED)) by tauto.
  destruct Hopv. 
  subst.
  
  (* opv = V$ OS_TASK_NOT_SUSPENDED *)
  hoare lifts (3::17::nil)%nat pre.

  hoare abscsq.
  apply noabs_oslinv.
  eapply absimp_taskres_not_suspended'.
  auto.
  go.
  eauto.


    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.


    sep cancel APthreadAttr.
    sep cancel CoreCommuInv.
    sep cancel PartitionInv.
    sep cancel CapabilityInv.
    sep cancel p_local. 
    sep cancel Aier.

    unfold AOSTCBPrioTbl.
    sep pauto.
  
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllseg.
    sep cancel tcbdllseg.

    unfold AOSRdyTblGrp.
    sep pauto.
    sep cancel AOSRdyTbl .
    sep cancel AOSRdyGrp .
    rewrite H47 in H56.
    sep cancel EvtInv.
    sep cancel tcbdllflag.

    instantiate(1 := (
      LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) ** LV prio @ Int8u |-> Vint32 i ** A_dom_lenv ((prio, Int8u) :: (ptcb, OS_TCB ∗) :: nil)
    )).

    sep pauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    go.

    (* (ptcb ′ → OSTCBStat &ₑ ′ OS_STAT_SUSPEND) !=ₑ ′ OS_STAT_RDY *)

    hoare forward.
    unfold OS_TASK_NOT_SUSPENDED.
    splits; auto.
    solve [clear; vm_compute; congruence].
    change Byte.max_unsigned with 255.
    solve [clear; vm_compute; congruence].

    (* opv <> V$ OS_TASK_NOT_SUSPENDED *)

    hoare lifts (3::17::nil)%nat pre.

    hoare abscsq.
    apply noabs_oslinv.
    eapply absimp_taskres_not_suspended_abt'.
    auto.
    go.
    eauto.
    eapply absabort_rule.
    

    hoare forward.
    hoare unfold.
    assert(Int16.max_unsigned < Int.unsigned (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) -> False) as Hmax.
    {
      unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_POSTQ, OS_STAT_PORT in *.
      change Int16.max_unsigned with 65535.
      clear - H62.
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             end.
      all: subst x22.
      all: vm_compute.
      all: congruence.
    }

    (* ptcb ′ → OSTCBStat &= ∼ ′ OS_STAT_SUSPEND;ₛ *)
      hoare forward.
      go.

      remember (TcbMod.set tcbls (toresblock, Int.zero) (i, st0, m0, false))
      as tcbls'.
      protect Heqtcbls'.

      (* If (ptcb ′ → OSTCBStat !=ₑ ′ OS_STAT_RDY) *)
      hoare forward.

    (* ptcb ′ → OSTCBStat !=ₑ ′ OS_STAT_RDY *)

    go.

      sifs.
      sifs.
      instantiate(1:=Afalse).
      hoare unfold.

      assert(Hx22: x22&ᵢ$ OS_STAT_SUSPEND <> $ OS_STAT_RDY).
      {
        clear -H50.        
        assert (Int.eq (x22&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = true \/ Int.eq (x22&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY) = false).
        {
          destruct (Int.eq (x22&ᵢ$ OS_STAT_SUSPEND) ($ OS_STAT_RDY));eauto.
        }
        
        destruct H50.

        destruct H.
        rewrite H in H0. 
        simpl in H0; tryfalse.
        apply int_eq_false_eq in H; auto.

        destruct H. 
        rewrite H in H0. 
        simpl in H0; tryfalse.  
        apply int_eq_false_eq in H; auto.
      }

      assert(Hx22': x22&ᵢInt.not ($ OS_STAT_SUSPEND) <> $ OS_STAT_RDY).
      {
        clear -H2.        
        assert (Int.eq (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY) = true \/ Int.eq (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY) = false).
        {
          destruct (Int.eq (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY));eauto.
        }

        destruct H.
        rewrite H in H2. 
        unfold val_inj in H2.
        unfold notint in H2.
        assert (Int.notbool Int.one = Int.zero) by mauto.
        rewrite H0 in H2.
        tryfalse.

        apply int_eq_false_eq in H; auto.
      }

      assert (Hx22stat: x22 = Int.or ($ OS_STAT_SEM) ($ OS_STAT_SUSPEND) \/
      x22 = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND) \/
      x22 = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND) \/
      x22 = Int.or ($ OS_STAT_MBOX) ($ OS_STAT_SUSPEND) \/ 
      x22 = Int.or ($ OS_STAT_MUTEX) ($ OS_STAT_SUSPEND) \/ 
      x22 = Int.or ($ OS_STAT_PORT) ($ OS_STAT_SUSPEND)).
      {
        clear - H62 Hx22 Hx22'.

        destruct H62.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND in *.
        false.
        destruct Hx22.
        mauto.

        destruct H. 
        rewrite H in Hx22'.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND in *.
        false.
        destruct Hx22'.
        mauto.

        destruct H.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM in *.
        false.
        destruct Hx22.
        mauto.

        destruct H.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_Q in *.
        false.
        destruct Hx22.
        mauto.

        destruct H.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_MBOX  in *.
        false.
        destruct Hx22.
        mauto.

        destruct H.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_MUTEX   in *.
        false.
        destruct Hx22.
        mauto.

        destruct H.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_POSTQ   in *.
        false.
        destruct Hx22.
        mauto.
        
        destruct H.
        rewrite H in Hx22.
        unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_PORT   in *.
        false.
        destruct Hx22.
        mauto.

        destruct H.
        rewrite H. auto.
        destruct H.   
        rewrite H. auto.
        destruct H.
        rewrite H. auto. 
        destruct H.
        rewrite H. auto. 
        destruct H.
        rewrite H. 
        right. right. right. right. auto. 
        rewrite H. 
        right. right. right. right. auto.
      } 


assert ((p, t, m, s)=(i, st0, m0, sus0))as abstcbeq. {
  clear - H13 H23 H25.
  assert(TcbMod.get v'11 (toresblock, Int.zero) = Some (p, t, m, s)). {
    unfolds in H25.
    unfold join, sig in H25.
    simpl in H25.
    apply TcbMod.join_sig_get in H25;eauto.
  }
  assert (TcbMod.get tcbls (toresblock, Int.zero) = Some (p, t, m, s)). {
    eapply TcbMod.join_get_get_r; eauto.
  }
  rewrite H0 in H13.
  inverts H13.
  reflexivity.
}

hoare_lifts_trms_pre (Aop, abstcblist).
eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_taskres_wait_suspend'; eauto.
can_change_aop_solver.
apply absinfer_eq.

assert (Hst_cond: 
(forall eid t, sus0 = true /\
  (st0 = wait (os_stat_sem eid) (Some t) \/
  st0 = wait (os_stat_q eid) (Some t) \/
  st0 = wait (os_stat_mbox eid) (Some t) \/
  st0 = wait (os_stat_mutexsem eid) (Some t) \/
  st0 = wait (os_stat_port eid) (Some t)) -> t <> Int.zero
)
\/ ~(forall eid t, sus0 = true /\
(st0 = wait (os_stat_sem eid) (Some t) \/
st0 = wait (os_stat_q eid) (Some t) \/
st0 = wait (os_stat_mbox eid) (Some t) \/
st0 = wait (os_stat_mutexsem eid) (Some t) \/
st0 = wait (os_stat_port eid) (Some t)) -> t <> Int.zero
)) by tauto.
destruct Hst_cond.
2:{
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_taskres_time_nzero_abt'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
}

eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_taskres_time_nzero'; eauto.
can_change_aop_solver.
apply absinfer_eq.

rename H49 into Htime_nzero.

unfold AOSRdyTbl.
hoare_split_pure_all.
destruct H49.
rename H49 into HHH49.
rename H52 into HHH52.



    assert(TCBList_P (Vptr (toresblock, Int.zero))
      ((x0
        :: v'9
           :: x23
              :: m
                 :: Vint32 i13
                    :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                       :: Vint32 p
                          :: Vint32 (p&ᵢ$ 7)
                             :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) :: v'8)
      rtbl (TcbMod.set v'11 (toresblock, Int.zero) (i, st0, m0, false))).  

    {

      unfold1 TCBList_P.
      do 4 eexists. splits. auto.
      unfolds. simpl. auto.
      eapply tcbjoin_set.
      eauto.

      inverts abstcbeq.
      unfolds.
      unfold1 TCBList_P in backup.
      simpljoin. 
(*       rename x14 into xx14.
      rename x19 into xx19.
      rename H53 into Htnzero.
      rename H54 into H52.
      rename H55 into H53.
      rename H56 into H54.
      rename H58 into H55. *)

      unfold R_TCB_Status_P in H51.

      unfolds in H54. destruct x13; destruct p; destruct p.
      destructs H54.
      splits; auto.
      apply RL_TCBblk_P_resume; auto. 
      eapply R_TCB_Status_P_resume'; auto.
      eauto.
      intros.
      lets bb: Htime_nzero eid time0.
      apply bb in H60.
      auto.
  Optimize Proof.
  Optimize Heap.
      auto.
    }
       
    assert(TCBList_P v'6 v'7 rtbl v'10).
    {
      auto.
    }
      

     assert (TcbMod.join v'10
      (TcbMod.set v'11 (toresblock, Int.zero)
         (i, st0, m0, false)) tcbls'). 
      (*  assert (TcbMod.join v'10 v'11 tcbls'). *) 
    {
      unprotect Heqtcbls'.
      rewrite Heqtcbls'.
      eapply TcbMod.join_set_r. auto.
      clear -H25.
      unfold TcbMod.indom. eexists.
      unfolds in H25.
      unfold join, sig in H25; simpl in H25.
      apply TcbMod.join_sig_get in H25. eauto.
    }

  unfold EvtInv.

  (* Recombine the tcbdllseg *)
  eapply backward_rule1.
  intros.


  instantiate(1 := (
  [|ptr_in_tcbdllseg (Vptr (toresblock, Int.zero)) v'6
  (v'7 ++
   (x0
    :: v'9
       :: x23
          :: m
             :: Vint32 i13
                :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                   :: Vint32 p
                      :: Vint32 (p&ᵢ$ 7)
                         :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
   :: v'8)|] **
  tcbdllseg v'6 Vnull v'20 Vnull (v'7 ++
  (x0
   :: v'9
      :: x23
         :: m
            :: Vint32 i13
               :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                  :: Vint32 p
                     :: Vint32 (p&ᵢ$ 7)
                        :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
  :: v'8) **
  [|TCBList_P v'6
  (v'7 ++
   (x0
    :: v'9
       :: x23
          :: m
             :: Vint32 i13
                :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                   :: Vint32 p
                      :: Vint32 (p&ᵢ$ 7)
                         :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
   :: v'8) rtbl tcbls'|] **

   <|| ifun_tasksus_spec.spec_code_cons
           (taskresume_succ (|Vint32 i :: opv :: nil|);; taskresume_ret (|Vint32 i :: opv :: nil|)
            ?? taskresume_succ (|Vint32 i :: opv :: nil|);; isched;; taskresume_ret (|Vint32 i :: opv :: nil|)) v'0 ||>  **
    LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) **
    (* Astruct (toresblock, Int.zero) OS_TCB_flag
      (x0
       :: v'9
          :: x23
             :: m
                :: Vint32 i13
                   :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                      :: Vint32 p
                         :: Vint32 (p&ᵢ$ 7)
                            :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) **
    dllseg x0 (Vptr (toresblock, Int.zero)) v'20 Vnull v'8 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) **
    dllseg v'6 Vnull v'9 (Vptr (toresblock, Int.zero)) v'7 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** *)
      PV vhold @ char_t |-> v'23 **
      GV OSTCBList @ OS_TCB ∗ |-> v'6 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
      AOSMapTbl **
      AOSUnMapTbl **
      GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
      G& OSPlaceHolder @ char_t == vhold **
      HPriotls v15 **
      AOSTCBFreeList v'17 v'18 **
      GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) rtbl **
      AOSRdyGrp v'12 **
      AOSTime (Vint32 v'15) **
      HTCBList tcbls **
      HTime v'15 **
      HCurTCB (cur_tcb_blk, Int.zero) **
      AGVars **
      APthreadAttr vpthattr **
      (EX (fecbh : val) (eventl : list vallist) (ectrl : list os_inv.EventCtr) (osql qblkl : list vallist)
          (msgql : list EventData) (evatoms : list (addrval * type * val)) (evstructs : list (addrval * type * list val))
          (evarrays : list (addrval * nat * list val)) (sinfol minfol qattrl : list vallist) (semeibs : EmbMod.map)
          (muxeibs : MibMod.map) (qeibs : MqattrMod.map) (pbls : PbMod.map) (ebls : EbMod.map) 
          (locmp : EvAuxLocMod.map) (ptrmp : EvAuxPtrMod.map),
          AOSEventFreeList fecbh eventl **
          AOSQFreeList osql **
          AOSQFreeBlk qblkl **
          AECBList ectrl msgql ecbls tcbls' **
          HECBList ecbls **
          Hebls ebls **
          AErrblkList ebls **
          Hpbls pbls **
          APosblkList pbls **
          HEvAtomHeap evatoms **
          AEvAtomHeap evatoms **
          HEvStructHeap evstructs **
          AEvStructHeap evstructs **
          HEvArrayHeap evarrays **
          AEvArrayHeap evarrays **
          [|R_Q_Data_P evstructs evarrays|] **
          HSEMInfo semeibs **
          ASemEIBs sinfol v18 semeibs ecbls vhold **
          HMuxInfo muxeibs **
          AMuxEIBs minfol v19 muxeibs ecbls vhold **
          HQAttr qeibs **
          AMqEIBs qattrl v20 qeibs ecbls vhold **
          [|vhold = vhold_addr|] **
          [|SEM_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|MUX_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|Q_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|evcre_nodup locmp ptrmp|] **
          [|evdel_nodup locmp ptrmp|] **
          [|eibref_distinct semeibs muxeibs qeibs|] **
          HEvLoc locmp ** HEvPtr ptrmp ** tcbllsegevaux v'6
          (v'7 ++
           (x0
            :: v'9
               :: x23
                  :: m
                     :: Vint32 i13
                        :: Vint32 x22
                           :: Vint32 p
                              :: Vint32 (p&ᵢ$ 7)
                                 :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
           :: v'8) locmp ptrmp) **
      A_isr_is_prop **
      IntInv **
      TmrInv **
      CoreCommuInv ecbls **
      PartitionInv ecbls **
      CapabilityInv vcspace **
    tcbdllflag v'6
      (v'7 ++
       (x0
        :: v'9
           :: x23
              :: m
                 :: Vint32 i13
                    :: Vint32 x22
                       :: Vint32 p
                          :: Vint32 (p&ᵢ$ 7)
                             :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
       :: v'8) **
       p_local OSLInv (cur_tcb_blk, Int.zero)
       (logic_val (V$ 1)
        :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
     Aisr empisr **
     Aie false **
     Ais nil **
     Acs (true :: nil) **
     Aier vier **
     aemp_isr_is ** LV prio @ char_t |-> Vint32 i ** A_dom_lenv ((prio, char_t) :: (ptcb, OS_TCB ∗) :: nil)    
    )).

  eapply tcbdllseg_combine.
  sep pauto.

  sep cancel AOSEventFreeList .
  sep cancel AOSQFreeList .
  sep cancel AOSQFreeBlk .
  sep cancel ASemEIBs .
  sep cancel AMuxEIBs .
  sep cancel AMqEIBs .
  sep cancel Aier.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel A_dom_lenv.

  sep cancel tcbdllflag.
  sep cancel Aop.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel tcbllsegevaux .
  sep cancel 4%nat 2%nat.
  sep pauto.
  sep cancel dllseg.
  unfold AECBList.
  unfold AECBList in H54.
  sep pauto.
  {
    unprotect Heqtcbls'. rewrite Heqtcbls'.
    apply ECBList_P_preserve_resume; eauto.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  auto.
  splits; auto. 
  go.
  go.

  eauto.
  eauto.
  auto.
  auto. 
  auto.

  hoare unfold.

  rename v'13 into vv13.
  rename v'14 into vv14.
  rename v'16 into vv16.
  rename v'21 into vv21.
  rename v'22 into vv22.
  rename v'24 into vv24.
  rename v'25 into vv25.
  rename v'26 into vv26.
  rename v'27 into vv27.
  rename v'28 into vv28.
  rename v'29 into vv29.
  rename v'30 into vv30.
  rename v'31 into vv31.
  rename v'32 into vv32.
  rename v'33 into vv33.
  rename v'34 into vv34.
  rename v'35 into vv35.
  rename v'36 into vv36.
  rename v'37 into vv37.

  rename H54 into HH54.
  rename H56 into HH56.
  rename H58 into HH58.
  rename H59 into HH59.
  rename H60 into HH60.
  rename H61 into HH61.
  rename H63 into HH63.
  rename H66 into H54.
  rename H67 into H55.

  assert(ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'6
  (v'7 ++
         (x0
          :: v'9
             :: x23
                :: m0
                   :: Vint32 i13
                      :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                         :: Vint32 i
                            :: Vint32 (i&ᵢ$ 7)
                               :: Vint32 (i >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(i >>ᵢ $ 3)) :: nil)
         :: v'8)).
  {
    eapply ptr_in_tcbdllseg_preserve.
    apply H14.
    unfolds; simpl; auto.
  }

  hoare_lifts_trms_pre(tcbdllseg).
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H58.
  eauto.
  eauto.

  
  instantiate (1 := tcbls').
  instantiate (1 := rtbl).
  assumption.

  hoare unfold.

  destruct v'14.
  {
    unfold tcbdllseg.
    simpl.
    hoare unfold.
    inverts H63.
  }

    (* Fix abstract operation *)
    hoare lifts (27::41::nil)%nat pre.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_taskres_succ_nosched'.
    can_change_aop_solver.
    eapply absinfer_eq.

    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_taskres_rdy_nosched'.
    can_change_aop_solver.
    eauto.
    eapply absinfer_eq.

    change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
    assert (Hopv: opv = Vint32 (Int.repr OS_NO_ERR) \/ opv <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
    destruct Hopv. 
    subst.

   (* opv = Vint32 (Int.repr OS_NO_ERR) *)    

   eapply abscsq_rule. 
   apply noabs_oslinv.
   eapply absimp_taskresume_ret.
   auto.
   can_change_aop_solver.
   eapply absinfer_eq.



    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.

    sep cancel APthreadAttr.
    sep cancel CoreCommuInv.
    sep cancel PartitionInv.
    sep cancel CapabilityInv.
    sep cancel p_local. 
    sep cancel Aier.
  
    unfold EvtInv.
    unfold AOSTCBPrioTbl.
    sep pauto.
    sep cancel AOSEventFreeList .
    sep cancel AOSQFreeBlk .
    sep cancel ASemEIBs .
    sep cancel AMuxEIBs .
    sep cancel AMqEIBs .
    sep cancel AOSQFreeList .
  
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllseg.
    sep cancel tcbdllseg.

    unfold AOSRdyTblGrp.
    sep pauto.
    sep cancel AOSRdyGrp .
    unfold AOSRdyTbl.
    sep pauto.

    unfold AECBList.
    unfold AECBList in H63.
    sep pauto.
    sep cancel evsllseg.

    instantiate(1 := (
      LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) ** LV prio @ Int8u |-> Vint32 i ** A_dom_lenv ((prio, Int8u) :: (ptcb, OS_TCB ∗) :: nil)
    )).

    sep pauto.
    {
      sep lifts (2::nil)%nat.
      eapply tcbdllflag_hold.
      instantiate (1 := (v'7 ++
      (x0
       :: v'9
          :: x23
             :: m0
                :: Vint32 i13
                   :: Vint32 x22
                      :: Vint32 i
                         :: Vint32 (i&ᵢ$ 7)
                            :: Vint32 (i >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(i >>ᵢ $ 3)) :: nil) :: v'8)).
      rewrite <- H58.
      apply eq_dllflag_set.
      unfold V_OSTCBNext; simpl; auto.
      unfold V_OSTCBflag; simpl; auto.
  
      sep lifts (2::nil)%nat.
      eapply tcbllsegevaux_hold.
      instantiate (1 := (v'7 ++
      (x0
       :: v'9
          :: x23
             :: m0
                :: Vint32 i13
                   :: Vint32 x22
                      :: Vint32 i
                         :: Vint32 (i&ᵢ$ 7)
                            :: Vint32 (i >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(i >>ᵢ $ 3)) :: nil) :: v'8)).
  
      rewrite <- H58.
      apply eq_dllflag_set.
      unfold V_OSTCBNext; simpl; auto.
      unfold V_OSTCBflag; simpl; auto.
  
      auto.
  Optimize Proof.
  Optimize Heap.
    }

    {
      unprotect Heqtcbls'.
      rewrite Heqtcbls' in H66.
      auto.
    }
    splits; auto.

    eauto.
    eauto.

    {
      unfold join; simpl.
      rewrite Heqtcbls' in H59.
      auto.
    }
    auto.
  
    eapply R_PrioTbl_P_resume; eauto.
    auto.
    auto. 
    auto. 
    auto. 

    {
      clear - H5.
      unfold RH_CurTCB in *.
      simpljoin.
      assert ((toresblock, Int.zero) = (cur_tcb_blk, Int.zero) \/
              (toresblock, Int.zero) <> (cur_tcb_blk, Int.zero)) as choice by tauto.
      destruct choice.
      do 4 eexists. rewrite H0. rewrite TcbMod.map_get_set. eauto.
      do 4 eexists. rewrite TcbMod.map_get_set'.
      unfold get in H; simpl in H. eauto. auto. 
    }

    eapply RH_TCBList_ECBList_P_resume; eauto.

    go.

    hoare forward.

    unfold OS_NO_ERR.
    splits; eauto.

    {
      clear -H10.
      mauto.
    }

    {
      clear -H10.
      mauto.
    }



  (* opv <> Vint32 (Int.repr OS_NO_ERR) *)    

   eapply abscsq_rule. 
   apply noabs_oslinv.
   eapply absimp_taskresume_ret_abt.
   can_change_aop_solver.
   auto.
   eapply absinfer_eq.
   eapply absabort_rule.

    hoare forward.




  lets H52: H42. (* place holder *)
  lets H53: H42.
  lets H2: H42.
  lets H3: H42.
  lets H47: H42.

  
        (* If (ptcb ′ → OSTCBDly ==ₑ ′ 0) *)
        hoare unfold.

        rename H49 into HH49.

        assert(Hx22: x22&ᵢInt.not($ OS_STAT_SUSPEND) = $ OS_STAT_RDY).
        {
          clear - HH49.
          assert (Int.eq (x22&ᵢInt.not($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY) = true \/ Int.eq (x22&ᵢInt.not($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY) = false).
          destruct (Int.eq (x22&ᵢInt.not($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY));eauto.
          destruct H.
          apply int_eq_true_eq in H;auto.
          rewrite H in HH49.
          unfold val_inj in HH49. simpl in HH49.
          destruct HH49.
          tryfalse.
          tryfalse.
        }
      
        assert(Hx22': x22&ᵢ($ OS_STAT_SUSPEND) <> $ OS_STAT_RDY).
        {
          clear - H50.
          assert (Int.eq (x22&ᵢ($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY) = true \/ Int.eq (x22&ᵢ($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY) = false).
          destruct (Int.eq (x22&ᵢ($ OS_STAT_SUSPEND)) ($ OS_STAT_RDY));eauto.
          destruct H. 
          rewrite H in H50.
          destruct H50.
          tryfalse.
          tryfalse.
          apply int_eq_false_eq in H;auto.
        }
      
        assert(Hx22stat: x22 = $ OS_STAT_SUSPEND).
        {
          clear -H62 Hx22 Hx22'.
          unfold OS_STAT_RDY, OS_STAT_SUSPEND, OS_STAT_SEM, OS_STAT_Q, OS_STAT_MBOX, OS_STAT_MUTEX, OS_STAT_POSTQ, OS_STAT_POSTQ, OS_STAT_PORT in *. 

          destruct H62.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.
          destruct H. auto.
          destruct H.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.
          destruct H.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.
          destruct H.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.
          destruct H.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.
          destruct H.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.
          destruct H.
          rewrite H in Hx22'.
          false. destruct Hx22'. mauto.

          destruct H.
          rewrite H in Hx22.
          rewrite Int.and_commut in Hx22.  
          rewrite Int.and_or_distrib in Hx22.
          assert(Int.or (Int.not ($ 8)&ᵢ$ 1) (Int.not ($ 8)&ᵢ$ 8) <> $ 0) by mauto.
          tryfalse.

          destruct H.
          rewrite H in Hx22.
          rewrite Int.and_commut in Hx22.  
          rewrite Int.and_or_distrib in Hx22.
          assert(Int.or (Int.not ($ 8)&ᵢ$ 4) (Int.not ($ 8)&ᵢ$ 8) <> $ 0) by mauto.
          tryfalse.

          destruct H.
          rewrite H in Hx22.
          rewrite Int.and_commut in Hx22.  
          rewrite Int.and_or_distrib in Hx22.
          assert(Int.or (Int.not ($ 8)&ᵢ$ 512) (Int.not ($ 8)&ᵢ$ 8) <> $ 0) by mauto.
          tryfalse.

          destruct H.
          rewrite H in Hx22.
          rewrite Int.and_commut in Hx22.  
          rewrite Int.and_or_distrib in Hx22.
          assert(Int.or (Int.not ($ 8)&ᵢ$ 2) (Int.not ($ 8)&ᵢ$ 8) <> $ 0) by mauto.
          tryfalse.          

          destruct H.
          rewrite H in Hx22.
          rewrite Int.and_commut in Hx22.  
          rewrite Int.and_or_distrib in Hx22.
          assert(Int.or (Int.not ($ 8)&ᵢ$ 16) (Int.not ($ 8)&ᵢ$ 8) <> $ 0) by mauto.
          tryfalse.          

          rewrite H in Hx22.
          rewrite Int.and_commut in Hx22.  
          rewrite Int.and_or_distrib in Hx22.
          assert(Int.or (Int.not ($ 8)&ᵢ$ 256) (Int.not ($ 8)&ᵢ$ 8) <> $ 0) by mauto.
          tryfalse. 
        }

        protect Hx22stat.
    
        hoare forward.
        3: instantiate(1:=Afalse).
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
          sep normal.
          sep eexists.
          ssplit_apure.
          (* sep pauto. *)
          sep cancel Aop.
          sep cancel (2%nat) (1%nat).
          sep cancel (3%nat) (1%nat).
          eauto.
      
          instantiate (1 := p).
          lia.
  Optimize Proof.
  Optimize Heap.
          eauto.
          eauto.
          eauto.
          eauto.
          go.
          math simpls.
          go.
          go.
          clear - H65.
          mauto.
      
          2: go.
          2: eauto.
          2: eauto. 
      
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
        rename H72 into Hpint.
        rename p into vprio.
        rename v'37 into p.
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


        assert ((p, t, m, s)=(i, st0, m0, sus0))as abstcbeq. {
          clear - H13 H23 H25.
          assert(TcbMod.get v'11 (toresblock, Int.zero) = Some (p, t, m, s)). {
            unfolds in H25.
            unfold join, sig in H25.
            simpl in H25.
            apply TcbMod.join_sig_get in H25;eauto.
          }
          assert (TcbMod.get tcbls (toresblock, Int.zero) = Some (p, t, m, s)). {
            eapply TcbMod.join_get_get_r; eauto.
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
          protect Hx22stat.
          simpljoin.
          unfolds in H74. destruct x13. destruct p. destruct p.
          destruct H74 as (Holdmsg & Holdprio & HoldblkP & HoldtcbP).
          splits; auto.
          apply RL_TCBblk_P_resume; auto.

          inverts Holdmsg;inverts Holdprio.
          lets HoldtcbBackup : HoldtcbP.
          unfold R_TCB_Status_P in HoldtcbP.
          destruct HoldtcbP as (_ & HRHLrdy & _).
          unfold RHL_RdyI_P in HRHLrdy;unfold V_OSTCBStat,V_OSTCBDly in HRHLrdy;simpl in HRHLrdy.

          (*
          assert (val_inj (if Int.eq resstat ($ OS_STAT_RDY) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <> Vint32 Int.zero) as H2.
          {
            clear - HH49.
            unfold val_inj, OS_STAT_RDY in *.
            int auto.
            simpl in HH49.
            destruct HH49.
            false.
            false.
          }

          apply val_inj_iftrue_impl_eqtrue in H2.
          apply int_eq_true_impl_eq in H2.
                    *)
          apply val_inj_iftrue_impl_eqtrue in H55.
          apply int_eq_true_impl_eq in H55 as Hdly0.
          (*
          apply eq_sym in Heqresstat.
          rewrite <- Heqresstat.
          rewrite H2 in Heqresstat.
          apply stat_resume_rdy_imp_rdy in Heqresstat.      
          2: auto.
*)

          assert (Int.eq x22 ($ OS_STAT_SUSPEND) = true). {
            rewrite Hx22stat.
            unfold OS_STAT_SUSPEND.
            auto.
          }
          

          lets Hprerdy : low_stat_rdy_or_sus_imp_high_rdy H49 H56 HoldblkP H51 H74.
          eapply Hprerdy in H55.
          inverts H55.
          clear H76 Hprerdy.
          rewrite Hdly0; rewrite Hdly0 in H51.

          assert (0 <= Int.unsigned p < 64)as Hprange by auto.
          rename H49 into typematch.
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
        

  unfold EvtInv.

        (* Recombine the tcbdllseg *)
        eapply backward_rule1.
        intros.

        instantiate(1 := (
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
          GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
  GV OSRdyGrp @ char_t |-> Vint32 v'34 **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) rtbl' **
  <||
  ASSERT (fun _ : osabst => 2%nat = 2%nat);;
  (taskresume_err_prio_invalid (|Vint32 i :: opv :: nil|);; v'0
   ?? taskresume_err_no_such_tcb (|Vint32 i :: opv :: nil|);; v'0
      ?? taskresume_err_not_suspended (|Vint32 i :: opv :: nil|);; v'0
         ?? taskresume_time_nzero (|Vint32 i :: opv :: nil|);;
            (taskresume_succ (|Vint32 i :: opv :: nil|);; taskresume_ret (|Vint32 i :: opv :: nil|);; v'0
             ?? taskresume_succ (|Vint32 i :: opv :: nil|);;
                isched;; taskresume_ret (|Vint32 i :: opv :: nil|);; v'0)) ||>  **
  LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) **
  (* Astruct (toresblock, Int.zero) OS_TCB_flag
    (x0 :: v'9 :: x23 :: m :: Vint32 i13 :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND)) :: resblk) **
  dllseg x0 (Vptr (toresblock, Int.zero)) v'20 Vnull l2' OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
    (fun vl : vallist => nth_val 0 vl) **
  dllseg v'6 Vnull v'9 (Vptr (toresblock, Int.zero)) l1' OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
    (fun vl : vallist => nth_val 0 vl) ** *)
  PV vhold @ char_t |-> v'23 **
  GV OSTCBList @ OS_TCB ∗ |-> v'6 **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
  AOSMapTbl **
  AOSUnMapTbl **
  G& OSPlaceHolder @ char_t == vhold **
  HPriotls v15 **
  AOSTCBFreeList v'17 v'18 **
  AOSTime (Vint32 v'15) **
  HTCBList tcbls **
  HTime v'15 **
  HCurTCB (cur_tcb_blk, Int.zero) **
  AGVars **
  APthreadAttr vpthattr **
  (EX (fecbh : val) (eventl : list vallist) (ectrl : list os_inv.EventCtr) (osql qblkl : list vallist)
          (msgql : list EventData) (evatoms : list (addrval * type * val)) (evstructs : list (addrval * type * list val))
          (evarrays : list (addrval * nat * list val)) (sinfol minfol qattrl : list vallist) (semeibs : EmbMod.map)
          (muxeibs : MibMod.map) (qeibs : MqattrMod.map) (pbls : PbMod.map) (ebls : EbMod.map) 
          (locmp : EvAuxLocMod.map) (ptrmp : EvAuxPtrMod.map),
          AOSEventFreeList fecbh eventl **
          AOSQFreeList osql **
          AOSQFreeBlk qblkl **
          AECBList ectrl msgql ecbls tcbls' **
          HECBList ecbls **
          Hebls ebls **
          AErrblkList ebls **
          Hpbls pbls **
          APosblkList pbls **
          HEvAtomHeap evatoms **
          AEvAtomHeap evatoms **
          HEvStructHeap evstructs **
          AEvStructHeap evstructs **
          HEvArrayHeap evarrays **
          AEvArrayHeap evarrays **
          [|R_Q_Data_P evstructs evarrays|] **
          HSEMInfo semeibs **
          ASemEIBs sinfol v18 semeibs ecbls vhold **
          HMuxInfo muxeibs **
          AMuxEIBs minfol v19 muxeibs ecbls vhold **
          HQAttr qeibs **
          AMqEIBs qattrl v20 qeibs ecbls vhold **
          [|vhold = vhold_addr|] **
          [|SEM_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|MUX_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|Q_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|evcre_nodup locmp ptrmp|] **
          [|evdel_nodup locmp ptrmp|] **
          [|eibref_distinct semeibs muxeibs qeibs|] **
          HEvLoc locmp **
          HEvPtr ptrmp ** tcbllsegevaux v'6 (l1' ++ (x0 :: v'9 :: x23 :: m :: Vint32 i13 :: Vint32 x22 :: resblk) :: l2')  locmp ptrmp) **
  A_isr_is_prop **
  IntInv **
  TmrInv **
  CoreCommuInv ecbls **
  PartitionInv ecbls **
  CapabilityInv vcspace **
  tcbdllflag v'6 (l1' ++ (x0 :: v'9 :: x23 :: m :: Vint32 i13 :: Vint32 x22 :: resblk) :: l2') **
  p_local OSLInv (cur_tcb_blk, Int.zero)
    (logic_val (V$ 1) :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  Aisr empisr **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aier vier ** aemp_isr_is ** LV prio @ char_t |-> Vint32 i ** A_dom_lenv ((prio, char_t) :: (ptcb, OS_TCB ∗) :: nil)
        )).

        eapply tcbdllseg_combine.
        sep pauto.

        sep cancel AOSEventFreeList .
        sep cancel AOSQFreeList .
        sep cancel AOSQFreeBlk .
        sep cancel ASemEIBs .
        sep cancel AMuxEIBs .
        sep cancel AMqEIBs .
        sep cancel Aier.
        sep cancel Aisr.
        sep cancel Aie.
        sep cancel Ais.
        sep cancel Acs.
        sep cancel A_dom_lenv.
      
        sep cancel tcbdllflag.
        sep cancel Aop.
        unfold tcbdllseg.
        unfold1 dllseg.
        unfold node.
        sep cancel tcbllsegevaux .
        sep cancel 4%nat 2%nat.
        sep pauto.
        sep cancel dllseg.
        unfold AECBList.
        unfold AECBList in H74.
        sep pauto.


        {
          unprotect Heqtcbls'. rewrite Heqtcbls'.
          apply ECBList_P_preserve_resume; eauto.
        }
        auto.
  Optimize Proof.
  Optimize Heap.
        auto.

        Open Scope Z_scope.
        Open Scope int_scope.
        (*
        assert ((Int.unsigned (x22&ᵢInt.not ($ OS_STAT_SUSPEND))) <= 255). {
          apply not_and_p'.
          auto. unfold OS_STAT_SUSPEND; clear; int auto.
        }
        *)
        go.
      
        eauto.
        eauto.
        auto.
        auto. 
        auto. 
        auto.  

        protect Heqresblk.
        protect Hx22stat.
        hoare unfold.

        rename v'7 into vv7.
        rename v'8 into vv8.
        rename v'12 into vv12.
        rename v'14 into vv14.
        rename v'21 into vv21.
        rename v'31 into vv31.
        rename v'32 into vv32.
        rename v'33 into vv33.
        rename v'36 into vv36.
        rename v'37 into vv37.
        rename v'38 into vv38.
        rename v'39 into vv39.
        rename v'40 into vv40.
        rename v'41 into vv41.
        rename v'42 into vv42.
        rename v'43 into vv43.
        rename v'44 into vv44.
        rename v'45 into vv45.

        rename H74 into HH74.
        rename H76 into HH76.
        rename H77 into HH77.
        rename H78 into HH78.
        rename H79 into HH79.
        rename H80 into HH80.
        rename H81 into HH81.
        rename H82 into H74.
        rename H83 into H75.

        (* tcbcur is still in the new array *)
        assert (ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'6
        (l1' ++
         (x0 :: v'9 :: x23 :: m0 :: Vint32 i13 :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
          :: resblk) :: l2')).
        eapply ptr_in_tcbdllseg_preserve.
        apply H14.
        unfolds; simpl; auto.
        
        hoare_lifts_trms_pre(tcbdllseg).
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
        hoare lifts (30::41::nil)%nat pre.
        
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply absimp_taskres_wait_suspend'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        
        assert (Hst_cond: 
        (forall eid t, sus0 = true /\
          (st0 = wait (os_stat_sem eid) (Some t) \/
          st0 = wait (os_stat_q eid) (Some t) \/
          st0 = wait (os_stat_mbox eid) (Some t) \/
          st0 = wait (os_stat_mutexsem eid) (Some t) \/
          st0 = wait (os_stat_port eid) (Some t)) -> t <> Int.zero
        )
        \/ ~(forall eid t, sus0 = true /\
        (st0 = wait (os_stat_sem eid) (Some t) \/
        st0 = wait (os_stat_q eid) (Some t) \/
        st0 = wait (os_stat_mbox eid) (Some t) \/
        st0 = wait (os_stat_mutexsem eid) (Some t) \/
        st0 = wait (os_stat_port eid) (Some t)) -> t <> Int.zero
        )) by tauto.
        destruct Hst_cond.
        2:{
          eapply abscsq_rule.
          apply noabs_oslinv.
          eapply absimp_taskres_time_nzero_abt'; eauto.
          can_change_aop_solver.
          apply absinfer_eq.
          eapply absabort_rule.
        }
        
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply absimp_taskres_time_nzero'; eauto.
        can_change_aop_solver.
        apply absinfer_eq.
        
        rename H81 into Htime_nzero.

        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply absimp_taskres_succ'.
        can_change_aop_solver.
        eapply absinfer_eq.
    
        eapply abscsq_rule.
        apply noabs_oslinv.
        eapply absimp_taskres_rdy'.
        can_change_aop_solver.
        eauto.
        eapply absinfer_eq.


        (* EXIT_CRITICAL;ₛ *)
        hoare forward prim.

        sep cancel APthreadAttr.
        sep cancel CoreCommuInv.
        sep cancel PartitionInv.
        sep cancel CapabilityInv.
        sep cancel p_local. 
        sep cancel Aier.
      
        unfold EvtInv.
        unfold AOSTCBPrioTbl.
        sep pauto.
        sep cancel AOSEventFreeList .
        sep cancel AOSQFreeBlk .
        sep cancel ASemEIBs .
        sep cancel AMuxEIBs .
        sep cancel AMqEIBs .
        sep cancel AOSQFreeList .
      
        unfold AOSTCBList.
        sep pauto.
        sep cancel tcbdllseg.
        sep cancel tcbdllseg.
    
        unfold AOSRdyTblGrp.
        sep pauto.
        unfold AOSRdyTbl.
        unfold AOSRdyGrp.
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
            sep lifts (2::nil)%nat.
            eapply tcbdllflag_hold.
            instantiate (1 := (l1' ++ (x0 :: v'9 :: x23 :: m0 :: Vint32 i13 :: Vint32 x22 :: resblk) :: l2')).
            rewrite <- H77.
            apply eq_dllflag_set.
            unfold V_OSTCBNext; simpl; auto.
            unfold V_OSTCBflag; simpl; auto.
        
            sep lifts (2::nil)%nat.
            eapply tcbllsegevaux_hold.
            instantiate (1 := (l1' ++ (x0 :: v'9 :: x23 :: m0 :: Vint32 i13 :: Vint32 x22 :: resblk) :: l2')).        
            rewrite <- H77.
            apply eq_dllflag_set.
            unfold V_OSTCBNext; simpl; auto.
            unfold V_OSTCBflag; simpl; auto.        
            auto.
  Optimize Proof.
  Optimize Heap.
          }

          {
            unprotect Heqtcbls'.
            rewrite Heqtcbls' in H82.
            auto.
          }


  split.
  auto.
  apply H71; auto.

  2:eauto.
  eauto.
  {
    unfold join; simpl.
    rewrite Heqtcbls' in H78.
    auto.
  }
  auto.
  eapply R_PrioTbl_P_resume; eauto. 

  {
    unprotect Heqrtbl'.
    rewrite Heqrtbl'.
    eapply rl_rtbl_priotbl_p_set_hold.
    3: {
      clear - H66.
      eapply nv'2nv in H66.
      eauto.
      auto.
      }
    3: {
      instantiate(1:= ($ 1<<ᵢ(i&ᵢ$ 7))).
      unfold or. 
      unfold val_inj.
      auto.
    }
    eauto. 

    3: {
      apply nv'2nv in H11.
      eauto.
      auto.
    }
    2: auto.

    
  unprotect Heqresblk.
  rewrite Heqresblk in  RL_TCBblk_P_backup.
  eauto.
  }

  auto. 
  auto. 
  auto. 

  {
    clear - H5.
    unfold RH_CurTCB in *.
    simpljoin.
    assert ((toresblock, Int.zero) = (cur_tcb_blk, Int.zero) \/
            (toresblock, Int.zero) <> (cur_tcb_blk, Int.zero)) as choice by tauto.
    destruct choice.
    do 4 eexists. rewrite H0. rewrite TcbMod.map_get_set. eauto.
    do 4 eexists. rewrite TcbMod.map_get_set'.
    unfold get in H; simpl in H. eauto. auto. 
  }

  eapply RH_TCBList_ECBList_P_resume; eauto.
  go.


  hoare forward.
  unfold isflag.
  left. auto.
  go. 

  {
    intros.
    sep destruct H81. 
    exists (logic_val (V$ 1) :: x12). 
    sep pauto.  
  }
  {
    intros.
    sep destruct H81.
    exists (logic_val x11 :: x12).
    sep pauto.
  }

  assert (Hopv: opv = Vint32 (Int.repr OS_NO_ERR) \/ opv <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
  destruct Hopv.
  subst.
 (* opv = V$ OS_NO_ERR *)

  hoare unfold.
  invert H81.
  intros.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply absimp_taskresume_ret.
  pure_auto.
  pure_auto.
  eapply absinfer_eq.

  (* RETURN ′ OS_NO_ERR *)
  hoare forward.
  unfold OS_NO_ERR.
  splits; eauto.
  rewrite Int.unsigned_repr. lia.
  rewrite max_unsigned_val. lia.
  rewrite Int.unsigned_repr.
  change Byte.max_unsigned with 255. lia.
  rewrite max_unsigned_val. lia.


  (* opv <> V$ OS_NO_ERR *)

  hoare unfold.
  invert H82.
  intros.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply absimp_taskresume_ret_abt.
  pure_auto.
  auto.
  eapply absinfer_eq.

  eapply absabort_rule.


  (* ptcb′→OSTCBDly !=ₑ ′ 0 *)

  hoare forward.
  hoare unfold.

hoare_lifts_trms_pre (Aop, abstcblist).
eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_taskres_wait_suspend'; eauto.
can_change_aop_solver.
apply absinfer_eq.

assert (Hst_cond: 
(forall eid t, sus0 = true /\
  (st0 = wait (os_stat_sem eid) (Some t) \/
  st0 = wait (os_stat_q eid) (Some t) \/
  st0 = wait (os_stat_mbox eid) (Some t) \/
  st0 = wait (os_stat_mutexsem eid) (Some t) \/
  st0 = wait (os_stat_port eid) (Some t)) -> t <> Int.zero
)
\/ ~(forall eid t, sus0 = true /\
(st0 = wait (os_stat_sem eid) (Some t) \/
st0 = wait (os_stat_q eid) (Some t) \/
st0 = wait (os_stat_mbox eid) (Some t) \/
st0 = wait (os_stat_mutexsem eid) (Some t) \/
st0 = wait (os_stat_port eid) (Some t)) -> t <> Int.zero
)) by tauto.
destruct Hst_cond.
2:{
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absimp_taskres_time_nzero_abt'; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  eapply absabort_rule.
}

eapply abscsq_rule.
apply noabs_oslinv.
eapply absimp_taskres_time_nzero'; eauto.
can_change_aop_solver.
apply absinfer_eq.

rename H54 into Htime_nzero.


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


  assert (Hdly: Int.ltu Int.zero i13 = true).
  {
    clear -H49.
    assert(Int.eq i13 ($ 0) = true \/ Int.eq i13 ($ 0) = false) by pauto.
    destruct H.
    rewrite H in H49.
    destruct H49.
    tryfalse.
    tryfalse.

    unfold Int.eq in H.
    unfold Int.ltu. 
    unfold Int.zero.
    mauto.
    clear H49.
    int auto.
  Optimize Proof.
  Optimize Heap.
    assert ( 0<= Int.unsigned i13).
    {
      clear -i13.
      int auto.
    }
    false.
    destruct n.
    lia.
  }
  
  clear H49 H52 H53.

  unfold AOSRdyTbl.
  hoare_split_pure_all.
  destruct H49.
  rename H49 into HHH49.
  rename H52 into HHH52.

  assert(TCBList_P (Vptr (toresblock, Int.zero))
  ((x0
    :: v'9
       :: x23
          :: m
             :: Vint32 i13
                :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                   :: Vint32 p
                      :: Vint32 (p&ᵢ$ 7)
                         :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) :: v'8)
  rtbl (TcbMod.set v'11 (toresblock, Int.zero) (i, st0, m0, false))). 
  {
    unfold1 TCBList_P.
    do 4 eexists. splits. auto.
    unfolds. simpl. auto.
    eapply tcbjoin_set.
    eauto.

    inverts abstcbeq.
    unfolds.
    unfold1 TCBList_P in backup.
    simpljoin. unfolds in H54. destruct x13; destruct p; destruct p.
    destructs H54.
    splits; auto.
    apply RL_TCBblk_P_resume; auto. 
    eapply R_TCB_Status_P_resume'; eauto.
    right.
    2: eauto.
    splits.
    auto.
    2: eauto.
    auto.
  }
  
  assert(TCBList_P v'6 v'7 rtbl v'10).
  {
    auto.
  }

  assert (TcbMod.join v'10
  (TcbMod.set v'11 (toresblock, Int.zero)
     (i, st0, m0, false)) tcbls'). 
  {
    unprotect Heqtcbls'.
    rewrite Heqtcbls'.
    eapply TcbMod.join_set_r. auto.
    clear -H25.
    unfold TcbMod.indom. eexists.
    unfolds in H25.
    unfold join, sig in H25; simpl in H25.
    apply TcbMod.join_sig_get in H25. eauto.
  }

  unfold EvtInv.

  (* Recombine the tcbdllseg *)
  eapply backward_rule1.
  intros.

  instantiate(1:= (
    [|ptr_in_tcbdllseg (Vptr (toresblock, Int.zero)) v'6
    (v'7 ++
    (x0
    :: v'9
      :: x23
          :: m
            :: Vint32 i13
                :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                  :: Vint32 p
                      :: Vint32 (p&ᵢ$ 7)
                        :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
    :: v'8)|] **
    tcbdllseg v'6 Vnull v'20 Vnull (v'7 ++
    (x0
    :: v'9
      :: x23
        :: m
            :: Vint32 i13
              :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                  :: Vint32 p
                    :: Vint32 (p&ᵢ$ 7)
                        :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
    :: v'8) **
    [|TCBList_P v'6
    (v'7 ++
    (x0
    :: v'9
      :: x23
          :: m
            :: Vint32 i13
                :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                  :: Vint32 p
                      :: Vint32 (p&ᵢ$ 7)
                        :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
    :: v'8) rtbl tcbls'|] **
    <||
         ifun_tasksus_spec.spec_code_cons
           (taskresume_succ (|Vint32 i :: opv :: nil|);; taskresume_ret (|Vint32 i :: opv :: nil|)
            ?? taskresume_succ (|Vint32 i :: opv :: nil|);; isched;; taskresume_ret (|Vint32 i :: opv :: nil|)) v'0
         ||>  **
  LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) **
  (* Astruct (toresblock, Int.zero) OS_TCB_flag
    (x0
     :: v'9
        :: x23
           :: m
              :: Vint32 i13
                 :: Vint32 (x22&ᵢInt.not ($ OS_STAT_SUSPEND))
                    :: Vint32 p
                       :: Vint32 (p&ᵢ$ 7)
                          :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) **
  dllseg x0 (Vptr (toresblock, Int.zero)) v'20 Vnull v'8 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
    (fun vl : vallist => nth_val 0 vl) **
  dllseg v'6 Vnull v'9 (Vptr (toresblock, Int.zero)) v'7 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
    (fun vl : vallist => nth_val 0 vl) ** *)
  PV vhold @ char_t |-> v'23 **
  GV OSTCBList @ OS_TCB ∗ |-> v'6 **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (cur_tcb_blk, Int.zero) **
  AOSMapTbl **
  AOSUnMapTbl **
  GAarray OSTCBPrioTbl (Tarray OS_TCB ∗ 64) ptbl **
  G& OSPlaceHolder @ char_t == vhold **
  HPriotls v15 **
  AOSTCBFreeList v'17 v'18 **
  GAarray OSRdyTbl (Tarray char_t ∘ OS_RDY_TBL_SIZE) rtbl **
  AOSRdyGrp v'12 **
  AOSTime (Vint32 v'15) **
  HTCBList tcbls **
  HTime v'15 **
  HCurTCB (cur_tcb_blk, Int.zero) **
  AGVars **
  APthreadAttr vpthattr **
  (EX (fecbh : val) (eventl : list vallist) (ectrl : list os_inv.EventCtr) (osql qblkl : list vallist)
          (msgql : list EventData) (evatoms : list (addrval * type * val)) (evstructs : list (addrval * type * list val))
          (evarrays : list (addrval * nat * list val)) (sinfol minfol qattrl : list vallist) (semeibs : EmbMod.map)
          (muxeibs : MibMod.map) (qeibs : MqattrMod.map) (pbls : PbMod.map) (ebls : EbMod.map) (locmp : EvAuxLocMod.map)
          (ptrmp : EvAuxPtrMod.map),
          AOSEventFreeList fecbh eventl **
          AOSQFreeList osql **
          AOSQFreeBlk qblkl **
          AECBList ectrl msgql ecbls tcbls' **
          HECBList ecbls **
          Hebls ebls **
          AErrblkList ebls **
          Hpbls pbls **
          APosblkList pbls **
          HEvAtomHeap evatoms **
          AEvAtomHeap evatoms **
          HEvStructHeap evstructs **
          AEvStructHeap evstructs **
          HEvArrayHeap evarrays **
          AEvArrayHeap evarrays **
          [|R_Q_Data_P evstructs evarrays|] **
          HSEMInfo semeibs **
          ASemEIBs sinfol v18 semeibs ecbls vhold **
          HMuxInfo muxeibs **
          AMuxEIBs minfol v19 muxeibs ecbls vhold **
          HQAttr qeibs **
          AMqEIBs qattrl v20 qeibs ecbls vhold **
          [|vhold = vhold_addr|] **
          [|SEM_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|MUX_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|Q_ECB_P locmp ptrmp ecbls fecbh eventl semeibs muxeibs qeibs|] **
          [|evcre_nodup locmp ptrmp|] **
          [|evdel_nodup locmp ptrmp|] **
          [|eibref_distinct semeibs muxeibs qeibs|] **
          HEvLoc locmp ** HEvPtr ptrmp ** tcbllsegevaux v'6
          (v'7 ++
           (x0
            :: v'9
               :: x23
                  :: m
                     :: Vint32 i13
                        :: Vint32 x22
                           :: Vint32 p
                              :: Vint32 (p&ᵢ$ 7)
                                 :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil) :: v'8) locmp ptrmp) **
  A_isr_is_prop **
  IntInv **
  TmrInv **
  CoreCommuInv ecbls **
  PartitionInv ecbls **
  CapabilityInv vcspace **
  tcbdllflag v'6
  (v'7 ++
  (x0
    :: v'9
      :: x23
          :: m
            :: Vint32 i13
                :: Vint32 x22
                  :: Vint32 p
                      :: Vint32 (p&ᵢ$ 7)
                        :: Vint32 (p >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(p&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(p >>ᵢ $ 3)) :: nil)
  :: v'8) **
  p_local OSLInv (cur_tcb_blk, Int.zero)
    (logic_val (V$ 1) :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  Aisr empisr **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  Aier vier ** aemp_isr_is ** LV prio @ char_t |-> Vint32 i ** A_dom_lenv ((prio, char_t) :: (ptcb, OS_TCB ∗) :: nil)
  )).


  eapply tcbdllseg_combine.
  sep pauto.

  sep cancel AOSEventFreeList .
  sep cancel AOSQFreeList .
  sep cancel AOSQFreeBlk .
  sep cancel ASemEIBs .
  sep cancel AMuxEIBs .
  sep cancel AMqEIBs .
  sep cancel Aier.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel A_dom_lenv.

  sep cancel tcbdllflag.
  sep cancel Aop.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep cancel tcbllsegevaux .
  sep cancel 4%nat 2%nat.
  sep pauto.
  sep cancel dllseg.
  unfold AECBList.
  unfold AECBList in H54.
  sep pauto.

  {
    unprotect Heqtcbls'. rewrite Heqtcbls'.
    apply ECBList_P_preserve_resume; eauto.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  auto.
  splits; auto.
  go.

  eauto.
  eauto.
  auto.
  auto. 
  auto. 
  auto. 

  unprotect Hx22stat.
  hoare unfold.

  rename v'13 into vv13.
  rename v'14 into vv14.
  rename v'16 into vv16.
  rename v'21 into vv21.
  rename v'22 into vv22.
  rename v'24 into vv24.
  rename v'25 into vv25.
  rename v'26 into vv26.
  rename v'27 into vv27.
  rename v'28 into vv28.
  rename v'29 into vv29.
  rename v'30 into vv30.
  rename v'31 into vv31.
  rename v'32 into vv32.
  rename v'33 into vv33.
  rename v'34 into vv34.
  rename v'35 into vv35.
  rename v'36 into vv36.
  rename v'37 into vv37.

  rename H54 into HH54.
  rename H56 into HH56.
  rename H58 into HH58.
  rename H59 into HH59.
  rename H60 into HH60.
  rename H61 into HH61.
  rename H63 into HH63.
  rename H66 into H54.
  rename H67 into H55.

  assert(ptr_in_tcbdllseg (Vptr (cur_tcb_blk, Int.zero)) v'6
  (v'7 ++
         (x0
          :: v'9
             :: x23
                :: m0
                   :: Vint32 i13
                      ::  Vint32 ($ OS_STAT_SUSPEND&ᵢInt.not ($ OS_STAT_SUSPEND))
                         :: Vint32 i
                            :: Vint32 (i&ᵢ$ 7)
                               :: Vint32 (i >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(i >>ᵢ $ 3)) :: nil)
         :: v'8)).
  {
    eapply ptr_in_tcbdllseg_preserve.
    apply H14.
    unfolds; simpl; auto.
  }

  hoare_lifts_trms_pre(tcbdllseg).
  eapply backward_rule1.
  intros.
  eapply tcbdllseg_split' in H58.
  eauto.
  eauto.


  instantiate (1 := tcbls').
  instantiate (1 := rtbl).
  assumption.

  hoare unfold.

  destruct v'14.
  {
  unfold tcbdllseg.
  simpl.
  hoare unfold.
  inverts H63.
  }


    (* Fix abstract operation *)
    hoare lifts (27::41::nil)%nat pre.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_taskres_succ_nosched'.
    can_change_aop_solver.
    eapply absinfer_eq.

    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply absimp_taskres_rdy_nosched'.
    can_change_aop_solver.
    eauto.
    eapply absinfer_eq.



    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.

    unfold EvtInv.
    sep normal.
    sep eexists.

    sep cancel APthreadAttr.
    sep cancel CoreCommuInv.
    sep cancel PartitionInv.
    sep cancel CapabilityInv.
    sep cancel p_local. 
    sep cancel Aier.

    sep cancel AOSEventFreeList .
    sep cancel AOSQFreeBlk .
    sep cancel ASemEIBs .
    sep cancel AMuxEIBs .
    sep cancel AMqEIBs .
    sep cancel AOSQFreeList .
    sep pauto.

    unfold AOSTCBPrioTbl.
    sep pauto.

  
    unfold AOSTCBList.
    sep pauto.
    sep cancel tcbdllseg.
    sep cancel tcbdllseg.

    unfold AOSRdyTblGrp.
    sep pauto.
    sep cancel AOSRdyGrp .
    unfold AOSRdyTbl.
    sep pauto.

    unfold AECBList.
    unfold AECBList in H63.
    sep pauto.
    sep cancel evsllseg.

    instantiate(1 := (
      LV ptcb @ OS_TCB ∗ |-> Vptr (toresblock, Int.zero) ** LV prio @ Int8u |-> Vint32 i ** A_dom_lenv ((prio, Int8u) :: (ptcb, OS_TCB ∗) :: nil)
    )).

    sep pauto.
    {
      sep lifts (2::nil)%nat.
      eapply tcbdllflag_hold.
      instantiate (1 := (v'7 ++
      (x0
       :: v'9
          :: x23
             :: m0
                :: Vint32 i13
                   :: V$ OS_STAT_SUSPEND
                      :: Vint32 i
                         :: Vint32 (i&ᵢ$ 7)
                            :: Vint32 (i >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(i >>ᵢ $ 3)) :: nil) :: v'8)).
      rewrite <- H58.
      apply eq_dllflag_set.
      unfold V_OSTCBNext; simpl; auto.
      unfold V_OSTCBflag; simpl; auto.
  
      sep lifts (2::nil)%nat.
      eapply tcbllsegevaux_hold.
      instantiate (1 := (v'7 ++
      (x0
       :: v'9
          :: x23
             :: m0
                :: Vint32 i13
                   :: V$ OS_STAT_SUSPEND
                      :: Vint32 i
                         :: Vint32 (i&ᵢ$ 7)
                            :: Vint32 (i >>ᵢ $ 3) :: Vint32 ($ 1<<ᵢ(i&ᵢ$ 7)) :: Vint32 ($ 1<<ᵢ(i >>ᵢ $ 3)) :: nil) :: v'8)).
  
      rewrite <- H58.
      apply eq_dllflag_set.
      unfold V_OSTCBNext; simpl; auto.
      unfold V_OSTCBflag; simpl; auto.
  
      auto.
  Optimize Proof.
  Optimize Heap.
    }

    {
      unprotect Heqtcbls'.
      rewrite Heqtcbls' in H66.
      auto.
    }

    eauto.
    eauto.
    eauto.

    {
      unfold join; simpl.
      rewrite Heqtcbls' in H59.
      auto.
    }
  
    eapply R_PrioTbl_P_resume; eauto.
    auto.

    {
      clear - H5.
      unfold RH_CurTCB in *.
      simpljoin.
      assert ((toresblock, Int.zero) = (cur_tcb_blk, Int.zero) \/
              (toresblock, Int.zero) <> (cur_tcb_blk, Int.zero)) as choice by tauto.
      destruct choice.
      do 4 eexists. rewrite H0. rewrite TcbMod.map_get_set. eauto.
      do 4 eexists. rewrite TcbMod.map_get_set'.
      unfold get in H; simpl in H. eauto. auto. 
    }

    eapply RH_TCBList_ECBList_P_resume; eauto.

    go.

    change ((Vint32 i :: nil) ++ opv :: nil) with (Vint32 i  :: opv :: nil).
    assert (Hopv: opv = Vint32 (Int.repr OS_NO_ERR) \/ opv <>Vint32 (Int.repr OS_NO_ERR)) by tauto.
    destruct Hopv. 
    subst.

   (* opv = Vint32 (Int.repr OS_NO_ERR) *)    

   eapply abscsq_rule. 
   apply noabs_oslinv.
   eapply absimp_taskresume_ret.
   auto.
   can_change_aop_solver.
   eapply absinfer_eq.

    hoare forward.

    unfold OS_NO_ERR.
    splits; eauto.
    rewrite Int.unsigned_repr.
    lia.
    change Int.max_unsigned with 4294967295.
    lia.

  (* opv <> Vint32 (Int.repr OS_NO_ERR) *)    

   eapply abscsq_rule. 
   apply noabs_oslinv.
   eapply absimp_taskresume_ret_abt.
   can_change_aop_solver.
   auto.
   eapply absinfer_eq.
   eapply absabort_rule.


Unshelve.
auto.
auto.
auto.
auto.
auto.
auto.
    
Qed.
