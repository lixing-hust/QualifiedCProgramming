
Require Import ucos_include.

Require Import OSTimeDlyPure.
Require Import go.
Require Import Lia.
Require Import symbolic_lemmas.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

Require Import ifun_spec. 
(* Require Import OS_EventTaskPostRdy_pure. *)
 
Ltac rtmatch_solve:=   
  apply true_if_else_true;
  apply Zle_is_le_bool;
  try rewrite byte_max_unsigned_val; try rewrite max_unsigned_val;
  try lia.

Lemma lt_8_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i < 8 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma lt_64_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i < 64 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma lt_256_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i < 256 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma le_128_le_byte_max_unsigned_true :
  forall i,
    Int.unsigned i <= 128 -> Int.unsigned i <=? Byte.max_unsigned = true.
Proof.
  intros; mauto.
Qed.

Lemma z_le_255_imp_n_lt_256 :
  forall x : int32,
    Int.unsigned x <= 255 -> (Z.to_nat (Int.unsigned x) < 256)%nat.
Proof.
  apply z_le_255_imp_n; auto.
Qed.

Lemma  rl_tbl_grp_neq_zero:
  forall  v'12  px v'13 v'69,
    Int.unsigned px < 8 ->
    Int.unsigned v'12 <= 255 ->
    v'12 <> $ 0 ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32  px -> 
    nth_val' (Z.to_nat (Int.unsigned px)) v'13 = Vint32 v'69 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    v'69 <> $ 0.
Proof.
  introv Hran Hras Hneq Hnth Hth2 Hr.
  unfolds in Hr.
  assert (0 <=Z.to_nat (Int.unsigned px) < 8 )%nat.
  clear - Hran.
  mauto.
  apply nth_val'_imp_nth_val_int in Hth2.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsr : Hr H Hth2 H0.
  simp join.
  lets Hneqz : math_8_255_eq Hras Hneq; eauto.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned px)) = px).
  clear -Hran.
  mauto.
  rewrite H0 in *.
  rewrite Hneqz in *.
  assert (v'69 = $ 0 \/ v'69 <> $ 0) by tauto.
  destruct H4; auto.
  apply H1 in H4.
  false.
  gen H4.
  clear - Hran.
  mauto.
Qed.

Lemma int_ltu_3_iwordsize :
  Int.ltu ($ 3) Int.iwordsize = true.
Proof.
  apply int_iwordsize_gt_3.
Qed.

Lemma disj_intro :
  forall P Q R,
    P ==> R ->
    Q ==> R ->
    P \\// Q ==> R.
Proof.
  intros.
  destruct H1.
  apply H; auto.
  apply H0; auto.
Qed.

Lemma disj_combine :
  forall F sd I r ri s P Q R S tid linv,
    P ==> S -> Q ==> S ->
    {|F, sd, linv, I, r, ri|}|-tid {{S}} s {{R}} ->
                               {|F, sd, linv, I, r, ri|}|-tid {{P\\//Q}} s {{R}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply disj_intro; eauto.
  auto.
Qed.

Lemma pos_to_nat_range_0_7:
  forall z, 0<=z -> z<=7 -> (0<=Z.to_nat z<=7)%nat.
Proof.
  intros.
  split.
  mauto.
  assert (Z.to_nat 7 = 7)%nat.
  clear -z.
  mauto.
  rewrite <- H1.
  eapply Z2Nat.inj_le; lia.
Qed.


Lemma rl_tbl_grp_p_set_hold1:
  forall v'12 v'38 v'13 v'69 v'39 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
(*    nth_val' (Z.to_nat (Int.unsigned ((v'38<<$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)-> *)
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = true ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 (v'12&ᵢInt.not v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H13 in Hps.
  unfolds in H14.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H16.
  inverts H16.
  assert (Int.unsigned v'38 < 8) as Ha by lia.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H16 in *.
  inverts H17.
  assert (($ 1<<ᵢv'38)&ᵢInt.not v'41 = $ 0).
  clear - Ha H11.
  mautoext.
  splits.
  split.
  intros.
  auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  rewrite Int.and_commut.
  rewrite <-Int.and_assoc.
  assert ( v'12&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢv'12) .
  rewrite Int.and_commut; auto.
  rewrite H19 in Hzs.
  rewrite Hzs.
  auto.
  splits.
  rewrite Int.and_assoc.
  intros.
  assert (Int.not v'41&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢInt.not v'41).
  apply Int.and_commut.
  rewrite H19 in H18.
  rewrite H17 in H18.
  rewrite Int.and_zero in H18.
  unfold Int.zero in H18.
  false.
  clear -Ha H18.
  gen H18.
  mauto.
  intros.
  rewrite Hps in H18.
  false.
  eapply nth_upd_neq in H16; eauto.
  inverts H17.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsa : H14 H15 H16 H17.
  destruct Hsa.
  lets Hasd : math_nth_8_neq_not  H11 H18; try lia; eauto.
  split.
  split;
    intros.
  apply H19.
  rewrite Int.and_assoc in H21.
  rewrite Hasd in H21.
  auto.
  intros.
  apply H19 in H21.
  assert (v'12&ᵢInt.not v'41 = Int.not v'41 &ᵢ v'12).
  apply Int.and_commut.
  rewrite H22.
  rewrite Int.and_assoc.
  rewrite H21.
  rewrite Int.and_zero; auto.
  split.
  intros.
  apply H20.
  rewrite Int.and_assoc in H21.
  rewrite Hasd in H21.
  auto.
  intros.
  apply H20 in H21.
  rewrite Int.and_assoc.
  rewrite Hasd.
  auto.
Qed.

Lemma rl_tbl_grp_p_set_hold2
: forall (v'12 v'38 : int32) (v'13 : vallist)  (v'69 v'39 : int32) (v'40 v'41 : int32),
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = false->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 v'12).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H13 in Hps.
  unfolds in H14.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H16.
  inverts H16.
  assert (Int.unsigned v'38 < 8) as Ha by lia.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H16 in *.
  inverts H17.
  splits.
  splits.
  intros.
  lets Hsa : math_8_255_eq H0 H3 H.
  rewrite Hsa in H17.
  false.
  gen H17.
  clear - Ha.
  mauto.
  intros.
  tryfalse.
  split.
  intros.
  unfolds.
  rewrite zlt_true; auto.
  remember (v'69&ᵢInt.not v'40) as x.
  clear - Hps.
  assert (0<=Int.unsigned x) by (int auto).
  assert (0 = Int.unsigned x \/ 0 < Int.unsigned x) by lia.
  destruct H0; auto.
  false.
  apply Hps.
  rewrite H0.
  int auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  auto.
  inverts H17.
  eapply nth_upd_neq in H16;  eauto.
Qed.

Definition rel_edata_etype edata etype :=
  match edata with
  | DMsgQ _ _ _ _ =>
    etype = Int.repr OS_EVENT_TYPE_Q
  | DSem _ =>
    etype = Int.repr OS_EVENT_TYPE_SEM
  | DMbox _ =>
    etype = Int.repr OS_EVENT_TYPE_MBOX
  | DPort  =>
    etype = Int.repr OS_EVENT_TYPE_PORT
  | DMutex _ _ =>
    etype = Int.repr OS_EVENT_TYPE_MUTEX
  end.

Lemma hoare_pure_gen : forall P1 P2 (p:Prop) S Q a b c d e f tid,
    (forall s, s |= P1 -> p) ->
    {|a,b,c,d,e,f|}|-tid {{P1 ** P2 ** [|p|]}} S {{Q}} ->
                     {|a,b,c,d,e,f|} |-tid {{P1 ** P2}} S {{Q}}.
Proof.
  intros.
  apply backward_rule1 with (p:=(P1 ** P2 ** [|p|])); auto.
  intros.
  sep auto.
  destruct_s s.
  simpl in H1; simp join.
  apply (H (e0, e1, x, i, i0,(i1, i2, c0), x2, a0)); auto.
Qed.

Definition rel_edata_stat eid edata stat :=
  match edata with
  | DMsgQ _ _ _ _ =>
    exists n, stat = wait (os_stat_postq eid) n
  | DSem _ =>
    exists n, stat = wait (os_stat_sem eid) n
  | DMbox _ =>
    exists n, stat = wait (os_stat_mbox eid) n
  | DPort  =>
    exists n, stat = wait (os_stat_port eid) n
  | DMutex _ _ =>
    exists n, stat = wait (os_stat_mutexsem eid) n
  end.

Lemma PrioWaitInQ_RLH_ECB_PETbl_P_tcbls_ex :
  forall prio osevent etbl petbl l tcbls d,
    PrioWaitInQ prio petbl ->
    V_OSEventType osevent = Some (Vint32 (Int.repr OS_EVENT_TYPE_Q)) ->
    rel_edata_etype d (Int.repr OS_EVENT_TYPE_Q) ->
    RLH_ECB_PETbl_Q_P l (osevent,etbl,petbl) tcbls ->
    exists tid st m sus, get tcbls tid = Some ($ prio, st, m, sus) /\
                     rel_edata_stat l d st.
Proof.
  intros.
  unfold RLH_ECB_PETbl_Q_P in H2; simp join.
  lets Hx:H2 H; clear H2.
  destruct d; tryfalse; simpl in H1. substs.
  apply Hx in H0. simp join. do 4 eexists; split; simpl ;eauto.

Qed.


Lemma nth_val_nth_val'_some_eq : forall n vl x,
  nth_val n vl = Some x -> nth_val' n vl = x.
Proof.
  inductions n; intros.
  destruct vl; simpl in H; tryfalse.
  unfolds; simpl; inverts H; auto.

  simpl.
  destruct vl; simpl in H; tryfalse.
  apply IHn in H; auto.
Qed.

Lemma tcbls_get_some_TCBList_P_ptr_in_tcblist :
  forall vltcb head tcbls tid pr st m sus rtbl,
    get tcbls tid = Some (pr, st, m, sus) ->
    TCBList_P head vltcb rtbl tcbls ->
    ptr_in_tcblist (Vptr tid) head vltcb.
Proof.
  unfold get; simpl.
  inductions vltcb; intros.
  simpl in H0; substs.
  rewrite TcbMod.emp_sem in H; tryfalse.

  unfold TCBList_P in H0; fold TCBList_P in H0; simp join.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  unfold ptr_in_tcblist.
  unfold ptr_in_tcbdllseg; fold ptr_in_tcbdllseg.
  rewrite eq1; auto.
  
  unfold ptr_in_tcblist in *.
  unfold ptr_in_tcbdllseg; fold ptr_in_tcbdllseg.
  rewrite eq1.
  rewrite H1.
  assert (TcbMod.get x1 tid = Some (pr, st, m, sus)).
  unfold TcbJoin in H2.
  pose proof H2 tid.
  rewrite TcbMod.get_sig_none in H0.
  destruct(TcbMod.get x1 tid);
    destruct(TcbMod.get tcbls tid); tryfalse.
  substs; auto.
  clear H0.
  intro; substs.
  simpl in eq1.
  unfolds in eq1; destruct tid.
  rewrite beq_pos_Pos_eqb_eq in eq1.
  rewrite Pos.eqb_refl in eq1.
  rewrite Int.eq_true in eq1.
  simpl in eq1; tryfalse.
  eapply IHvltcb; eauto.
Qed.

Require Import new_inv.

Lemma tcbdllseg1_init_pre :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext,
    {|F, sd, linv, I, r, ri|}|-tid {{tcbdllseg1 head headprev tail tailnext vltcb nil **
                                                [|distinct_tcbdllseg_next_ptr head vltcb|] ** P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid {{tcbdllseg head headprev tail tailnext vltcb ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply tcbdllseg1_init'.
  auto.
Qed.


Lemma tcbdllseg1_split_pre :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext p holes,
    ptr_in_tcblist1 p head vltcb holes -> 
    {|F, sd, linv, I, r, ri|}|-tid {{ EX vl, node p vl OS_TCB_flag **
                                                  tcbdllseg1 head headprev tail tailnext vltcb ((p,vl)::holes) ** [|tcbdllseg1_get_node p head vltcb = Some vl|] **  P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid {{tcbdllseg1 head headprev tail tailnext vltcb holes ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule1.
  intros.
  eapply tcbdllseg1_split.
  sep auto.
  eauto.
  eapply backward_rule2; eauto.
  intros.
  sep pauto.
  sep lift 2%nat in H1.
  eapply ptr_in_tcbdllseg1_get_some; eauto.
  unfolds in H; simp join; auto.
Qed.

Lemma osmapvallist_prop:forall x, (Int.unsigned x <=7) -> exists i, nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 i /\ Int.unsigned i <= 128.
Proof.
  intros.
  lets Hx:Int.unsigned_range x.
  destruct Hx.
  clear H1.
  remember (Int.unsigned x) as z.
  clear Heqz.


  lets Hx: pos_to_nat_range_0_7 H0 H.
  destruct Hx.
  clear H H0.
  remember (Z.to_nat z) as n.
  clear Heqn.
  do 8 (
       destruct n;
       [ 
         simpl;
         eexists;split;eauto;
         rewrite Int.unsigned_repr;
         try solve [lia];
         rewrite max_unsigned_val;lia | ]).
  lia.
Qed.

Open Scope int_scope.

Lemma unsigned_int_and_not_range:
  forall x y,
    Int.unsigned x <= 255 ->
    Int.unsigned y<=255 ->
    Int.unsigned (x &ᵢInt.not y) <=? 255 = true.
Proof.
  intros.
  assert (Int.unsigned (x&ᵢInt.not y) <= Int.unsigned x).
  apply Int.and_le.
  assert (Int.unsigned (x&ᵢInt.not y) <= 255) by lia.
  apply Zle_imp_le_bool; auto.
Qed.

Lemma osq_same_blk_st_in':
  forall (qptr qst qend qin qout qsz qen : val) (b : block) (i : int32),
    WellformedOSQ0
      (qptr :: qst :: qend :: qin :: qout :: qsz :: qen :: Vptr (b, i) :: nil) ->
    exists i', qin = Vptr (b, i').
Proof.
  intros.
  funfold H.
  funfold H9.
  funfold H8.
  funfold H3.
   unfolds in H10.
  simpljoin1.
  unfold ptr_minus in *.
  unfold ptr_offset_right in *.
  fsimpl.
  simpl in H5.
  inverts H5.
  eexists; eauto.
Qed.

Definition auxand P Q := P /\ Q.

Lemma wellq_in_props:
  forall (x12 x11 x5 x6 : val) (v'49 : block) (x i2 i1 : int32)
         (v'47 : block) (x13 x14 : val) (v2 : list val) 
         (v'46 : absecb.B),
    length v2 = ∘OS_MAX_Q_SIZE ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x12
                :: x11
                :: x5
                :: Vptr (v'49, x)
                :: x6
                :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x13 :: x14 :: nil) v2) v'46 ->
    WellformedOSQ
      (x12
         :: x11
         :: x5
         :: Vptr (v'49, x)
         :: x6
         :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x /\
    4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
    Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
    Z.of_nat (length v2).
Proof.
  introv Hlen Hrl  Hwf.  
  assert (auxand (Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x)
                 (4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
                  Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
                  Z.of_nat (length v2)
                 )).
  funfold Hwf.
  unfold arrayelem_addr_right, qend_right  in *.
  unfold  ptr_offset_right, ptr_minus in *.
  simpljoin1.
  fsimpl.
  simpl in H7.
  subst i0.
  simpl in H13, H12,H10.
  clear H5.
  assert (Int.zero+ᵢ($ 4+ᵢInt.zero) = $4) as Heq.
  clear -x.
  mauto.
  rewrite Heq in *.
  clear Heq.
  unfolds in Hrl.
  destruct v'46. 
  destruct e; tryfalse.
  splits.
  clear - H0.
  int auto.
  apply eq_sym.
  eapply Z_div_exact_2; try lia.
  eapply math_prop_int_modu; eauto.
  eapply math_prop_ltu_20; eauto.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE.
  simpl.
  eapply math_prop_ltu_20; eauto.
  auto.
Qed.

Lemma wellq_in_props':
  forall (x12 x11 x5 x6 : val) (v'49 : block) (x i2 i1 : int32)  (v2 : list val) ,           
    length v2 = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ0
      (x12
         :: x11
         :: x5
         :: Vptr (v'49, x)
         :: x6
         :: Vint32 i2 :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x /\
    4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
    Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
    Z.of_nat (length v2).
Proof.
  introv Hlen (* Hrl  *) Hwf.  
  assert (auxand (Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x)
                 (4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
                  Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
                  Z.of_nat (length v2)
                 )).
  funfold Hwf.
  unfold arrayelem_addr_right, qend_right  in *.
  unfold  ptr_offset_right, ptr_minus in *.
  simpljoin1.
  fsimpl.
  simpl in H7.
  subst i0.
  simpl in H13, H12,H10.
  clear H5.
  assert (Int.zero+ᵢ($ 4+ᵢInt.zero) = $4) as Heq.
  clear -x.
  mauto.
  rewrite Heq in *.
  clear Heq.
  
  splits.
  clear - H0.
  int auto.
  apply eq_sym.
  eapply Z_div_exact_2; try lia.
  eapply math_prop_int_modu; eauto.
  eapply math_prop_ltu_20; eauto.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE.
  simpl.
  eapply math_prop_ltu_20; eauto.
  auto.
Qed.

Lemma wellformedosq_ens_add_1:
  forall x13 x12 x6 v'49 x x8 i2 i1 x10 x11 v'46 v2 v'36,
    length v2 = ∘OS_MAX_Q_SIZE ->
    RLH_ECBData_P
         (DMsgQ (Vptr (v'36, Int.zero))
                (x13
                   :: x12
                   :: x6
                   :: Vptr (v'49, x)
                   :: x8
                   :: Vint32 i2
                   :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
            (x10 :: x11 :: nil) v2) v'46 ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) -> Int.unsigned (i1+ᵢ$ 1) <= Int16.max_unsigned.
Proof.
  introv Ha Hlh Hwf.
  funfold Hwf.
  unfolds in Hlh.
  destruct v'46.
  destruct e;tryfalse.
  simpljoin1.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right,  ptr_minus in *.
  fsimpl.
  funfold H.
  simpl in H18, H17, H16 , H5. 
  inverts H5.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $4). 
  clear. 
  mauto.
  rewrite H in *.
  funfold H0.
  funfold H1.
  unfold distance in *.
  simpl in H23, H25, H26. 
  rewrite Int.repr_unsigned in *.
  clear H.
  remember ( ((Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) )) as M.
  remember ( Int.unsigned (Int.divu (i-ᵢ$ 4) ($ 4))) as N.
  assert (M = N \/ M > N \/ M < N).
  {
    clear.
    lia.
  }
  destruct H as [Ha1 | [Ha2 | Ha3]].
  match goal with H: M = N -> ?Q |- _ => apply H in Ha1 end.
  (* apply H25 in Ha1. *)
  destruct Ha1.
  simpljoin1.
  pose (Int.eq_spec x0 Int.zero) as Hps.
  rewrite H in Hps.
  subst.
  clear. 
  mauto.
  simpljoin1.
  pose (Int.eq_spec x0 m) as Hps.
  rewrite H in Hps.
  subst x0.
  clear - H13. 
  unfold OS_MAX_Q_SIZE in H13. 
  unfold  Int16.max_unsigned.
  simpl.
  mauto.
  match goal with H: M>N -> ?Q |- _ => lets Hzs: H Ha2 end. 
  eapply vallist_seg_length_prop in Hzs.
  rewrite Hzs in H5.
  eapply math_MN_le_int16; eauto.
  eapply math_MN_le_max; eauto.
  rewrite Ha.
  eapply math_MN_le_max; eauto.
  match goal with H: M<N -> ?Q |- _ => lets Hasb: H Ha3 end.
  (* lets Hasb : H24 Ha3. *)
  remember (vallist_seg ∘N ∘(Int.unsigned m) v2) as l1.
  eapply eq_sym in Heql1.
  eapply vallist_seg_length_prop in Heql1.
  remember (vallist_seg 0 ∘M v2) as l2.
  eapply eq_sym in Heql2.
  eapply vallist_seg_length_prop in Heql2.
  assert (length (l1 ++ l2) = length l )%nat.
  rewrite Hasb.
  auto.
  rewrite app_length in H.
  rewrite Heql1 in H; rewrite Heql2 in H.
  assert (length l < ∘(Int.unsigned m))%nat.
  assert (∘M < ∘N)%nat.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt.
  subst M.
  apply Int.unsigned_range.
  subst N.
  apply Int.unsigned_range.
  auto.
  clear - H9 H12 H H0.
  lia.
  eapply math_le_int16; eauto.
  clear. 
  lia.
  rewrite Ha.
  eapply math_MN_max_prop; eauto.
  eapply math_MN_max_prop; eauto.
  rewrite Ha.
  eapply math_MN_max_prop; eauto.
Qed.


Lemma tcbdllseg1_node_join_pre1 :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext b holes vl vl',
    struct_type_vallist_match OS_TCB_flag vl' ->
    ptr_in_tcbdllseg (Vptr (b, Int.zero)) head vltcb -> 
    same_prev_next vl' vl ->
    ~ptr_in (Vptr (b, Int.zero)) holes ->
    distinct_ptr holes ->
    distinct_tcbdllseg_next_ptr head vltcb ->
    {|F, sd, linv, I, r, ri|}|-tid
                                 {{ tcbdllseg1 head headprev tail tailnext (set_node (Vptr (b, Int.zero)) vl' head vltcb) holes ** P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid
                                                            {{ Astruct (b, Int.zero) OS_TCB_flag vl' ** tcbdllseg1 head headprev tail tailnext vltcb (((Vptr (b, Int.zero)),vl)::holes) ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule2.
  eauto.
  intros.
  eapply tcbdllseg1_node_join'; eauto.
  unfold node.
  sep pauto.
Qed.

Lemma tcbdllseg1_to_tcbdllseg_pre1 :
  forall F sd I r ri s linv tid P Q vltcb head headprev tail tailnext b vl',
    {|F, sd, linv, I, r, ri|}|-tid
                                 {{ tcbdllseg head headprev tail tailnext (set_node (Vptr (b, Int.zero)) vl' head vltcb) ** P}} s {{Q}} ->
                               {|F, sd, linv, I, r, ri|}|-tid
                                                            {{ tcbdllseg1 head headprev tail tailnext (set_node (Vptr (b, Int.zero)) vl' head vltcb) nil ** P}} s {{Q}}.
Proof.
  intros.
  eapply backward_rule1.
  eapply tcbdllseg1_tcbdllseg'.
  auto.
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

Lemma nth_val'2nth_val:
  forall n rtbl x,
    nth_val' n rtbl = Vint32 x ->
    nth_val n rtbl = Some (Vint32 x).
Proof.
  intros.
  inductions n;
    simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
Qed.

Lemma prio_in_tbl_preserv :
  forall tbl prio prio1 y row bitx,
    nth_val' (Z.to_nat (Int.unsigned y)) tbl = Vint32 row ->
    prio_in_tbl prio tbl ->
    y = prio1>>ᵢ$ 3 ->
    bitx = $ 1<<ᵢ(prio1&ᵢ$ 7) ->
    Int.unsigned prio1 < 64 ->
    prio_in_tbl prio (update_nth_val (Z.to_nat (Int.unsigned y)) tbl
                                     (Vint32 (Int.or row bitx))).
Proof.
  intros.
  substs.
  unfold prio_in_tbl in *.
  intros.
  lets fff: H0 H1 H2.
  unfold nat_of_Z in *.
  assert ( (Z.to_nat (Int.unsigned y)) <> (Z.to_nat (Int.unsigned (prio1>>ᵢ$ 3)))  \/ (Z.to_nat (Int.unsigned y)) = (Z.to_nat (Int.unsigned (prio1>>ᵢ$ 3))) ). 
  tauto.
  elim H5; intros.
  apply nth_upd_neq in H4.
  apply fff.
  exact H4.
  intro; tryfalse.
  
  rewrite <- H6 in *.    

  lets fffb: H0 H1 H2 (nth_val'2nth_val _ _ _ H).
  apply nth_upd_eq in H4.
  simpl in H4.
  inverts H4.
  rewrite Int.and_or_distrib_l.
  rewrite fffb.
  assert ( 0<=Int.unsigned (($ 1<<ᵢ(prio1&ᵢ$ 7))) < 256).
  clear -H3; mauto.
  assert (0<=Int.unsigned x < 8).
  rewrite H1.
  rewrite Int.and_commut.
  clear.
  split.
  remember ($ 7&ᵢprio).
  int auto.
  change 8 with (Int.unsigned ($ 8)).
  assert ( Int.unsigned ($ 7&ᵢprio) <= Int.unsigned ($ 7)).
  apply Int.and_le.
  ur_rewriter.
  ur_rewriter_in H.
  lia.
  lets bbba: prio_int_disj H4 H7.
  clear -bbba H7.
  destruct bbba; intros; rewrite H.
  clear -H7; mauto.
  clear -H7; mauto.
Qed.

Lemma rl_rtbl_priotbl_p_hold:
  forall v'36 v'12 v'13 v'38 v'69 v'39 v'58 v'40 v'41 v'57 v'37 vhold,
    (v'58, Int.zero) <> vhold ->
    RL_RTbl_PrioTbl_P v'37 v'36 vhold->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_EVENT_TBL_SIZE ->
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
    Int.unsigned v'57 <= 255 ->
    array_type_vallist_match Tint8 v'37 ->
    length v'37 = nat_of_Z OS_RDY_TBL_SIZE ->
    RL_RTbl_PrioTbl_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                      (val_inj
                         (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
      v'36 vhold.
Proof.
  introv Hnvhold.
  intros.
  unfold  RL_RTbl_PrioTbl_P  in *.
  unfolds in H17.
  unfolds in H18.
  intros.
  unfolds in H23.
  assert (  p&ᵢ$ 7  = p&ᵢ$ 7 ) by auto.
  assert (Int.shru p ($ 3) = Int.shru p ($ 3)) by auto.
  assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <> Z.to_nat (Int.unsigned v'38) \/
           ∘(Int.unsigned (Int.shru p ($ 3))) = (Z.to_nat (Int.unsigned v'38)))%nat.
  tauto.

  lets Hy : math_unmap_get_y H1 H6.
  assert ( ∘(Int.unsigned (Int.shru p ($ 3))) <∘OS_EVENT_TBL_SIZE)%nat.
  clear -H22.
  mauto.
  lets Ha : nthval'_has_value H4  H27; eauto.
  destruct Ha as (x&Hnth & Htru).
  lets Hnt : nth_val'_imp_nth_val_int Hnth.
  destruct H26.
  assert ( nth_val ∘(Int.unsigned (Int.shru p ($ 3)))
                   (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                   (val_inj
                                      (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                          (Vint32 v'40)))) = Some (Vint32 x)).
  eapply nth_upd_neqrev; eauto.
  lets Hb : H23 H24 H25 H28 .
  assert (Int.unsigned (Int.shru p ($ 3))<8). 
  clear - H22.
  mauto.
  remember (Int.shru p ($3)) as px. 
  assert ($ Z.of_nat ∘(Int.unsigned px) = px).
  clear - H29.
  mauto.
  assert (prio_in_tbl p v'37 ).
  unfolds.
  intros.
  subst.
  rewrite H33 in Hnt.
  inverts Hnt.
  auto.
  eapply H; eauto.
  assert (  p&ᵢ$ 7 = v'39 \/  p&ᵢ$ 7 <> v'39).
  tauto.
  destruct H28.
  subst v'39.

  lets Hzzp : int_usigned_tcb_range H22.
  destruct Hzzp.
  remember (Int.shru p ($3)) as px.
  assert (px = v'38).
  clear - Hy  H29 H26.
  gen H26.
  mauto.
  subst v'38.
  subst px.
  assert ( (((Int.shru p ($ 3))<<ᵢ$ 3)+ᵢ(p&ᵢ$ 7)) = p).
  clear -H22.
  mauto.
  rewrite H30 in H12.
  apply nth_val'_imp_nth_val_vptr in H12.
  eexists; eauto.
  assert ( prio_in_tbl p v'37).
  unfolds.
  intros.
  subst.
  lets Hzzp : int_usigned_tcb_range H22.
  destruct Hzzp.
  remember (Int.shru p ($3)) as px.
  remember (p&ᵢ$ 7) as py.
  assert ( px = v'38).
  clear -Hy H30 H26.
  gen H26.
  mauto.
  subst v'38.
  rewrite Hnt in H31.
  inverts H31.
  remember ((val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned px)) v'37)
                   (Vint32 v'40)))) as v.
  unfold val_inj in Heqv.
  rewrite H26 in Hnth.
  rewrite Hnth in Heqv.
  unfold or in Heqv.
  subst v.
  assert ( nth_val ∘(Int.unsigned (px))
                   (update_nth_val (Z.to_nat (Int.unsigned px)) v'37
                                   (Vint32 (Int.or z v'40))) =Some (Vint32 (Int.or z v'40))).
  rewrite <- H26.
  eapply pure_lib.update_nth; eauto.
  lets Hd : H23 H31; eauto.
  rewrite Int.and_commut in Hd.
  rewrite Int.and_or_distrib in Hd.
  lets Hzzps :  math_nth_8_eq_zero'  H13 H29 H28; eauto; try lia.
  rewrite Int.and_commut in Hzzps.
  rewrite Hzzps in Hd.
  rewrite Int.or_zero in Hd.
  rewrite Int.and_commut in Hd.
  auto.
  eapply H; eauto.
Qed.

Lemma get_wellformedosq_in_setst:
  forall i1 i2 x13 x12 x6 v'49 x x8,
    (* Int.ltu i1 i2 = true -> *)
    WellformedOSQ0
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    val_inj
      match x6 with
        | Vundef => None
        | Vnull => Some (Vint32 Int.zero)
        | Vint32 _ => None
        | Vptr (b2, ofs2) =>
          if peq v'49 b2
          then
            if Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) ofs2
            then Some (Vint32 Int.one)
            else Some (Vint32 Int.zero)
          else Some (Vint32 Int.zero)
      end <> Vint32 Int.zero ->
    WellformedOSQ0
      (x13
         :: x12
         :: x6
         :: x12
         :: x8
         :: Vint32 i2
         :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil).
Proof.
  introv (* Hlt *) Hvl Hj.
  funfold Hvl.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  destruct x1.
  destruct x3.
  destruct x5.
  fsimpl.
  rewrite peq_true in Hj.
  remember (Int.eq (x+ᵢInt.mul ($ 1) ($ 4)) i) as Hb.
  destruct Hb; simpl in Hj; tryfalse.
  apply eq_sym in HeqHb.
  pose ( Int.eq_spec (x+ᵢInt.mul ($ 1) ($ 4)) i ) as Hpx.
  rewrite HeqHb in Hpx.
  subst i.
  simpl in H7.
  subst.
  simpl in H5.
  assert ( Int.zero+ᵢ($ 4+ᵢInt.zero) = $ 4) as Hx.
  clear.
  int auto.
  int auto.
  rewrite Hx in *.
  assert (Int.mul ($ 1) ($ 4) = $ 4) as Hy.
  clear.
  int auto.
  rewrite Hy in *.
  simpl in *.
  do 7 eexists.
  splits; try solve [unfolds; simpl; eauto].
  splits; eauto.
  unfolds.
  splits; simpl; eauto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; auto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  auto.
  unfolds.
  eexists.
  unfold ptr_offset_right, ptr_minus in *.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
  simpl.
  assert (Int.divu ($ 4-ᵢ$ 4) ($ 4) = $0).
  clear.
  mauto.
  rewrite H1.
  rewrite Int.unsigned_repr.
  eapply Z2Nat.inj_lt;lia.
  clear.
   int auto.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  eexists; splits; eauto.
Qed.

(* Goal (forall i j, (Int.unsigned (Int.add i j) <=? Int.max_unsigned) = true). *)
(*     intros. clear. *)
(*     destruct (Int.add i j). simpl. unfold Int.max_unsigned. *)
(*     destruct intrange. *)
(*     mauto. *)
(* Qed.  *)

Lemma get_wellformedosq_in_setst':
  forall i1 i2 x13 x12 x6 v'49 x x8,
    x6 <> Vptr (v'49,  (x+ᵢInt.mul ($ 1) ($ 4))) ->
    WellformedOSQ0
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    WellformedOSQ0
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
         :: x8
         :: Vint32 i2
         :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil).
Proof.
  intros.
  assert (Int.mul ($ 1) ($ 4) = $ 4) by mauto.
  rewrite H1 in *.
  funfold H0.
  unfold qend_right, arrayelem_addr_right in *.
  simpljoin1.
  unfold ptr_offset_right, ptr_minus in *.
  fsimpl.
  simpl in *.
  assert ( Int.zero+ᵢ($ 4+ᵢInt.zero) = $ 4).
  clear -x.
  mauto.
  rewrite H3 in *.
  inverts H7.
  (* unfolds. *)
  do 7 eexists. 
  splits; try solve [unfolds; simpl; eauto].
  rewrite H3 in *.
  splits; eauto.
  unfolds.
  splits; simpl; auto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  auto.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  eexists.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
  simpl.
  eapply  math_ltu_false_false; eauto.
  simpl.
  eapply math_lt_mod_lt with i2 ;eauto.
  intro Hf.
  subst i2.
  tryfalse.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  eexists.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  splits; eauto.
Qed.

Lemma TCBList_P_get_node_TCBNode_P :
  forall vltcb head rtbl tcbls vl tid prio st m,
    TCBList_P head vltcb rtbl tcbls ->
    tcbdllseg1_get_node (Vptr tid) head vltcb = Some vl ->
    get tcbls tid = Some (prio, st, m) ->
    TCBNode_P vl rtbl (prio, st, m).
Proof.
  unfold get; simpl.
  inductions vltcb; intros.
  simpl in H; substs.
  rewrite TcbMod.emp_sem in H1; inversion H1.

  unfold TCBList_P in H; fold TCBList_P in H.
  unfold tcbdllseg1_get_node in H0; fold tcbdllseg1_get_node in H0; simp join.
  destruct (beq_val (Vptr tid) (Vptr x)) eqn : eq1.
  inverts H0.
  pose proof H3 tid.
  rewrite H1 in H.
  apply beq_val_true_eq in eq1; inverts eq1.
  rewrite TcbMod.get_sig_some in H.
  destruct (TcbMod.get x1 x); tryfalse.
  substs; auto.
  destruct(V_OSTCBNext a); tryfalse.
  inverts H2.
  eapply IHvltcb; eauto.
  pose proof H3 tid.
  rewrite H1 in H.
  rewrite TcbMod.get_sig_none in H.
  destruct(TcbMod.get x1 tid); tryfalse.
  substs; auto.
  intro; substs.
  rewrite beq_val_true in eq1; tryfalse.
Qed.

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

Theorem cast_rv_tint32_tint16 :
  forall s e v v',
    s |= Rv e @ Tint32 == (Vint32 v) ->
    cast_eval v Tint32 Tint16 = Some v' ->
    s |= Rv (ecast e (Tint16)) @ (Tint16) == (Vint32 v').
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  auto.
  simpl.
  rewrite H.
  simpl in H0.
  inverts H0.
  auto.
  simpl.
  rewrite H1.

  auto.
Qed.

Require Import sem_lab. 
Require Import seplog_trm_tacs. 
     
Lemma OSEventTaskPostRdy_qdel_proof:
  forall vl p r ll ct, 
    Some p =
    BuildPreI os_internal OS_EventTaskPostRdyDel vl ll OS_EventTaskPostRdyDelPre ct ->
    Some r =
    BuildRetI os_internal OS_EventTaskPostRdyDel vl ll OS_EventTaskPostRdyDelPost ct ->
    exists t d1 d2 s,
      os_internal OS_EventTaskPostRdyDel = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.

  rename v'29 into lg'.   
  rename H13 into Htype.
  rename H14 into HR_ECB_PETbl_P.
  rename H15 into Hll.  
  simpl in H10, H11; inverts H10; inverts H11.  
  rename v'18 into dd1. 
  rename v'26 into dd2. 
  rename v'19 into dd3.
  rename v'20 into dd4.
  rename v'30 into ier.
  hoare unfold.
  unfold AOSPostEventTbl.
  hoare_split_pure_all.

  hoare unfold.
  rename v'13 into pegrp. 
  rename v'16 into etbl.
  assert (v'26 = Vint32 pegrp).
  {
    rewrite H20 in H12.
    clear -H12. inverts H12; auto. 
  } 
  subst v'26. 
  inverts H12.
  clear H20.  
  rename i0 into egrp. 
  rename v'17 into petbl.

  assert (H_: 
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
  {
    lets Hx1: osunmapvallist_prop H32; simpljoin. 
    apply Zle_bool_imp_le in H12. 
    pose proof z_le_7_imp_n x H12.
    lets Hx2: array_int8u_nth_lt_len H.
    rewrite H3 in Hx2.
    unfold OS_EVENT_TBL_SIZE in Hx2.
    lets Hx2': Hx2 H14; clear Hx2; simpljoin.
    lets Hx3: osunmapvallist_prop H20; simpljoin. 
    apply Zle_bool_imp_le in H41. 
    lets Hx4: osmapvallist_prop H12.
    lets Hx5: osmapvallist_prop H41. 
    simp join.
    exists x3 x x0 x5 x6. 
    splits; eauto.
    clear - H12; int auto. 
    clear - H20; int auto. 
    clear H20 H40 H42 H44. 

    eapply rl_tbl_grp_neq_zero; eauto.
    clear - H12.
    int auto.
    clear - H41; int auto. 
  }  
  destruct H_ as [x [y [erow [bitx [bity H_]]]]]. 
  destruct H_ as
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
  rewrite H3; simpl; auto. 
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
  rewrite H3; simpl; auto.
  simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
  rewrite map_x; rewrite bitx_ble_max; auto.
  rewrite map_x; simpl; intro; tryfalse.
  rewrite nth_val_etbl; rewrite map_x; simpl; intro; tryfalse.
  rewrite y_ble_max; auto.
  apply eq_int; auto.
  rewrite H3; simpl; auto.

  (*If((pevent ′ → OSEventTbl) [y ′] ==ₑ ′0)*)
  hoare forward.
  rewrite y_ble_max; auto.
  rewrite update_nth_val_len_eq; rewrite H3; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  rewrite unsigned_int_and_not_range; auto.
  lia.
  lia.
  rewrite H3; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)); simpl; intro; tryfalse.
  rewrite H3; simpl; auto.
 
  (*pevent ′ → OSPostEventGrp &= ∼ os_code_defs.bity ′*)
  hoare forward; pure_auto.

  (*combine the 2 cases after the IF stmt into one case*)
  rewrite nth_val_etbl; rewrite map_x. 
  apply disj_combine with (S:=(
                                EX pegrp',
                                  [| RL_Tbl_Grp_P (update_nth_val (Z.to_nat (Int.unsigned y)) petbl
                                                                (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) (Vint32 pegrp')  /\
                                     Int.unsigned pegrp' <= 255|] **
                                   <|| v'21 ||>  **
                                   Aarray v'18 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
                                   LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
                                   Astruct (v'29, Int.zero) os_ucos_h.OS_EVENT
                                     (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i4 :: Vptr (v'30, Int.zero) :: x1 :: x2 :: Vint32 pegrp' :: x4 :: nil)  **
                                   Aarray v'20 (Tarray char_t ∘OS_EVENT_TBL_SIZE)
                                     (update_nth_val (Z.to_nat (Int.unsigned y)) petbl
                                                   (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) **
                                   LV prio @ char_t |-> val_inj
                                     (add
                                        (val_inj
                                           (if Int.ltu ($ 3) Int.iwordsize
                                            then Some (Vint32 (y<<ᵢ$ 3))
                                            else None))
                                        (nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist) Int32u char_t) **
                                   LV os_code_defs.bitx @ char_t |-> Vint32 bitx **
                                   LV os_code_defs.x @ char_t |-> nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist **
                                   LV os_code_defs.bity @ char_t |-> Vint32 bity **
                                   LV os_code_defs.y @ char_t |-> Vint32 y **
                                   Aie false **
                                   Ais nil **
                                   Acs (true :: nil) **
                                   Aisr empisr **
                                   A_isr_is_prop **
                                   Aier ier **
                                   Astruct (v'32, Int.zero) os_ucos_h.OS_Q_FREEBLK (x15 :: x16 :: nil) **
                                   Aarray v'31 (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE) dd4 **
                                   Astruct (v'30, Int.zero) os_ucos_h.OS_Q
                                     (x14 :: x13 :: x7 :: x8 :: x9 :: Vint32 i3 :: Vint32 i2 :: Vptr (v'32, Int.zero) :: nil) ** 
                                   GAarray OSUnMapTbl (Tarray char_t 256) OSUnMapVallist **
                                   GAarray OSMapTbl (Tarray char_t 8) OSMapVallist **
                                   AOSRdyTblGrp v'10 v'11 **
                                   GAarray OSTCBPrioTbl (Tarray os_ucos_h.OS_TCB ∗ 64) v'9 **
                                   tcbdllseg v'22 v'23 v'24 v'25 v'12 **
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
  eapply rl_tbl_grp_p_set_hold1; eauto.
  clear - y_lt8; int auto.
  clear - erow_lt256; int auto.
  clear - x_lt8; int auto.
  clear - H14 H17 H20 H3 y_lt8.
  simpl val_inj in *.
  assert(Int.unsigned y < Z.of_nat (length petbl)).
  rewrite H3; int auto.
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
  clear - H20 y_lt8 H3. 
  simpl val_inj in H20.
  rewrite len_lt_update_get_eq in *.
  simpl val_eq in H20.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)) eqn : eq1; auto.
  destruct H20; simpl in H; tryfalse.
  rewrite H3; unfold OS_EVENT_TBL_SIZE; simpl; auto.
   
  (*ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ*)
  rewrite int_ltu_3_iwordsize.
  rewrite unmap_erow.
  simpl val_inj.

  (*get the relation between event data and event type*)
  hoare_split_pure_all. 

  assert (rel_ed_et:
            rel_edata_etype (DMsgQ (Vptr (v'30, Int.zero)) dd2 (x15 :: x16 :: nil) dd4) ($ OS_EVENT_TYPE_Q))  
  by (simpl; auto). 
  rename v'8 into tcbls. 
  rename v'9 into ptbl.  
 
  (*prove prio lt 64*)
  assert (prio_lt64: Int.unsigned ((y<<ᵢ$ 3)+ᵢx) < 64). 
  {
    clear - y_lt8 x_lt8. mauto.
  }

  (*prio ble max byte*)
  pose proof lt_64_le_byte_max_unsigned_true ((y<<ᵢ$ 3)+ᵢx) prio_lt64 as prio_ble_max.

  (*prove exist a tid coresponding to prio in tcbls*)
  assert(ex_tid_prio_rel:
           exists tid st m sus,
             get tcbls tid = Some ((y<<ᵢ$ 3)+ᵢx, st, m, sus) /\
             rel_edata_stat (v'29, Int.zero) (DMsgQ (Vptr (v'30, Int.zero)) dd2 (x15 :: x16 :: nil) dd4) st). 
  {
    assert (y_shl3_shr3: ($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)>>ᵢ$ 3) = y).
    { clear - x_lt8 y_lt8. mauto. } 

    assert (y_shl3_and7: ($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)&ᵢ$ 7) = x). 
    { clear - x_lt8 y_lt8. mauto. }

    unfold R_ECB_ETbl_P in H7; simp join. 
    eapply PrioWaitInQ_RLH_ECB_PETbl_P_tcbls_ex; eauto.
    
    2: { 
      instantiate (1:=(V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i4 :: Vptr (v'30, Int.zero)
                        :: x1 :: x2 :: Vint32 pegrp :: x4 :: nil)).  
      simpl; auto.
    }
    2: { eapply HR_ECB_PETbl_P. }
    
    unfolds.
    clear - prio_lt64 y_lt8 x_lt8 H H3 nth_val_etbl unmap_erow erow_lt256 erow_ne0 y_shl3_shr3 y_shl3_and7. 
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
  }
  destruct ex_tid_prio_rel as [tid [st [m [sus [tcbls_tid_prio rel_ed_st]]]]]. 

  (*prove vptr tid indexed by prio in prio table*)
  rename v'7 into vhold.
  assert (nth_val_ptbl_vhold:
        nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl = Vptr tid /\ tid <> vhold). 
  clear - H7 (* R_PrioTbl_P *) tcbls_tid_prio.  
  unfolds in H7; destruct H7; destruct H0. 
  eapply H0 in tcbls_tid_prio; simp join; split; auto. 
  
  apply nth_val_nth_val'_some_eq; auto.
  destruct nth_val_ptbl_vhold as [nth_val_ptbl tid_neq_vhold].
  
  (*do the statement*)
  hoare forward.
  rewrite prio_ble_max; auto.
  rewrite nth_val_ptbl.
  simpl; auto.

  (*key step: prove tid in tcbdllseg*)
  rename v'22 into head; rename v'23 into headprev;
  rename v'24 into tail; rename v'25 into tailnext;
  rename v'12 into vltcb.

  assert (ptr_in_tcblist (Vptr tid) head vltcb).
  { eapply tcbls_get_some_TCBList_P_ptr_in_tcblist; eauto. }
  
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
  lets Hx: osq_same_blk_st_in' H0; simpljoin.  
  simpl in H11; inverts H11. 
  lets Hy: wellq_in_props' H22 (*length dd4 = ...*) (* Hlh_ecbdata *) H0; eauto. 
  simpljoin.

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
  sep cancel (Astruct (v'30, Int.zero)).
  eauto.
  introv Hsat.
  auto. 
  go. go. go. go. go. go. go. go. go. 
  introv Hsat.
  eapply cast_rv_tint32_tint16; eauto. 
  eapply bop_rv.
  eapply struct_member_rv''.
  sep cancel pq.
  sep cancel (Astruct (v'30, Int.zero)).
  eauto.
  go. go. go. go. go. go. go. simpl. eauto. go.
  clear -H38.
  asserts_rewrite ((Int.unsigned i2 <=? Int16.max_unsigned) = true).
  {
    change (Int16.max_unsigned) with 65535.
    apply Zle_imp_le_bool in H38; auto.
  }
  auto. 
  sep get rv.
  pure_auto.
  pure_auto.
  go.
  go.
  apply eq_int. auto.
  simpl. clear. mauto.
  simpl. eauto.
  introv Hsat. sep pauto. sep cancel p_local. sep auto.  
  
  (* If(pq ′ → OSQIn ==ₑ pq ′ → OSQEnd)*)
  (* pure intro. *)
  (* lets Hx: wellformedosq_ens_add_1 H47 Hlh_ecbdata H45. *)
  (* rename Hx'' into Hx. *)
  eapply seq_rule. 
  eapply lzh_if_then_rule.
  introv Hsat.
  eapply bop_rv.
  sep_lifts_trms_in Hsat (pq, Astruct (v'30, Int.zero)).
  eapply struct_member_rv''.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  go. go. go. go. go. go. go. go. go.
  sep_lifts_trms_in Hsat (pq, Astruct (v'30, Int.zero)).
  eapply struct_member_rv''.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto.
  go. go. go. go. go. go. go. go.
  pure_auto.  (* rule_type_val_match ((Void) ∗) ∗ x7 *)
  go.
  clear -H34.
  destruct H34.
  subst. pure_auto.
  simpljoin. destruct x. destruct (peq v'32 b). pure_auto. pure_auto. 
  go.

  (* hoare forward. *)
  (* simpl.  *)
  (* splits; (try (pure_auto; fail)).  *)
  hoare unfold.
  eapply assign_rule_struct_aop.
  split.
  introv Hsat.
  sep cancel pq.
  sep cancel (Astruct (v'30, Int.zero)).
  eauto. 
  introv Hsat.
  auto.
  go. go. go. go. go. go. go.
  introv Hsat.
  eapply struct_member_rv''.
  sep cancel pq.
  sep cancel (Astruct (v'30, Int.zero)).
  eauto.
  go. go. go. go. go. go. go. go.
  clear -H33. (* isptr x13 *)
  destruct H33. subst. pure_auto. simpljoin. pure_auto.
  apply eq_vptr. do 2 eexists; split; eauto.
  simpl. clear. mauto.
  go.
  introv Hsat.
  sep pauto.
  sep cancel p_local. sep auto.

  assert (Hend: exists aend, x7 = Vptr aend).
  {
    clear -H0. (* Wellformed ... *)
    funfold H0.
    eexists; eauto. 
  }
  destruct Hend as (aend & Hend). subst x7.
  
  eapply backward_rule1 with
  (p:= (EX new_qin,
        [| ((v'32, x0 +ᵢ  Int.mul ($ 1) ($ 4)) = aend /\ new_qin = x13) \/
         ((v'32, x0 +ᵢ  Int.mul ($ 1) ($ 4)) <> aend /\ new_qin = (Vptr (v'32, x0 +ᵢ  Int.mul ($ 1) ($ 4)))) |] **
         <|| v'21 ||>  ** 
   LV pq @ os_ucos_h.OS_Q ∗ |-> Vptr (v'30, Int.zero) **
   Astruct (v'30, Int.zero) os_ucos_h.OS_Q
   (x14 :: x13 :: Vptr aend :: new_qin :: x9 :: Vint32 i3 ::
        Vint32 (Int.modu (i2 +ᵢ  $ 1) ($ Int16.modulus)) :: Vptr (v'32, Int.zero) :: nil) ** 
   Aarray (v'32, Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero)) (Tarray (Void) ∗ ∘ OS_MAX_Q_SIZE)
     (update_nth_val (Z.to_nat ((Int.unsigned x0 - Int.unsigned (Int.zero +ᵢ  ($ 4 +ᵢ  Int.zero))) / 4)) dd4 x17) **
   Astruct (v'32, Int.zero) os_ucos_h.OS_Q_FREEBLK (x15 :: x16 :: nil) **
   LV ptcb @ os_ucos_h.OS_TCB ∗ |-> Vptr (v'8, Int.zero) **
   Astruct (v'8, Int.zero) OS_TCB_flag
     (x20
      :: x19
         :: Vnull :: x17 :: V$ 0 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil) **
   tcbdllseg1 head headprev tail tailnext vltcb
     ((Vptr (v'8, Int.zero),
      x20
      :: x19
         :: x18
            :: x17 :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
      :: nil) **
   Aarray v'18 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl **
   LV pevent @ os_ucos_h.OS_EVENT ∗ |-> Vptr (v'29, Int.zero) **
   Astruct (v'29, Int.zero) os_ucos_h.OS_EVENT
     (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i4 :: Vptr (v'30, Int.zero) :: x1 :: x2 :: Vint32 v'13 :: x4 :: nil) **
   Aarray v'20 (Tarray char_t ∘ OS_EVENT_TBL_SIZE)
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
   Aier ier **
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
                     :: (os_code_defs.bity, char_t) :: (prio, char_t) :: (pq, os_ucos_h.OS_Q ∗) :: nil))). 
  
  introv Hsat.
  destruct Hsat.
  
  (*if true*)
  sep auto. 
  left.
  split; auto.
  simpljoin.
  clear - H57. 
  destruct aend. 
  destruct (peq v'32 b) eqn : eq1; 
    destruct (Int.eq (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H57; tryfalse. 
  substs.
  pose proof Int.eq_spec (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i.
  rewrite eq2 in H.
  substs; auto. 

  (*if false*)
  sep auto.
  right.
  split; auto.
  simpljoin.
  clear - H57. 
  destruct aend. 
  destruct (peq v'32 b) eqn : eq1; 
    destruct (Int.eq (x0 +ᵢ  Int.mul ($ 1) ($ 4)) i) eqn : eq2;
    simpl in H57; destruct H57; tryfalse. 
  substs.
  introv Hf.
  inverts Hf.
  pose proof Int.eq_spec (x0 +ᵢ  Int.mul ($ 1) ($ 4)) (x0 +ᵢ  Int.mul ($ 1) ($ 4)).
  rewrite eq2 in H0.
  tryfalse.

  introv Hf; inverts Hf.
  tryfalse.

  introv Hf; inverts Hf.
  tryfalse.
  
  (*ptcb ′ → OSTCBStat &= ∼ msk ′;ₛ*)
  hoare forward; pure_auto.

  (* If (ptcb ′ .. OSTCBStat ==ₑ ′ OS_STAT_RDY) *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyGrp.
  hoare unfold.
  rename v'10 into rtbl.
  rename i9 into rgrp.
  rename H57 into rgrp_le255.
  hoare_assert_pure (array_type_vallist_match char_t rtbl /\ length rtbl = ∘ OS_RDY_TBL_SIZE).
  { unfold AOSRdyTbl in H57.
    seplog_trm_tacs.sep_lifts_trms_in H57 array_type_vallist_match.
    eapply sep_pure_split in H57; destruct H57 as (Hmat & _).
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
  rewrite H60.
  clear - map_x x_lt8.
  apply math_mapval_core_prop; auto.

  assert (Hprop: Int.unsigned (i7&ᵢInt.not v'6) <= 65535).
  {eapply Z.le_trans. apply Int.and_le. eauto. }
  hoare forward.
  go.
  pure_auto.
  hoare_split_pure_all.
  destruct (Int.eq (i7&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H57; destruct H57 as (Hif & _); tryfalse.
  clear Hif.

  hoare_lifts_trms_pre (Astruct (v'8, Int.zero) OS_TCB_flag, tcbdllseg1).
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
  destruct H57.
  
  hoare unfold.
  hoare forward.
  pure_auto.
  rewrite H60; unfold OS_RDY_TBL_SIZE; simpl; auto. 
  simpl; rewrite nth_val_rtbl; pure_auto.
  pure_auto.
  rewrite nth_val_rtbl; simpl; intro; tryfalse.
  pure_auto.
  unfold OS_RDY_TBL_SIZE; simpl; auto.
  rewrite H60; unfold OS_RDY_TBL_SIZE; simpl; auto.

  assert (Hwell: WellformedOSQ0
  (x14
   :: x13
      :: Vptr aend
         :: v'7
            :: x9
               :: Vint32 i3
                  :: Vint32 (Int.modu (i2 +ᵢ  $ 1) ($ Int16.modulus))
                     :: Vptr (v'32, Int.zero) :: nil)).
  {
     destruct H56; simpljoin; substs.
     eapply get_wellformedosq_in_setst; eauto.
     rewrite Int.eq_true.
     rewrite peq_true.
     pure_auto.
     eapply get_wellformedosq_in_setst'; eauto.
     introv Hf; inverts Hf; tryfalse.
   }
  assert(Hqmat: struct_type_vallist_match OS_Q
  (x14
   :: x13
      :: Vptr aend
         :: v'7
            :: x9
               :: Vint32 i3
                  :: Vint32 (Int.modu (i2 +ᵢ  $ 1) ($ Int16.modulus))
                     :: Vptr (v'32, Int.zero) :: nil)).
  { assert(Hr: Int.unsigned (Int.modu (i2 +ᵢ  $ 1) ($ Int16.modulus)) <= Int16.max_unsigned).
    assert (Hbound: 0 <= Int.unsigned (Int.add i2 ($1)) mod 65536 < 65536).
    {
      apply Z.mod_pos_bound. mauto. 
    }
    unfold Int.modu.
     change (Int.unsigned ($ Int16.modulus)) with 65536.
     change Int16.max_unsigned with 65535.
     lets Heq: Int.unsigned_repr (Int.unsigned (i2 +ᵢ  $ 1) mod 65536).
     rewrite Heq.
     auto with zarith.
     change Int.max_unsigned with 4294967295.
     auto with zarith.
     destruct H56; simpljoin; substs.
     go.
     go.
  }

  assert (Hstat: i7 = $ OS_STAT_POSTQ \/ i7 = Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND)).
  {
    lets Hx: TCBList_P_get_node_TCBNode_P H9 H17 tcbls_tid_prio.
    clear - Hx rel_ed_st.
    unfold TCBNode_P in Hx; simp join.
    clear - H2 rel_ed_st.
    unfolds in H2; simp join.
    lets H00: RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat H4 rel_ed_st; eauto.
  }

  hoare forward.
  Focus 2.
  hoare_split_pure_all.
  destruct (Int.eq (i7&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H57; destruct H57 as [Hif1 |  Hif2]; tryfalse.
  clear Hif1.
  hoare_lifts_trms_pre (Astruct (v'8, Int.zero) OS_TCB_flag, tcbdllseg1).
  apply tcbdllseg1_node_join_pre1; auto.
  go.
  unfolds; simpl; auto.
  simpl; auto.
  apply tcbdllseg1_to_tcbdllseg_pre1.
(*   hoare forward. *)
  eapply rete_rule.
  introv Hsat.
  eapply aconj_intro.
  2: { sep get rv.
          rewrite prio_ble_max; auto. }
 sep normal.
 sep eexists.
eapply astar_l_apure_intro.
eapply astar_l_apure_intro.
2: instantiate(7:= i7); eauto.
sep cancel Aop.
sep cancel Aier.
sep cancel Aie.
sep cancel Ais.
sep cancel Acs.
sep cancel Aisr.
sep cancel A_isr_is_prop.
sep cancel A_dom_lenv.
sep cancel p_local.
sep cancel tcbdllseg.
sep split; try rewrite Hifrdy; auto;
[ simpl update_nth_val;
unfold AOSUnMapTbl, AOSMapTbl;
sep auto
| idtac | .. | idtac];
eauto.
{
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
auto.
split; auto.
go.
rtmatch_solve.
split.
eauto.
go.
eauto.

  (* case: OS_STAT_RDY *)
  hoare_split_pure_all.
  destruct (Int.eq (i7&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H57; destruct H57 as (Hif & _); tryfalse.
  clear Hif.
  rewrite nth_val_rtbl.
  simpl val_inj.

  (*RETURN prio ′*)
(*   hoare_split_pure_all. *)
(*   hoare forward. *)
 eapply rete_rule.
  introv Hsat.
  eapply aconj_intro.
  2: { sep get rv.
          rewrite prio_ble_max; auto. }
 sep normal.
 sep eexists.
eapply astar_l_apure_intro.
eapply astar_l_apure_intro.
2: instantiate(7:= i7); eauto.
sep cancel Aop.
sep cancel Aier.
sep cancel Aie.
sep cancel Ais.
sep cancel Acs.
sep cancel Aisr.
sep cancel A_isr_is_prop.
sep cancel A_dom_lenv.
sep cancel p_local.
sep cancel tcbdllseg.
sep split; try rewrite Hifrdy; auto;
[ simpl update_nth_val;
unfold AOSUnMapTbl, AOSMapTbl;
sep auto
| idtac | .. | idtac];
eauto.

  {
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
  }

  {
     lets Hx1: nth_val_etbl.
     eapply rl_rtbl_priotbl_p_hold with (v'12:= pegrp) in Hx1; eauto.
     rewrite nth_val_rtbl in Hx1; simpl val_inj in Hx1.
     auto.
  }
  {
    eapply ptr_in_tcbdllseg1_set_node; eauto.
    unfolds; simpl; auto.
  }
  {
    clear - rgrp_le255 bity_le128.
    rtmatch_solve.
    apply int_unsigned_or_prop; auto.
  } 
  simpl;eauto.
  {
  eapply array_type_vallist_match_int8u_update_hold; eauto.
 }
  split; auto.
  go.
  auto.
  split; auto.
  go.
  pure_auto.
  split; eauto.
  go.
  auto.
Qed.

Close Scope code_scope.
