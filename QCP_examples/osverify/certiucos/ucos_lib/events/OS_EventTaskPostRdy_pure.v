Require Import ucos_include.
Require Import OSTimeDlyPure.
Require Import go.
Require Import Lia.
Require Import symbolic_lemmas.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

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
  apply H in H5; auto.
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
  apply Hx in H0. simp join. 
  do 4 eexists; split; simpl; eauto.  
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
  forall vltcb head tcbls tid pr st m rtbl,
    get tcbls tid = Some (pr, st, m) ->
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
  assert (TcbMod.get x1 tid = Some (pr, st, m)).
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
    WellformedOSQ
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
  forall (x12 x11 x5 x6 : val) (v'49 : block) (x i2 i1 : int32)
         (v'47 : block) (x13 x14 : val) (v2 : list val) 
         (v'46 : absecb.B) d1 d10 d11 dd2,
    length v2 = ∘OS_MAX_Q_SIZE ->
    RLH_ECBData_P
      (DMsgQ (Vptr (d1, Int.zero))
             (dd2)
             (d10 :: d11 :: nil) v2) v'46 ->
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
  introv e1 e2 e3.
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
  eapply update_nth; eauto.
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
    Int.unsigned (i1+ᵢ$ 1) <= Int.unsigned i2 -> (* new add *)
    (* Int.ltu i1 i2 = true -> *)
    WellformedOSQ
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
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: x12
         :: x8
         :: Vint32 i2
         :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil).
Proof.
  introv Hlt Hvl Hj.
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
  clear -x.
  int auto.
  int auto.
  rewrite Hx in *.
  assert (Int.mul ($ 1) ($ 4) = $ 4) as Hy.
  clear -x.
  int auto.
  rewrite Hy in *.
  simpl in *.
  do 7 eexists;
  exists (x9 +ᵢ  $ 1); (* new add *)
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
  clear -x.
  mauto.
  rewrite H1.
  rewrite Int.unsigned_repr.
  eapply Z2Nat.inj_lt;lia.
  clear -x.
  int auto.
  unfolds.
  unfold ptr_offset_right, ptr_minus in *.
  rewrite Pos2Z.inj_eqb .
  rewrite Z.eqb_refl.
  eexists;  splits; eauto.
Qed.

Lemma get_wellformedosq_in_setst':
  forall i1 i2 x13 x12 x6 v'49 x x8,
    Int.unsigned (i1+ᵢ$ 1) <= Int.unsigned i2 -> (* new add *)
    x6 <> Vptr (v'49,  (x+ᵢInt.mul ($ 1) ($ 4))) ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x)
         :: x8
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    WellformedOSQ
      (x13
         :: x12
         :: x6
         :: Vptr (v'49, x+ᵢInt.mul ($ 1) ($ 4))
         :: x8
         :: Vint32 i2
         :: Vint32 (i1+ᵢ$ 1) :: Vptr (v'49, Int.zero) :: nil).
Proof.
  introv Hlt. (* new add *)
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
  unfolds.
  do 7 eexists; 
  exists (x9 +ᵢ  $ 1); (* new add *)
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
  eapply math_lt_mod_lt with (* i2 *) i1 ;eauto.
  intro Hf.
  subst (* i2 *) i1.
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

(* Lemma RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat :
  forall x13 x12 x11 x10 i7 i6 i5 i4 i3 i2 i prio st m eid d rtbl,
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
      rtbl (prio, st, m) ->
    rel_edata_stat eid d st ->
    rel_edata_tcbstat_postrdy d i6.
Proof.
  intros.
  unfolds in H; simp join.
  destruct d.
  clear - H5 H0; unfolds in H5.
  simpl in H0; simp join.
  pose proof H5 prio eid x m; clear H5.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.
  
  clear - H1 H0; unfolds in H1.
  simpl in H0; simp join.
  pose proof H1 prio eid x m; clear H1.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H3 H0; unfolds in H3.
  simpl in H0; simp join.
  pose proof H3 prio eid x m; clear H3.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.

  clear - H4 H0; unfolds in H4.
  simpl in H0; simp join.
  pose proof H4 prio eid x m; clear H4.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.
Qed. *)

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

Lemma ecast_intlemma1: 
forall x, Int.unsigned x <= 65535 ->  (Int.modu x ($ Int16.modulus)) = x.
Proof.
  intros.
  unfold Int.modu.
  unfold Int16.max_unsigned.
  unfold Int16.modulus.
  unfold Int16.wordsize.
  unfold Wordsize_16.wordsize.
  unfold two_power_nat.
  unfold shift_nat.
  simpl.
  repeat ur_rewriter.
  fold Int16.modulus.
  rewrite <- Int16.unsigned_repr_eq.
  assert (0 <= Int.unsigned x <= Int16.max_unsigned).
  change (Int16.max_unsigned) with 65535.
  int auto.
  eapply Int16.unsigned_repr in H0.
  rewrite H0.
  rewrite Int.repr_unsigned. auto.
Qed.
