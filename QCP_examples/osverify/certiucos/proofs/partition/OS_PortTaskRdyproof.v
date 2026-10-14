Require Import ucos_include.
Require Import OSTimeDlyPure.
Require Import go.
Require Import Lia.
Require Import corecommu_tactics.
Require Import corecommu_sep_added.
Require Import partition_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import qportpostproof_aux.

Open Scope code_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope list_scope.

Lemma z_le_n_lt':
  forall x1,
    Int.unsigned x1 <= 7 ->
    (Z.to_nat (Int.unsigned x1) < ∘OS_EVENT_TBL_SIZE)%nat.
Proof.
  introv Hx.
  mauto.
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

(* ** ac: Locate "&ᵢ". *)
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


Lemma shl3_add_le_255:
  forall x1 x2, 
    Int.unsigned x1 <= 7 ->
    Int.unsigned x2 <= 7 ->
    Int.unsigned ((x1<<ᵢ$ 3)+ᵢx2) <64.
Proof.
  intros.
  mauto.
Qed.

Lemma shl3_add_le_255':
  forall x1 x2, 
    Int.unsigned x1 <= 7 ->
    Int.unsigned x2 <= 7 ->
    ((Z.to_nat (Int.unsigned ((x1<<ᵢ$ 3)+ᵢx2))) <64) %nat.
Proof.
  intros.
  mauto.
Qed.


Lemma tcb_join_disj_get:
  forall tcbls1 tcbls2 tcbls tid x,
    TcbMod.join tcbls1 tcbls2 tcbls -> 
    TcbMod.get tcbls tid = Some x  ->
    (TcbMod.get tcbls1 tid = Some x /\ TcbMod.get tcbls2 tid = None)
    \/(TcbMod.get tcbls2 tid = Some x /\ TcbMod.get tcbls1 tid = None).
Proof.
  intros.
  pose proof H tid; clear H.
  rewrite H0 in H1.
  destruct (TcbMod.get tcbls1 tid);
  destruct (TcbMod.get tcbls2 tid);
  tryfalse; substs; auto.  
Qed.

Lemma last_eq:
  forall x2 (x4 : vallist),
    (last (x2 ++ x4 :: nil) nil) = x4.
Proof.
  inductions x2; intros.
  simpl; auto.
  simpl.
  rewrite IHx2.
  destruct x2; simpl; auto.
Qed.

Lemma tcbdllseg_isvptr:
  forall l s p1 tail1 ct p z,
    s |= tcbdllseg p1 z tail1 (Vptr ct) l ** p -> exists x, p1 = Vptr x.
Proof.
  inductions l.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  sep split in H.
  eauto.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  unfold node in H.
  sep normal in H.
  sep destruct  H.
  sep split in H.
  heat; jeauto2.
Qed.


Lemma list_app_neq_nil:
  forall x2 (x4 : vallist),
    (x2 ++ x4 :: nil  <> nil).
Proof.
  destruct x2; auto.
Qed.


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
  | DMutex _ _ =>
    etype = Int.repr OS_EVENT_TYPE_MUTEX
  | DPort =>
    etype = Int.repr OS_EVENT_TYPE_PORT
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
  apply (H (e0, e1, x, i, i0, (i1, i2, c0), x2, a0)); auto.
Qed.


Definition rel_edata_stat eid edata stat :=
  match edata with
  | DMsgQ _ _ _ _ =>
    exists n, stat = wait (os_stat_q eid) n
  | DSem _ =>
    exists n, stat = wait (os_stat_sem eid) n
  | DMbox _ =>
    exists n, stat = wait (os_stat_mbox eid) n
  | DMutex _ _ =>
    exists n, stat = wait (os_stat_mutexsem eid) n
  | DPort  =>
    exists n, stat = wait (os_stat_port eid) n
  end.

Lemma PrioWaitInQ_RLH_ECB_ETbl_P_tcbls_ex :
  forall prio osevent etbl petbl l tcbls te d,
    PrioWaitInQ prio etbl ->
    V_OSEventType osevent = Some (Vint32 te) ->
    rel_edata_etype d te ->
    RLH_ECB_ETbl_P l (osevent, etbl, petbl) tcbls ->
    exists tid st m sus, get tcbls tid = Some ($ prio, st, m, sus) /\
                     rel_edata_stat l d st.
Proof.
  intros.
  unfold RLH_ECB_ETbl_P in H2; simp join.
  unfold RLH_ECB_ETbl_Q_P in H2; lets Hx1: H2 H; clear H2.
  unfold RLH_ECB_ETbl_SEM_P in H3; lets Hx2: H3 H; clear H3.
  unfold RLH_ECB_ETbl_MBOX_P in H4; lets Hx3: H4 H; clear H4.
  unfold RLH_ECB_ETbl_MUTEX_P in H5; lets Hx4: H5 H; clear H5.
  unfold RLH_ECB_ETbl_PORT_P in H6; lets Hx5: H6 H; clear H6.
  destruct d; simpl in H1; substs.
  apply Hx1 in H0; simp join; do 4 eexists; split; simpl; eauto.
  apply Hx2 in H0; simp join; do 4 eexists; split; simpl; eauto.
  apply Hx3 in H0; simp join; do 4 eexists; split; simpl; eauto.
  apply Hx4 in H0; simp join; do 4 eexists; split; simpl; eauto.
  apply Hx5 in H0; simp join; do 4 eexists; split; simpl; eauto.
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

Lemma tcbdllseg1_GoodFrm :
  forall vltcb l head headprev tail tailnext ,
    GoodFrm (tcbdllseg1 head headprev tail tailnext vltcb l).
Proof.
  inductions vltcb.
  simpl; intros.
  go.
  simpl; intros.
  splits; auto.
  intros. splits; auto.
  destruct (pair_list_get head); go.
Qed.

Lemma isptr_match :
  forall x,
    isptr x ->
    match x with
    | Vundef => false
    | Vnull => true
    | Vint32 _ => false
    | Vptr _ => true
    end = true.
Proof.
  intros; destruct x; unfolds in H; destruct H; tryfalse; destruct H; tryfalse; auto.
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
    rel_edata_tcbstat d i6.
Proof.
  intros.
  unfolds in H; simp join.
  destruct d.
  clear - H2 H0 H7; unfolds in H2.
  simpl in H0; simp join.
  destruct sus.
  specialize (H7 _ _ _ _ (eq_refl _)).
  simpljoin.
  inverts H1.
  simpl; auto.
  pose proof H2 prio eid x m; clear H2.
  elim H; auto; intros; simp join.
  unfolds in H2; simpl in H2; inverts H2.
  simpl; auto.
  
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
  
  clear - H12 H0 H11; unfolds in H11.
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

Lemma OS_PortTaskRdy_proof:
  forall vl p r ll ct, 
    Some p =
    BuildPreI os_internal OS_PortTaskRdy vl ll OS_PortTaskRdyPre ct ->
    Some r =
    BuildRetI os_internal OS_PortTaskRdy vl ll OS_PortTaskRdyPost ct ->
    exists t d1 d2 s,
      os_internal OS_PortTaskRdy = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  hoare_split_pure_all.
  inverts H8.
  hoare unfold.
 
  rename v'13 into egrp.
  rename v'16 into etbl.
  rename v'26 into dport.
  rename v'30 into qend.
  rename v'29 into qstart.
  rename v'27 into qin.
  rename v'28 into qout.
  rename v'31 into qentries.
  rename v'32 into qsize.
  rename v'25 into msg.
  rename v'24 into mlen.
  rename v'5 into msgptr.
  rename v'33 into dportmsgl.
  rename v'34 into irdportmsgl.
  rename v'18 into s.
  rename v'23 into er.
  rename H into Hptr_in_tcblist.
  rename H0 into H_OS_TCB_type_match.
  rename H35 into Hlen_64.
  rename H4 into HRL_RTbl_PrioTbl_P.
  rename H5 into HR_PrioTbl_P.
  rename H6 into HR_ECB_ETbl_P.
  rename H7 into HTCBList_P.
  rename H34 into Hegrp_neq_zero.
  rename H11 into HSmlen.
  rename H12 into Hdport_V_End.
  rename H13 into Hdport_V_Start.
  rename H14 into Hdport_V_In.
  rename H15 into Hdport_V_Out. 
  rename H16 into Hdport_V_Entries.
  rename H17 into Hdport_V_Size.
  rename H18 into Hdport_V_mode.
  rename H19 into Hdport_type_match.
  rename H20 into Hentries_le_size.
  rename H21 into Hmlen_le_Channel_size.
  rename H22 into Hmsg_type_match.
  rename H23 into Hqsize_range.
  rename H24 into HQport_msg_ptrs.
  rename H25 into Hetbl_type_match.
  rename H26 into H_id_addrval_OSEventTbl.
  rename H28 into HRL_Tbl_Grp_P.
  rename H29 into H_id_addrval_OSPostEventTbl.
  rename H30 into HV_OSPostEventGrp.
  rename H31 into HRL_Tbl_Grp_P'.
  rename H32 into Hlen_etbl_eq_OS_EVENT_TBL_SIZE.
  rename H10 into i1_range.
  rename H33 into Hegrp_range.
  rename H36 into Hi2_range.
  rename H37 into Hisptr_x0.
  rename H38 into Hisptr_x2.
  rename H39 into Hi_range.

(*get the conditions used by following reasoning steps first*)
  assert (
      exists x y erow bitx bity,
        nth_val' (Z.to_nat (Int.unsigned egrp)) OSUnMapVallist = Vint32 y /\
        Int.unsigned y < 8 /\
        nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 erow /\
        Int.unsigned erow < 256 /\ erow <> $ 0 /\
        nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist = Vint32 x /\
        Int.unsigned x < 8 /\
        nth_val' (Z.to_nat (Int.unsigned y)) OSMapVallist = Vint32 bity /\
        Int.unsigned bity <= 128 /\
        nth_val' (Z.to_nat (Int.unsigned x)) OSMapVallist = Vint32 bitx /\
        Int.unsigned bitx <= 128
    ) as Htmp.
  lets Hx1: osunmapvallist_prop Hegrp_range; simpljoin.
  apply Zle_bool_imp_le in H0.
  pose proof z_le_7_imp_n x H0.
  lets Hx2: array_int8u_nth_lt_len Hetbl_type_match.
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE in Hx2.
  unfold OS_EVENT_TBL_SIZE in Hx2.
  lets Hx2': Hx2 H4; clear Hx2; simpljoin.
  lets Hx3: osunmapvallist_prop H6; simpljoin.
  apply Zle_bool_imp_le in H8.
  lets Hx4: osmapvallist_prop H0.
  lets Hx5: osmapvallist_prop H8.
  simp join.
  exists x5 x x3 x6 x7.
  splits; eauto.
  clear - H0; int auto.
  clear - H6; int auto.
  clear H6 H7 H9 H11.

  eapply rl_tbl_grp_neq_zero with (v'12:= egrp); eauto.
  int auto.
  clear - H8; int auto.
  
  destruct Htmp as [x [y [erow [bitx [bity Htmp]]]]].
  destruct Htmp as
      [unmap_egrp [y_lt8 [nth_val_etbl [erow_lt256 [erow_ne0 [unmap_erow [x_lt8 [map_y
       [bity_le128 [map_x bitx_le128]]]]]]]]]].
  simp join.
  pose proof lt_8_le_byte_max_unsigned_true y y_lt8 as y_ble_max.
  pose proof lt_8_le_byte_max_unsigned_true x x_lt8 as x_ble_max.
  pose proof lt_256_le_byte_max_unsigned_true erow as erow_ble_max.
  pose proof le_128_le_byte_max_unsigned_true bity bity_le128 as bity_ble_max.
  pose proof le_128_le_byte_max_unsigned_true bitx bitx_le128 as bitx_ble_max.
(**)

  (* y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ *)
  hoare unfold.
  rename v'39 into portptrb.
  (*不可以*)
  unfold AOSUnMapTbl at 2.

  (* unfold AOSPostEventTbl at 2. *)
  hoare forward; pure_auto.
  rewrite unmap_egrp.
  rtmatch_solve.

  (*bity′ =ₑ OSMapTbl′[y′];ₛ*)
  unfold AOSMapTbl at 2.
  hoare forward.
  rewrite unmap_egrp. rtmatch_solve; rewrite y_ble_max; auto.
  eauto.
  auto.
  auto.
  simpl; rewrite map_y; rewrite bity_ble_max; auto.
  
  (*x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ*)
  rewrite unmap_egrp.
  rewrite map_y.
  hoare forward.
  4: eauto.
  rewrite y_ble_max; auto.
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; simpl; auto.
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
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; simpl; auto.
  simpl; rewrite nth_val_etbl; rewrite erow_ble_max; auto.
  rewrite map_x; rewrite bitx_ble_max; auto.
  rewrite map_x; simpl; intro; tryfalse.
  rewrite nth_val_etbl; rewrite map_x; simpl; intro; tryfalse.
  rewrite y_ble_max; auto.
  apply eq_int; auto.
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; simpl; auto.

  (*If((pevent ′ → OSEventTbl) [y ′] ==ₑ ′0)*)
  hoare forward.
  rewrite y_ble_max; auto.
  rewrite update_nth_val_len_eq; rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  rewrite unsigned_int_and_not_range; auto.
  lia.
  lia.
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; simpl; auto.
  rewrite nth_val_etbl; rewrite map_x.
  rewrite len_lt_update_get_eq; simpl.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)); simpl; intro; tryfalse.
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; simpl; auto.
 
  (*pevent ′ → OSEventGrp &= ∼ os_code_defs.bity ′*)
    hoare forward; pure_auto.
  
  (*combine the 2 cases after the IF stmt into one case*)
  rewrite nth_val_etbl; rewrite map_x.
  apply disj_combine with (S:=(
   EX egrp',
     [| RL_Tbl_Grp_P (update_nth_val (Z.to_nat (Int.unsigned y)) etbl
                                     (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) (Vint32 egrp')  /\ Int.unsigned egrp' <= 255|] **
      <||s ||>  **
      LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr (portptrb, Int.zero) **
      Astruct (portptrb, Int.zero) os_ucos_h.OS_EVENT
        (Vint32 i1 :: Vint32 egrp' :: Vint32 i2 :: x0 :: x1 :: x2:: Vint32 i :: x4 :: nil) **
      Aarray v'35 (Tarray Int8u ∘OS_EVENT_TBL_SIZE)
        (update_nth_val (Z.to_nat (Int.unsigned y)) etbl
           (val_inj (and (Vint32 erow) (val_inj (negint (Vint32 bitx)))))) **
      LV prio @ Int8u
      |-> val_inj
            (add
               (val_inj
                  (if Int.ltu ($ 3) Int.iwordsize
                   then Some (Vint32 (y<<ᵢ$ 3))
                   else None))
               (nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist)
               Int32u Int8u) **
      LV os_code_defs.bitx @ Int8u |-> Vint32 bitx **
      LV os_code_defs.x @ Int8u
      |-> nth_val' (Z.to_nat (Int.unsigned erow)) OSUnMapVallist **
      LV os_code_defs.bity @ Int8u |-> Vint32 bity **
      LV os_code_defs.y @ Int8u |-> Vint32 y **
      AOSPostEventTbl v'37 v'17 **
      Aie false **
      Ais nil **
      Acs (true::nil) **
      Aisr empisr **
      Aier er **
      A_isr_is_prop **
      AEventData
        (Vint32 i1 :: Vint32 egrp :: Vint32 i2 :: x0 :: x1 :: x2 :: Vint32 i :: x4 :: nil) DPort **
      GAarray OSUnMapTbl (Tarray Int8u 256) OSUnMapVallist **
      GAarray OSMapTbl (Tarray Int8u 8) OSMapVallist **
      AOSRdyTblGrp v'10 v'11 **
      GAarray OSTCBPrioTbl (Tarray os_ucos_h.OS_TCB ∗ 64) v'9 **
      tcbdllseg v'19 v'20 v'21 v'22 v'12 **
      Aarray msgptr (Tarray char_t (S (length msg))) (Vint32 mlen :: msg) **
      APortStruct (portptrb, Int.zero) dport **
      dmportp_sllseg_qport_msg qout qin qstart qend ∘ (Int.unsigned qentries) dportmsgl **
      dmportp_sllseg_qport_msg qin qout qstart qend ∘ (Int.unsigned qsize - Int.unsigned qentries) irdportmsgl **
      p_local OSLInv ct init_lg **
      LV ptcb @ os_ucos_h.OS_TCB ∗ |-> v' **
      LV msk @ Int16u |-> Vint32 v'6 **
      LV msg_ptr @ (os_ucos_h.OSMsg_t) ∗ |-> Vptr msgptr **
      A_dom_lenv
     ((msk, Int16u)
      :: (msg_ptr, os_ucos_h.OSMsg_t ∗)
         :: (pevent, os_ucos_h.OS_Port ∗)
            :: (ptcb, os_ucos_h.OS_TCB ∗)
               :: (os_code_defs.x, char_t)
                  :: (os_code_defs.y, char_t)
                     :: (os_code_defs.bitx, char_t) :: (os_code_defs.bity, char_t) :: (prio, char_t) :: nil))
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
  clear - H4 Hi2_range Hisptr_x0 Hlen_etbl_eq_OS_EVENT_TBL_SIZE y_lt8.
  simpl val_inj in *.
  assert(Int.unsigned y < Z.of_nat (length etbl)).
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; int auto.
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
  clear - H6 y_lt8 Hlen_etbl_eq_OS_EVENT_TBL_SIZE.
  simpl val_inj in H6.
  rewrite len_lt_update_get_eq in *.
  simpl val_eq in H6.
  destruct (Int.eq (erow&ᵢInt.not bitx) ($ 0)) eqn : eq1; auto.
  destruct H6; simpl in H; tryfalse.
  rewrite Hlen_etbl_eq_OS_EVENT_TBL_SIZE; unfold OS_EVENT_TBL_SIZE; simpl; auto.

  (*ptcb ′ =ₑ OSTCBPrioTbl ′ [prio ′];ₛ*)
  rewrite int_ltu_3_iwordsize.
  rewrite unmap_erow.
  simpl val_inj.

  (*get the relation between event data and event type*)
  hoare_split_pure_all.
  hoare name lift AEventData pre.

  apply hoare_pure_gen with (p:=(rel_edata_etype DPort i1)).
  intros.
  clear - H0.
  unfold AEventData in H0.
  sep split in H0. inverts H. hnf. easy.
  rename H into HRL_Tbl_Grp_P_new.
  hoare_split_pure_all.
  rename H into rel_ed_et.
  rename v'8 into tcbls.
  rename v'9 into ptbl.

  (*prove prio lt 64*)
  assert(Int.unsigned ((y<<ᵢ$ 3)+ᵢx) < 64) as prio_lt64.
  clear - y_lt8 x_lt8.
  mauto.

  (*prio ble max byte*)
  pose proof lt_64_le_byte_max_unsigned_true ((y<<ᵢ$ 3)+ᵢx) prio_lt64 as prio_ble_max.

  (*prove exist a tid coresponding to prio in tcbls*)
  assert(exists tid st m sus, get tcbls tid = Some ((y<<ᵢ$ 3)+ᵢx, st, m, sus) /\ rel_edata_stat (portptrb, Int.zero) DPort st) as ex_tid_prio_rel.
  
  assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)>>ᵢ$ 3) = y) as y_shl3_shr3.
  clear - x_lt8 y_lt8.
  mauto.

  assert(($ (Int.unsigned (y<<ᵢ$ 3) + Int.unsigned x)&ᵢ$ 7) = x) as y_shl3_and7.
  clear - x_lt8 y_lt8.
  mauto.

  unfold R_ECB_ETbl_P in HR_ECB_ETbl_P; simp join.
  eapply PrioWaitInQ_RLH_ECB_ETbl_P_tcbls_ex; eauto.
  2: unfolds; simpl; auto.
  unfolds.
  clear - prio_lt64 y_lt8 x_lt8 Hetbl_type_match H_id_addrval_OSPostEventTbl nth_val_etbl unmap_erow erow_lt256 erow_ne0 y_shl3_shr3 y_shl3_and7.
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
  clear - HR_PrioTbl_P tcbls_tid_prio.
  unfolds in HR_PrioTbl_P; destruct HR_PrioTbl_P; destruct H0.
  eapply H0 in tcbls_tid_prio; simp join; split;  auto.
  
  apply nth_val_nth_val'_some_eq; auto.
  destruct nth_val_ptbl_vhold as [nth_val_ptbl tid_neq_vhold].
  
  (*do the statement*)
  hoare forward.
  rewrite prio_ble_max; auto.
  rewrite nth_val_ptbl.
  simpl; auto.
  
  (*key step: prove tid in tcbdllseg*)
  rename v'19 into head; rename v'20 into headprev;
  rename v'21 into tail; rename v'22 into tailnext.
  rename v'12 into vltcb.
  assert (ptr_in_tcblist (Vptr tid) head vltcb) as Htid_ptr_in_tcblist.
  eapply tcbls_get_some_TCBList_P_ptr_in_tcblist; eauto.

  (*get the tcb node pointed by tid*)
  hoare name lift tcbdllseg pre.
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

  (* If (msg_ptr ′ !=ₑ NULL)
    {ptcb ′ → OSTCBMsg =ₑ eptrconst OS_PARTITION_MESSAGE_COME_ptr;ₛ
    If (pevent ′ → OSQEntries ≥ pevent ′ → OSQSize)
    {(pevent ′ → OSQIn) → len =ₑ msg_ptr ′ → len;ₛ
    memcpy (­&ₐ ((pevent ′ → OSQIn) → data) [′ 0], &ₐ (pevent ′ → data) [′ 0],
    〈 long 〉 msg_ptr ′ → len­);ₛ
    ++ pevent ′ → OSQIn;ₛ
    ++ pevent ′ → OSQEntries;ₛ
    If (pevent ′ → OSQIn ==ₑ pevent ′ → OSQEnd)
    {pevent ′ → OSQIn =ₑ pevent ′ → OSQStart}}} *)
  hoare name lift OS_TCB_flag (Aarray msgptr) APortStruct dportmsgl irdportmsgl pre.
  hoare remember (1::2::3::4::5::nil)%nat pre.
  apply seq_rule with
  ((APortStruct (portptrb, Int.zero) dport **
  dmportp_sllseg_qport_msg qout qin qstart qend ∘ (Int.unsigned qentries) dportmsgl **
  dmportp_sllseg_qport_msg qin qout qstart qend
    ∘ (Int.unsigned qsize - Int.unsigned qentries) irdportmsgl \\//
    EX irportmsgl', APortStruct (portptrb, Int.zero)
    (update_nth_val 17 (update_nth_val 14 dport (Vptr (dmportp_sllseg_qport_msg_next qin qstart qend)))
       (Vint32 (qentries +ᵢ  $ 1))) **
    dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next qin qstart qend) qout qstart qend
    (Init.Nat.pred ∘ (Int.unsigned qsize - Int.unsigned qentries)) irportmsgl' **
    dmportp_sllseg_qport_msg qout
    (dmportp_sllseg_qport_msg_next qin qstart qend) qstart qend
    (Z.to_nat (Int.unsigned (qentries +ᵢ  $ 1))) (dportmsgl ++ msg :: nil) **
    [|Int.unsigned (qentries +ᵢ  $ 1) <= Int.unsigned qsize|])
  ** Astruct (v'8, Int.zero) OS_TCB_flag
  (x14
   :: x13
      :: Vnull
         :: Vptr OS_PARTITION_MESSAGE_COME_ptr
            :: V$ 0
               :: Vint32 i7
                  :: Vint32 i6
                     :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i0::nil)** 
  Aarray msgptr (Tarray char_t (S (length msg))) (Vint32 mlen :: msg) **H4).
  {
    subst H4. apply corecommu_rules.ift_nonzero_rule.
    {
      exists (Int.one). sep split.
      symbolic_execution. now destruct msgptr.
      destruct msgptr. simpl. reflexivity.
      pauto. 
    }

    (* ptcb ′ → OSTCBMsg =ₑ eptrconst OS_PARTITION_MESSAGE_COME_ptr;ₛ *)
    hoare forward.
    {
      hoare abs lift pre.
      eapply assign_rule_struct_aop_typeneq.
      - split; intros.
        + sep autocancel. apply H4.
        + sep pauto.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - intros. auto.
      - intros. auto.
      - intros. auto.
      - intros. instantiate (2:= Tptr Tint32).
        simpl. destruct s0 as [[[[[[]]]]]]. simpl. destruct p.
        splits; eauto.
      - apply assign_type_match_true; auto.
      - simpl. lia.
      - simpl. reflexivity.
      - intros. eexists. sep autocancel. cbv. tauto.
    }
    lets Hqsize_qentries_compare: Ztrichotomy (Int.unsigned qentries) (Int.unsigned qsize).
    destruct Hqsize_qentries_compare.
    2:{
        destruct H4.
        2:{
            clear - Hentries_le_size H4. lia.
        }
        eapply forward_rule1.
        2:{
          apply corecommu_rules.ift_zero_rule.
          intros. 
          eapply symbolic_lemmas.bop_rv.
          eapply event_port_QEntries_rv; eauto.
          sep autocancel. apply H19.
          eapply event_port_QSize_rv; eauto.
          sep autocancel. apply H19.
          simpl.
          assert (Int.ltu qentries qsize = false).
          apply Intlt_false_is_Zge. lia.
          now rewrite H20. auto. reflexivity.
        }
        intros. sep autocancel.
        left. auto.
    }
    rename H into Hdistinct_tcbdllseg_nexr_ptr.
    rename H0 into Htcbdllsegl_get_node.
    rename H5 into Hlen_update_etbl_EVENT_TBL_SIZE.
    rename H6 into Hisptr_x14.
    rename H9 into Hisptr_x13.
    rename H10 into Hisptr_x12.
    rename H11 into Hisptr_x11.
    rename H12 into Hi8_range.
    rename H13 into Hi7_range.
    rename H14 into Hi6_range.
    rename H15 into Hi5_range.
    rename H16 into Hi4_range.
    rename H17 into Hi3_range.
    rename H18 into Hi0_range.
    rename H4 into Hentries_lt_size.
    rename H1 into Hv'6_range.
    clear H2 H3.
    rename H7 into HRL_Tbl_Grp_P_new.
    rename H8 into Hv'5_range.
    destruct msgptr as [msgptrb msgptro].
    destruct qin as [qinb qino].
    destruct qend as [qendb qendo].
    hoare name lift (dmportp_sllseg_qport_msg (qinb,qino)) pre.
       eapply backward_rule1.
       {
         eapply dmportp_sllseg_qport_msg_ngt0.
         clear - Hentries_lt_size.
         unfold Coqlib.nat_of_Z. lia.
       }
       naive pure intro.
       destruct H as (msghold&msgholdl&?&Hmsg_le_channel_size). subst irdportmsgl.

    apply corecommu_rules.ift_nonzero_rule.
    {
      exists Int.one.
      sep split.
      eapply symbolic_lemmas.bop_rv.
      eapply event_port_QEntries_rv; eauto.
      sep autocancel. apply H.
      eapply event_port_QSize_rv; eauto.
      sep autocancel. apply H.
      simpl. 
      assert (Int.ltu qentries qsize = true).
      apply Intlt_true_is_Zlt. lia.
      now rewrite H0. auto. reflexivity.
      pauto.
    }
    
    (* (pevent ′ → OSQIn) → len =ₑ msg_ptr ′ → len;ₛ *)
    assert (Z.to_nat (Int.unsigned mlen + 1) = S (Z.to_nat (Int.unsigned mlen))) as HSmlen' by lia.
    rewrite HSmlen' in HSmlen. inverts HSmlen.
    hoare name lift msghold pre.
    eapply backward_rule1.
    {
      apply dmportp_sllseg_qport_msg_split.
      unfold Coqlib.nat_of_Z. lia. 
    }
    naive pure intro.
    destruct H. destruct H1.
    invertsr H1. rename v'12 into irrmsghold.
    rename H2 into Hmsghold_type_match.
    rename H into Hmsghold_channel_size.
    rename H3 into Hmsghold_le_channel_size.
    cbn [Aarray Aarray'].
    hoare name lift Aop (Aptrmapsto (qinb,qino)) pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      {
        intros.
        eapply symbolic_lemmas.struct_offset_rv.
        { 
          eapply symbolic_lemmas.addrof_deref_rv.
          eapply event_port_QIn_rv; eauto.
          sep autocancel. apply H.
        }
        all: reflexivity.
      }
      {
        cbn [fst snd].
        rewrite Int.add_zero.
        split; intros; eauto.
      }
      { 
        intros. 
        eapply symbolic_lemmas.struct_member_rv_flag.
        sep autocancel.
        2-6: try reflexivity.
        unfold get_off_addr. cbn [fst snd].
        rewrite Int.add_zero.
        sep autocancel. apply H.
        simpl. clear - Hmsg_type_match.
        simpl in Hmsg_type_match. tauto.
      }
      { now apply assign_type_match_true. }
      {
        intros. sep eexists. sep auto.
      }
    }
    clear Hmsg_le_channel_size.
    rename H0 into Hlenmsg_mlen.
    (* memcpy (­&ₐ ((pevent ′ → OSQIn) → data) [′ 0], &ₐ (msg_ptr ′ → data) [′ 0],
    〈 long 〉 msg_ptr ′ → len­);ₛ *)
    cbn [fst snd]. rewrite ! Int.add_zero.
    
    unfold get_off_addr.  cbn[fst snd].
    hoare name lift (Alvarmapsto pevent) APortStruct (Aptrmapsto (qinb, qino)) pre.
    eapply seq_rule.
    {
      eapply call_rule'; try reflexivity.
      {
        intros.
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply event_port_OSQIn_data_rv'; eauto.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim.
        {
          eapply symbolic_lemmas.addrof_array_elem_rv.
          {
            eapply struct_member_array_rv. symbolic_execution.
            all: reflexivity.
          }
          { symbolic execution. }
          all: pauto.
        }
        eapply rvl_elim; [ |apply rvl_nil].
        instantiate (1:=(Vint32 mlen)).
        eapply cast_rv_tint8_tint32; auto.
        eapply symbolic_lemmas.struct_member_rv_flag.
        {
          sep autocancel.
          assert ((msgptrb, msgptro) = get_off_addr (msgptrb, msgptro) Int.zero).
          { unfold get_off_addr; cbn [fst snd]; rewrite Int.add_zero; reflexivity. }
          rewrite <- H0. sep autocancel.
          exact H.
        }
        all: try reflexivity.
        simpl in Hmsg_type_match. tauto.
      }
      {
        intros; unfold_spec. cbn [fst snd].
        sep normal. sep eexists.
        sep autocancel; sep split; eauto.
        rewrite ! Int.add_zero.
        sep name lift msghold in H.
        eapply Aarray_split_single with (m:=(Z.to_nat (Int.unsigned mlen)))in H.
        2:{
          unfold CHANNEL_CACHE_SZIE. clear. mauto. 
        }
        2:{
          clear - Hmlen_le_Channel_size. unfold Coqlib.nat_of_Z. lia.
        }
        2: rewrite app_length; auto.
        sep autocancel.
        sep name lift Aarray' in H. unfold Aarray.
        rewrite <- Hlenmsg_mlen.
        sep autocancel. apply H.
      }
      { good_frm_sovler. apply tcbdllseg1_GoodFrm. }
      { sep_unfold_funpost. intros. sep destruct H. sep auto. }
      { sep_unfold_funpre. intros. sep destruct H. sep auto. }
      { pauto. }
    }
    unfold getasrt; unfold OS_memcopyPost, OS_memcopyPost'.
    hoare normal pre. pure intro.
    invertsr H.
    invertsr H0. clear H1.
    rename H2 into Hlen_irrmsghold.
    rewrite ! Int.add_zero.
    hoare abs lift pre.
    (* ++ pevent ′ → OSQIn;ₛ *)
    eapply seq_rule.
    {
    eapply event_port_memeber_asgn; try reflexivity.
      - split; intros.
        sep autocancel. exact H.
        sep auto.
      - intros. eapply symbolic_lemmas.bop_rv.
        * eapply event_port_QIn_rv; eauto.
          sep autocancel. apply H.
        * symbolic_execution.
        * simpl. reflexivity.
        * auto.
        * reflexivity.
      - instantiate (1:=14%nat).  reflexivity.
      - eauto.
      - auto.
      - auto.
      - auto.
      - now apply assign_type_match_true.
      - reflexivity.
      - intros. sep auto.
    }
    assert (Int.unsigned (qentries +ᵢ  $ 1) <=? Int16.max_unsigned = true) as Hqentries_range.
    {
      clear - Hentries_lt_size Hqsize_range.
      pose proof Int_add_one_Sn qentries ltac:(lia).
      rewrite Z.leb_le. rewrite int16_max_unsigned_val. lia.
    }
    eapply seq_rule.
    {
      eapply event_port_memeber_asgn; try reflexivity.
      - intros. eapply symbolic_lemmas.bop_rv.
        * eapply event_port_QEntries_rv. 
          3: { sep autocancel. apply H. }
          { 
            qportpostproof_tac. 
          }
          { port_nth_val_solve. }
        * symbolic_execution.
        * simpl. reflexivity.
        * auto.
        * reflexivity.
      - instantiate (1:=17%nat). reflexivity.
      - port_nth_val_solve.
      - auto.
      - auto.
      - auto.
      - now apply assign_type_match_true.
      - simpl. now rewrite Hqentries_range.
      - intros. sep auto.
    }
    (* If (pevent ′ → OSQIn ==ₑ pevent ′ → OSQEnd)
    {pevent ′ → OSQIn =ₑ pevent ′ → OSQStart};ₛ *)
    hoare normal pre.
    hoare name lift APortStruct pre.
    hoare remember (1::nil)%nat pre.
    apply forward_rule1 with (APortStruct (portptrb,Int.zero) (update_nth_val 17
    (update_nth_val 14 dport
      (Vptr (dmportp_sllseg_qport_msg_next (qinb,qino) qstart (qendb,qendo))))
    (Vint32 (qentries +ᵢ  $ 1)))**H).
    2:{
      eapply ift_rule.
      - intros. eexists. subst H.
        eapply symbolic_lemmas.bop_rv.
        * eapply event_port_QIn_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac. 
          }
          port_nth_val_solve. 
        * eapply event_port_QEnd_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac.
          }
          port_nth_val_solve.
        * simpl. reflexivity.
        * destruct (peq qinb qendb); auto.
          destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
        * reflexivity.
      - intros. 
        eapply sep_aconj_r_aisfalse_to_astar in H0.
        2:{ intros. subst H.
        eapply symbolic_lemmas.bop_rv.
        * eapply event_port_QIn_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac. 
          }
          port_nth_val_solve. 
        * eapply event_port_QEnd_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac.
          }
          port_nth_val_solve.
        * simpl. reflexivity.
        * destruct (peq qinb qendb); auto.
          destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
        * reflexivity.
        }
        sep split in H0.
        destruct H1. 2:{ destruct (peq qinb qendb); auto.
        destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto; simpl in H1; discriminate.
        simpl in H1. discriminate. }
        unfold dmportp_sllseg_qport_msg_next.
        sep autocancel. 
        simpl typelen. unfold msg_distance.
        unfold Qport_msg_ptrs_P in HQport_msg_ptrs.
        destruct qstart. simpljoin1. unfold get_off_addr in *.
        simpl in H3, H5.
        invertsr H3. invertsr H5.
        cbn [fst snd] in *.
        rewrite ! Int.add_zero_l in *.
        rewrite peq_true in H1.
        destruct (Int.eq (Int.mul ($ x5) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
        (Int.mul ($ Int.unsigned qsize) ($ 33))) eqn:E'; [discriminate | ].
        simpl typelen. simpl Z.of_nat.
        assert (
        (qinb, Int.mul ($ x5) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33)) =
        (if
                Int.unsigned
                  (Int.divu
                     (Int.mul ($ Int.unsigned qsize) ($ 33) -ᵢ
                      Int.mul ($ x5) ($ 33)) ($ 33)) =? 1
               then (qinb, Int.zero)
               else (qinb, Int.mul ($ x5) ($ 33) +ᵢ  $ 33))).
        {
          clear - H7 H8 Hqsize_range E'.
          destruct (Int.unsigned (Int.divu (Int.mul ($ Int.unsigned qsize) ($ 33) -ᵢ Int.mul ($ x5) ($ 33)) ($ 33)) =? 1) eqn:?.
          2: { rewrite (Int.mul_commut ($ 1)).  rewrite Int.mul_one. reflexivity. }
          exfalso.
          assert (exists n,  Int.unsigned qsize = n + x5 /\ 1 <= n <= 65536).
          { exists (Int.unsigned qsize- x5). split;lia. }
          destruct H as [n [H0 H1]].
          rewrite H0 in Heqb.
          assert (x5 <= 65536) by lia. 
          erewrite  <- (Int.unsigned_repr n) in Heqb at 1.
          rewrite  <- (Int.unsigned_repr x5) in Heqb at 1.  
          rewrite  <- Int.add_unsigned in Heqb.
          rewrite Int.mul_add_distr_l in Heqb.
          rewrite Int.add_commut in Heqb.
          rewrite Int.sub_add_l in Heqb. rewrite Int.sub_idem in Heqb.  rewrite Int.add_zero_l in Heqb.
          assert ((Int.divu (Int.mul ($ n) ($ 33)) ($ 33)) = $ n).
          { erewrite Int.Int_mul_divu_r;auto. clear. rewrite Int.unsigned_repr by mauto. lia.
            rewrite Int.unsigned_repr. 
            rewrite Int.unsigned_repr.  
            assert (n * 33 <= 2162688) by lia. 
            assert (2162688 < Int.modulus) by (clear;mauto). lia.
            clear;mauto.
            clear - H1;unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia.
           }
          rewrite H2 in Heqb.
          rewrite Int.unsigned_repr in Heqb. assert (n = 1) by lia.
          subst n.
          rewrite H0 in E'.
          rewrite <- (Int.unsigned_repr 1) in E' at 2.
          rewrite <- (Int.unsigned_repr x5) in E' at 2.
          rewrite <- Int.add_unsigned in E'.
          rewrite Int.mul_add_distr_l in E'.
          rewrite (Int.add_commut (Int.mul ($ 1) ($ 33))) in E'. 
          rewrite Int.eq_true in E'. discriminate.
          all: rewrite max_unsigned_val; lia.
        }
        rewrite H in H0. sep autocancel.
      - intros.
        eapply backward_rule1. 
        eapply sep_aconj_r_aistrue_to_astar.
        { intros. subst H.
        eapply symbolic_lemmas.bop_rv.
        * eapply event_port_QIn_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac. 
          }
          port_nth_val_solve. 
        * eapply event_port_QEnd_rv.
          3:{ sep autocancel. eauto. }
          { 
            qportpostproof_tac.
          }
          port_nth_val_solve.
        * simpl. reflexivity.
        * destruct (peq qinb qendb); auto.
          destruct (Int.eq (qino +ᵢ  Int.mul ($ 1) ($ 33)) qendo); auto.
        * reflexivity.
        }
        naive pure intro.
        subst H.
        hoare evar lift pevent pre.
        hoare abs lift pre.
        eapply forward_rule1.
        2:{
          eapply event_port_memeber_asgn; try reflexivity.
          - intros. eapply event_port_QStart_rv.
            3:{ sep autocancel. eauto. }
            { 
              qportpostproof_tac. 
            }
            port_nth_val_solve.
          - instantiate (1:=14%nat). reflexivity.
          - port_nth_val_solve.
          - auto.
          - auto.
          - auto.
          - now apply assign_type_match_true.
          - reflexivity.
          - intros. sep auto.
        }
        intros. sep autocancel.
        unfold dmportp_sllseg_qport_msg_next.
        simpl typelen. unfold msg_distance.
        unfold Qport_msg_ptrs_P in HQport_msg_ptrs.
        destruct qstart. simpljoin1. unfold get_off_addr in *.
        simpl in H4, H6.
        invertsr H4. invertsr H6.
        cbn [fst snd] in *.
        clear H1 H2.
        rewrite ! Int.add_zero_l in *.
        rewrite peq_true in H0.
        destruct (Int.eq (Int.mul ($ x5) ($ 33) +ᵢ  Int.mul ($ 1) ($ 33))
        (Int.mul ($ Int.unsigned qsize) ($ 33))) eqn:E'.
        2:{
          simpl in H0. congruence.
        }
        simpl typelen. simpl Z.of_nat.
        rewrite aux_pureLib.Int_eq_dec in E'.
        rewrite <- E'.
        rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_zero_l. 
        rewrite (Int.mul_commut ($ 1)).
        rewrite Int.mul_one.
        assert ((Int.divu ($ 33) ($ 33)) = Int.one)  by (clear;mauto).
        rewrite H1.
        rewrite Int.unsigned_one.
        rewrite Z.eqb_refl.
        rewrite update_nth_val_diff in H. 2:lia.
        rewrite update_nth_val_same in H.
        sep auto.
    }
    subst H. 
    intros. apply disj_split. right.  
    sep autocancel.
    sep normal. sep eexists.
    sep cancel APortStruct.
    simpl typelen. simpl Z.of_nat.
    unfold Aarray at 2 in H.
    rewrite Hlenmsg_mlen.
    unfold get_off_addr in H.
    cbn [fst snd] in H.
    sep cancel Aarray'.
    sep name lift msg.
    eapply dmportp_sllseg_qport_msg_append_tail; eauto.
    lia.
    sep eexists. sep autocancel.
    sep auto.
    lets Htmp: Int_add_one_Sn qentries.
    assert (Int.unsigned qentries < 4294967295) by lia.
    apply Htmp in H0.
    assert (Int.unsigned (qentries +ᵢ  $ 1) = Z.of_nat (S (Z.to_nat (Int.unsigned qentries)))) by lia.
    rewrite H1.
    pose proof Int.unsigned_range_2 qentries. rewrite max_unsigned_val in H2. lia.
    apply array_type_vallist_match_app. split.
    - inverts Hmsg_type_match. auto.
    - erewrite <- firstn_skipn in Hmsghold_type_match.
      apply array_type_vallist_match_app in Hmsghold_type_match. jauto. 
  }
  subst H4.

  (*ptcb ′ → OSTCBStat &= ∼ msk ′;ₛ*)
  hoare forward; pure_auto.

  (* If (ptcb ′ → OSTCBStat ==ₑ ′ OS_STAT_RDY) *)
  unfold AOSRdyTblGrp.
  unfold AOSRdyGrp.
  hoare unfold.

  rename v'10 into rtbl.
  rename i9 into rgrp.
  rename H4 into rgrp_le255.
  hoare_assert_pure (array_type_vallist_match char_t rtbl /\ length rtbl = ∘ OS_RDY_TBL_SIZE).
  { unfold AOSRdyTbl in H4.
    seplog_trm_tacs.sep_lifts_trms_in H4 array_type_vallist_match.
    eapply sep_pure_split in H4; destruct H4 as (Hmat & _).
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
  lets Hx: array_int8u_nth_lt_len Hmat.
  rewrite Hlen in Hx.
  unfold OS_RDY_TBL_SIZE in Hx.
  eapply Hx; eauto.
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
  lets Hx: rl_tbl_grp_p_set_hold' Hegrp_neq_zero Hegrp_range Hetbl_type_match Hlen_etbl_eq_OS_EVENT_TBL_SIZE Hmat.
  lets Hx1: nth_val_etbl.
  eapply Hx in Hx1; eauto.
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
  rewrite H21.
  clear - map_x x_lt8.
  apply math_mapval_core_prop; auto.

  assert(Hor_prop: Int.unsigned (i7&ᵢInt.not v'6) <= 65535).
  {eapply Z.le_trans. apply Int.and_le. eauto. }
  hoare forward.
  go.
  pure_auto.
  hoare_split_pure_all.
  destruct (Int.eq (i7&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H4; destruct H4 as (Hif & _); tryfalse.
  clear Hif.
  (**)
  (*key step: put the tcb node back into the tcblist*)
  hoare name lift Astruct tcbdllseg1 pre.
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
  destruct H4.

  hoare unfold.
  hoare forward.
  pure_auto.
  rewrite H21; unfold OS_RDY_TBL_SIZE; simpl; auto.
  simpl; rewrite nth_val_rtbl; pure_auto.
  pure_auto.
  rewrite nth_val_rtbl; simpl; intro; tryfalse.
  pure_auto.
  unfold OS_RDY_TBL_SIZE; simpl; auto.
  rewrite H21; unfold OS_RDY_TBL_SIZE; simpl; auto.

  hoare forward.
 2:{
    hoare_split_pure_all.
    destruct (Int.eq (i7&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
    simpl in H4; destruct H4 as [Hif1 |  Hif2]; tryfalse.
    clear Hif1.
    hoare name lift Astruct tcbdllseg1 pre.
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
      sep autocancel.
      unfold AOSUnMapTbl, AOSMapTbl.
      sep autocancel.
    }
    {
      clear - Hptr_in_tcblist H0.
      eapply ptr_in_tcbdllseg1_set_node; eauto.
      unfolds; simpl; auto.
    }
    reflexivity.
    (* split; auto. *)
    rtmatch_solve.
    (* eauto. *)
    (* unfolds; *) simpl; auto.
    {
      eapply array_type_vallist_match_int8u_update_hold; eauto.
    }
    split; auto.
    go.
    rtmatch_solve.
    unfold AOSRdyTbl in H4.
    sep split in H4; auto.
    {
      lets Hx: TCBList_P_get_node_TCBNode_P HTCBList_P H0 tcbls_tid_prio.
      clear - Hx rel_ed_st.
      unfold TCBNode_P in Hx; simp join.
      clear - H2 rel_ed_st.
      unfolds in H2; simp join.
      eapply RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat; eauto.
    }
    split.
    eauto.
    go.
 }
  (* case: OS_STAT_RDY *)
  hoare_split_pure_all.
  destruct (Int.eq (i7&ᵢInt.not v'6) ($ OS_STAT_RDY)) eqn: Hifrdy;
  simpl in H4; destruct H4 as (Hif & _); tryfalse.
  clear Hif.
  rewrite nth_val_rtbl.
  simpl val_inj.
  (*RETURN prio ′*)
(*   hoare_split_pure_all. *)

  hoare forward.
  (*side conditions*)
  {
    rewrite prio_ble_max; auto.
  }

  {
    simpl update_nth_val.
    unfold AOSUnMapTbl, AOSMapTbl.
    rewrite Hifrdy.
    sep autocancel.
    unfold AOSRdyTbl.
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
  }
    auto.
    eauto.
    auto.
    auto.

  { rewrite Hifrdy.
    lets Hx: rl_rtbl_priotbl_p_hold tid_neq_vhold HRL_RTbl_PrioTbl_P Hegrp_neq_zero Hegrp_range Hetbl_type_match.
    lets Hx': nth_val_etbl.
    eapply Hx in Hx'; eauto.
    clear Hx.
    rewrite nth_val_rtbl in Hx'; simpl val_inj in Hx'.
    auto.
  }

  {
    clear - Hptr_in_tcblist H0.
    eapply ptr_in_tcbdllseg1_set_node; eauto.
    unfolds; simpl; auto.
  }
  reflexivity.
  { rewrite Hifrdy.
    split; eauto.
  }

  {
    clear - rgrp_le255 bity_le128.
    rtmatch_solve.
    apply int_unsigned_or_prop; auto.
  }
  eauto.
  simpl; auto.
  auto. eauto.
  3: {
    eapply array_type_vallist_match_int8u_update_hold; eauto.
  }
  (* split; auto. *)
  simpl; auto.
  auto.
  split; eauto. go. pure_auto.
  auto.
  eauto.
  auto.
  auto.
  {
    lets Hx: TCBList_P_get_node_TCBNode_P HTCBList_P H0 tcbls_tid_prio.
    clear - Hx rel_ed_st.
    unfold TCBNode_P in Hx; simp join.
    clear - H2 rel_ed_st.
    unfolds in H2; simp join.
    eapply RHL_TCB_Status_Wait_P_rel_edata_stat_rel_edata_tcbstat; eauto.
  }
  split.
  eauto.
  go.
  auto.
  {
    rewrite nth_val_rtbl.
    eauto.
  }
Qed.

Close Scope code_scope.
