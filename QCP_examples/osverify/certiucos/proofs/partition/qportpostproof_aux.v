Require Import ucos_include.
Require Import Lia.


Require Import aux_pureLib.
Require Import abs_op_corecommu_rules.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import OSTimeTickPure.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.

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


Lemma Qport_msg_ptrs_P_hold:
  forall qstart qend qin qout qsize,
    qsize <= 65535 ->
    Qport_msg_ptrs_P qstart qend qout qin qsize ->
    Qport_msg_ptrs_P qstart qend qout (dmportp_sllseg_qport_msg_next qin qstart qend) qsize.
Proof.
  unfold Qport_msg_ptrs_P.
  intros. destruct qstart. unfold get_off_addr in *.
  simpl in *. simpljoin. splits; auto.
  unfold dmportp_sllseg_qport_msg_next. simpl.
  unfold msg_distance. simpl. destruct (Int.unsigned
  (Int.divu
     ((Int.zero +ᵢ  Int.mul ($ qsize) ($ 33)) -ᵢ
      (Int.zero +ᵢ  Int.mul ($ x0) ($ 33))) ($ 33)) =? 1) eqn:E; auto.
  do 2 eexists.
  split; eauto. 
  instantiate (1:=0). rewrite Int.mul_commut.
  rewrite Int.mul_zero. rewrite Int.add_zero. splits;auto;lia.
  do 2 eexists.
  split; eauto.
  instantiate (1:=(x0+1) ). splits; auto; try lia.
  rewrite ! Int.add_zero_l.
  rewrite Int_add_one_Sn''.
  rewrite Int.mul_add_distr_l. reflexivity.
  lia.
  assert (x0+1=qsize\/ x0+1<qsize) by lia.
  destruct H0; auto.
  subst qsize. exfalso.
  rewrite ! Int.add_zero_l in E. 
  rewrite Int_add_one_Sn'' in E; try lia.
  rewrite Int.mul_add_distr_l in E.
  rewrite Int.sub_add_l in E.
  rewrite Int.sub_idem in E.
  rewrite Int.add_zero_l in E.
  discriminate.
Qed.

Lemma event_port_memeber_asgn  : forall 
r ri aop (p p':asrt ) (tid: tid) pptr dport e tp2 v' v n t' id ,
p <==> LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr ** APortStruct pptr dport ** p' ->
p ==>  Rv e @ tp2 == v ->
nth_id n OS_Port_Seg_dls = Some id ->
nth_val n dport = Some v' -> 
ftype id OS_Port_Seg_dls = Some t' ->
(forall (ids : ident) (dl : decllist), t' <> STRUCT ids ­{ dl }­) ->
(forall (ids : ident) (dl : decllist), t' <> Tunion ids dl ) ->
(forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
assign_type_match t' tp2 ->
rule_type_val_match t' v = true ->
LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' ==>
       EX lg : list logicvar, p_local OSLInv tid lg ** Atrue ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  ** p }} 
  pevent ′ →  id =ₑ e
{{  <|| aop ||> ** LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' }}.
Proof.
  intros * H H0 H1 H2 H3 H4 H4'. intros.
  unfold APortStruct in *.
  lets Hoff: symbolic_lemmas.nth_id_exists_off H1.
  destruct Hoff as (off&Hoff).
  destruct pptr as (b&i).
  assert (p <==> PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v' **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV pevent @ OS_Port ∗ |-> Vptr (b, i) ** p').
  {  assert (Astruct' (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport <==> PV (b,Int.add (i +ᵢ  $ 29) off) @ t' |-> v' ** Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id).
  { eapply symbolic_lemmas.struct_asrt_eq;eauto. }
  eapply asrt_eq_trans;eauto.
  split.
  intros.
  sep name lift Astruct' in H10.
  eapply astar_mono in H10.
  2: apply H9.
  2: intros s' Hs';exact Hs'.
  sep auto. 
  intros.
  sep name lift Astruct'.
  eapply astar_mono.
  apply H9. instantiate (1:=LV pevent @ OS_Port ∗ |-> Vptr (b, i) ** p'). sep auto.
  sep auto. }
  clear H.
  assert (PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV pevent @ OS_Port ∗ |-> Vptr (b, i) ** p' ==> EX lg : list logicvar, p_local OSLInv tid lg ** Atrue).
  { intros. apply H8.
    assert (Astruct' (b, i +ᵢ  $ 29) OS_Port_Seg_dls (update_nth_val n dport v) <==> PV (b,Int.add (i +ᵢ  $ 29) off) @ t' |-> v ** Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls (update_nth_val n dport v) id).
    { eapply symbolic_lemmas.struct_asrt_eq;eauto. eapply update_nth;eauto. }
    sep name lift Astruct_rm in H.
    eapply astar_mono in H.
    2: { intros. eapply symbolic_lemmas.struct_rm_update_eq in H11;eauto. }
    2: { intros s' Hs';exact Hs'. }
    sep auto.
    apply H10.
    sep auto. }
  eapply backward_rule1.
  { eapply astar_mono. intros s Hs;exact Hs. apply H9. }
  eapply forward_rule2.
  eapply assign_rule_general.
  { intros.
  eapply symbolic_lemmas.struct_offset_rv.
  eapply symbolic_lemmas.addrof_deref_rv.
  symbolic_execution.
  unfold OS_Port. eauto.
  unfold field_offset in *. 
  rewrite <- (Int.add_zero Int.zero).
  eapply sub_decllist_skipn_offsetfld with (n:= 8%nat);eauto.
  cbn. auto.
  { clear - H1. 
    do 18 (destruct n;[simpl in H1;inverts H1;cbn;auto | ]).
    destruct n.
    simpl in H1. inversion H1. simpl in H1. inversion H1. } 
  cbn. lia.
  clear - H3 H1.
  do 18 (destruct n;[simpl in H1;inverts H1;simpl in H3;inverts H3;cbn;auto  | ]).
  destruct n.
  simpl in H1. inversion H1. simpl in H1. inversion H1.  }
  { unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  reflexivity. }
  { intros. apply H9 in H10. apply H0. auto. }
  auto.
  { unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  intros. apply H in H10. auto. }
  unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  intros.
  sep auto.
  eapply symbolic_lemmas.struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply symbolic_lemmas.struct_rm_update_eq;eauto.
Qed.


Lemma event_port_QEntries_rv : forall s pptr qentries dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQEntries dport = Some (Vint32 qentries) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv pevent ′ → OSQEntries @ Int16u == (Vint32 qentries).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold os_ucos_h.OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 17 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma event_port_QSize_rv : forall s pptr qsize dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQSize dport = Some (Vint32 qsize) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv pevent ′ → OSQSize @ Int16u == (Vint32 qsize).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold os_ucos_h.OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 16 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma event_port_QIn_rv : forall s pptr qinptr dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qinptr) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv pevent ′ → OSQIn @ (Tptr os_ucos_h.OSMsg_t) == (Vptr qinptr).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  destruct dport;tryfalse. 
  do 14 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma event_port_QOut_rv : forall s pptr qout dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQOut dport = Some (Vptr qout) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv pevent ′ → OSQOut @ (Tptr os_ucos_h.OSMsg_t) == (Vptr qout).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold os_ucos_h.OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma event_port_QStart_rv : forall s pptr qstart dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQStart dport = Some (Vptr qstart) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv pevent ′ → OSQStart @ (Tptr os_ucos_h.OSMsg_t) == (Vptr qstart).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold os_ucos_h.OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 12 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma event_port_QEnd_rv : forall s pptr qend dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQEnd dport = Some (Vptr qend) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv pevent ′ → OSQEnd @ (Tptr os_ucos_h.OSMsg_t) == (Vptr qend).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold os_ucos_h.OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 13 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma event_port_OSQIn_data_rv' : forall s pptr dport qin z P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qin) ->
  s  |= LV pevent @ os_ucos_h.OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        PV qin @ char_t |-> (Vint32 z) ** P ->
  s  |= Rv (pevent ′ → OSQIn) → data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE) == Vptr (fst qin, (snd qin) +ᵢ Int.one).
Proof.
  intros.
  destruct qin as [qin_b qin_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_array_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl; lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  all: reflexivity.
Qed.

Lemma port_exwt_succ_pre_lemma:
  forall v'36 v'14 v'13 v'12 v'32 v'15 v'24 v'35 v'0 v'8 v'9 v'11 x1 v'6 v'10 v'38 v'69 v'39 v'58
               a b c v'62 v'7 vhold sus,
    v'12 <> Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P v'32
                ( (V$OS_EVENT_TYPE_PORT
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil,
                  v'13),v'14) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig v'32 (absport, x1) v'6 v'10 ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    TcbJoin (v'58, Int.zero) (a,b,c, sus) v'62 v'7 ->
    x1<>nil /\ GetHWait v'7 x1 (v'58,Int.zero) /\ TcbMod.get v'7 (v'58,Int.zero) = Some (a,b,c, sus) /\ a = ((v'38<<ᵢ$ 3)+ᵢv'39).
Proof.
  intros.
  lets Hs : tcbjoin_get_a H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  destruct H17 as (H17&Htype).
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by lia.
  assert (Int.unsigned v'39 < 8) as Hy by lia.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & sus' & Hst).
  intro; tryfalse.

  unfold get in Hst; simpl in Hst.
  rewrite Hs in Hst.
  inverts Hst.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'13)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'13).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
  assert (
    RLH_ECB_ETbl_PORT_P v'32
       (V$ OS_EVENT_TYPE_PORT
        :: Vint32 v'12
           :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
       v'14) v'7 /\
    RLH_ECB_ETbl_Q_P v'32
       (V$ OS_EVENT_TYPE_PORT
        :: Vint32 v'12
           :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
       v'14) v'7 /\
     RLH_ECB_ETbl_SEM_P v'32
       (V$ OS_EVENT_TYPE_PORT
        :: Vint32 v'12
           :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
       v'14) v'7 /\
     RLH_ECB_ETbl_MBOX_P v'32
       (V$ OS_EVENT_TYPE_PORT
        :: Vint32 v'12
           :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
       v'14) v'7 /\
     RLH_ECB_ETbl_MUTEX_P v'32
       (V$ OS_EVENT_TYPE_PORT
        :: Vint32 v'12
           :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
       v'14) v'7 
  ) by tauto. clear H2. rename H20 into H2.
  destruct H2 as (H2&Hres).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_PORT) = Some (V$OS_EVENT_TYPE_PORT)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & sus'' & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
  unfold get in Hge; simpl in Hge.
  rewrite Hs in Hge.
  inverts Hge.
  assert (
    RH_TCBList_ECBList_PORT_P v'11 v'7 v'8 /\
    RH_TCBList_ECBList_Q_P v'11 v'7 v'8 /\
     RH_TCBList_ECBList_SEM_P v'11 v'7 v'8 /\
     RH_TCBList_ECBList_MBOX_P v'11 v'7 v'8 /\
     RH_TCBList_ECBList_MUTEX_P v'11 v'7 v'8 
  ) by tauto.
  clear H3. rename H20 into H3.
  destruct H3 as (H3&Hres').
  destruct H3 as (Heg1 & Heg2).

  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (qw & Hem & Hin).
  unfold get in Hem; simpl in Hem.
  rewrite Hg in Hem.
  inverts Hem.
  assert (qw = nil \/ qw <> nil) by tauto.
  destruct H3.
  subst qw.
  simpl in Hin; tryfalse.
  splits; auto.
  unfolds.
  splits; auto.
  do 4 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 v'32 = Some (absport, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & sus' & Hbs).
  do 4 eexists; splits; eauto.
  assert (
    RHL_ECB_ETbl_PORT_P v'32
        (V$ OS_EVENT_TYPE_PORT
         :: Vint32 v'12
            :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
        v'14) v'7 /\
      RHL_ECB_ETbl_Q_P v'32
        (V$ OS_EVENT_TYPE_PORT
         :: Vint32 v'12
            :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
        v'14) v'7 /\
      RHL_ECB_ETbl_SEM_P v'32
        (V$ OS_EVENT_TYPE_PORT
         :: Vint32 v'12
            :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
        v'14) v'7 /\
      RHL_ECB_ETbl_MBOX_P v'32
        (V$ OS_EVENT_TYPE_PORT
         :: Vint32 v'12
            :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
        v'14) v'7 /\
      RHL_ECB_ETbl_MUTEX_P v'32
        (V$ OS_EVENT_TYPE_PORT
         :: Vint32 v'12
            :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: nil, v'13,
        v'14) v'7 
  ) by tauto. clear H17. rename H23 into H17.
  destruct H17 as (H17&Hres'').
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try lia;
    eauto.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  lia.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
         Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  lia.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.

Lemma array_int8u_nth_le_255:
  forall vl m i,
    array_type_vallist_match Int8u vl ->
    nth_val' m vl = Vint32 i ->
    Int.unsigned i <= 255.
Proof.
  inductions vl; intros.
  destruct m; simpl in H0; tryfalse.
  destruct m; simpl in H0; tryfalse.
  subst a. simpl in H. destruct (Int.unsigned i <=? Byte.max_unsigned)eqn:E; tryfalse.
  rewrite byte_max_unsigned_val in E. lia.
  destruct H; discriminate.
  destruct H. eauto. 
Qed.

Lemma port_exwt_succ_pre:
  forall ptbl petbl etbl evgrp dstportp  et ct ecbls1 ecbls wt ecbls2 ecblsc2 y i1 x t
               a b c v'62 tcbls vhold sus,
    evgrp <> Int.zero ->
    R_PrioTbl_P ptbl tcbls vhold ->
    RL_Tbl_Grp_P etbl (Vint32 evgrp) ->
    struct_type_vallist_match OS_EVENT et ->
    V_OSEventType et = Some (V$ OS_EVENT_TYPE_PORT) ->
    V_OSEventGrp et = Some (Vint32 evgrp) ->
    R_ECB_ETbl_P dstportp (et,etbl,petbl) tcbls ->
    RH_TCBList_ECBList_P ecbls tcbls ct ->
    EcbMod.join ecbls1 ecblsc2 ecbls ->
    TcbJoin dstportp (absport, wt) ecbls2 ecblsc2 ->
    array_type_vallist_match Int8u etbl ->
    length etbl = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned evgrp)) OSUnMapVallist = Vint32 y ->
    nth_val' (Z.to_nat (Int.unsigned y)) etbl = Vint32 i1 ->
    nth_val' (Z.to_nat (Int.unsigned i1)) OSUnMapVallist = Vint32 x ->
    nth_val' (Z.to_nat (Int.unsigned ((y<<ᵢ$ 3)+ᵢx))) ptbl = Vptr (t, Int.zero)->
    TcbJoin (t, Int.zero) (a,b,c, sus) v'62 tcbls ->
    wt<>nil /\ GetHWait tcbls wt (t,Int.zero) /\ TcbMod.get tcbls (t,Int.zero) = Some (a,b,c, sus) /\ a = ((y<<ᵢ$ 3)+ᵢx).
Proof.
  intros.
  lets Htm: array_int8u_nth_lt_len H9.
  struct_type_vallist_match_elim.
  invertsr H3. invertsr H4.
  assert (Int.unsigned i1 <= 255) by (eapply array_int8u_nth_le_255; eauto).
  eapply port_exwt_succ_pre_lemma; eauto.
  assert (Int.unsigned y <8).
  eapply math_unmap_get_y. 2: eauto. auto. lia.
  assert (Int.unsigned x <8).
  eapply math_unmap_get_y. 2: eauto. auto. lia.
  Unshelve.
  all: auto.
  exact O.
Qed.

Lemma Int_divu_self:
  forall i,  i <> Int.zero -> Int.divu i i = Int.one.
Proof.
  intros. mauto. f_equal. 
  pose proof Int.unsigned_range_2 i.
  destruct (Z.eq_dec (Int.unsigned i) 0).
  rewrite <- Int.unsigned_zero in e.
  apply unsigned_inj in e. subst. congruence.
  now apply Z_div_same_full.
Qed.

Lemma update_nth_val_same:
  forall l n a b,
  update_nth_val n (update_nth_val n l a) b = update_nth_val n l b.
Proof.
  induction l; intros.
  simpl. destruct n; auto.
  simpl. destruct n; auto.
  simpl. f_equal. apply IHl.
Qed.

Lemma update_nth_val_diff:
  forall l n m a b,
  n <> m ->
  update_nth_val n (update_nth_val m l a) b = update_nth_val m (update_nth_val n l b) a.
Proof.
  induction l; intros.
  simpl. destruct n, m; auto.
  simpl. destruct n, m; auto; try lia.
  simpl. f_equal. apply IHl; auto.
Qed.

Lemma nth_error_S_middle:
  forall {A : Type} (l1 l2 : list A) (a b: A),
  nth_error (l1 ++ a :: b:: l2) (S(length l1)) = Some b.
Proof.
  intros. pose proof nth_error_middle (l1++a::nil) (l2) b.
  rewrite app_length in H.
  simpl in H.
  rewrite <- app_assoc in H. simpl in H.
  assert (length l1 + 1 = S(length l1))%nat by lia.
  now rewrite <- H0.
Qed.

Lemma QPortPost_struct_type_vallist_match_1: forall chanid i1 dpnum csemid v'22 x15 x16 x17,
  Int.unsigned chanid <= 255 ->
  Int.unsigned i1 <= 255 ->
  Int.unsigned dpnum <= 255 ->
  Int.unsigned ($ Z.of_nat csemid) <= 255 ->
  isptr v'22 ->
  isptr x15 ->
  isptr x16 ->
  isptr x17 ->
  struct_type_vallist_match OS_Channel
  (Vint32 chanid
    :: Vint32 i1
      :: Vint32 dpnum
       :: V$ Z.of_nat csemid :: v'22 :: x15 :: x16 :: x17 :: nil).
Proof. intros. pauto. Qed.

Lemma QPortPost_struct_type_vallist_match_2: forall dport p,
   struct_type_vallist_match' OS_Port_Seg_dls dport ->
   struct_type_vallist_match' OS_Port_Seg_dls (update_nth_val 14 dport (Vptr p)).
Proof.
   intros.
   unfold OS_Port_Seg_dls in H. struct_type_vallist_match'_elim. simpl. pauto.
Qed.

Lemma QPortPost_struct_type_vallist_match_3: forall dport v p,
   (Int.unsigned v <=? Int16.max_unsigned) = true ->
   struct_type_vallist_match' OS_Port_Seg_dls dport ->
   struct_type_vallist_match' OS_Port_Seg_dls (update_nth_val 17 (update_nth_val 14 dport (Vptr p)) (Vint32 v)).
Proof.
   intros.
   unfold OS_Port_Seg_dls in H0. struct_type_vallist_match'_elim. simpl. pauto.
Qed.

Lemma QPortPost_struct_type_vallist_match_4: forall x15 x17 chanid p,
   isptr x15 ->
   isptr x17 ->
   Int.unsigned chanid <= 255 ->
   struct_type_vallist_match OS_Channel
  (Vint32 chanid
   :: V$ 1
      :: V$ 0
         :: V$ DEFAULT_CHANNLE_SEMAPHROE
            :: Vnull :: x15 :: Vptr p :: x17 :: nil).
Proof. intros. pauto. Qed.

Lemma QPortPost_pauto_ltu_1: forall csemid,
  Int.unsigned ($ Z.of_nat csemid) <= 255 ->
  (if Int.unsigned ($ Z.of_nat csemid) <=? Byte.max_unsigned then true else false) = true.
Proof. intros. pauto. Qed.


Ltac qportpostproof_tac:=
  try match goal with
  | |- struct_type_vallist_match OS_Channel _ => 
        first[now apply QPortPost_struct_type_vallist_match_1 |
              now apply QPortPost_struct_type_vallist_match_4]
  | |- struct_type_vallist_match' OS_Port_Seg_dls _ =>
        first[now apply QPortPost_struct_type_vallist_match_2| 
              now apply QPortPost_struct_type_vallist_match_3]
  | |- (if Int.unsigned ($ Z.of_nat _) <=? Byte.max_unsigned then true else false) = true => 
        first [now apply QPortPost_pauto_ltu_1]
  end.