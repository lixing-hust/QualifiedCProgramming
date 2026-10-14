Require Import ucos_include.
Require Import Lia.

Require Import corecommu_rules.
Require Import corecommu_tactics.
Require Import os_ucos_h.

Open Scope code_scope.

Open Scope int_scope.

Lemma Aarray_fold:
  forall a b c d,
  Aarray a (Tarray b c) d =
  Aarray' a c b d.
Proof.
  intros. unfold Aarray; auto.
Qed.

Lemma AOScoreheapl_app:
  forall l1 l2,
    AOScoreheapl (l1 ++ l2) <==>
    AOScoreheapl l1 ** AOScoreheapl l2.
Proof.
  induction l1; intros.
  - simpl app.
    simpl AOScoreheapl at 2.
    split; sep auto.
  - destruct a as [[? ?] ?].
    simpl AOScoreheapl at 1 2.
    split; sep auto;
    apply IHl1; auto.
Qed.

Lemma AOScoreheapl_app_frame:
  forall l1 l2 P,
    AOScoreheapl (l1 ++ l2) ** P <==>
    AOScoreheapl l1 ** AOScoreheapl l2 ** P.
Proof.
  intros.
  split;
  sep auto;
  apply AOScoreheapl_app; auto.
Qed.

Lemma get_off_addr_0: forall l,
  get_off_addr l ($ 0) = l.
Proof.
  destruct l.
  unfold get_off_addr.
  simpl.
  rewrite Int.add_zero.
  auto.
Qed.

Fixpoint get_off_addr_repeat (n:nat) t o:addrval:=
  match n with
  | O => t
  | S n' => get_off_addr_repeat n' (get_off_addr t o) o
  end.

Lemma get_off_addr_repeat_get_off_addr:
  forall n p o, get_off_addr_repeat n (get_off_addr p o) o = get_off_addr (get_off_addr_repeat n p o) o.
Proof.
  induction n; intros; simpl; auto.
 Qed.


(* FIXME: extra conditions restricting the length of vl1 and vl2 may be required *)
Lemma Aarray'_app:
  forall l vl1 vl2,
    (Z.of_nat (length vl1 + length vl2) <= Int.max_unsigned)%Z ->
    Aarray' l (length vl1 + length vl2) Int8u (vl1 ++ vl2) <==>
    Aarray' l (length vl1) Int8u vl1 **
    Aarray' (get_off_addr l ($ Z.of_nat (length vl1))) (length vl2) Int8u vl2.
Proof.
  intros l vl1; revert l.
  induction vl1; intros;
  rename H into Hr.
  - simpl Nat.add; simpl app.
    simpl Aarray' at 2.
    simpl get_off_addr.
    rewrite get_off_addr_0.
    split; sep auto.
  - simpl length; simpl app.
    replace (S (length vl1) + length vl2)%nat with (S (length vl1 + length vl2)); auto.
    destruct l.
    simpl Aarray' at 1;
    simpl Aarray' at 2.
    assert (
      get_off_addr (b, i) ($ Z.of_nat (S (length vl1))) = get_off_addr (b, i +ᵢ  $ 1) ($ Z.of_nat (length vl1))
    ).
    {
      assert (Z.of_nat (S (length vl1)) = 1 + Z.of_nat (length vl1))%Z; [rewrite Nat2Z.inj_succ; lia | ].
      rewrite H.
      unfold get_off_addr.
      simpl fst; simpl snd.
      assert ($ (1 + Z.of_nat (length vl1)) = Int.add ($ 1) ($ (Z.of_nat (length vl1)))).
      {
        (* Search ($ (_ + _)). *)
        rewrite Int.add_unsigned.
        (* Search (Int.unsigned ($ _)). *)
        assert (Int.unsigned ($ 1) = 1)%Z; auto.
        assert (Int.unsigned ($ Z.of_nat (length vl1)) = Z.of_nat (length vl1)).
        {
          apply int_usign_eq; try lia.
          rewrite Nat2Z.inj_add in Hr.
          simpl length in Hr.
          int auto.
        }
        rewrite H0, H1; auto.
      }
      rewrite H0.
      rewrite Int.add_assoc.
      auto.
    }
    rewrite H.
    simpl length in Hr.
    split; sep auto;
    apply IHvl1; auto;
    int auto.
Qed.

Lemma Aarray'_app_frame:
  forall l vl1 vl2 P,
    (Z.of_nat (length vl1 + length vl2) <= Int.max_unsigned)%Z ->
    Aarray' l (length vl1 + length vl2) Int8u (vl1 ++ vl2) ** P <==>
    Aarray' l (length vl1) Int8u vl1 **
    Aarray' (get_off_addr l ($ Z.of_nat (length vl1))) (length vl2) Int8u vl2 ** P.
Proof.
  intros.
  split;
  sep auto;
  apply Aarray'_app; auto.
Qed.

Lemma array_type_vallist_match_app:
  forall t l1 l2,
  array_type_vallist_match t (l1 ++ l2) <->
  array_type_vallist_match t l1 /\
  array_type_vallist_match t l2.
Proof.
  induction l1; intros.
  - simpl; tauto.
  - simpl.
    rewrite IHl1.
    tauto.
Qed.

Lemma In_heapl_addrval_split:
  forall coreheapl l m,
  In_heapl_addrval coreheapl l m ->
  forall P,
  AOScoreheapl coreheapl ** P
  ==>
  EX l1 l2 n vl1 vl2,
  [| coreheapl = l1 ++ (l, n, vl1 ++ vl2) :: l2 /\
     length vl1 = m |] **
  AOScoreheapl coreheapl ** P.
Proof.
  intros.
  destruct H as [n [vl [? ?]]].
  apply in_split in H as [l1 [l2 ?]].
  pose proof firstn_skipn m vl; subst.
  exists l1 l2 n (firstn m vl) (skipn m vl).
  rewrite <- H2 at 1.
  sep auto. split; auto.
  apply AOScoreheapl_app_frame in H0.
  simpl AOScoreheapl at 2 in H0.
  apply astar_assoc_intro in H0.
  sep lift 2%nat in H0.
  destruct l.
  eapply array'_length_intro in H0.
  apply firstn_length_le; lia.
Qed.

Lemma split_coreheapl:
  forall l1 l2 l n vl1 vl2 m,
  length vl1 = m ->
  In_heapl_addrval (l1 ++ (l, n, vl1 ++ vl2) :: l2) l m ->
  forall P,
  AOScoreheapl (l1 ++ (l, n, vl1 ++ vl2) :: l2) ** P
  ==>
  AOScoreheapl (l1 ++ (get_off_addr l (Int.repr (Z.of_nat m)), (n - m)%nat, vl2) :: l2) **
  Aarray l (Tarray Tint8 m) vl1 **
  (* required when rebuilding the entire cheapl *)
  [| array_type_vallist_match Tint8 vl1 /\ (length (vl1 ++ vl2) <= (Z.to_nat HEAP_MAX_LENGTH ))%nat|] ** P.
Proof.
  intros.
  sep cancel 2%nat 4%nat.
  apply AOScoreheapl_app in H1.
  simpl AOScoreheapl at 2 in H1.
  apply AOScoreheapl_app_frame.
  simpl AOScoreheapl at 2.
  assert (length vl1 + length vl2 = n)%nat as Htmp.
  {
    sep lift 2%nat in H1.
    destruct l.
    eapply array'_length_intro in H1.
    rewrite app_length in H1; lia.
  }
  subst.
  sep auto.
  - replace (length vl1 + length vl2 - length vl1)%nat with (length vl2); try lia.
    apply Aarray'_app in H1; [sep auto | ].
    mauto.
  - split; try split.
    + destruct H as [? _].
      apply array_type_vallist_match_app in H; tauto.
    + rewrite app_length.
      mauto.
  - destruct H.
    split.
    + apply array_type_vallist_match_app in H; tauto.
    + lia.
Qed.

Lemma AOScoreheapl_length:
  forall cheapl l n vl,
    In (l, n, vl) cheapl ->
    AOScoreheapl cheapl ==>
    [|n = length vl|] ** AOScoreheapl cheapl.
Proof.
  intros.
  apply in_split in H as [l1 [l2 ?]]; subst.
  apply AOScoreheapl_app in H0.
  simpl AOScoreheapl at 2 in H0.
  sep lift 2%nat in H0.
  destruct l.
  pose proof array'_length_intro _ _ _ _ _ H0.
  apply astar_l_apure_intro; auto.
  apply AOScoreheapl_app.
  simpl AOScoreheapl at 2.
  sep lift 2%nat.
  auto.
Qed.


Lemma AOScoreheapl_length_frm:
  forall cheapl l n vl P,
    In (l, n, vl) cheapl ->
    AOScoreheapl cheapl ** P ==>
    [|n = length vl|] ** AOScoreheapl cheapl ** P.
Proof.
  intros.
  sep cancel P.
  eapply AOScoreheapl_length;eauto.
Qed.

Lemma Get_heapl_addrval_in_list:
  forall cheapl l n vl1 vl2 P,
    In (l, n, vl1 ++ vl2) cheapl ->
    AOScoreheapl cheapl ** P ==>
    [|Get_heapl_addrval cheapl l (length vl1) vl1|] ** AOScoreheapl cheapl ** P.
Proof.
  intros.
  sep cancel 2%nat 3%nat.
  apply (AOScoreheapl_length _ _ _ _ H) in H0.
  sep auto.
  apply in_split in H as [l1 [l2 ?]]; subst.
  exists (length (vl1 ++ vl2)) (vl1 ++ vl2).
  split; [apply in_elt | ].
  split; [rewrite app_length; lia | ].
  replace (length vl1) with (length vl1 + 0)%nat; try lia.
  rewrite firstn_app_2.
  simpl. rewrite app_nil_r. auto.
Qed.


Lemma match_sendheap_length:
  forall step memll vll,
    match_sendheap step memll vll ->
    length memll = length vll.
Proof.
  induction memll; intros.
  - destruct vll; auto.
    inversion H.
  - destruct vll; inversion H.
    apply IHmemll in H1.
    simpl. lia.
Qed.

Lemma sendheap_length:
  forall memll sh,
    length memll = Z.to_nat CORENUM ->
   RLH_IpcSendHeap_P memll sh ->
    length sh = (Z.to_nat CORENUM - 1)%nat.
Proof.
  intros.
  rewrite <- (firstn_skipn curcore sh).
  rewrite app_length.
  simpl.
  destruct H0.
  apply match_sendheap_length in H0, H1.
  assert ( length (firstn curcore memll) + length (skipn (S curcore) memll) = 7)%nat.
  {  clear H0 H1.
  pose proof eq_refl (length memll).
  rewrite <- (firstn_skipn (S curcore) memll) in H0 at 1.
  rewrite app_length in H0.
  pose proof dnum_range.
  assert (S curcore <= length memll)%nat;
  [unfold curcore; rewrite H; unfold CORENUM; lia| ].
  assert (curcore <= length memll)%nat; try lia.
  apply firstn_length_le in H2, H3.
  rewrite H2 in H0. rewrite H3.
  rewrite H in H0.
  unfold CORENUM in H0. lia.
  }
  rewrite H0, H1 in H2.
  auto.
Qed.

Lemma set_sendheap_valid:
  forall memll sh n v size,
    (n < Z.to_nat CORENUM - 1)%nat ->
    length memll = Z.to_nat CORENUM ->
   RLH_IpcSendHeap_P memll sh ->
    exists sh', set_sendheap n sh size v sh'.
Proof.
  intros.
  pose proof sendheap_length _ _ H0 H1.
  rewrite <- H2 in H.
  apply nth_error_Some in H.
  destruct (nth_error sh n) eqn:eq; try tauto.
  apply nth_error_split in eq as [sh1 [sh2 [? ?]]].
  exists (sh1 ++ (v ++ skipn size l) :: sh2).
  exists sh1 sh2 l; auto.
Qed.

Lemma match_sendheap_app:
  forall memll1 memll2 sh1 sh2 step,
    length memll1 = length sh1 ->
    match_sendheap step (memll1 ++ memll2) (sh1 ++ sh2) <->
    match_sendheap step memll1 sh1 /\
    match_sendheap step memll2 sh2.
Proof.
  induction memll1; destruct sh1; intros;
  simpl in H; try inversion H; simpl; try tauto.
  split; intros.
  - destruct H0.
    apply IHmemll1 in H2; auto.
    tauto.
  - destruct H0 as [[? ?] ?].
    split; auto.
    apply IHmemll1; auto.
Qed.

Lemma nth_error_middle {A: Type}:
  forall l1 l2 (a: A),
    nth_error (l1 ++ a :: l2) (length l1) = Some a.
Proof.
  intros.
  replace a with (nth (length l1) (l1 ++ a :: l2) a) at 2;
  [ |apply nth_middle].
  apply nth_error_nth'.
  rewrite app_length; simpl; lia.
Qed.

Lemma ipcsend_RLH_IpcSendHeap_P_preserve:
  forall meml1 meml2 memll1 memll2 dst step idx size vldst vl1 sendh sendh',
  ((dst > curcore) /\ step = curcore /\ idx = (dst - 1)\/
  (dst < curcore) /\ step = (curcore - 1) /\ idx = dst)%nat ->
  length meml1 = step ->
  length memll1 = dst ->
  set_sendheap idx sendh size vl1 sendh' ->
 RLH_IpcSendHeap_P (memll1 ++ (meml1 ++ vldst :: meml2) :: memll2) sendh ->
 RLH_IpcSendHeap_P (memll1 ++ (meml1 ++ (vl1 ++ skipn size vldst) :: meml2) :: memll2) sendh'.
Proof.
  intros.
  rename H2 into Htmp; rename H3 into H2; rename Htmp into H3.
  destruct H3 as [sh1 [sh2 [vldst' [? [? ?]]]]]; subst.
  
  destruct H as [[? [? Hidx]] | [? [? Hidx]]].
  {
    destruct H2.
    assert (curcore - length memll1 = 0)%nat; try lia.
    assert (S curcore - length memll1 = 0)%nat; try lia.
    assert (curcore - length sh1 = 0)%nat; try lia.
    do 2 rewrite firstn_app in H1.
    do 2 rewrite skipn_app in H2.
    split;
    try do 2 rewrite firstn_app;
    try do 2 rewrite skipn_app;
    rewrite H3, H4, H5 in *;
    simpl firstn in *;
    repeat rewrite skipn_O in *; auto.
    apply match_sendheap_app in H2 as [? ?];
    [ |do 2 rewrite skipn_length; lia].
    apply match_sendheap_app;
    [do 2 rewrite skipn_length; lia| ].
    split; auto.
    destruct H6; split; auto.
    rewrite <- H0 in *.
    rewrite nth_error_middle in H6;
    inversion H6; subst vldst'; clear H6.
    rewrite nth_error_middle; auto.
  }
  {
    rewrite list_cons_assoc in H2.
    rewrite (list_cons_assoc sh1) in H2.
    rewrite list_cons_assoc.
    rewrite (list_cons_assoc sh1).
    destruct H2.

    rewrite firstn_app in H1.
    rewrite (firstn_app _ _ sh2) in H1.
    rewrite firstn_all2 in H1;
    [ |rewrite app_length; simpl; lia].
    rewrite (@firstn_all2 _ curcore) in H1;
    [ |rewrite app_length; simpl; lia].

    rewrite skipn_app in H2.
    rewrite (skipn_app _ _ sh2) in H2.
    rewrite skipn_all2 in H2;
    [ |repeat rewrite app_length; simpl; lia].
    rewrite (@skipn_all2 _ curcore) in H2;
    [ |repeat rewrite app_length; simpl; lia].
    repeat rewrite app_nil_l in H2.

    apply match_sendheap_app in H1 as [? ?];
    [ |repeat rewrite app_length; simpl; auto].
    apply match_sendheap_app in H1 as [? ?];
    [ |repeat rewrite app_length; simpl; auto].
    destruct H4 as [? ?].
    rewrite <- H0 in H4.
    rewrite nth_error_middle in H4;
    inversion H4; subst vldst'; clear H4.
    
    repeat rewrite app_length in *.
    simpl length in *.

    split.
    + rewrite firstn_app.
      rewrite (firstn_app _ _ sh2).
      rewrite firstn_all2;
      [ |rewrite app_length; simpl; lia].
      rewrite (@firstn_all2 _ curcore);
      [ |rewrite app_length; simpl; lia].
      apply match_sendheap_app;
      [repeat rewrite app_length; simpl; auto| ].
      repeat rewrite app_length.
      simpl length. split; auto.
      apply match_sendheap_app;
      [repeat rewrite app_length; simpl; auto| ].
      simpl. repeat split; auto.
      rewrite <- H0.
      apply nth_error_middle.
    + rewrite skipn_app.
      rewrite (skipn_app _ _ sh2).
      rewrite skipn_all2;
      [ |repeat rewrite app_length; simpl; lia].
      rewrite (@skipn_all2 _ curcore);
      [ |repeat rewrite app_length; simpl; lia].
      repeat rewrite app_nil_l.
      repeat rewrite app_length.
      simpl length; auto.
  }
Qed.

Lemma ipcsend_generateipc_Rv_ipcinfo:
  forall v P,
    v = CORE0_IPC \/ v = CORE1_IPC \/
    v = CORE2_IPC \/ v = CORE3_IPC \/
    v = CORE4_IPC \/ v = CORE5_IPC \/
    v = CORE6_IPC \/ v = CORE7_IPC ->
    LV ipcinfo @ Int32u |-> (V$ v) ** P ==>
    LV ipcinfo @ Int32u |-> (V$ v) ** P **
    [|exists r, (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/
            r = 4 \/ r = 5 \/ r = 6 \/ r = 7)%nat /\
      forall s0 P0 z, s0 |= LV ipcinfo @ Int32u |-> (V$ v) ** P0 -> s0 |= Rv (ipcinfo ′ |ₑ ′ z) @ Tint32 == (Vint32 (IPCINFO_brach r z))|].
Proof.
  intros.
  sep auto.
  (* assert (s |= Rv (ipcinfo ′) @ Int32u == (V$ v));
  [symbolic_execution| ]. *)
  destruct H as [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]; subst;
  [exists 0%nat|exists 1%nat|exists 2%nat|exists 3%nat|
   exists 4%nat|exists 5%nat|exists 6%nat|exists 7%nat];
  split; try lia;
  try symbolic_execution.
Qed.
    

Lemma ipcsend_RLH_IpcRecvHeap_P_preserve:
  forall memll1 memll2 recvh v w,
    length memll1 <> curcore ->
    RLH_IpcRecvHeap_P (memll1 ++ v :: memll2) recvh ->
    RLH_IpcRecvHeap_P (memll1 ++ w :: memll2) recvh.
Proof.
  intros.
  unfold RLH_IpcRecvHeap_P in *.
  assert (length memll1 < curcore \/ length memll1 > curcore \/ length memll1 = curcore)%nat as [? | [? | ?]];
  [ lia | | | tauto ].
  - rewrite list_cons_assoc in *.
    rewrite nth_error_app2 in H0;
    try (rewrite app_length; simpl length; lia).
    rewrite nth_error_app2;
    rewrite app_length; simpl length; try lia.
    rewrite app_length in H0; simpl in H0; auto.
  - rewrite nth_error_app1 in H0; try lia.
    rewrite nth_error_app1; try lia. auto.
Qed.


Fixpoint AOSIPCMem_aux_rm (i: nat) (pl : list val) (memlls:list (list vallist)) :=
  match pl with 
  | nil => match memlls with nil => Aemp | _ => Afalse end 
  | Vptr p::pl' => match memlls with 
                  | nil => Afalse 
                  | memls :: memlls' => match i with
                     | 0%nat => AOSIPCMem_aux pl' memlls'
                     | S i' => Memory_sigcore p memls ** AOSIPCMem_aux_rm i' pl' memlls'
                     end
                  end 
  | _ :: _ => Afalse
  end.

Lemma good_frm_AOSIPCMem_aux_rm : 
  forall pl memlls i, GoodFrm (AOSIPCMem_aux_rm i pl memlls).
Proof.
  induction pl;intros;destruct memlls.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm; good_frm_sovler.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm; good_frm_sovler.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm;destruct a; good_frm_sovler.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm; 
    destruct a; try (good_frm_sovler).
    unfold Memory_sigcore;good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIPCMem_aux_rm : good_frm_lemmas.


Lemma can_change_aop_AOSIPCMem_aux_rm : 
  forall pl memlls i, can_change_aop (AOSIPCMem_aux_rm i pl memlls).
Proof.
  induction pl;intros;destruct memlls.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm; can_change_aop_solver.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm; can_change_aop_solver.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm;destruct a; can_change_aop_solver.
  - destruct i; unfold AOSIPCMem_aux_rm;fold AOSIPCMem_aux_rm; 
    destruct a; try (can_change_aop_solver).
    unfold Memory_sigcore;can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCMem_aux_rm : can_change_aop.

Lemma firstn_firstn_app : 
forall [A : Type] i (vl vl': list A), (i < length vl)%nat -> firstn i vl = firstn i ((firstn i vl) ++ vl').
Proof.
 intros.
 rewrite firstn_app. erewrite firstn_length_le by lia.
 assert ( i - i = 0)%nat by lia.
 rewrite H0. cbn.
 erewrite firstn_firstn.
 assert (Init.Nat.min i i = i)%nat by lia.
 rewrite H1.
 apply app_nil_end.
Qed.

Lemma skipn_firstn_app : 
forall [A : Type] i (vl vl': list A), (length vl' = i)%nat -> skipn i vl = skipn i (vl' ++ (skipn i vl)).
Proof.
 intros.
 rewrite skipn_app.
 assert (length  (skipn i vl') = (length vl' - i)%nat) by (apply skipn_length).
 rewrite H in *.
 assert ( i - i = 0)%nat by lia.
 rewrite H1 in *. cbn.
 destruct (skipn i vl');tryfalse.
 auto.
Qed.

Lemma AOSIPCMem_aux_separate : forall pl memlls n i p memls, 
  length pl = n -> 
  (i < n)%nat ->
  nth_val' i pl = Vptr p -> nth_error memlls i = Some memls -> 
   AOSIPCMem_aux pl memlls <==>  Memory_sigcore p memls ** AOSIPCMem_aux_rm i pl memlls.
Proof.
  induction pl;intros.
  - simpl in H. subst. inversion H0. 
  -  destruct n;tryfalse.
     destruct memlls. rewrite nth_error_nil in H2. inversion H2.
     destruct i. 
    + simpl in H,H1,H2. inversion H2. subst. 
      split;intros.
      * unfold AOSIPCMem_aux in *;fold AOSIPCMem_aux in *.
        cbn [AOSIPCMem_aux_rm]. sep_auto.
      * unfold AOSIPCMem_aux in *;fold AOSIPCMem_aux in *.
        cbn [AOSIPCMem_aux_rm] in *. sep auto.
    + simpl in H,H1,H2. apply eq_add_S in H.
      apply lt_S_n in H0.
      specialize (IHpl _ _ _ _ _ H H0 H1 H2).
      cbn [AOSIPCMem_aux AOSIPCMem_aux_rm]. 
      split;intros.
      * destruct a;
        afalse_tryfalse.  
        sep lift 2%nat. sep cancel Memory_sigcore.
        eapply IHpl;auto.
      * destruct a;sep lift 2%nat in H3;afalse_tryfalse.  
        sep cancel Memory_sigcore.
        eapply IHpl;auto.
Qed.

Lemma AOSIPCMem_aux_updatei' : forall pl memlls n i  memls P, 
  length pl = n -> 
  (i < n)%nat -> AOSIPCMem_aux_rm i pl memlls ** P ==>
  AOSIPCMem_aux_rm i pl ((firstn i memlls) ++ memls :: (skipn (i+1) memlls)) ** P.
Proof.
  induction pl;intros.
  - simpl in H. subst. inversion H0. 
  -  destruct n;tryfalse.
     destruct memlls.
     { destruct i;unfold AOSIPCMem_aux_rm in H1; destruct a;afalse_tryfalse. }
     destruct i. 
    + simpl in H,H0. 
      cbn [AOSIPCMem_aux_rm firstn] in *.
      destruct a;afalse_tryfalse. rewrite app_nil_l.
      rewrite plus_O_n. cbn [skipn].
      sep_auto.
    + simpl in H,H0. apply eq_add_S in H.
      apply lt_S_n in H0.
      cbn [AOSIPCMem_aux_rm firstn] in *.
      destruct a;afalse_tryfalse.
      rewrite <- app_comm_cons.
      sep cancel Memory_sigcore.
      assert ((S i + 1 ) = (S (i + 1)))%nat by lia.
      rewrite H2.
      cbn [firstn skipn].
      eapply IHpl;eauto. 
Qed.

Lemma AOSIPCMem_aux_updatei : forall pl memlls1 memlls2 n i  memls memls' P, 
  length (memlls1 ++ memls :: memlls2) = n ->
  length pl = n -> 
  length memlls1 = i ->
  (i < n)%nat ->
  AOSIPCMem_aux_rm i pl (memlls1 ++ memls :: memlls2) ** P ==>
  AOSIPCMem_aux_rm i pl (memlls1 ++ memls' :: memlls2) ** P.
Proof.
  intros.
  assert (memlls1 = firstn i (memlls1 ++ memls :: memlls2)).
  { rewrite firstn_app.  rewrite H1. rewrite Nat.sub_diag.
   cbn. rewrite <- H1. rewrite firstn_all. apply app_nil_end. }
  assert (i+1 = length (memlls1 ++ memls :: nil))%nat.
  { rewrite app_length. cbn. rewrite H1. auto. }
  assert (memlls2 = skipn (i+1)  (memlls1 ++ memls :: memlls2)).
  { rewrite list_cons_assoc.
    rewrite skipn_app. rewrite H5. rewrite Nat.sub_diag. cbn.
    rewrite  skipn_all. auto. }
  remember (memlls1 ++ memls :: memlls2) as memlls'.
  rewrite H4, H6.
  eapply AOSIPCMem_aux_updatei';eauto.
Qed.

Lemma ipcsend_AOSIPCMem_aux_updatei : forall pl memlls1 memlls2 i memls memls' P, 
  length (memlls1 ++ memls :: memlls2) = length pl ->
  length memlls1 = i ->
  AOSIPCMem_aux_rm i pl (memlls1 ++ memls :: memlls2) ** P ==>
  AOSIPCMem_aux_rm i pl (memlls1 ++ memls' :: memlls2) ** P.
Proof.
  intros.
  eapply AOSIPCMem_aux_updatei with (memls:=memls); auto.
  rewrite <- H0, app_length; simpl; lia.
Qed.

Lemma AOSIPCMem_aux_separate_frm : forall pl memlls n i p memls P,  
  length pl = n -> 
  (i < n)%nat ->
  nth_val' i pl = Vptr p -> nth_error memlls i = Some memls -> 
   AOSIPCMem_aux pl memlls ** P <==>  Memory_sigcore p memls ** AOSIPCMem_aux_rm i pl memlls ** P.
Proof.
  intros.
  split;intros;sep cancel P;
  eapply AOSIPCMem_aux_separate;eauto.
Qed.

Fixpoint Memory_sigcore_aux_rm (i: nat) (n:nat) (p: addrval) (memls: list vallist):=
  match memls with 
  | nil => Aemp
  | meml::memls' => if Nat.eqb i n then Memory_sigcore_aux (S n) p memls' else  Memory_Node n p meml ** Memory_sigcore_aux_rm i (S n) p memls'
  end.

Lemma good_frm_Memory_sigcore_aux_rm : 
  forall memls i n p, GoodFrm (Memory_sigcore_aux_rm i n p memls).
Proof.
  induction memls;intros.
  - cbn;auto.
  - cbn;auto. 
    destruct ((i =? n)%nat);
    good_frm_sovler.
    unfold Memory_Node. 
    good_frm_sovler.
Qed.

Hint Resolve good_frm_Memory_sigcore_aux_rm : good_frm_lemmas.

Lemma can_change_aop_Memory_sigcore_aux_rm : 
  forall memls i n p, can_change_aop (Memory_sigcore_aux_rm i n p memls).
Proof.
  induction memls;intros.
  - cbn;auto.
  - cbn;auto. 
    destruct ((i =? n)%nat);
    can_change_aop_solver.
    unfold Memory_Node.
    can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_Memory_sigcore_aux_rm : can_change_aop.

Lemma Memory_sigcore_aux_separate :
  forall memls p n m i  meml,
  length memls = n ->
  (i < n)%nat ->
  nth_error memls i = Some meml ->
  Memory_sigcore_aux m p memls <==> 
  Memory_Node (i + m) p meml ** Memory_sigcore_aux_rm (i+m) m p memls.
Proof.
  induction memls;intros.
  - simpl in H. subst. inversion H0.
  - destruct n;tryfalse.
    destruct i. 
    + simpl in H1. inversion H1.
      rewrite Nat.add_0_l in *. cbn [Memory_sigcore_aux Memory_sigcore_aux_rm].
      rewrite Nat.eqb_refl. tauto.
    + simpl in H, H1.  
      apply eq_add_S in H.
      apply lt_S_n in H0.
      specialize (IHmemls p _ (S m) _ _ H H0 H1).
      cbn [Memory_sigcore_aux Memory_sigcore_aux_rm].
      assert ((S i + m =? m)%nat = false). { apply Nat.eqb_neq. lia. }
      rewrite H2.
      assert (i + S m = S i + m)%nat by lia.
      rewrite H3 in *.
      split;intros.
      * sep lift 2%nat. sep cancel Memory_Node. eapply IHmemls;eauto.
      * sep lift 2%nat in H4. sep cancel Memory_Node. eapply IHmemls;eauto.
Qed.
    
Lemma Memory_sigcore_aux_separate_frm :
  forall memls p n m i  meml P, 
  length memls = n ->
  (i < n)%nat ->
  nth_error memls i = Some meml ->
  Memory_sigcore_aux m p memls ** P <==> 
  Memory_Node (i + m) p meml ** Memory_sigcore_aux_rm (i+m) m p memls ** P. 
Proof.
  intros.
  split;intros;sep cancel P;
  eapply Memory_sigcore_aux_separate;eauto.
Qed.

Lemma Memory_sigcore_aux_updatei' : forall memls  p  n m i meml P, 
 length memls = n ->
 (i < n )%nat ->
 Memory_sigcore_aux_rm (i+m) m p memls ** P ==>
 Memory_sigcore_aux_rm (i+m) m p ((firstn i memls) ++ meml :: (skipn (i+1) memls)) ** P.
Proof. 
  induction memls;intros.
  - simpl in H,H0. subst n. inversion H0.
  - simpl in H. destruct n. inversion H.
    apply eq_add_S in H.
    destruct i. 
    + assert (0+1= 1)%nat by lia.
      rewrite H2. cbn [firstn skipn].
      rewrite app_nil_l.
      assert (0+m = m)%nat by lia.
      rewrite H3 in *.
      cbn [Memory_sigcore_aux_rm] in *.
      assert ((m =? m)%nat = true) by (apply Nat.eqb_refl).
      rewrite H4 in *.
      sep auto. 
    + apply lt_S_n in H0.
      assert ((S i + m ) = (i + S m))%nat by lia.
      rewrite H2 in *.
      assert ((S i + 1 ) = (S (i + 1)))%nat by lia.
      rewrite H3.
      cbn [firstn skipn].
      rewrite <- app_comm_cons.
      cbn [Memory_sigcore_aux_rm] in *.
      assert ((i + S m =? m)%nat  = false). { apply Nat.eqb_neq. lia. }
      rewrite H4 in *.
      sep cancel Memory_Node.
      eapply IHmemls;eauto.
Qed.

Lemma Memory_sigcore_aux_updatei : forall memls1 memls2  p n m i meml meml' P, 
 length (memls1 ++ meml :: memls2) = n ->
 length memls1 = i ->
 (i < n )%nat ->
 Memory_sigcore_aux_rm (i+m) m p (memls1 ++ meml :: memls2) ** P ==>
 Memory_sigcore_aux_rm (i+m) m p (memls1 ++ meml' :: memls2) ** P.
Proof.
  intros.
  assert (memls1 = firstn i (memls1 ++ meml :: memls2)).
  { rewrite firstn_app.  rewrite H0. rewrite Nat.sub_diag.
   cbn. rewrite <- H0. rewrite firstn_all. apply app_nil_end. }
  assert (i+1 = length (memls1 ++ meml :: nil))%nat.
  { rewrite app_length. cbn. rewrite H0. auto. }
  assert (memls2 = skipn (i+1)  (memls1 ++ meml :: memls2)).
  { rewrite list_cons_assoc.
    rewrite skipn_app. rewrite H4. rewrite Nat.sub_diag. cbn.
    rewrite  skipn_all. auto. }
  remember (memls1 ++ meml :: memls2) as memls'.
  rewrite H3, H5.
  eapply Memory_sigcore_aux_updatei';eauto.
Qed.

Lemma ipcsend_Memory_sigcore_aux_updatei :
forall memls1 memls2 p i meml meml' P, 
 length memls1 = i ->
 Memory_sigcore_aux_rm i O p (memls1 ++ meml :: memls2) ** P ==>
 Memory_sigcore_aux_rm i O p (memls1 ++ meml' :: memls2) ** P.
Proof.
  intros.
  replace i with (i + 0)%nat; [ |lia].
  replace i with (i + 0)%nat in H0; [ |lia].
  eapply Memory_sigcore_aux_updatei;
  [ | | | apply H0]; auto.
  rewrite <- H, app_length.
  simpl. lia.
Qed.

Lemma AOSIPCMem_separate : 
  forall pl memlls P corei step,
  (corei < 8)%nat ->
  (step < 7)%nat -> 
  AOSIPCMem pl memlls ** P ==>
  EX p memls meml, Memory_Node step p meml ** Memory_sigcore_aux_rm step O p memls**
   AOSIPCMem_aux_rm corei pl memlls **  GAarray IPCMem (Tarray (Tptr Tint8) 8%nat) pl 
   **  [| isvptr_list pl /\ length pl = 8%nat /\ length memlls = 8%nat|] **
  [| nth_val' corei pl = Vptr p /\  nth_error memlls corei = Some memls /\ length memls = 7%nat /\ 
    nth_error memls step = Some meml|] ** P.
Proof. 
  intros.
  unfold AOSIPCMem in H1.
  sep split in H1. destruct H2 as [H2 [H3 H4]].
  lets Hp: isptr_list_nth_ptr_ex H3 H H2.
  destruct Hp as [p [Hp1 Hp2]].
  remember (nth_error memlls corei) eqn:Hm.
  destruct o as [ memls | ].
  2: { symmetry in Hm. apply nth_error_None in Hm.  false. lia. }
  sep lift 2%nat in H1.
  eapply AOSIPCMem_aux_separate_frm in H1;eauto.
  unfold Memory_sigcore in H1.
  sep split in H1.
  remember (nth_error memls step) eqn:Hm2.
  destruct o as [ meml | ].
  2: { symmetry in Hm2. apply nth_error_None in Hm2.   false. lia. }
  eapply Memory_sigcore_aux_separate_frm in H1;eauto.
  rewrite Nat.add_0_r in *.
  sep auto.
Qed.

Lemma AOSIPCMem_merge : 
  forall pl memlls P corei step p memls meml,
  (corei < 8)%nat ->
  (step < 7)%nat -> 
  Memory_Node step p meml ** Memory_sigcore_aux_rm step O p memls **
   AOSIPCMem_aux_rm corei pl memlls **  GAarray IPCMem (Tarray (Tptr Tint8) 8%nat) pl 
   **  [| isvptr_list pl /\ length pl = 8%nat /\ length memlls = 8%nat|] **
  [| nth_val' corei pl = Vptr p /\  nth_error memlls corei = Some memls /\ length memls = 7%nat /\ 
    nth_error memls step = Some meml|] ** P ==> 
    AOSIPCMem pl memlls ** P.
Proof.
  intros.
  sep split in H1.
  destruct H2 as [H2 [H4 H5]].
  destruct H3 as [H3 [H6 [H7 H8]]]. 
  rewrite <- (Nat.add_0_r step) in H1.
  eapply Memory_sigcore_aux_separate_frm in H1;eauto.
  assert (s |= Memory_sigcore p memls **
  AOSIPCMem_aux_rm corei pl memlls **
  GAarray IPCMem (Tarray (Tint8) ∗ 8) pl ** P).
  { unfold Memory_sigcore. sep auto.  }
  clear H1.
  eapply AOSIPCMem_aux_separate_frm in H9;eauto.
  unfold AOSIPCMem;sep auto.
Qed.

Lemma ipcsend_AOSIPCMem_merge : 
  forall pl memlls P corei step p memls meml,
  (corei < 8)%nat ->
  (step < 7)%nat -> 
  isvptr_list pl ->
  length pl = 8%nat ->
  length memlls = 8%nat ->
  nth_val' corei pl = Vptr p ->
  nth_error memlls corei = Some memls ->
  length memls = 7%nat ->
  nth_error memls step = Some meml ->
  Memory_Node step p meml ** Memory_sigcore_aux_rm step O p memls **
   AOSIPCMem_aux_rm corei pl memlls **  GAarray IPCMem (Tarray (Tptr Tint8) 8%nat) pl ** P ==> 
    AOSIPCMem pl memlls ** P.
Proof.
  intros.
  eapply AOSIPCMem_merge;
  [apply H | apply H0 | sep auto].
Qed.

Lemma AOScoreheapl_merge : forall l n m vl1 vl2 cheapl1 cheapl2 P, 
 (m <= n)%nat ->
 (n <= Z.to_nat HEAP_MAX_LENGTH)%nat ->
 length vl1 = m -> length vl2 = (n - m)%nat ->
 array_type_vallist_match Tint8 vl1 ->
 Aarray l (Tarray Tint8 m) vl1 **
 AOScoreheapl (cheapl1 ++ (get_off_addr l ($ (Z.of_nat m)), (n - m)%nat, vl2)::cheapl2)  ** P ==>
 AOScoreheapl (cheapl1 ++ (l, n, vl1 ++ vl2)::cheapl2) ** P.
Proof.
  intros.
  sep lift 2%nat in H4.
  apply AOScoreheapl_app_frame in H4.
  eapply AOScoreheapl_app_frame.
  sep cancel AOScoreheapl.
  cbn [AOScoreheapl] in *.
  sep split in H4.
  destruct H5.
  sep lift 3%nat.
  sep cancel AOScoreheapl.
  unfold Aarray in *.
  sep lift 2%nat in H4.
  rewrite <- H2, <- H1 in H4.
  assert (length vl1 + length vl2 = n)%nat.
  { rewrite H1, H2. eapply le_plus_minus_r;auto. }
  eapply Aarray'_app_frame in H4.
  rewrite H7 in *. sep auto.
  split;auto. apply array_type_vallist_match_app;auto.
  rewrite H7.
  clear -H0.
  eapply Z.le_trans.
  2: apply HEAP_MAX_LENGTH_range.
  apply inj_le in H0.
  rewrite Z2Nat.id in H0. auto.
  apply HEAP_MAX_LENGTH_range.
Qed. 

Lemma fold_Memory_Node: forall pb pi ni meml P,
  array_type_vallist_match Tint8 meml ->
  length meml = (Z.to_nat HEAP_MAX_LENGTH) ->
  Aarray' (pb,pi  +ᵢ(Int.mul ni ($ IPC_STEP))) 
  (Z.to_nat HEAP_MAX_LENGTH) Tint8 meml  ** P==>
  Memory_Node (Z.to_nat(Int.unsigned ni)) (pb,pi) meml ** P.
Proof.
  intros.
  unfold Memory_Node, Aarray, get_off_addr, fst, snd.
  unfold type_eq, os_ucos_h.dyn_refac_cfg .
  erewrite Z2Nat.id ;[auto |apply Int.unsigned_range].
  erewrite Int.repr_unsigned.
  sep auto.
Qed.

Definition same_option {A:Type} (v1 v2: option A):=
   match v1,v2 with
   | Some _, Some _ => True
   | None, None => True
   | _, _ => False
   end. 

Lemma PhdrArray_Pure_app_split: forall v11 v12 v21 v22 v31 v32 v41 v42,
length v11 = length v21 ->
length v11 = length v31 ->
length v11 = length v41 ->
length v12 = length v32 ->
length v12 = length v42 ->
length v12 = length v22 ->
PhdrArray_Pure (v11++v12) (v21++v22) (v31++v32)(v41++v42) ->
PhdrArray_Pure v11 v21 v31 v41 /\ PhdrArray_Pure v12 v22 v32 v42.
Proof.
induction v11; intros.
+ destruct v21; destruct v31; destruct v41; try discriminate. simpl. split. constructor. now simpl in H5.
+ destruct v21; destruct v31; destruct v41; try discriminate. simpl in H5.
    split.
    - simpl in H, H0, H1. inversion H. inversion H0. inversion H1.  inversion H5.
      * apply IHv11 in H14; try congruence. subst. eapply PhdrArray_Pure_NOT_LOAD; try tauto. exact H18. tauto.
      * apply IHv11 in H25; try congruence. subst.  eapply PhdrArray_PURE_LOAD1 ; eauto. tauto.
      * apply IHv11 in H25; try congruence. subst.  eapply PhdrArray_PURE_LOAD2 ; eauto. tauto.
      * apply IHv11 in H25; try congruence. subst.  eapply PhdrArray_PURE_LOAD3 ; eauto. tauto.
      * apply IHv11 in H25; try congruence. subst.  eapply PhdrArray_PURE_LOAD4 ; eauto. tauto.
    -  simpl in H, H0, H1. inversion H. inversion H0. inversion H1.  inversion H5;subst.
      * apply IHv11 in H14; tauto.
      * apply IHv11 in H25; tauto.
      * apply IHv11 in H25; tauto.
      * apply IHv11 in H25; tauto.
      * apply IHv11 in H25; tauto.
Qed.

Lemma PhdrArray_Pure_app_merge: forall v11 v12 v21 v22 v31 v32 v41 v42,
  PhdrArray_Pure v11 v21 v31 v41 ->
  PhdrArray_Pure v12 v22 v32 v42 ->
  PhdrArray_Pure (v11++v12) (v21++v22) (v31++v32)(v41++v42).
Proof.
  intros. induction H; simpl.
  + easy.
  + econstructor 2; eauto.
  + econstructor 3; eauto.
  + econstructor 4; eauto.
  + econstructor 5; eauto.
  + econstructor 6; eauto.
Qed.     

Lemma PhdrArray_Pure_same_length: forall  v1 v2 v3 v4,
  PhdrArray_Pure  v1 v2 v3 v4 ->
  length v2 = length v1 /\ length v3 = length v1 /\ length v4 = length v1.
Proof.
  intros. induction H; intros; simpl; try tauto; repeat split; try f_equal; try tauto.
Qed.

Lemma PhdrArray_Pure_change_single: forall mem1 mem2 dst1 dst2 vl file,
  same_option mem1 mem2 ->
  same_option dst1 dst2 ->
  PhdrArray_Pure (vl::nil)(file::nil) (mem1::nil) (dst1::nil) ->
  PhdrArray_Pure (vl::nil)(file::nil) (mem2::nil) (dst2::nil).
Proof.
  intros. inverts H1.
  - inverts H7. destruct mem2; inverts H. destruct dst2; inverts H0.
    econstructor 2; eauto. constructor.
  - inverts H18. destruct mem2; inverts H. destruct dst2; inverts H0.
    econstructor 3; eauto. constructor.
  - inverts H18. destruct mem2; inverts H. destruct dst2; inverts H0.
    econstructor 4; eauto. constructor.
  - inverts H18. destruct mem2; inverts H. destruct dst2; inverts H0.
    econstructor 5; eauto. constructor.
  - inverts H18. destruct mem2; inverts H. destruct dst2; inverts H0.
    econstructor 6; eauto. constructor.
Qed.

Lemma PhdrArray_Pure_change: forall mem1 mem2 dst1 dst2 vl file vll filel meml dstl,
  same_option mem1 mem2 ->
  same_option dst1 dst2 ->
  PhdrArray_Pure (vl::vll)(file::filel) (mem1::meml) (dst1::dstl) ->
  PhdrArray_Pure (vl::vll)(file::filel) (mem2::meml) (dst2::dstl).
Proof.
  intros. 
  assert (forall A a (b:list A), (a::nil)++b=a::b) as cons_app by reflexivity.
  rewrite <- cons_app. 
  rewrite <- cons_app with (a:=file).
  rewrite <- cons_app with (a:=mem2).
  rewrite <- cons_app with (a:=dst2).
  apply PhdrArray_Pure_same_length in H1 as ?.
  destruct H2 as (?&?&?).
  inverts H2. inverts H3. inverts H4.
  rewrite <- cons_app with (a:=vl) in H1.
  rewrite <- cons_app with (a:=file) in H1.
  rewrite <- cons_app with (a:=mem1) in H1.
  rewrite <- cons_app with (a:=dst1) in H1. 
  apply PhdrArray_Pure_app_split in H1 as (?&?); auto.
  apply PhdrArray_Pure_app_merge.
  eapply PhdrArray_Pure_change_single; eauto.
  auto.
Qed.


Lemma PhdrArray_app_split: forall v11 v12 v21 v22 v31 v32 v41 v42 file p,
length v11 = length v21 ->
length v11 = length v31 ->
length v11 = length v41 ->
length v12 = length v32 ->
length v12 = length v42 ->
length v12 = length v22 ->
PhdrArray file p (v11++v12) (v21++v22) (v31++v32)(v41++v42) ==>
PhdrArray file p v11 v21 v31 v41 ** PhdrArray file (get_off_addr_repeat  (length v11) p ($size_of_Elf32_Phdr)) v12 v22 v32 v42.
Proof.
induction v11; intros.
+ destruct v21; destruct v31; destruct v41; try discriminate. simpl PhdrArray at 1.
   simpl in H5. simpl get_off_addr_repeat. sep auto.
+ destruct v21; destruct v31; destruct v41; try discriminate. 
    inversion H. inversion H0. inversion H1. clear H H0 H1.  simpl app in H5.
    unfold PhdrArray in H5. rewrite PhdrArray_fold in H5.
    sep remember (4::nil)%nat in H5.
    assert (s |= PhdrArray file  (get_off_addr p ($ size_of_Elf32_Phdr)) v11 v21 v31 v41 **
      PhdrArray file  (get_off_addr_repeat (length v11) (get_off_addr p ($ size_of_Elf32_Phdr)) ($size_of_Elf32_Phdr)) v12 v22 v32
        v42 ** H).
    { sep autocancel. apply IHv11 in H5; auto. }  
    assert (get_off_addr_repeat (length v11) (get_off_addr p ($ size_of_Elf32_Phdr))
           ($ size_of_Elf32_Phdr)= get_off_addr_repeat (S (length v11))  p ($size_of_Elf32_Phdr)) by reflexivity.
    rewrite H1 in H0. clear H1 H5. subst H.  simpl length. sep autocancel. 
    unfold PhdrArray. rewrite PhdrArray_fold. sep auto.
Qed.

Lemma PhdrArray_app_merge: forall v11 v12 v21 v22 v31 v32 v41 v42 file p,
PhdrArray file p v11 v21 v31 v41 ** PhdrArray file (get_off_addr_repeat  (length v11) p ($size_of_Elf32_Phdr)) v12 v22 v32 v42 ==>
PhdrArray file p (v11++v12) (v21++v22) (v31++v32)(v41++v42).
Proof.
induction v11; intros.
+ simpl length in H. simpl get_off_addr_repeat in H. simpl app. 
  destruct v21; destruct v31; destruct v41;[idtac| simpl PhdrArray at 1 in H; apply astar_l_afalse_elim in H; inversion H..]. 
  simpl app. simpl PhdrArray at 1 in H. sep auto.
+ destruct v21; destruct v31; destruct v41;[simpl PhdrArray at 1 in H; apply astar_l_afalse_elim in H; inversion H..|idtac ]. 
  unfold PhdrArray at 1 in H. rewrite PhdrArray_fold in H.
  simpl app.  unfold PhdrArray at 1.  rewrite PhdrArray_fold.
  sep normal in H. sep autocancel.
  apply IHv11. 
  simpl length in H. simpl get_off_addr_repeat in H.
  assumption.  
Qed.

Lemma PhdrArray_app_split_frm: forall v11 v12 v21 v22 v31 v32 v41 v42 file p P,
length v11 = length v21 ->
length v11 = length v31 ->
length v11 = length v41 ->
length v12 = length v32 ->
length v12 = length v42 ->
length v12 = length v22 ->
PhdrArray file p (v11++v12) (v21++v22) (v31++v32)(v41++v42) ** P ==>
PhdrArray file p v11 v21 v31 v41 ** PhdrArray file (get_off_addr_repeat  (length v11) p ($size_of_Elf32_Phdr)) v12 v22 v32 v42 ** P.
Proof.
intros. sep autocancel. now apply PhdrArray_app_split.
Qed.

Lemma PhdrArray_app_merge_frm: forall v11 v12 v21 v22 v31 v32 v41 v42 file p P,
PhdrArray file p v11 v21 v31 v41 ** PhdrArray file (get_off_addr_repeat  (length v11) p ($size_of_Elf32_Phdr)) v12 v22 v32 v42 ** P ==>
PhdrArray file p (v11++v12) (v21++v22) (v31++v32)(v41++v42) ** P.
Proof.
  intros. sep autocancel. now apply PhdrArray_app_merge.
Qed.

Lemma PhdrArray_cons: forall file p vl filevl memvl dstvl vll filevll memvll dstvll,
  PhdrArray file p (vl::vll) (filevl::filevll) (memvl::memvll) (dstvl:: dstvll) =
  Astruct p os_ucos_h.Elf32_Phdr vl **
  [|struct_type_vallist_match os_ucos_h.Elf32_Phdr vl|] **
  PhdrSingle file vl filevl memvl dstvl **
  PhdrArray file (get_off_addr p ($ size_of_Elf32_Phdr)) vll filevll memvll dstvll.
Proof. reflexivity. Qed. 

(* Lemma AOSIPCGRinfo_aux_separate : 
forall n pl vl m,
  length pl = n -> length vl = n -> (m < n)%nat ->
  AOSIPCGRinfo_aux pl vl
  ==>
  EX p v pl1 pl2 vl1 vl2,
  [| pl = pl1 ++ (Vptr p) :: pl2 /\ vl = vl1 ++ (Vint32 v) :: vl2 /\
     length pl1 = m  /\ length vl1 = m |] **
  PV p @ Tint32 |-> (Vint32 v) ** 
  AOSIPCGRinfo_aux pl1 vl1 ** AOSIPCGRinfo_aux pl2 vl2.
Proof.
  induction n;intros.
  - inversion H1.
  - destruct m.
    + destruct pl as [  |p pl];tryfalse.
      destruct vl as [ |v vl];tryfalse.
      cbn [AOSIPCGRinfo_aux] in H2.
      destruct p as [ | | |p];tryfalse.
      destruct v as [ | |v| ];tryfalse.
      exists p v (@nil val) pl (@nil val) vl.
      sep auto.
    + destruct pl as [  |p pl];tryfalse.
      destruct vl as [ |v vl];tryfalse.
      cbn [AOSIPCGRinfo_aux] in H2.
      destruct p as [ | | |p];tryfalse.
      destruct v as [ | |v| ];tryfalse.
      apply lt_S_n in H1.
      simpl in H, H0.
      apply eq_add_S in H,H0.
      specialize (IHn pl vl m H H0 H1).
      eapply astar_mono with (P' := PV p @ Int32u |-> Vint32 v) in H2.
      2: auto.
      2: apply IHn.
      sep normal in H2.
      sep destruct H2.
      sep split in H2.
      destruct H3 as [ ? [? [? ?]]].
      exists x x0 ((Vptr p)::x1) x2 ((Vint32 v)::x3) x4.
      cbn [AOSIPCGRinfo_aux].
      sep auto.
      splits;simpl;auto.
Qed.

Lemma AOSIPCGRinfo_aux_separate_frm : 
forall n pl vl m P,
  length pl = n -> length vl = n -> (m < n)%nat ->
  AOSIPCGRinfo_aux pl vl ** P
  ==>
  EX p v pl1 pl2 vl1 vl2,
  [| pl = pl1 ++ (Vptr p) :: pl2 /\ vl = vl1 ++ (Vint32 v) :: vl2 /\
     length pl1 = m  /\ length vl1 = m |] **
  PV p @ Tint32 |-> (Vint32 v) ** 
  AOSIPCGRinfo_aux pl1 vl1 ** AOSIPCGRinfo_aux pl2 vl2 ** P.
Proof.
  intros.
  eapply astar_mono with (Q' :=P) in H2.
  2: { eapply AOSIPCGRinfo_aux_separate;eauto. }
  2: auto.
  sep auto.
Qed.

Lemma AOSIPCGRinfo_aux_merge : 
forall m pl1 vl1 n pl2 vl2 p v,
  length pl1 = m ->
  length vl1 = m ->
  length pl2 = n -> 
  length vl2 = n ->
  PV p @ Tint32 |-> (Vint32 v) ** 
  AOSIPCGRinfo_aux pl1 vl1 ** AOSIPCGRinfo_aux pl2 vl2 ==>
  AOSIPCGRinfo_aux (pl1 ++ (Vptr p) :: pl2) (vl1 ++ (Vint32 v) :: vl2).
Proof.
  induction m;intros.
  - destruct pl1;tryfalse. destruct vl1;tryfalse.
    simpl (nil ++ _).
    cbn [AOSIPCGRinfo_aux] in *.
    sep auto.
  - destruct pl1;tryfalse. destruct vl1;tryfalse.
    simpl ((_ :: _ ) ++ _).
    cbn [AOSIPCGRinfo_aux] in *.
    sep lift 2%nat in H3.
    destruct v0;afalse_tryfalse.
    destruct v1;afalse_tryfalse.
    sep normal in H3.
    simpl in H,H0.
    eapply eq_add_S in H,H0.
    specialize (IHm _ _ _ _ _ p v H H0 H1 H2).
    sep lifts (1::3::2::nil)%nat in H3.
    eapply astar_mono with (P' := PV a @ Int32u |-> Vint32 i) in H3.
    2: auto.
    2: apply IHm.
    sep auto.
Qed.

Lemma AOSIPCGRinfo_aux_merge_frm : 
forall m pl1 vl1 n pl2 vl2 p v P,
  length pl1 = m ->
  length vl1 = m ->
  length pl2 = n -> 
  length vl2 = n ->
  PV p @ Tint32 |-> (Vint32 v) ** 
  AOSIPCGRinfo_aux pl1 vl1 ** AOSIPCGRinfo_aux pl2 vl2 ** P ==>
  AOSIPCGRinfo_aux (pl1 ++ (Vptr p) :: pl2) (vl1 ++ (Vint32 v) :: vl2) ** P.
Proof.
  intros.
  sep lift 4%nat in H3.
  eapply astar_mono with (P' :=P) in H3.
  3: { eapply AOSIPCGRinfo_aux_merge;eauto. }
  2: auto.
  sep auto.
Qed. *)


Lemma fold_Memory_Node_dyn_refac_cfg: forall pb pi ni meml P,
  struct_type_vallist_match dyn_refac_cfg meml ->
  Astruct (pb,pi  +ᵢ(Int.mul ni ($ IPC_STEP))) 
  dyn_refac_cfg meml  ** P==>
  Memory_Node (Z.to_nat(Int.unsigned ni)) (pb,pi) meml ** P.
Proof.
  intros.
  unfold Memory_Node, Aarray, get_off_addr, fst, snd.
  erewrite Z2Nat.id ;[auto |apply Int.unsigned_range].
  erewrite Int.repr_unsigned.
  sep auto. unfold dyn_refac_cfg. simpl type_eq. sep auto.
Abort.

Lemma AdynrefaccfgFreeList_head_isptr: forall p l,
  AdynrefaccfgFreeList p l ==>
  AdynrefaccfgFreeList p l ** [|isptr p |].
Proof.
  intros. unfold AdynrefaccfgFreeList in *.
  sep lift 2%nat in H.
  apply sll_head_isptr in H as ?.
  sep auto.
Qed.

Lemma AdynrefaccfgFreeList_head_isptr_frm: forall p l P,
  AdynrefaccfgFreeList p l ** P ==>
  AdynrefaccfgFreeList p l ** [|isptr p |] ** P.
Proof.
  intros. sep cancel P.
  now apply AdynrefaccfgFreeList_head_isptr.
Qed.

Lemma AdynrefaccfgFreeList_cons: forall p l ,
  sll (Vptr p) l dyn_refac_cfg V_dyn_refac_cfg_Next ==>
  EX v vl newp, [| l=v::vl /\ V_dyn_refac_cfg_Next v =  Some newp /\ struct_type_vallist_match dyn_refac_cfg
       v |] ** Astruct p dyn_refac_cfg v ** sll newp vl dyn_refac_cfg V_dyn_refac_cfg_Next.
Proof.
  unfold sll.  intros. destruct l.
  +  simpl in H. destruct H. discriminate.
  + exists v l. unfold sllseg in H. sep split in H. sep destruct H.  sep split in H. 
     exists x. unfold sllseg.  sep cancel  2%nat 3%nat.  
     unfold node in H.  sep destruct H. sep split in H. destruct H2. injection H2 as ?. subst p. sep auto. 
Qed.

Lemma AdynrefaccfgFreeList_cons_frm: forall p l P,
  sll (Vptr p) l dyn_refac_cfg V_dyn_refac_cfg_Next ** P==>
  (EX v vl newp, [| l=v::vl /\ V_dyn_refac_cfg_Next v =  Some newp /\ struct_type_vallist_match dyn_refac_cfg
       v |] ** Astruct p dyn_refac_cfg v ** sll newp vl dyn_refac_cfg V_dyn_refac_cfg_Next) ** P.
Proof.
  intros. sep cancel P. now apply AdynrefaccfgFreeList_cons.
Qed.


Lemma AdynrefaccfgFreeList_null: forall  l ,
  sll Vnull l dyn_refac_cfg V_dyn_refac_cfg_Next ==>
  sll Vnull l dyn_refac_cfg V_dyn_refac_cfg_Next ** [| l = nil |].
Proof.
  unfold sll.  intros. destruct l.
  + sep auto. 
  + unfold sllseg in H. sep split in H. sep destruct H. unfold node in H. sep split in H. sep normal in H.
      sep destruct H. sep split in H. destruct H2. discriminate. 
Qed.

Lemma AdynrefaccfgFreeList_null_frm: forall  l P,
  sll Vnull l dyn_refac_cfg V_dyn_refac_cfg_Next ** P ==>
  sll Vnull l dyn_refac_cfg V_dyn_refac_cfg_Next ** [| l = nil |] ** P.
Proof.
  intros. sep cancel P. now apply AdynrefaccfgFreeList_null.
Qed.

Lemma sll_add:
 forall newp t structvl  headp sllvl V,
  struct_type_vallist_match t structvl ->
  V structvl = Some headp ->
  Astruct (newp, Int.zero) t structvl ** sll headp sllvl t V ==>
  sll (Vptr (newp, Int.zero)) (structvl::sllvl) t V.
Proof.
  intros. unfold sll in *. simpl sllseg.
  sep auto. 2: eauto. 
  unfold node.
  sep auto.
Qed.  

Lemma sll_add_frm:
 forall newp t structvl  headp sllvl V P,
  struct_type_vallist_match t structvl ->
  V structvl = Some headp ->
  Astruct (newp, Int.zero) t structvl ** sll headp sllvl t V ** P ==>
  sll (Vptr (newp, Int.zero)) (structvl::sllvl) t V ** P.
Proof.
  intros. sep cancel 3%nat 2%nat.
  eapply sll_add; eauto.
Qed.


Lemma AdynrefaccfgFreeList_merge:
 forall p l P,
  GV dynrefaccfgFreeList @ dyn_refac_cfg ∗ |-> p **
  sll p l dyn_refac_cfg V_dyn_refac_cfg_Next ** P ==>
  AdynrefaccfgFreeList p l ** P.
Proof.
  intros. sep auto. 
Qed.  

Lemma AOScoreheapt_app:
  forall l1 l2,
    AOScoreheapt (l1 ++ l2) <==>
    AOScoreheapt l1 ** AOScoreheapt l2.
Proof.
  induction l1; intros.
  - simpl app.
    simpl AOScoreheapt at 2.
    split; sep auto.
  - destruct a as [[? ?] ?].
    simpl AOScoreheapt at 1 2.
    split; sep auto;
    apply IHl1; auto.
Qed.


Lemma AOScoreheapt_app_frame:
  forall l1 l2 P,
    AOScoreheapt (l1 ++ l2) ** P <==>
    AOScoreheapt l1 ** AOScoreheapt l2 ** P.
Proof.
  intros.
  split;
  sep auto;
  apply AOScoreheapt_app; auto.
Qed.

Lemma Astruct_AOScoreheapt_addr_not_in: forall l s p t vl  P,
  simple_struct t ->
  s |= Astruct p t vl **  AOScoreheapt l ** P ->
  ~ In p (map (fun p => fst (fst p)) l).
Proof.
  induction l; intros.
  + tauto.
  + destruct a. destruct p0. 
      simpl AOScoreheapt in H0.
      sep normal in H0.
      sep split in H0.
      destruct H1.
      unfold simple_struct in *.
      destruct t; auto. destruct d; auto.
      destruct t0; auto. destruct d0; auto.
      apply astruct_neq_ptr in H0 as ?; auto.
      simpl. unfold not. intros.
      destruct H4. congruence.  
      sep lift 3%nat in H0. sep lift 2%nat in H0. 
      eapply IHl in H0; eauto. 
Qed.
     

Lemma AOScoreheapt_addr_nodup: forall  s l P,
  s |= AOScoreheapt l ** P ->
  NoDup (map (fun p => fst (fst p)) l).
Proof.
  induction l; intros.
  + constructor.
  + destruct a. destruct p.
     simpl AOScoreheapt in H.
     simpl. sep split in H.
     destruct H0.
     constructor.
     - eapply Astruct_AOScoreheapt_addr_not_in; eauto. 
     - eapply IHl;eauto. sep name lift AOScoreheapt in H. eauto.
Qed.

Lemma Coreheapt_remove_nothing: forall p l,
  ~ In p (map (fun p : addrval * type * list val => fst (fst p)) l) ->
  Coreheapt_remove p l = l.
Proof.
  induction l; intros.
  + easy.
  + destruct a. destruct p0. simpl. simpl in H. destruct (addrval_eq_dec p a) eqn:E.
    - destruct H. now left.
    - assert (Coreheapt_remove p l = l) by tauto. now rewrite H0.
Qed.

Lemma set_Coreheapt_nothing: forall p vl l,
  ~ In p (map (fun p : addrval * type * list val => fst (fst p)) l) ->
  set_Coreheapt p vl l = l.
Proof.
  induction l; intros.
  + easy.
  + destruct a. destruct p0. simpl. simpl in H. destruct (addrval_eq_dec p a) eqn:E.
    - destruct H. now left.
    - assert (set_Coreheapt p vl l = l) by tauto. now rewrite H0.
Qed.

Lemma Coreheapt_remove_middle: forall p t vl l1 l2,
  NoDup (map (fun p => fst (fst p)) (l1++(p,t,vl)::l2)) ->
  Coreheapt_remove p (l1++(p,t,vl)::l2) = l1++l2.
Proof.
  induction l1; intros.
  + simpl. simpl in H. inverts H. 
    destruct (addrval_eq_dec p p); tryfalse.
    now apply Coreheapt_remove_nothing.
  + destruct a. destruct p0. simpl in *. inverts H.
    destruct (addrval_eq_dec p a) eqn:E.
    - subst. exfalso. apply H2. rewrite map_app. 
      simpl. apply in_or_app. right. now left.  
    - f_equal. eauto.
Qed.

Lemma In_heapt_addrval_split_Pure:
  forall coreheapt l t,
  In_heapt_addrval coreheapt l t  ->
  forall P,
  AOScoreheapt coreheapt ** P
  ==>
  EX l1 l2 vl,
  [| coreheapt = l1 ++ (l, t,vl) :: l2  |] **
  [|struct_type_vallist_match t vl /\ simple_struct t |]**
  AOScoreheapt coreheapt ** P.
Proof.
  intros.  unfold In_heapt_addrval in H.
  destruct H as  [vl ?].
  apply in_split in H as [l1 [l2 ?]].
  subst.
  exists l1 l2  vl. 
  apply AOScoreheapt_app_frame in H0 as H1.
  sep lift 2%nat in H1. 
  simpl AOScoreheapt in H1. sep normal in H1.
  sep auto.
  rewrite AOScoreheapt_app. simpl AOScoreheapt at 2.
  sep auto.
Qed.

 
Lemma In_heapt_addrval_split:
  forall coreheapt l t P,
  In_heapt_addrval coreheapt l t  ->
  AOScoreheapt coreheapt ** P
  ==>
  EX vl,
  [|struct_type_vallist_match t vl /\ simple_struct t|]**
  [| Get_heapt_addrval coreheapt l t vl|]**
  Astruct l t vl ** AOScoreheapt (Coreheapt_remove l coreheapt) ** P.
Proof.
  intros. eapply In_heapt_addrval_split_Pure in H0; eauto.
  sep destruct H0. sep split in H0.
  destruct H2. exists x1.
  sep auto.
  - assert (s|=AOScoreheapt (x++ (l,t,x1)::x0) ** Atrue) by sep auto.
    apply AOScoreheapt_addr_nodup in H1.
    rewrite Coreheapt_remove_middle; auto.
    apply AOScoreheapt_app in H0.
    sep lift 2%nat.
    apply AOScoreheapt_app_frame.
    unfold AOScoreheapt at 2 in H0.
    sep auto.
  - hnf. do 2 eexists. splits; eauto.
    apply in_or_app. right. now left.
Qed.

Lemma split_coreheapt_middle:
  forall l1 l2 l t vl P,
  AOScoreheapt (l1 ++ (l, t, vl) :: l2) ** P
  <==>
  AOScoreheapt (l1 ++ l2) **
  Astruct l t vl **
  (* required when rebuilding the entire cheapt *)
  [| struct_type_vallist_match t vl /\ simple_struct t|] ** P.
Proof.
  split; intros.
  + sep autocancel.
    apply AOScoreheapt_app in H.
    simpl AOScoreheapt at 2 in H.
    apply AOScoreheapt_app_frame.
    sep auto.
  + apply AOScoreheapt_app_frame.
    simpl AOScoreheapt.
    apply AOScoreheapt_app_frame in H. 
    sep auto.
Qed.

Lemma AOScoreheapt_struct_type_vallist_match:
  forall cheapt l t vl,
    In (l, t, vl) cheapt ->
    AOScoreheapt cheapt ==>
    [|struct_type_vallist_match t vl /\ simple_struct t|] ** AOScoreheapt cheapt.
Proof.
  intros.
  apply in_split in H as [l1 [l2 ?]]; subst.
  apply AOScoreheapt_app in H0.
  simpl AOScoreheapt at 2 in H0.
  sep lift 2%nat in H0.
  sep split in H0.
  destruct H.
  sep auto.
  assert (s |=  AOScoreheapt (l1++(l,t,vl)::l2) ** Aemp).
  {
    apply split_coreheapt_middle. sep auto.
    now apply AOScoreheapt_app.
  }
  clear H0.
  sep auto. 
Qed. 


 Lemma AOScoreheapt_struct_type_vallist_match_frm:
  forall cheapt l t vl P,
    In (l, t, vl) cheapt ->
    AOScoreheapt cheapt ** P ==>
    [|struct_type_vallist_match t vl /\ simple_struct t|] **  AOScoreheapt cheapt ** P.
Proof.
  intros.
  sep cancel P.
  eapply AOScoreheapt_struct_type_vallist_match;eauto.
Qed. 

Lemma AOScoreheapt_Get_heapt_addrval:
  forall cheapt l  t vl P,
    In (l,t, vl) cheapt ->
    AOScoreheapt cheapt ** P ==>
    [|Get_heapt_addrval cheapt l t vl|] ** AOScoreheapt cheapt ** P.
Proof.
  intros. sep auto.
  unfold Get_heapt_addrval.
  eauto.
Qed.

 Lemma AOScoreheapt_merge : forall l t vl cheapt1 cheapt2 P, 
 simple_struct t ->
 struct_type_vallist_match t vl ->
 Astruct l t vl **
 AOScoreheapt (cheapt1 ++ cheapt2)  ** P ==>
 AOScoreheapt (cheapt1 ++ (l, t, vl)::cheapt2) ** P.
Proof.
  intros.
  apply split_coreheapt_middle.
  sep auto.
Qed.

Lemma Get_heapt_addrval_impl_In_heapt_addrval: forall cheapt l t vl,
  Get_heapt_addrval cheapt l t vl ->
  In_heapt_addrval cheapt l t.
Proof.
  induction cheapt; intros.
  + inverts H. destruct H0. inversion H. tauto.
  + unfold Get_heapt_addrval in H. unfold In_heapt_addrval.
      destruct H as [? [? []]]; eauto. destruct H0. subst. eauto.
Qed.

Lemma Nodup_Get_Heapt_addrval_cons: forall l t1 t2 vl1 vl2 cheapt,
  NoDup (map (fun p => fst (fst p)) ((l,t1,vl1)::cheapt)) ->
  Get_heapt_addrval ((l,t1,vl1)::cheapt) l t2 vl2 ->
  t1 = t2 /\ vl1 = vl2.
Proof.
  induction cheapt; intros.
  + inverts H0. destruct H1. destruct H0. inverts H0.
    inverts H2. destruct H1. split; congruence. inverts H2.
  + destruct a. destruct p. simpl in H.
    inverts H. 
    unfold Get_heapt_addrval in H0.
    destruct H0 as (?&?&?&?&?).
    simpl in H. destruct H.
    - inverts H. subst. tauto. 
    - inverts H4. apply IHcheapt.
      simpl. constructor; auto.
      unfold not. intros. apply H3.
      now right.
      destruct H.
      inverts H. subst.
      exfalso. apply H3. now left.
      hnf. exists x x0.
      split.
      now right.
      subst. tauto.
Qed.


Lemma AOScoreheapt_Get_heapt_addrval_injective:
forall cheapt l t1 t2 vl1 vl2 s P,
 s |= AOScoreheapt cheapt ** P ->
 Get_heapt_addrval cheapt l t1 vl1 ->
 Get_heapt_addrval cheapt l t2 vl2 ->
 t1 = t2 /\ vl1 = vl2. 
Proof.
  intros. apply AOScoreheapt_addr_nodup in H.
  revert H H0 H1.
  induction cheapt; intros.
  + inverts H0. destruct H2. destruct H0. inverts H0.
  + destruct a. destruct p.
    destruct (addrval_eq_dec a l).
    - subst. apply Nodup_Get_Heapt_addrval_cons in H1; auto.
      apply Nodup_Get_Heapt_addrval_cons in H0; auto.
      destruct H1. destruct H0. split; congruence.
    - apply IHcheapt.
      simpl in H. now inverts H.
      hnf in H0. destruct H0 as (?&?&?&?&?).
      simpl in H0. destruct H0. inverts H0. congruence.
      hnf. eauto.
      destruct H1 as (?&?&?&?&?).
      simpl in H1. destruct H1. inverts H1. congruence.
      hnf. eauto.
Qed. 

Lemma AOScoreheapt_remove_merge: forall l t vlold vlnew cheapt P, 
  NoDup (map (fun p => (fst (fst p))) cheapt) ->
  Get_heapt_addrval cheapt l t vlold ->
  simple_struct t ->
  struct_type_vallist_match t vlnew ->
  Astruct l t vlnew **
  AOScoreheapt (Coreheapt_remove l cheapt)  ** P ==>  
  AOScoreheapt (set_Coreheapt l vlnew cheapt) ** P.
Proof.
  induction cheapt; intros.
  + inverts H0. inverts H4. destruct H0. inverts H0.
  + destruct a. destruct p.
    simpl set_Coreheapt. simpl Coreheapt_remove in H2.
    destruct (addrval_eq_dec l a) eqn:E.
    - subst. simpl AOScoreheapt.
      apply Nodup_Get_Heapt_addrval_cons in H0; auto.
      destruct H0. subst. sep normal.  
      sep auto.
      simpl Coreheapt_remove in H3.
      destruct (addrval_eq_dec a a); try congruence.
      simpl in H. inverts H.
      rewrite Coreheapt_remove_nothing in H3; auto.
      rewrite set_Coreheapt_nothing; auto.
    - assert (Get_heapt_addrval cheapt l t vlold).
      {
        hnf in H0. destruct H0 as (?&?&?&?&?).
        destruct H0. inverts H0. congruence.
        subst. hnf. eauto.
      }
      clear H0.
      simpl Coreheapt_remove in H3.
      rewrite E in H3.
      simpl AOScoreheapt.
      simpl AOScoreheapt in H3.
      sep auto.
      assert (s |= AOScoreheapt (set_Coreheapt l vlnew cheapt) ** Aemp).
      {
        apply IHcheapt; auto. now inverts H. sep auto.
      }
      sep auto.
Qed.

Lemma set_Coreheapt_nochange: forall p t vl l,
  NoDup (map (fun p => fst (fst p)) l) ->
  Get_heapt_addrval l p t vl ->
  set_Coreheapt p vl l = l.
Proof.
  induction l; intros.
  + easy.
  + destruct a. destruct p0. simpl. simpl in H. destruct (addrval_eq_dec p a) eqn:E.
    - subst. apply Nodup_Get_Heapt_addrval_cons in H0. destruct H0. subst. 
      f_equal. apply set_Coreheapt_nothing.
      now inverts H. now simpl.  
    - assert (Get_heapt_addrval l p t vl).
      {
        hnf in H0. destruct H0 as (?&?&?&?&?).
        destruct H0. inverts H0. congruence.
        hnf. eauto.
      }
      f_equal. apply IHl; auto.
      now inverts H.
Qed.

Lemma AOScoreheapt_remove_merge_nochange: forall l t vl cheapt P, 
  NoDup (map (fun p => (fst (fst p))) cheapt) ->
  simple_struct t ->
  struct_type_vallist_match t vl ->
  Get_heapt_addrval cheapt l t vl ->
  Astruct l t vl **
  AOScoreheapt (Coreheapt_remove l cheapt)  ** P ==>  
  AOScoreheapt cheapt ** P.
Proof.
  intros.
  eapply AOScoreheapt_remove_merge in H3; eauto.
  erewrite set_Coreheapt_nochange in H3; eauto.
Qed.


Lemma Aarray_merge: forall m n l t vl1 vl2 P,
  (Z.of_nat (m + n) <= Int.max_unsigned)%Z ->
  length vl1 = m -> 
  length vl2 = n -> 
  Aarray l (Tarray t m) vl1 ** Aarray (get_off_addr l (Int.mul ($ Z.of_nat m)($ Z.of_nat (typelen t)))) (Tarray t n) vl2 ** P ==>
  Aarray l (Tarray t (m+n)) (vl1++vl2) ** P.
Proof.
  unfold Aarray.
  induction m; intros.
  + destruct vl1; inverts H0. simpl Aarray' in *.
    rewrite Int.mul_commut in H2. 
    rewrite Int.mul_zero in H2.
    unfold get_off_addr in H2. 
    rewrite Int.add_zero in H2.
    destruct l. 
    simpl fst in H2. simpl snd in H2.
    sep auto.
  + destruct vl1; inverts H0. destruct l. cbn [Aarray'] in *.  simpl Aarray'.
    sep normal. sep autocancel.
    specialize IHm with (n:=n) (l:=(b, i +ᵢ  $ Z.of_nat (typelen t))) (t:=t)  (vl1:=vl1) (vl2:=vl2)(P:=P).
    apply IHm; auto. lia.
    assert (Z.of_nat (S (length vl1)) = (Z.of_nat (length vl1) + 1)%Z) by lia.
    rewrite H0 in H2.   
    assert (Int.repr (Z.of_nat (length vl1) +1) = Int.add Int.one (Int.repr (Z.of_nat (length vl1))) ).
    {
      rewrite Int.add_unsigned.
      f_equal.
      rewrite Z.add_comm.
      f_equal.
      rewrite Int.unsigned_repr.
      auto.
      clear - H. lia.
    }
    rewrite H3 in H2. clear H0 H3.
    rewrite Int.mul_commut in H2.
    rewrite Int.mul_add_distr_r in H2.
    rewrite Int.mul_one in H2.
    unfold get_off_addr in *.
    simpl fst in *. simpl snd in *.
    rewrite Int.add_assoc.
    rewrite Int.mul_commut.
    assumption.
Qed.

Lemma Aarray_merge_single: forall m n l t vl P,
  (Z.of_nat n <= Int.max_unsigned)%Z ->
  (m <= n)%nat ->
  length vl = n ->
  Aarray l (Tarray t m) (firstn m vl) ** Aarray (get_off_addr l (Int.mul ($ Z.of_nat m)($ Z.of_nat (typelen t)))) (Tarray t (n-m)) (skipn m vl) ** P ==>
  Aarray l (Tarray t n) vl ** P.
Proof.
  intros.
  pose proof Aarray_merge m (n-m) l t (firstn m vl) (skipn m vl) P.
  assert (m + (n - m) = n)%nat by lia.
  rewrite H4 in *. clear H4.
  assert (firstn m vl ++ skipn m vl = vl) by now rewrite firstn_skipn.
  rewrite H4 in H3. clear H4.
  apply H3; auto.
  rewrite firstn_length_le; auto. lia.
  rewrite skipn_length. lia.
Qed.


Lemma Aarray_split: forall m n l t vl1 vl2 P,
  (Z.of_nat (m + n) <= Int.max_unsigned)%Z ->
  length vl1 = m -> 
  length vl2 = n -> 
  Aarray l (Tarray t (m+n)) (vl1++vl2) ** P ==>
  Aarray l (Tarray t m) vl1 ** Aarray (get_off_addr l (Int.mul ($ Z.of_nat m)($ Z.of_nat (typelen t)))) (Tarray t n) vl2 ** P.
Proof.
  unfold Aarray.
  induction m; intros.
  + destruct vl1; inverts H0. simpl Aarray' in *.
    rewrite Int.mul_commut. 
    rewrite Int.mul_zero.
    unfold get_off_addr. 
    rewrite Int.add_zero.
    destruct l. 
    simpl fst. simpl snd.
    sep auto.
  + destruct vl1; inverts H0. destruct l. cbn [Aarray'] in *.  simpl Aarray' in H2.
    sep normal in H2. sep normal. sep cancel v.
    specialize IHm with (n:=n) (l:=(b, i +ᵢ  $ Z.of_nat (typelen t))) (t:=t)  (vl1:=vl1) (vl2:=vl2)(P:=P).
    assert (Z.of_nat (S (length vl1)) = (Z.of_nat (length vl1) + 1)%Z) by lia.
    rewrite H0.   
    assert (Int.repr (Z.of_nat (length vl1) +1) = Int.add Int.one (Int.repr (Z.of_nat (length vl1))) ).
    {
      rewrite Int.add_unsigned.
      f_equal.
      rewrite Z.add_comm.
      f_equal.
      rewrite Int.unsigned_repr.
      auto.
      clear - H. lia.
    }
    rewrite H3. clear H0 H3.
    rewrite Int.mul_commut.
    rewrite Int.mul_add_distr_r.
    rewrite Int.mul_one.
    unfold get_off_addr in *.
    simpl fst in *. simpl snd in *.
    rewrite Int.add_assoc in IHm.
    rewrite Int.mul_commut in IHm.
    apply IHm; auto.
    lia.
Qed.
      
Lemma Aarray_split_single: forall m n l t vl P,
  (Z.of_nat n <= Int.max_unsigned)%Z ->
  (m <= n)%nat ->
  length vl = n ->
  Aarray l (Tarray t n) vl ** P ==>
  Aarray l (Tarray t m) (firstn m vl) ** Aarray (get_off_addr l (Int.mul ($ Z.of_nat m)($ Z.of_nat (typelen t)))) (Tarray t (n-m)) (skipn m vl) ** P.
Proof.
  intros.
  pose proof Aarray_split m (n-m) l t (firstn m vl) (skipn m vl) P.
  assert (m + (n - m) = n)%nat by lia.
  rewrite H4 in *. clear H4.
  assert (firstn m vl ++ skipn m vl = vl) by now rewrite firstn_skipn.
  rewrite H4 in H3. clear H4.
  apply H3; auto.
  rewrite firstn_length_le; auto. lia.
  rewrite skipn_length. lia.
Qed.