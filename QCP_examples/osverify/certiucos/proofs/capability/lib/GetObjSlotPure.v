Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import include_frm.
Require Import sep_auto.
Require Import CapPure.
Require Import math_auto.
Require Import ACSpace_defs.
Require Import Lia.
Require Import CapSpec.

Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Lemma GAarray_unfold:
  forall x t l vl s p,
  s |= G& x @ t == l ** Aarray l t vl ** p
  -> s |= GAarray x t vl ** p.
Proof.
  intros.
  unfold GAarray.
  sep cancel p.
  exists l. auto.
Qed.





Lemma Ais_true_x_y:
forall s x y i j p,
Z.of_nat x < 255 ->
s |= LV i @ long |-> (V$ Z.of_nat x) ** LV j @ long |-> Vint32 y ** p 
-> s |= Aistrue (j ′ >ₑ i ′) 
->(S x <= Z.to_nat (Int.unsigned y))%nat.  
Proof.
    introv Hx.
    intros.
    destruct_s s. 
    destruct H. simpljoin.
    simpl in H1, H3, H4. simpljoin1.
    destruct H5. simpljoin.
    simpl in H2, H4, H5. simpljoin1.
    simpl in H0. destruct H0.
    rewrite H7, H10 in H. 
    unfold cmp_int_type in H. 
    apply mapstoval_load in H8, H11.
    lets Hloadx0: load_local H1 H8.
    lets Hloadx2': load_local H2 H11.
    apply map_join_comm in H1.
    lets Hloadx2: load_local H1 Hloadx2'.
    rewrite Int.unsigned_zero in Hloadx0, Hloadx2.
    rewrite Hloadx0 in H. rewrite Hloadx2 in H. 
    destruct H. unfold istrue in H0. 
    destruct x4; simpl in H0; tryfalse.
    destruct (Int.eq i4 Int.zero) eqn: Heqn.
    tryfalse.
    2:{
    unfold cmp_val in H. 
    destruct(cmpu Clt ($ Z.of_nat x) y); tryfalse.
    }
    2: simpl; auto.
    2: simpl; auto. 
    unfold cmp_val in H. 
    destruct (cmpu Clt ($ Z.of_nat x) y) eqn: Hcmpu.
    unfold cmpu in Hcmpu. 
    apply Int.ltu_inv in Hcmpu.
    destruct Hcmpu. 
    rewrite Int.unsigned_repr in H4.
    assert(Int.unsigned y = Z.of_nat(Z.to_nat(Int.unsigned y))).
    rewrite of_to_nat_unsignedv'. auto.
    rewrite H5 in H4.
    apply Nat2Z.inj_lt in H4.
    lia. rewrite max_unsigned_val.
    lia.
    inverts H. tryfalse.
Qed.

Lemma list_5_assoc:
      forall l1 l2 l3 l4 l5: list (int32 * (int32 * cap_content_type)),
        l1 ++ l2 ++ l3 ++ l4 ++ l5 = l1 ++ (l2 ++ l3 ++ l4) ++ l5.
      Proof.
        intros.
        rewrite app_assoc_reverse.
        rewrite app_assoc_reverse. auto.
      Qed.

Lemma Slots_neq_object_nil: 
forall v,
    Slots_neq_object nil v.
    Proof.
    unfold Slots_neq_object.
    simpl.
    auto with zarith.
Qed.
Lemma Slots_neq_object_succ:
forall a vl v,
Slots_neq_object (a::vl) v <-> (Slots_neq_object (a::nil) v /\ Slots_neq_object vl v).
Proof.
    unfold Slots_neq_object.
    split; intros.
    simpl in *.
    split; intros.
    eapply H. instantiate(1:=idx). int auto.
    assert(idx = 0). lia. 
    rewrite H3 in H1. rewrite H3.
    simpl in H1. simpl. inverts H1. eauto.
    eauto.
    eapply H. instantiate(1:=idx+1). int auto.  
    assert(Z.to_nat(idx+1) = S(Z.to_nat idx)). lia. 
    rewrite H3. simpl. rewrite H1. eauto.
    eauto. 
    destruct H. 
    destruct H0. 
    assert (Hi: idx= 0 \/ idx <> 0) by tauto.
    destruct Hi.
    eapply H.  simpl in *. eauto with zarith. 
    subst idx. simpl in H1. simpl. eauto.
    eauto. 
    eapply H3. instantiate(1:=idx-1). simpl in H4. lia. 
    assert(idx = idx - 1 + 1).
    rewrite Z.sub_add. auto.
    rewrite H6 in H1.
    assert(Z.to_nat (idx - 1 + 1) = (Z.to_nat (idx - 1) + 1)%nat).
    eapply nat_of_Z_plus; auto with zarith.
    rewrite Nat.add_1_r in H7. 
    rewrite H7 in H1.
    simpl in H1. rewrite H1.
    eauto. eauto.
Qed.
Lemma Slots_neq_object_split: 
forall l1 l2 v,
(Slots_neq_object l1 v /\ Slots_neq_object l2 v) 
<-> Slots_neq_object (l1++l2) v.
Proof.
    induction l1; intros.
    simpl. splits; try pure_auto.
    eapply Slots_neq_object_nil.
    simpl. 
    rewrite Slots_neq_object_succ. 
    rewrite Slots_neq_object_succ with (vl:= l1 ++ l2).
    rewrite <- IHl1.
    tauto.
Qed.

Ltac val_help H:=
    try change (Int.ltu Int.zero Int.zero) with (false) in H;
    try change (Int.ltu Int.one Int.zero) with (false) in H;
    try change (Int.ltu Int.zero Int.one) with (true) in H;
    try change (Int.ltu Int.one Int.one) with (false) in H;
    try change (Int.eq Int.one Int.one) with (true) in H;
    try change (Int.eq Int.one Int.zero) with (false) in H;
    try change (Int.eq Int.zero Int.one) with (false) in H;
    try change (Int.eq Int.zero Int.zero) with (true) in H.

Lemma val_if_true:
forall i, 
    val_inj
    (bool_and
    (val_inj
        (bool_or
            (val_inj
                (if Int.ltu ($ OS_LOWEST_PRIO) i
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))
            (val_inj
                (if Int.eq i ($ OS_LOWEST_PRIO)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))))
    (val_inj
        (notint
            (val_inj
                (if Int.eq i ($ OS_PRIO_SELF)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))))) <>
    Vint32 Int.zero /\
    val_inj
    (bool_and
    (val_inj
        (bool_or
            (val_inj
                (if Int.ltu ($ OS_LOWEST_PRIO) i
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))
            (val_inj
                (if Int.eq i ($ OS_LOWEST_PRIO)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))))
    (val_inj
        (notint
            (val_inj
                (if Int.eq i ($ OS_PRIO_SELF)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))))) <>
    Vnull /\
    val_inj
    (bool_and
    (val_inj
        (bool_or
            (val_inj
                (if Int.ltu ($ OS_LOWEST_PRIO) i
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))
            (val_inj
                (if Int.eq i ($ OS_LOWEST_PRIO)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))))
    (val_inj
        (notint
            (val_inj
                (if Int.eq i ($ OS_PRIO_SELF)
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))))) <>
    Vundef ->
    Int.unsigned i >= OS_LOWEST_PRIO /\
    Int.unsigned i <> OS_PRIO_SELF.
Proof.

    intros.
    split;
    destruct (Int.ltu ($ OS_LOWEST_PRIO) i) eqn: He1;
    destruct (Int.eq i ($ OS_LOWEST_PRIO)) eqn: He2;
    destruct (Int.eq i ($ OS_PRIO_SELF)) eqn: He3.
    rewrite Intlt_true_is_Zlt in He1.
    clear -He1. rewrite Int.unsigned_repr in He1. lia.
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    rewrite Intlt_true_is_Zlt in He1.
    clear -He1. rewrite Int.unsigned_repr in He1. lia.
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    rewrite Intlt_true_is_Zlt in He1.
    clear -He1. rewrite Int.unsigned_repr in He1. lia.
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    rewrite Intlt_true_is_Zlt in He1.
    clear -He1. rewrite Int.unsigned_repr in He1. lia.
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    pure_auto.
    rewrite Inteq_true_is_Zeq in He2. 
    rewrite Int.unsigned_repr in He2. lia.
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    simpl in H. 
    val_help H. simpl in H. val_help H. 
    simpl in H. destruct H. tryfalse.
    simpl in H. 
    val_help H. simpl in H. val_help H. 
    simpl in H. destruct H. tryfalse.

    simpl in H. 
    val_help H. simpl in H. val_help H. 
    simpl in H. unfold Int.notbool in H. 
    val_help H. simpl in H. val_help H. simpl in H. 
    destruct H. tryfalse.
    eapply Inteq_false_is_Zneq in He3. 
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia.
    simpl in H. 
    val_help H. simpl in H. val_help H. 
    simpl in H. unfold Int.notbool in H. 
    val_help H. simpl in H. val_help H. simpl in H. 
    destruct H. tryfalse.
    eapply Inteq_false_is_Zneq in He3. 
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia.
    simpl in H. 
    val_help H. simpl in H. val_help H. 
    simpl in H. unfold Int.notbool in H. 
    val_help H. simpl in H. val_help H. simpl in H. 
    destruct H. tryfalse.
    eapply Inteq_false_is_Zneq in He3. 
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia.
    simpl in H. 
    val_help H. simpl in H. val_help H. 
    simpl in H. unfold Int.notbool in H. 
    val_help H. simpl in H. val_help H. simpl in H. 
    destruct H. tryfalse.
    eapply Inteq_false_is_Zneq in He3. 
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia.
Qed.

Lemma val_if_false: 
    forall v'2, 
    val_inj
       (bool_and
          (val_inj
             (bool_or
                (val_inj
                   (if Int.ltu ($ OS_LOWEST_PRIO) v'2
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))
                (val_inj
                   (if Int.eq v'2 ($ OS_LOWEST_PRIO)
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))))
          (val_inj
             (notint
                (val_inj
                   (if Int.eq v'2 ($ OS_PRIO_SELF)
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))))) =
     Vint32 Int.zero \/
     val_inj
       (bool_and
          (val_inj
             (bool_or
                (val_inj
                   (if Int.ltu ($ OS_LOWEST_PRIO) v'2
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))
                (val_inj
                   (if Int.eq v'2 ($ OS_LOWEST_PRIO)
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))))
          (val_inj
             (notint
                (val_inj
                   (if Int.eq v'2 ($ OS_PRIO_SELF)
                    then Some (Vint32 Int.one)
                    else Some (Vint32 Int.zero)))))) =
     Vnull ->
     Int.unsigned v'2 < OS_LOWEST_PRIO \/
     Int.unsigned v'2 = OS_PRIO_SELF.
Proof.
    intros.
    destruct (Int.ltu ($ OS_LOWEST_PRIO) v'2) eqn: He1;
    destruct (Int.eq v'2 ($ OS_LOWEST_PRIO)) eqn: He2;
    destruct (Int.eq v'2 ($ OS_PRIO_SELF)) eqn: He3.
    rewrite Inteq_true_is_Zeq in He3. right.
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia. 

    simpl in H. 
    val_help H.  simpl in H. val_help H. simpl in H. 
    unfold Int.notbool in H. val_help H. 
    simpl in H. val_help H. simpl in H. destruct H; tryfalse.

    rewrite Inteq_true_is_Zeq in He3. right.
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia. 

    simpl in H. 
    val_help H.  simpl in H. val_help H. simpl in H. 
    unfold Int.notbool in H. val_help H. 
    simpl in H. val_help H. simpl in H. destruct H; tryfalse.

    rewrite Inteq_true_is_Zeq in He3. right.
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia. 

    simpl in H. 
    val_help H.  simpl in H. val_help H. simpl in H. 
    unfold Int.notbool in H. val_help H. 
    simpl in H. val_help H. simpl in H. destruct H; tryfalse.

    rewrite Inteq_true_is_Zeq in He3. right.
    rewrite Int.unsigned_repr in He3. auto.
    unfold OS_PRIO_SELF. rewrite max_unsigned_val. lia. 

    rewrite Intlt_false_is_Zge in He1. 
    rewrite Int.unsigned_repr in He1. rewrite Inteq_false_is_Zneq in He2.
    rewrite Int.unsigned_repr in He2.
    clear -He1 He2. 
    left.  lia. 
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia. 
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia. 
Qed.
