Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import ACSpace_defs.
Require Import CapSpec.
Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import Lia.
Require Import sem_lab. 
Require Import CapPure.
Set Keyed Unification.
Ltac val_help H:=
    simpl in H;
    try change (Int.ltu Int.zero Int.zero) with (false) in H;
    try change (Int.ltu Int.one Int.zero) with (false) in H;
    try change (Int.ltu Int.zero Int.one) with (true) in H;
    try change (Int.ltu Int.one Int.one) with (false) in H;
    try change (Int.eq Int.one Int.one) with (true) in H;
    try change (Int.eq Int.one Int.zero) with (false) in H;
    try change (Int.eq Int.zero Int.one) with (false) in H;
    try change (Int.eq Int.zero Int.zero) with (true) in H.



Lemma if_condition_imply: 
forall i16 v'48 x3,
val_inj
        (bop_eval
           (val_inj
              (bop_eval (V$ 1)
                 (Vint32 Int.zero) char_t
                 long oeq))
           (val_inj
              (bop_eval
                 (val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                            (val_inj
                            (bop_eval
                            (Vint32 i16)
                            (V$ CNODE_GRANT_CAP)
                            long long
                            obitand))
                            (V$ 0) long
                            long oeq))
                       oppsite))
                 (val_inj
                    (val_eq (Vint32 x3)
                       (Vint32 v'48))) long
                 long oand)) long long oor) <>
      Vint32 Int.zero /\
      val_inj
        (bop_eval
           (val_inj
              (bop_eval (V$ 1)
                 (Vint32 Int.zero) char_t
                 long oeq))
           (val_inj
              (bop_eval
                 (val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                            (val_inj
                            (bop_eval
                            (Vint32 i16)
                            (V$ CNODE_GRANT_CAP)
                            long long
                            obitand))
                            (V$ 0) long
                            long oeq))
                       oppsite))
                 (val_inj
                    (val_eq (Vint32 x3)
                       (Vint32 v'48))) long
                 long oand)) long long oor) <>
      Vnull /\
      val_inj
        (bop_eval
           (val_inj
              (bop_eval (V$ 1)
                 (Vint32 Int.zero) char_t
                 long oeq))
           (val_inj
              (bop_eval
                 (val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                            (val_inj
                            (bop_eval
                            (Vint32 i16)
                            (V$ CNODE_GRANT_CAP)
                            long long
                            obitand))
                            (V$ 0) long
                            long oeq))
                       oppsite))
                 (val_inj
                    (val_eq (Vint32 x3)
                       (Vint32 v'48))) long
                 long oand)) long long oor) <>
      Vundef ->Int.eq
      (i16&ᵢ
        $ CNODE_GRANT_CAP)
      ($ 0) = false /\ Int.eq v'48 x3 = true.
Proof.
  intros.
  destruct H.
  clear -H.
  unfold val_inj, bop_eval, val_eq in H.
  assert(Int.eq ($1) (Int.zero) = false).
  int auto.
  unfold and in H.
  rewrite H0 in H.
  unfold bool_or, bool_and, uop_eval, notint, Int.notbool in H.
  destruct (Int.eq(i16&ᵢ$ CNODE_GRANT_CAP)
  ($ 0)) eqn: Ha;
  destruct (Int.eq x3 v'48) eqn: Hb; repeat val_help H; tryfalse.
  split; auto.
  rewrite Int.eq_sym. auto.
Qed.

Lemma if_condition_imply_false: 
  forall i16 x3 i6,
  val_inj
        (bop_eval
           (val_inj
              (bop_eval (V$ 1)
                 (Vint32 Int.zero) char_t long
                 oeq))
           (val_inj
              (bop_eval
                 (val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                             (val_inj
                              (bop_eval
                              (Vint32 i16)
                              (V$ CNODE_GRANT_CAP)
                              long long
                              obitand)) 
                             (V$ 0) long long
                             oeq)) oppsite))
                 (val_inj
                    (val_eq (Vint32 x3)
                       (Vint32 i6))) long long
                 oand)) long long oor) =
      Vint32 Int.zero \/
      val_inj
        (bop_eval
           (val_inj
              (bop_eval (V$ 1)
                 (Vint32 Int.zero) char_t long
                 oeq))
           (val_inj
              (bop_eval
                 (val_inj
                    (uop_eval
                       (val_inj
                          (bop_eval
                             (val_inj
                              (bop_eval
                              (Vint32 i16)
                              (V$ CNODE_GRANT_CAP)
                              long long
                              obitand)) 
                             (V$ 0) long long
                             oeq)) oppsite))
                 (val_inj
                    (val_eq (Vint32 x3)
                       (Vint32 i6))) long long
                 oand)) long long oor) = Vnull ->
                 Int.eq (i16&ᵢ$ CNODE_GRANT_CAP) ($ 0) = true \/
Int.eq i6 x3 = false.
Proof.
  intros.
  unfold val_inj, bop_eval, val_eq in H.
  assert(Int.eq ($1) (Int.zero) = false).
  int auto.
  unfold and in H.
  rewrite H0 in H.
  unfold bool_or, bool_and, uop_eval, notint, Int.notbool in H.
  destruct (Int.eq (i16&ᵢ$ CNODE_GRANT_CAP) ($ 0));
  destruct (Int.eq i6 x3) eqn: Hb; repeat val_help H; tryfalse; auto. 
  rewrite Int.eq_sym in Hb. rewrite Hb in H. 
  repeat (val_help H). destruct H; tryfalse.
Qed.

(* Lemma  nth_cpsace_val_length_imp: 
  forall n vl1 a vl2,
  length vl1 = n ->
  nth_cspace_val n (vl1 ++ a :: vl2) = Some a.
  Proof.
  induction n; induction vl1; intros.
  simpl. auto.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. 
  assert(length vl1 = n) by auto with arith.
  eapply IHn  with(a:=a)(vl2:=vl2) in H0 . 
  simpl.
  auto.
Qed.

Lemma add_isr_is_prop:
forall P, Aisr empisr ** Ais nil ** P ==> Aisr empisr ** Ais nil ** A_isr_is_prop ** P.
Proof.
  intros.
  unfold A_isr_is_prop.
  sep normal.
  sep auto.
  rewrite H0.
  rewrite H1.
  unfolds.
  intros.
  auto.
Qed.

Lemma update_nth_cspace_slot_cap_child_similar:
  forall ls desc class v,
  child_similar ls (update_nth_cspace_slots_cap desc class ls v).
Proof.
  intros. 
  unfold update_nth_cspace_slots_cap.
  destruct (nth_cspace
  desc ls) eqn: Heq.
  destruct c, p, p, c, p. 
  destruct (ACSpace_defs.nth_slots class l0).
  destruct p, p, c, p.  

  {
    remember (i0, i1,
    ACSpace_defs.update_nth_list slot_val_type
      class l0
      (i2, v), i, l, v0) as uval. 
    unfold child_similar.
    intros.
    lets Hc1: nat_ltorge (Z.to_nat(Int.unsigned node)) (length ls).
    lets Hc2: nat_ltorge (desc) (length ls).
    lets Hc3: nat_eqorneq (Z.to_nat(Int.unsigned node)) (desc).
    destruct Hc1; destruct Hc2; destruct Hc3.
    unfold child. 
    rewrite H1 in *.
    rewrite Heq.
    assert(nth_cspace desc
    (ACSpace_defs.update_nth_list cspace_val_type
       (desc) ls
       uval) = Some uval).
    eapply update_nth_cspace_eq; auto. 
    rewrite H2. subst uval. auto. 
    unfold child. 
    assert( nth_cspace
    (Z.to_nat (Int.unsigned node))
    (ACSpace_defs.update_nth_list cspace_val_type
       (desc)
       ls uval) = nth_cspace
       (Z.to_nat (Int.unsigned node)) ls).
    eapply update_nth_cspace_neqrev; auto.
    rewrite H2. auto.  
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    
    rewrite H0. auto. 
    eapply update_nth_cspace_remain with(v:= uval)in H0. 
    rewrite H0. auto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
    unfold child. 
    rewrite nth_cspace_none; eauto. 
    rewrite nth_cspace_none; eauto. 
    rewrite update_nth_list_len_eq; eauto. 
  }
  unfold child_similar; intros. auto.
  unfold child_similar; intros. auto.
Qed.


Lemma nth_cspace_eq_nth_cspace_val: 
  forall vl x,
  nth_cspace_val x vl = nth_cspace x vl.
Proof.
  induction vl; destruct x; intros; simpl; auto.
Qed.
Lemma update_nth_cspace_slots_cap_length_eq:
  forall ls desc class v,
  length ls = length (update_nth_cspace_slots_cap desc
  class ls v).
Proof.
  intros. 
  unfold update_nth_cspace_slots_cap.
  destruct (nth_cspace
  desc ls) eqn: Heq.
  destruct c, p, p, c, p. 
  destruct (ACSpace_defs.nth_slots class l0).
  destruct p, p, c, p.  

  {
    remember (i0, i1,
    ACSpace_defs.update_nth_list slot_val_type
      class l0
      (i2, v), i, l, v0) as uval. 
    intros.
    rewrite update_nth_list_len_eq.
    auto. 
  }
  auto. auto.
Qed.




Lemma update_nth_cspace_slots_cap_imply_exists:
forall x0 x y cspacevl v cspace,
  nth_cspace_val∘ (Int.unsigned x0)(update_nth_cspace_slots_cap
    x y cspacevl v) =
  Some cspace ->
  exists cspace', nth_cspace_val∘ (Int.unsigned x0) cspacevl = Some cspace'. 
Proof.
  intros.
  assert(∘ (Int.unsigned x0) < (length cspacevl))%nat. 
  assert(length cspacevl = length (update_nth_cspace_slots_cap x
  y cspacevl v)).
  eapply update_nth_cspace_slots_cap_length_eq.
  rewrite H0.
  lets Hc: nat_ltorge (∘ (Int.unsigned x0)) (length
  (update_nth_cspace_slots_cap x y
     cspacevl v)).
  destruct Hc. auto.
  rewrite nth_cspace_eq_nth_cspace_val in H. 
  rewrite nth_cspace_none in H; auto.
  tryfalse.
  rewrite nth_cspace_eq_nth_cspace_val.
  eapply nth_cspace_exists; auto.
Qed.

Lemma update_nth_cspace_slots_cap_remain:
  forall cspacevl x0 x y  v cspace cspace',
  nth_cspace_val (Z.to_nat (Int.unsigned x0)) cspacevl = Some cspace ->
  nth_cspace_val (Z.to_nat (Int.unsigned x0))
  (update_nth_cspace_slots_cap x y
    cspacevl v) = Some cspace' ->
  get_Childlist cspace = get_Childlist cspace'.
Proof.
  intros.
  assert(child_similar cspacevl (update_nth_cspace_slots_cap x y cspacevl  v)).
  eapply update_nth_cspace_slot_cap_child_similar.
  unfolds in H1.
  lets Hx: H1 x0.
  destruct Hx. 
  unfolds.
  destruct cspace, p, p.
  destruct cspace', p, p.
  rewrite nth_cspace_eq_nth_cspace_val in H.
  rewrite nth_cspace_eq_nth_cspace_val in H0.
  rewrite H, H0 in H3.
  unfolds in H3. inverts H3. 
  auto.
Qed.
Lemma RL_Cap_Parent_Child_remain: 
  forall cspacevl vl x y  v,
  RL_Cap_Parent_Child vl cspacevl ->
  RL_Cap_Parent_Child vl (update_nth_cspace_slots_cap x y cspacevl v).
Proof.
  unfold RL_Cap_Parent_Child. intros.
  destruct H. 
  splits; intros.
  assert(H4_bak: nth_cspace_val
  ∘ (Int.unsigned x0)
  (update_nth_cspace_slots_cap
     x y cspacevl v) =
Some cspace) by auto.
  eapply update_nth_cspace_slots_cap_imply_exists in H4.
  destruct H4.
  lets Hx: H H1 H2 H3 H4.
  assert(child_similar cspacevl (update_nth_cspace_slots_cap x y cspacevl v)).
  eapply update_nth_cspace_slot_cap_child_similar.
  unfold child_similar in H5.
  lets Hy: H5 x0. 
  destruct Hy.
  rewrite nth_cspace_eq_nth_cspace_val in H4.
  rewrite nth_cspace_eq_nth_cspace_val in H4_bak.
  rewrite H4, H4_bak in H7.
  assert(get_Childlist x1 = get_Childlist cspace).
  unfolds.
  destruct x1, p, p.
  destruct cspace, p, p.
  unfolds in H7. inverts H7. auto.
  rewrite <- H8. auto.
  auto.

  (*right*)
  assert(H2_bak: nth_cspace_val
  ∘ (Int.unsigned prio)
  (update_nth_cspace_slots_cap
     x y cspacevl v) =
Some cspace) by auto.
 eapply update_nth_cspace_slots_cap_imply_exists in H2.
 destruct H2.
 lets Hx: H0 H1 H2 .
 lets Hy: Hx x0.
 assert(get_Childlist x1 = get_Childlist cspace).
 {
  assert(child_similar cspacevl (update_nth_cspace_slots_cap x y cspacevl v)).
  eapply update_nth_cspace_slot_cap_child_similar.
  unfold child_similar in H4.
  lets Hz: H4 prio.
  destruct Hz.
  rewrite nth_cspace_eq_nth_cspace_val in H2, H2_bak.
  rewrite H2, H2_bak in H6.
  unfolds. destruct x1, p, p.
  destruct cspace, p, p.
  unfolds in H6. inverts H6. auto.
 }
 rewrite <- H4 in H3.
 eapply Hy. auto.
Qed. *)