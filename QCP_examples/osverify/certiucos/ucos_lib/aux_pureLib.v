Require Export ucos_include.
Require Export os_ucos_h.
Require Import Lia.

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

Lemma Int_ltu_true_intrepr_l : 
 forall x i, 
 (0 <= x <= Int.max_unsigned)%Z ->
 Int.ltu ($ x) i = true -> 
 (x < Int.unsigned i)%Z.
Proof.
  intros.
  rewrite <- (Int.unsigned_repr x);auto.
  apply Intlt_true_is_Zlt;auto.
Qed.

Lemma Int_ltu_true_intrepr_r : 
 forall x i, 
 (0 <= x <= Int.max_unsigned)%Z ->
 Int.ltu i ($ x) = true -> 
 (Int.unsigned i < x)%Z.
Proof.
  intros.
  rewrite <- (Int.unsigned_repr x);auto.
  apply Intlt_true_is_Zlt;auto.
Qed.

Lemma Int_ltu_false_intrepr_l : 
 forall x i, 
 (0 <= x <= Int.max_unsigned)%Z ->
 Int.ltu ($ x) i = false -> 
 (x >= Int.unsigned i)%Z.
Proof.
  intros.
  rewrite <- (Int.unsigned_repr x);auto.
  apply Intlt_false_is_Zge;auto.
Qed.

Lemma Int_ltu_false_intrepr_r : 
 forall x i, 
 (0 <= x <= Int.max_unsigned)%Z ->
 Int.ltu i ($ x) = false -> 
 (Int.unsigned i >= x)%Z.
Proof.
  intros.
  rewrite <- (Int.unsigned_repr x);auto.
  apply Intlt_false_is_Zge;auto.
Qed.

Lemma Int_eq_dec : forall x y , Int.eq x y = true <-> x = y.
Proof.
  intros.
  split;intros.
  { pose proof Int.eq_spec x y.
  rewrite H in H0. auto. }
  rewrite H. apply Int.eq_true.
Qed.

Lemma Int_eq_false_intrepr_r : forall x i,
(0 <= x <= Int.max_unsigned)%Z ->  Int.eq i ($ x) = false -> Int.unsigned i <> x.
Proof.
  intros.
  rewrite <- (Int.unsigned_repr x);auto.
  eapply Inteq_false_is_Zneq;eauto.
Qed.

Lemma Int_eq_false_intrepr_l : forall x i,
(0 <= x <= Int.max_unsigned)%Z ->  Int.eq  ($ x) i = false -> x <> Int.unsigned i.
Proof.
  intros.
  rewrite <- (Int.unsigned_repr x);auto.
  eapply Inteq_false_is_Zneq;eauto.
Qed.

Lemma Int_lt_refl : forall x, Int.lt x x = false.
Proof.
  intros.
  unfold Int.lt.
  apply zlt_false.
  lia.
Qed.

Lemma Int_ltu_refl : forall x, Int.ltu x x = false.
Proof.
  intros.
  unfold Int.ltu.
  apply zlt_false.
  lia.
Qed.

Lemma Int_lt_true_intrepr_l : 
 forall x i, 
 (Int.min_signed <= x <= Int.max_signed)%Z ->
 Int.lt ($ x) i = true -> 
 (x < Int.signed i)%Z.
Proof.
  intros.
  rewrite <- (Int.signed_repr x);auto.
  unfold Int.lt in H0.
  destruct zlt; tryfalse.
  auto.
Qed.

Lemma Int_lt_true_intrepr_r : 
 forall x i, 
 (Int.min_signed <= x <= Int.max_signed)%Z ->
 Int.lt i ($ x) = true -> 
 (Int.signed i < x)%Z.
Proof.
  intros.
  rewrite <- (Int.signed_repr x);auto.
  unfold Int.lt in H0.
  destruct zlt; tryfalse.
  auto.
Qed.

Lemma Int_lt_false_intrepr_l : 
 forall x i, 
 (Int.min_signed <= x <= Int.max_signed)%Z ->
 Int.lt ($ x) i = false -> 
 (x >= Int.signed i)%Z.
Proof.
  intros.
  rewrite <- (Int.signed_repr x);auto.
  unfold Int.lt in H0.
  destruct zlt; tryfalse.
  auto.
Qed.

Lemma Int_lt_false_intrepr_r : 
 forall x i, 
 (Int.min_signed <= x <= Int.max_signed)%Z ->
 Int.lt i ($ x) = false -> 
 (Int.signed i >= x)%Z.
Proof.
  intros.
  rewrite <- (Int.signed_repr x);auto.
  unfold Int.lt in H0.
  destruct zlt; tryfalse.
  auto.
Qed.

Lemma Int_unsigned_minus : forall x y, 
  Int.unsigned y <= Int.unsigned x ->
  Int.unsigned (x -ᵢ y) = Int.unsigned x - Int.unsigned y.
Proof.
  intros.
  unfold Int.sub.
  rewrite Int.unsigned_repr;auto.
  split.
  lia.
  pose proof Int.unsigned_range x.
  pose proof Int.unsigned_range y.
  unfold Int.modulus,Int.wordsize,Wordsize_32.wordsize,two_power_nat in H0.
  cbn in *. lia.
Qed.

Ltac simpl_intltbool :=
  repeat progress match goal with 
  | H : Int.ltu ($ ?x) ?i = true |- _ => 
    apply Int_ltu_true_intrepr_l in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.ltu ?i ($ ?x) = true |- _ => 
    apply Int_ltu_true_intrepr_r in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.ltu ($ ?x) ?i = false |- _ => 
    apply Int_ltu_false_intrepr_l in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.ltu ?i ($ ?x) = false |- _ => 
    apply Int_ltu_false_intrepr_r in H;[ | clear;try (unfold x);cbn;lia] 
  | H : Int.lt ($ ?x) ?i = true |- _ => 
    apply Int_lt_true_intrepr_l in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.lt ?i ($ ?x) = true |- _ => 
    apply Int_lt_true_intrepr_r in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.lt ($ ?x) ?i = false |- _ => 
    apply Int_lt_false_intrepr_l in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.lt ?i ($ ?x) = false |- _ => 
    apply Int_lt_false_intrepr_r in H;[ | clear;try (unfold x);cbn;lia] 
  | H : Int.eq ($ ?x) ?i = false |- _ => 
    apply Int_eq_false_intrepr_l in H;[ | clear;try (unfold x);cbn;lia]
  | H : Int.eq ?i ($ ?x) = false |- _ => 
    apply Int_eq_false_intrepr_r in H;[ | clear;try (unfold x);cbn;lia]   
  end.

Lemma nth_val_In: 
  forall n vl x, nth_val n vl = Some x -> In x vl.
Proof.
  induction n;intros.
  - destruct vl;tryfalse.
    simpl in H. 
    inversion H. 
    constructor. auto.
  - destruct vl;tryfalse.
    simpl in H. 
    apply in_cons.
    eapply IHn;eauto.
Qed.

Lemma nth_val_In_firstn: 
  forall n vl x, nth_val n vl = Some x -> In x (firstn (n+1) vl).
Proof.
  induction n;intros.
  - destruct vl;tryfalse.
    simpl in *. 
    inversion H. 
    constructor. auto.
  - destruct vl;tryfalse.
    simpl in *.
    right. 
    eapply IHn;eauto.
Qed.

Lemma Forall_firstn : 
  forall [A: Type] n vl (p : A -> Prop), Forall p vl -> Forall p (firstn n vl).
Proof. 
  induction n;intros.
  - simpl. constructor.
  - destruct vl.
    + simpl. auto.
    + simpl. 
      inversion H. auto.
Qed.

Lemma Forall_firstn_lt : 
  forall [A: Type]  m n vl (p : A -> Prop), 
  (m < n)%nat ->
  Forall p (firstn n vl) -> Forall p (firstn m vl).
Proof.
  induction m;intros.
  - destruct n;[lia | ].
    cbn. auto.
  - destruct n;[lia | ].
    destruct vl.
    simpl in *;auto.
    simpl in H0. simpl.
    inversion H0;subst.
    constructor;auto.
    eapply (IHm n);eauto.
    lia.
Qed. 

Lemma Forall_update_nth_val : 
  forall vl n v P, Forall P vl -> P v -> Forall P (update_nth_val n vl v).
Proof.
  induction vl;intros.
  - simpl;auto.
  - inversion H;subst.
    destruct n;simpl.
    + constructor;auto. 
    + constructor;auto.
Qed.

Lemma firstn_update_nth_val : 
  forall n vl v, firstn n (update_nth_val n vl v) = firstn n vl.
Proof. 
  induction n;intros.
  - simpl. auto.
  - destruct vl.
    + simpl. auto.
    + simpl.
      specialize (IHn vl v).
      rewrite IHn.
      auto.
Qed.

Lemma update_nth_val_midlle : forall vl1 v vl2 v',
            update_nth_val (length vl1) (vl1 ++ v :: vl2) v' = vl1 ++ v' :: vl2.
          Proof.
            induction vl1;intros.
            - simpl;reflexivity.
            - simpl.
              rewrite IHvl1.
              reflexivity.
          Qed.

Lemma skipn_stack : 
  forall [A: Type](n : nat) (vl : list A) (v : A) (vl' : list A),
  skipn n vl = v :: vl' -> skipn (n + 1) vl = vl'.
Proof. 
  induction n;intros.
  - destruct vl;simpl in *. false. inversion H; auto.
  - destruct vl.
    + simpl in *. false.
    + simpl in *.
      eapply IHn;eauto.
Qed.

Lemma array_type_vallist_match_app:
 forall vl1 vl2 t, array_type_vallist_match t (vl1 ++ vl2) <->
  array_type_vallist_match t vl1 /\ array_type_vallist_match t vl2.
Proof.
  induction vl1.
  - split;intros;cbn;tauto.
  - split;intros.
    + cbn in *.
      destruct H.
      apply IHvl1 in H0.
      tauto.
    + destruct H as [[? ?] ?].
      cbn.
      split;auto.
      apply IHvl1;auto.
Qed.

Lemma nth_val_middle:
  forall l1 l2 a,
    nth_val (length l1)  (l1 ++ a :: l2)= Some a.
Proof.
  induction l1;intros.
  - simpl. auto.
  - simpl. apply IHl1.
Qed.

Lemma nth_val_nth_error : forall n vl v, nth_val n vl = Some v <-> nth_error vl n = Some v.
Proof.
  induction n;intros.
  - destruct vl;simpl in *.
    split;intros;false.
    split;intros H;inversion H;auto.
  - destruct vl;simpl in *.
    split;intros;false.
    split;intros H;apply IHn;auto.
Qed.

Lemma revfirstn_nth_error : 
  forall [A:Type ]n vl (v x: A) vl', 
  rev (firstn (n+1) vl) = x :: vl' -> nth_error vl n = Some v -> x = v.
Proof.
  intros. 
  apply nth_error_split in H0.
  destruct H0 as [? [? [? ?]]].
  subst vl.
  rewrite <- H1 in H.
  rewrite firstn_app_2 in H.
  cbn in H.
  rewrite rev_app_distr in H.
  simpl in H.
  inversion H.
  auto.
Qed.

Lemma update_nth_val_firstn : forall m n v vl, 
  (m < n)%nat ->
  update_nth_val m (firstn n vl) v = firstn n (update_nth_val m vl v).
Proof.
  induction m;intros.
  - destruct n;[false;lia | ].
    destruct vl;auto.
  - destruct n;[false;lia | ].
    destruct vl;auto.
    cbn [firstn update_nth_val].
    apply lt_S_n in H.
    erewrite IHm;eauto.
Qed.

Lemma nth_error_update_nth_val : forall m n v vl,
  (m < n)%nat ->
  nth_error (update_nth_val m vl v) n = nth_error vl n.
Proof.
  induction m;intros.
  - destruct n;[false;lia | ].
    destruct vl;auto.
  - destruct n;[false;lia | ].
    destruct vl;auto.
    cbn [nth_error update_nth_val].
    apply lt_S_n in H.
    erewrite IHm;eauto.
Qed.

Lemma nth_error_update_nth_val_eq : forall  n v vl v',
  nth_error vl n = Some v' ->
  nth_error (update_nth_val n vl v) n = Some v.
Proof.
  induction n;intros.
  - destruct vl;auto.
    simpl in H.
    tryfalse.
  - destruct vl;auto;
    cbn [nth_error update_nth_val] in *.
    tryfalse.
    erewrite IHn;eauto.
Qed.

