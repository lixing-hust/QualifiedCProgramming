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

Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Notation "E '..' I" := (efield E I) (at level 10)  : code_scope.

Lemma three_bool_and_false:
forall i i0 v'6 ,
  val_inj
  (bool_and
    (val_inj
        (bool_and
          (val_inj
              (if Int.eq i ($ CAP_CATEGORY_TYPE)
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))
          (val_inj
              (if Int.eq (Int.not i0&ᵢv'6) ($ 0)
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))))
    (val_inj
        (notint
          (val_inj
              (if Int.eq i0 v'6
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))))) =
  Vint32 Int.zero \/
  val_inj
  (bool_and
    (val_inj
        (bool_and
          (val_inj
              (if Int.eq i ($ CAP_CATEGORY_TYPE)
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))
          (val_inj
              (if Int.eq (Int.not i0&ᵢv'6) ($ 0)
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))))
    (val_inj
        (notint
          (val_inj
              (if Int.eq i0 v'6
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))))) =
  Vnull ->
  i <> $ CAP_CATEGORY_TYPE \/ Int.not i0&ᵢv'6 <> $ 0 \/ i0 = v'6.
Proof. 
  intros. 
  assert(Int.ltu Int.zero Int.one = true) by auto.
  assert(Int.eq Int.one Int.zero = false) by auto.
  assert(Int.ltu Int.zero Int.zero = false) by auto.
  destruct (Int.eq i ($ CAP_CATEGORY_TYPE)) eqn: Hb1.
  destruct (Int.eq(Int.not i0&ᵢv'6)($ 0)) eqn: Hb2.
  destruct(Int.eq i0 v'6) eqn: Hb3.
  {
    clear -Hb3.
    right. right.
    lets Hx: Int.eq_spec i0 v'6.
    rewrite Hb3 in Hx. auto.
  }
  simpl in H. 
  
  rewrite H0 in H. simpl in H.
  rewrite H0 in H. simpl in H.
  unfold Int.notbool in H.
  rewrite Int.eq_true in H.
  rewrite H0 in H.
  destruct H; tryfalse.
  right. left.
  {
    clear -Hb2.
    lets Hx: Int.eq_spec (Int.not i0&ᵢv'6) ($ 0).
    rewrite Hb2 in Hx.
    auto.
  }
  left.
  clear -Hb1.
  lets Hx: Int.eq_spec i ($ CAP_CATEGORY_TYPE).
  rewrite Hb1 in Hx.
  auto.
Qed.
  
Lemma three_and_true: 
forall i i0 v'6, 
val_inj
      (bool_and
         (val_inj
            (bool_and
               (val_inj
                  (if
                    Int.eq i
                      ($ CAP_CATEGORY_TYPE)
                   then
                    Some (Vint32 Int.one)
                   else
                    Some (Vint32 Int.zero)))
               (val_inj
                  (if
                    Int.eq (Int.not i0&ᵢv'6)
                      ($ 0)
                   then
                    Some (Vint32 Int.one)
                   else
                    Some (Vint32 Int.zero)))))
         (val_inj
            (notint
               (val_inj
                  (if Int.eq i0 v'6
                   then
                    Some (Vint32 Int.one)
                   else
                    Some (Vint32 Int.zero)))))) <>
    Vint32 Int.zero ->
    i = $ CAP_CATEGORY_TYPE /\Int.not i0&ᵢv'6 = $ 0 /\ i0 <> v'6.
Proof.
  intros.
  assert(Int.ltu Int.zero Int.one = true) by auto.
  assert(Int.eq Int.one Int.zero = false) by auto.
  assert(Int.ltu Int.zero Int.zero = false) by auto.
  destruct (Int.eq i ($ CAP_CATEGORY_TYPE)) eqn: Hb1.
  destruct (Int.eq(Int.not i0&ᵢv'6)($ 0)) eqn: Hb2.
  destruct(Int.eq i0 v'6) eqn: Hb3.
  simpl in H.
  rewrite H0 in H.  simpl in H. 
  assert(Int.ltu Int.zero Int.one = true) by auto.
  rewrite H3 in H. simpl in H.
  unfold Int.notbool in H. 
  rewrite H1 in H. 
  rewrite H2 in H. 
  simpl in  H. tryfalse.

  {
    clear -Hb1 Hb2 Hb3.
    lets Hx1: Int.eq_spec i ($ CAP_CATEGORY_TYPE).
    rewrite Hb1 in Hx1.
    lets Hx2: Int.eq_spec (Int.not i0&ᵢv'6) ($ 0).
    rewrite Hb2 in Hx2.
    lets Hx3: Int.eq_spec i0 v'6.
    rewrite Hb3 in Hx3.
    splits; eauto.
  }

  simpl in H. 
  rewrite H0 in H.  simpl in H. 
  rewrite H2 in H. 
  simpl in H. 
  destruct (Int.eq i0 v'6).
  simpl in H. unfold Int.notbool in H. 
  rewrite H1, H2 in H. 
  simpl in H. tryfalse.
  rewrite H2 in H. simpl in H. 
  tryfalse.
  destruct(Int.eq (Int.not i0&ᵢv'6)($ 0)).
  destruct (Int.eq i0 v'6).
  simpl in H. rewrite H0, H2 in H. 
  simpl in H. unfold Int.notbool in H. 
  rewrite H1, H2 in H. simpl in H. tryfalse.
  simpl in H. unfold Int.notbool in H. 
  rewrite H0, H2, Int.eq_true in H. 
  simpl in H. rewrite H0, H2 in H. simpl in H. tryfalse.
  destruct (Int.eq i0 v'6).
  simpl in H. unfold Int.notbool in H. 
  assert(Int.eq Int.one Int.zero = false) by auto.
  rewrite H3, H2 in H. 
  simpl in H. rewrite H2 in H. simpl in H. tryfalse.
  simpl in H. rewrite H2 in H. unfold Int.notbool in H. 
  simpl in H. rewrite H2, Int.eq_true, H0 in H. 
  simpl in H. tryfalse.
Qed.




