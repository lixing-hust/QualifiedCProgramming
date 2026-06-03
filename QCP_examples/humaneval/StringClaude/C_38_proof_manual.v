Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_38_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_38.
Local Open Scope sac.

Ltac decode_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Ltac decode_source_open_true :=
  unfold decode_source_index_z;
  replace (Z.ltb _ _) with true by (symmetry; apply Z.ltb_lt; lia);
  replace (Z.eqb (Z.rem (_ + 1) 3) 1) with true by
    (symmetry; apply Z.eqb_eq; assumption).

Ltac decode_source_open_false :=
  unfold decode_source_index_z;
  replace (Z.ltb _ _) with true by (symmetry; apply Z.ltb_lt; lia);
  replace (Z.eqb (Z.rem (_ + 1) 3) 1) with false by
    (symmetry; apply Z.eqb_neq; assumption).

Ltac decode_source_tail :=
  unfold decode_source_index_z;
  replace (Z.ltb _ _) with false by (symmetry; apply Z.ltb_ge; lia).

Ltac prove_source_range :=
  match goal with
  | Hsrc : decode_source_index_z ?len ?i = ?src |- _ =>
      pose proof (decode_source_index_z_range len i ltac:(lia) ltac:(lia)) as Hrange;
      rewrite Hsrc in Hrange;
      lia
  end.

Ltac finish_decode_step :=
  entailer!;
  [ intros k Hk;
    match goal with
    | Hlen : Zlength ?old = ?idx,
      Hpref : forall k : Z, _ -> Znth k ?old 0 = decode_char_z ?len ?l k |- _ =>
        destruct (Z_lt_ge_dec k idx) as [Hlt | Hge]
        ; [ rewrite app_Znth1 by lia; apply Hpref; lia
          | assert (k = idx) by lia; subst k;
            rewrite app_Znth2 by lia;
            replace (idx - Zlength old) with 0 by lia;
            rewrite Znth0_cons;
            repeat rewrite app_Znth1 by lia;
            unfold decode_char_z;
            match goal with
            | Hsrc : decode_source_index_z len idx = _ |- _ => rewrite Hsrc
            end;
            reflexivity ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_decode_cyclic_safety_wit_3 : decode_cyclic_safety_wit_3.
Proof.
  unfold decode_cyclic_safety_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  all: pose proof (full_decode_len_z_bounds (Zlength l) ltac:(lia)) as [[Hge Hle] _];
       unfold full_decode_len_z in *;
       lia.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_1 : decode_cyclic_entail_wit_1.
Proof.
  unfold decode_cyclic_entail_wit_1.
  intros.
  decode_pre.
  subst retval.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_2 0 (len + 1)).
  rewrite (CharArray.undef_seg_empty retval_2 0).
  rewrite (CharArray.full_empty retval_2 0).
  unfold full_decode_len_z.
  entailer!.
  lia.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_2 : decode_cyclic_entail_wit_2.
Proof.
  unfold decode_cyclic_entail_wit_2.
  intros.
  decode_pre.
  Exists out_l_2.
  assert (Hsrc : decode_source_index_z len i = i + 2).
  {
    decode_source_open_true.
    reflexivity.
  }
  entailer!.
  prove_source_range.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_3 : decode_cyclic_entail_wit_3.
Proof.
  unfold decode_cyclic_entail_wit_3.
  intros.
  decode_pre.
  Exists out_l_2.
  assert (Hsrc : decode_source_index_z len i = i - 1).
  {
    decode_source_open_false.
    reflexivity.
  }
  entailer!.
  prove_source_range.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_4 : decode_cyclic_entail_wit_4.
Proof.
  unfold decode_cyclic_entail_wit_4.
  intros.
  decode_pre.
  Exists out_l_2.
  assert (Hsrc : decode_source_index_z len i = i).
  {
    decode_source_tail.
    reflexivity.
  }
  entailer!.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_5_1 : decode_cyclic_entail_wit_5_1.
Proof.
  unfold decode_cyclic_entail_wit_5_1.
  intros.
  decode_pre.
  Exists (app out_l_2 (cons (Znth (i + 2) l 0) nil)).
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply H13. lia.
    + assert (k = i) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      unfold decode_char_z.
      rewrite H14.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_5_2 : decode_cyclic_entail_wit_5_2.
Proof.
  unfold decode_cyclic_entail_wit_5_2.
  intros.
  decode_pre.
  Exists (app out_l_2 (cons (Znth (i - 1) l 0) nil)).
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply H13. lia.
    + assert (k = i) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      unfold decode_char_z.
      rewrite H14.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_decode_cyclic_entail_wit_5_3 : decode_cyclic_entail_wit_5_3.
Proof.
  unfold decode_cyclic_entail_wit_5_3.
  intros.
  decode_pre.
  Exists (app out_l_2 (cons (Znth i l 0) nil)).
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply H10. lia.
    + assert (k = i) by lia. subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      unfold decode_char_z.
      rewrite H11.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_decode_cyclic_return_wit_1 : decode_cyclic_return_wit_1.
Proof.
  unfold decode_cyclic_return_wit_1.
  intros.
  decode_pre.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  replace (Zlength out_l_2 + 1) with (len + 1) by lia.
  entailer!.
  apply problem_38_spec_z_intro with (len := len); try lia.
  - exact H6.
  - intros k Hk.
    apply H10.
    lia.
Qed.
