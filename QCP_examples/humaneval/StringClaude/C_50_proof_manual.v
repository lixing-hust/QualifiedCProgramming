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
From SimpleC.EE Require Import C_50_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_50.
Local Open Scope sac.

Ltac shift_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Ltac lower_at :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hpre : problem_50_pre_z ?l,
    Hrange : ascii_range_z ?l |- context[Znth ?i ?l 0] =>
      let Hlower := fresh "Hlower" in
      pose proof (lower_char_z_from_problem_50_pre l i Hpre Hrange ltac:(lia)) as Hlower;
      unfold lower_char_z in Hlower
  end.

Ltac solve_shift_safety :=
  shift_pre;
  lower_at;
  unfold encode_shift_char_z, decode_shift_char_z in *;
  match goal with
  | |- context[((Znth ?i ?l 0 + 5 - 97) % 26)] =>
      pose proof (Z.rem_bound_pos (Znth i l 0 + 5 - 97) 26 ltac:(lia) ltac:(lia))
  | |- context[((Znth ?i ?l 0 + 21 - 97) % 26)] =>
      pose proof (Z.rem_bound_pos (Znth i l 0 + 21 - 97) 26 ltac:(lia) ltac:(lia))
  | _ => idtac
  end;
  entailer!.

Ltac rewrite_signed_shift :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hpre : problem_50_pre_z ?l,
    Hrange : ascii_range_z ?l |- context[signed_last_nbits ?x 8] =>
      let idx := match x with context[Znth ?i l 0] => i end in
      let Hlower := fresh "Hlower" in
      pose proof (lower_char_z_from_problem_50_pre l idx Hpre Hrange ltac:(lia)) as Hlower;
      unfold lower_char_z in Hlower;
      rewrite (signed_last_nbits_eq x 8)
        by (try lia;
            pose proof (Z.rem_bound_pos (Znth idx l 0 + 5 - 97) 26 ltac:(lia) ltac:(lia));
            pose proof (Z.rem_bound_pos (Znth idx l 0 + 21 - 97) 26 ltac:(lia) ltac:(lia));
            lia)
  end.

Ltac solve_shift_step_value :=
  intros k Hk;
  match goal with
  | Hlen : Zlength ?ol = ?i,
    Hprefix : forall k : Z, _ -> Znth k ?ol 0 = ?f (Znth k ?l 0) |- _ =>
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
      [ rewrite app_Znth1 by lia;
        apply Hprefix;
        lia
      | assert (k = i) by lia;
        subst k;
        rewrite app_Znth2 by lia;
        replace (i - Zlength ol) with 0 by lia;
        rewrite Znth0_cons;
        rewrite_signed_shift;
        unfold encode_shift_char_z, decode_shift_char_z;
        repeat rewrite app_Znth1 in * by lia;
        reflexivity ]
  end.

Ltac solve_shift_step :=
  shift_pre;
  match goal with
  | |- context[CharArray.full ?out (?i + 1) (app ?ol (cons ?v nil))] =>
      Exists (app ol (cons v nil))
  end;
  entailer!;
  [ solve_shift_step_value
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac solve_shift_init :=
  shift_pre;
  subst;
  Exists nil;
  match goal with
  | |- context[CharArray.undef_full ?p (Zlength ?l + 1)] =>
      sep_apply (CharArray.undef_full_split_to_undef_seg p 0 (Zlength l + 1));
      [ idtac | lia ];
      rewrite (CharArray.undef_seg_empty p 0);
      rewrite (CharArray.full_empty p 0)
  end;
  entailer!;
  lia.

Lemma proof_of_encode_shift_safety_wit_4 : encode_shift_safety_wit_4.
Proof. unfold encode_shift_safety_wit_4; intros; solve_shift_safety. Qed. 

Lemma proof_of_encode_shift_safety_wit_6 : encode_shift_safety_wit_6.
Proof. unfold encode_shift_safety_wit_6; intros; solve_shift_safety. Qed. 

Lemma proof_of_encode_shift_safety_wit_7 : encode_shift_safety_wit_7.
Proof. unfold encode_shift_safety_wit_7; intros; solve_shift_safety. Qed. 

Lemma proof_of_encode_shift_entail_wit_1 : encode_shift_entail_wit_1.
Proof. unfold encode_shift_entail_wit_1; intros; solve_shift_init. Qed. 

Lemma proof_of_encode_shift_entail_wit_2 : encode_shift_entail_wit_2.
Proof. unfold encode_shift_entail_wit_2; intros; solve_shift_step. Qed. 

Lemma proof_of_encode_shift_return_wit_1 : encode_shift_return_wit_1.
Proof.
  unfold encode_shift_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  - match goal with
    | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
    end.
    entailer!.
  - eapply problem_50_encode_spec_z_intro with (n := len); try lia.
    intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = encode_shift_char_z (Znth k l 0) |- _ =>
        apply Hprefix; lia
    end.
Qed. 

Lemma proof_of_decode_shift_safety_wit_4 : decode_shift_safety_wit_4.
Proof. unfold decode_shift_safety_wit_4; intros; solve_shift_safety. Qed. 

Lemma proof_of_decode_shift_safety_wit_6 : decode_shift_safety_wit_6.
Proof. unfold decode_shift_safety_wit_6; intros; solve_shift_safety. Qed. 

Lemma proof_of_decode_shift_safety_wit_7 : decode_shift_safety_wit_7.
Proof. unfold decode_shift_safety_wit_7; intros; solve_shift_safety. Qed. 

Lemma proof_of_decode_shift_entail_wit_1 : decode_shift_entail_wit_1.
Proof. unfold decode_shift_entail_wit_1; intros; solve_shift_init. Qed. 

Lemma proof_of_decode_shift_entail_wit_2 : decode_shift_entail_wit_2.
Proof. unfold decode_shift_entail_wit_2; intros; solve_shift_step. Qed. 

Lemma proof_of_decode_shift_return_wit_1 : decode_shift_return_wit_1.
Proof.
  unfold decode_shift_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  - match goal with
    | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
    end.
    entailer!.
  - eapply problem_50_decode_spec_z_intro with (n := len); try lia; try assumption.
    intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = decode_shift_char_z (Znth k l 0) |- _ =>
        apply Hprefix; lia
    end.
Qed. 
