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
From SimpleC.EE Require Import C_93_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_93.
Local Open Scope sac.

Ltac normalize_input_char :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hpre : problem_93_pre_z ?l,
    Hrange : ascii_range_z ?l |- context[Znth ?i ?l 0] =>
      let Hchar := fresh "Hchar" in
      pose proof (problem_93_pre_z_char l i Hpre Hrange ltac:(lia)) as Hchar;
      unfold is_upper_z, is_lower_z, is_space_z in Hchar;
      destruct Hchar as [Hchar | [Hchar | Hchar]]
  | _ => idtac
  end;
  try lia.

Ltac simplify_encode_char :=
  normalize_input_char;
  repeat match goal with
  | |- context[signed_last_nbits (Znth ?i ?l 0) 8] =>
      rewrite (signed_last_nbits_eq (Znth i l 0) 8) by lia
  end;
  unfold encode_char_z, swap_case_z, is_vowel_z;
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  | |- context[Z.eqb ?x ?y] =>
      destruct (Z.eqb_spec x y); simpl
  end;
  lia.

Ltac solve_encode_step_value :=
  intros k Hk;
  match goal with
  | Hlen : Zlength ?ol = ?i,
    Hprefix : forall k : Z, _ -> Znth k ?ol 0 = encode_char_z (Znth k ?l 0) |- _ =>
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
      [ rewrite app_Znth1 by lia;
        apply Hprefix;
        lia
      | assert (k = i) by lia;
        subst k;
        rewrite app_Znth2 by lia;
        replace (i - Zlength ol) with 0 by lia;
        rewrite Znth0_cons;
        simplify_encode_char ]
  end.

Ltac solve_encode_step :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | |- context[CharArray.full ?out (?i + 1) (app ?ol (cons ?v nil))] =>
      Exists (app ol (cons v nil))
  end;
  entailer!;
  [ solve_encode_step_value
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_encode_entail_wit_1 : encode_entail_wit_1.
Proof.
  unfold encode_entail_wit_1.
  intros.
  pre_process.
  subst.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  lia.
Qed. 

Lemma proof_of_encode_entail_wit_2_1 : encode_entail_wit_2_1.
Proof. unfold encode_entail_wit_2_1; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_2 : encode_entail_wit_2_2.
Proof. unfold encode_entail_wit_2_2; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_3 : encode_entail_wit_2_3.
Proof. unfold encode_entail_wit_2_3; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_4 : encode_entail_wit_2_4.
Proof. unfold encode_entail_wit_2_4; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_5 : encode_entail_wit_2_5.
Proof. unfold encode_entail_wit_2_5; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_6 : encode_entail_wit_2_6.
Proof. unfold encode_entail_wit_2_6; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_7 : encode_entail_wit_2_7.
Proof. unfold encode_entail_wit_2_7; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_8 : encode_entail_wit_2_8.
Proof. unfold encode_entail_wit_2_8; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_9 : encode_entail_wit_2_9.
Proof. unfold encode_entail_wit_2_9; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_10 : encode_entail_wit_2_10.
Proof. unfold encode_entail_wit_2_10; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_11 : encode_entail_wit_2_11.
Proof. unfold encode_entail_wit_2_11; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_12 : encode_entail_wit_2_12.
Proof. unfold encode_entail_wit_2_12; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_13 : encode_entail_wit_2_13.
Proof. unfold encode_entail_wit_2_13; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_14 : encode_entail_wit_2_14.
Proof. unfold encode_entail_wit_2_14; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_entail_wit_2_15 : encode_entail_wit_2_15.
Proof. unfold encode_entail_wit_2_15; intros; solve_encode_step. Qed. 

Lemma proof_of_encode_return_wit_1 : encode_return_wit_1.
Proof.
  unfold encode_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  match goal with
  | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
  end.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  apply problem_93_spec_z_intro with (n := len); try lia; try assumption.
  intros k Hk.
  match goal with
  | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = encode_char_z (Znth k l 0) |- _ =>
      apply Hprefix; lia
  end.
Qed. 
