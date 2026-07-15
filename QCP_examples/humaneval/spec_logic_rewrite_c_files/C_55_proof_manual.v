Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_55_goal.
From SimpleC.EE Require Import C_55_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_55.
Local Open Scope sac.

Ltac solve_model_pures :=
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption;
  try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; try lia; try assumption
  end.

Ltac solve_fib_vc :=
  pre_process; subst; entailer!;
  try match goal with
      | Hgt : ?i > ?n, Hle : ?i <= ?n + 1 |- _ =>
          replace i with (n + 1) in * by lia
      end;
  try match goal with
      | Heq : ?i = 2 |- _ =>
          replace i with 2 in * by lia
      end;
  repeat match goal with
  | |- context[Znth ?k (fib_prefix_z ?len) 0] =>
      rewrite (fib_prefix_znth_55 len k) by lia
  | H : context[Znth ?k (fib_prefix_z ?len) 0] |- _ =>
      rewrite (fib_prefix_znth_55 len k) in H by lia
  | |- context[fib_prefix_z (?i + 1)] =>
      rewrite (fib_prefix_z_snoc i) by lia
  | H : context[fib_prefix_z (?i + 1)] |- _ =>
      rewrite (fib_prefix_z_snoc i) in H by lia
  | |- context[fib_z ?i] =>
      rewrite (fib_z_step_55 i) by lia
  | H : context[fib_z ?i] |- _ =>
      rewrite (fib_z_step_55 i) in H by lia
  | Hlt : ?n < 2 |- context[fib_fill_len_z ?n (?n + 1)] =>
      rewrite (fib_fill_len_done_lt_55 n) by lia
  | Hlt : ?n < 2, H : context[fib_fill_len_z ?n (?n + 1)] |- _ =>
      rewrite (fib_fill_len_done_lt_55 n) in H by lia
  | Hge : 2 <= ?n |- context[fib_fill_len_z ?n (?n + 1)] =>
      rewrite (fib_fill_len_done_ge_55 n) by lia
  | Hge : 2 <= ?n, H : context[fib_fill_len_z ?n (?n + 1)] |- _ =>
      rewrite (fib_fill_len_done_ge_55 n) in H by lia
  | |- context[fib_fill_len_z ?n 2] =>
      rewrite (fib_fill_len_initial_55 n) by lia
  | H : context[fib_fill_len_z ?n 2] |- _ =>
      rewrite (fib_fill_len_initial_55 n) in H by lia
  | |- context[fib_fill_len_z ?n (?i + 1)] =>
      rewrite (fib_fill_len_after_step_55 n i) by lia
  | H : context[fib_fill_len_z ?n (?i + 1)] |- _ =>
      rewrite (fib_fill_len_after_step_55 n i) in H by lia
  | |- context[fib_fill_len_z ?n ?i] =>
      rewrite (fib_fill_len_loop_55 n i) by lia
  | H : context[fib_fill_len_z ?n ?i] |- _ =>
      rewrite (fib_fill_len_loop_55 n i) in H by lia
  end;
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  | H : context[?x - 0] |- _ => replace (x - 0) with x in H by lia
  end;
  try match goal with
      | Hsafe : fib_safe_z ?n |- context[fib_z (?i - 1) + fib_z (?i - 2)] =>
          pose proof (fib_safe_z_bound_sum_55 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fib_safe_z ?n, Hi1 : 2 <= ?i, Hi2 : ?i <= ?n |- _ =>
          pose proof (fib_safe_z_bound_sum_55 n i Hsafe ltac:(lia));
          pose proof (fib_z_bound_55 n (i - 1) Hsafe ltac:(lia));
          pose proof (fib_z_bound_55 n (i - 2) Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fib_safe_z ?n |- context[fib_z ?i] =>
          pose proof (fib_z_bound_55 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | |- (?p + ?lo * sizeof ( INT )) # Int |-> ?v |-- IntArray.seg ?p ?lo (?lo + 1) (?v :: nil) =>
          sep_apply (IntArray.seg_single p lo v); entailer!
      | |- (?p + ?lo * sizeof ( INT )) # Int |-> ?v |-- IntArray.seg ?p ?lo ?hi (?v :: nil) =>
          replace hi with (lo + 1) by lia;
          sep_apply (IntArray.seg_single p lo v); entailer!
      end;
  try match goal with
      | |- (?p + 1 * sizeof ( INT )) # Int |-> 1 **
           (IntArray.undef_seg ?p (1 + 1) 1000 **
            (?p + 0 * sizeof ( INT )) # Int |-> 0)
           |-- IntArray.seg ?p 0 2 (fib_prefix_z 2) **
               IntArray.undef_seg ?p 2 1000 =>
          rewrite fib_prefix_0_2;
          sep_apply (IntArray.seg_single p 1 1);
          sep_apply (IntArray.seg_single p 0 0);
          sep_apply (IntArray.seg_merge_to_seg p 0 1 2); [ | lia];
          entailer!
      end;
  try match goal with
      | Hlo : 0 <= ?n |- _ |-- _ || _ =>
          destruct (Z_lt_ge_dec n 2);
          [left; entailer!; solve_model_pures
          | right; entailer!; solve_model_pures]
      end;
  try entailer!;
  try (apply problem_55_spec_z_from_fib; lia);
  try lia.

Lemma proof_of_fib_safety_wit_12 : fib_safety_wit_12.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_1 : fib_entail_wit_1.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_2 : fib_entail_wit_2.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_3 : fib_entail_wit_3.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_4 : fib_entail_wit_4.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_5 : fib_entail_wit_5.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_6_1 : fib_entail_wit_6_1.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_6_2 : fib_entail_wit_6_2.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_7_1 : fib_entail_wit_7_1.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_7_2 : fib_entail_wit_7_2.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_entail_wit_8 : fib_entail_wit_8.
Proof. solve_fib_vc. Qed.

Lemma proof_of_fib_return_wit_1 : fib_return_wit_1.
Proof. solve_fib_vc. Qed.
