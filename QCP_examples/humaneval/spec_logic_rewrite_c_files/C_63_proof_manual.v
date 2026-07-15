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
From SimpleC.EE Require Import C_63_goal.
From SimpleC.EE Require Import C_63_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_63.
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

Ltac solve_fibfib_vc :=
  pre_process; subst; entailer!;
  try match goal with
      | Hgt : ?i > ?n, Hle : ?i <= ?n + 1 |- _ =>
          replace i with (n + 1) in * by lia
      end;
  try match goal with
      | Heq : ?i = 3 |- _ =>
          replace i with 3 in * by lia
      end;
  repeat match goal with
  | |- context[Znth ?k (fibfib_prefix_z ?len) 0] =>
      rewrite (fibfib_prefix_znth_63 len k) by lia
  | H : context[Znth ?k (fibfib_prefix_z ?len) 0] |- _ =>
      rewrite (fibfib_prefix_znth_63 len k) in H by lia
  | |- context[fibfib_prefix_z (?i + 1)] =>
      rewrite (fibfib_prefix_z_snoc i) by lia
  | H : context[fibfib_prefix_z (?i + 1)] |- _ =>
      rewrite (fibfib_prefix_z_snoc i) in H by lia
  | |- context[fibfib_z ?i] =>
      rewrite (fibfib_z_step_63 i) by lia
  | H : context[fibfib_z ?i] |- _ =>
      rewrite (fibfib_z_step_63 i) in H by lia
  | Hlt : ?n < 3 |- context[fibfib_fill_len_z ?n (?n + 1)] =>
      rewrite (fibfib_fill_len_done_lt_63 n) by lia
  | Hlt : ?n < 3, H : context[fibfib_fill_len_z ?n (?n + 1)] |- _ =>
      rewrite (fibfib_fill_len_done_lt_63 n) in H by lia
  | Hge : 3 <= ?n |- context[fibfib_fill_len_z ?n (?n + 1)] =>
      rewrite (fibfib_fill_len_done_ge_63 n) by lia
  | Hge : 3 <= ?n, H : context[fibfib_fill_len_z ?n (?n + 1)] |- _ =>
      rewrite (fibfib_fill_len_done_ge_63 n) in H by lia
  | |- context[fibfib_fill_len_z ?n 3] =>
      rewrite (fibfib_fill_len_initial_63 n) by lia
  | H : context[fibfib_fill_len_z ?n 3] |- _ =>
      rewrite (fibfib_fill_len_initial_63 n) in H by lia
  | |- context[fibfib_fill_len_z ?n (?i + 1)] =>
      rewrite (fibfib_fill_len_after_step_63 n i) by lia
  | H : context[fibfib_fill_len_z ?n (?i + 1)] |- _ =>
      rewrite (fibfib_fill_len_after_step_63 n i) in H by lia
  | |- context[fibfib_fill_len_z ?n ?i] =>
      rewrite (fibfib_fill_len_loop_63 n i) by lia
  | H : context[fibfib_fill_len_z ?n ?i] |- _ =>
      rewrite (fibfib_fill_len_loop_63 n i) in H by lia
  end;
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  | H : context[?x - 0] |- _ => replace (x - 0) with x in H by lia
  end;
  try match goal with
      | Hsafe : fibfib_safe_z ?n |- context[fibfib_z (?i - 1) + fibfib_z (?i - 2) + fibfib_z (?i - 3)] =>
          pose proof (fibfib_safe_z_bound_sum_63 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fibfib_safe_z ?n |- context[fibfib_z (?i - 1) + fibfib_z (?i - 2)] =>
          pose proof (fibfib_safe_z_bound_pair_sum_63 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fibfib_safe_z ?n, Hi1 : 3 <= ?i, Hi2 : ?i <= ?n |- _ =>
          pose proof (fibfib_safe_z_bound_sum_63 n i Hsafe ltac:(lia));
          pose proof (fibfib_safe_z_bound_pair_sum_63 n i Hsafe ltac:(lia));
          pose proof (fibfib_z_bound_63 n (i - 1) Hsafe ltac:(lia));
          pose proof (fibfib_z_bound_63 n (i - 2) Hsafe ltac:(lia));
          pose proof (fibfib_z_bound_63 n (i - 3) Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fibfib_safe_z ?n |- context[fibfib_z ?i] =>
          pose proof (fibfib_z_bound_63 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | |- (?p + ?lo * sizeof ( INT )) # Int |-> ?v |-- IntArray.seg ?p ?lo (?lo + 1) (?v :: nil) =>
          sep_apply (IntArray.seg_single p lo v); entailer!
      | |- (?p + ?lo * sizeof ( INT )) # Int |-> ?v |-- IntArray.seg ?p ?lo ?hi (?v :: nil) =>
          replace hi with (lo + 1) by lia;
          sep_apply (IntArray.seg_single p lo v); entailer!
      end;
  try match goal with
      | |- (?p + 2 * sizeof ( INT )) # Int |-> 1 **
           (IntArray.undef_seg ?p (2 + 1) 100 **
            ((?p + 1 * sizeof ( INT )) # Int |-> 0 **
             (?p + 0 * sizeof ( INT )) # Int |-> 0))
           |-- IntArray.seg ?p 0 3 (fibfib_prefix_z 3) **
               IntArray.undef_seg ?p 3 100 =>
          rewrite fibfib_prefix_0_3;
          sep_apply (IntArray.seg_single p 2 1);
          sep_apply (IntArray.seg_single p 1 0);
          sep_apply (IntArray.seg_single p 0 0);
          sep_apply (IntArray.seg_merge_to_seg p 0 1 2); [ | lia];
          sep_apply (IntArray.seg_merge_to_seg p 0 2 3); [ | lia];
          entailer!
      end;
  try match goal with
      | Hi : 3 <= ?i, Hle : ?i <= ?n |- _ |-- _ || _ =>
          right;
          rewrite (fibfib_fill_len_after_step_63 n i) by lia;
          entailer!;
          solve_model_pures
      end;
  try match goal with
      | Hlo : 0 <= ?n |- _ |-- _ || _ =>
          destruct (Z_lt_ge_dec n 3);
          [left; entailer!; solve_model_pures
          | right; entailer!; solve_model_pures]
      end;
  try entailer!;
  try (apply problem_63_spec_z_from_fibfib; lia);
  try lia.

Lemma proof_of_fibfib_safety_wit_16 : fibfib_safety_wit_16.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_safety_wit_17 : fibfib_safety_wit_17.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_1 : fibfib_entail_wit_1.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_2 : fibfib_entail_wit_2.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_3 : fibfib_entail_wit_3.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_4 : fibfib_entail_wit_4.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_5 : fibfib_entail_wit_5.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_6 : fibfib_entail_wit_6.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_7 : fibfib_entail_wit_7.
Proof.
  pre_process; subst; entailer!.
  right.
  rewrite (fibfib_fill_len_after_step_63 n0 i) by lia.
  entailer!.
  solve_model_pures.
Qed.

Lemma proof_of_fibfib_entail_wit_8_1 : fibfib_entail_wit_8_1.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_8_2 : fibfib_entail_wit_8_2.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_9_1 : fibfib_entail_wit_9_1.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_9_2 : fibfib_entail_wit_9_2.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_entail_wit_10 : fibfib_entail_wit_10.
Proof. solve_fibfib_vc. Qed.

Lemma proof_of_fibfib_return_wit_1 : fibfib_return_wit_1.
Proof. solve_fibfib_vc. Qed.
