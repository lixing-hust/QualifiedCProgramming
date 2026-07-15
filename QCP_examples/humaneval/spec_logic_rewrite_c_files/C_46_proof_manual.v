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
From SimpleC.EE Require Import C_46_goal.
From SimpleC.EE Require Import C_46_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_46.
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

Ltac solve_fib4_vc :=
  pre_process; subst; entailer!;
  try match goal with
      | Hgt : ?i > ?n, Hle : ?i <= ?n + 1 |- _ =>
          replace i with (n + 1) in * by lia
      end;
  try match goal with
      | Heq : ?i = 4 |- _ =>
          replace i with 4 in * by lia
      end;
  repeat match goal with
  | |- context[Znth ?k (fib4_prefix_z ?len) 0] =>
      rewrite (fib4_prefix_znth_46 len k) by lia
  | H : context[Znth ?k (fib4_prefix_z ?len) 0] |- _ =>
      rewrite (fib4_prefix_znth_46 len k) in H by lia
  | |- context[fib4_prefix_z (?i + 1)] =>
      rewrite (fib4_prefix_z_snoc i) by lia
  | H : context[fib4_prefix_z (?i + 1)] |- _ =>
      rewrite (fib4_prefix_z_snoc i) in H by lia
  | |- context[fib4_z ?i] =>
      rewrite (fib4_z_step_46 i) by lia
  | H : context[fib4_z ?i] |- _ =>
      rewrite (fib4_z_step_46 i) in H by lia
  | Hlt : ?n < 4 |- context[fib4_fill_len_z ?n (?n + 1)] =>
      rewrite (fib4_fill_len_done_lt_46 n) by lia
  | Hlt : ?n < 4, H : context[fib4_fill_len_z ?n (?n + 1)] |- _ =>
      rewrite (fib4_fill_len_done_lt_46 n) in H by lia
  | Hge : 4 <= ?n |- context[fib4_fill_len_z ?n (?n + 1)] =>
      rewrite (fib4_fill_len_done_ge_46 n) by lia
  | Hge : 4 <= ?n, H : context[fib4_fill_len_z ?n (?n + 1)] |- _ =>
      rewrite (fib4_fill_len_done_ge_46 n) in H by lia
  | |- context[fib4_fill_len_z ?n 4] =>
      rewrite (fib4_fill_len_initial_46 n) by lia
  | H : context[fib4_fill_len_z ?n 4] |- _ =>
      rewrite (fib4_fill_len_initial_46 n) in H by lia
  | |- context[fib4_fill_len_z ?n (?i + 1)] =>
      rewrite (fib4_fill_len_after_step_46 n i) by lia
  | H : context[fib4_fill_len_z ?n (?i + 1)] |- _ =>
      rewrite (fib4_fill_len_after_step_46 n i) in H by lia
  | |- context[fib4_fill_len_z ?n ?i] =>
      rewrite (fib4_fill_len_loop_46 n i) by lia
  | H : context[fib4_fill_len_z ?n ?i] |- _ =>
      rewrite (fib4_fill_len_loop_46 n i) in H by lia
  end;
  repeat match goal with
  | |- context[?x - 0] => replace (x - 0) with x by lia
  | H : context[?x - 0] |- _ => replace (x - 0) with x in H by lia
  end;
  try match goal with
      | Hsafe : fib4_safe_z ?n |- context[fib4_z (?i - 1) + fib4_z (?i - 2) + fib4_z (?i - 3) + fib4_z (?i - 4)] =>
          pose proof (fib4_safe_z_bound_sum_46 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fib4_safe_z ?n, Hi1 : 4 <= ?i, Hi2 : ?i <= ?n |- _ =>
          pose proof (fib4_safe_z_bound_sum_46 n i Hsafe ltac:(lia));
          pose proof (fib4_z_bound_46 n (i - 1) Hsafe ltac:(lia));
          pose proof (fib4_z_bound_46 n (i - 2) Hsafe ltac:(lia));
          pose proof (fib4_z_bound_46 n (i - 3) Hsafe ltac:(lia));
          pose proof (fib4_z_bound_46 n (i - 4) Hsafe ltac:(lia))
      end;
  try match goal with
      | Hsafe : fib4_safe_z ?n |- context[fib4_z ?i] =>
          pose proof (fib4_z_bound_46 n i Hsafe ltac:(lia))
      end;
  try match goal with
      | |- (?p + ?lo * sizeof ( INT )) # Int |-> ?v |-- IntArray.seg ?p ?lo (?lo + 1) (?v :: nil) =>
          sep_apply (IntArray.seg_single p lo v); entailer!
      | |- (?p + ?lo * sizeof ( INT )) # Int |-> ?v |-- IntArray.seg ?p ?lo ?hi (?v :: nil) =>
          replace hi with (lo + 1) by lia;
          sep_apply (IntArray.seg_single p lo v); entailer!
      end;
  try match goal with
      | Hlo : 0 <= ?n |- _ |-- _ || _ =>
          destruct (Z_lt_ge_dec n 4);
          [left; entailer!; solve_model_pures
          | right; entailer!; solve_model_pures]
      end;
  try entailer!;
  try (apply problem_46_spec_z_from_fib4; lia);
  try lia.

Lemma proof_of_fib4_safety_wit_20 : fib4_safety_wit_20.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_safety_wit_21 : fib4_safety_wit_21.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_safety_wit_22 : fib4_safety_wit_22.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_1 : fib4_entail_wit_1.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_2 : fib4_entail_wit_2.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_3 : fib4_entail_wit_3.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_4 : fib4_entail_wit_4.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_5 : fib4_entail_wit_5.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_6 : fib4_entail_wit_6.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_7 : fib4_entail_wit_7.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_8 : fib4_entail_wit_8.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_9_1 : fib4_entail_wit_9_1.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_9_2 : fib4_entail_wit_9_2.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_10_1 : fib4_entail_wit_10_1.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_10_2 : fib4_entail_wit_10_2.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_entail_wit_11 : fib4_entail_wit_11.
Proof. solve_fib4_vc. Qed.
Lemma proof_of_fib4_return_wit_1 : fib4_return_wit_1.
Proof. solve_fib4_vc. Qed.
