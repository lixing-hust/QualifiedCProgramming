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
From SimpleC.EE Require Import C_148_goal.
From SimpleC.EE Require Import C_148_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_148.
Local Open Scope sac.

Ltac solve_scan_state_148 :=
  match goal with
  | |- planet_scan_state_148 ?p (?m + 1) ?pos =>
      match goal with
      | Hcmp : strcmp_result (planet_payload_148 ?i) p ?ret |- _ =>
          first
            [ match goal with
              | Hstate : planet_scan_state_148 p m pos |- _ =>
                  assert (m = i) by lia; subst m;
                  eapply planet_scan_state_148_step_miss_strcmp;
                  [ eassumption | lia | eassumption | exact Hcmp | lia ]
              end
            | match goal with
              | Hstate : planet_scan_state_148 p m ?old_pos |- _ =>
                  replace pos with m by lia;
                  assert (m = i) by lia; subst m;
                  eapply planet_scan_state_148_step_hit_strcmp;
                  [ eassumption | lia | eassumption | exact Hcmp | lia ]
              end ]
      end
  end.

Ltac solve_planet_literals_heap_148 :=
  right;
  pre_process_default;
  let Hsafe := fresh "Hplanet_payloads_string_safe_148" in
  pose proof planet_payloads_string_safe_148_proof as Hsafe;
  repeat match goal with
  | H : ?x = planet_ptr_148 LitMap _ |- _ => subst x
  | H : planet_ptr_148 LitMap _ = ?x |- _ => subst x
  end;
  unfold planet_literals_heap_148, string_lib.store_string;
  entailer!;
  try solve_scan_state_148.

Ltac assert_output_ptrs_before_lt_6_148 :=
  match goal with
  | H : output_state_148 LitMap ?lo ?hi ?k ?rows ?ptrs |- _ =>
      assert (Hlen : Zlength ptrs < 6);
      [ replace k with ((k + 1) - 1) in H by lia;
        eapply output_state_148_ptrs_length_before_lt_6 with (m := k + 1) (rows := rows);
        [lia | lia | exact H]
      | idtac ]
  end.

Ltac pose_scan_finals_148 :=
  match goal with
  | H1 : planet_scan_state_148 ?p1 ?m ?pos1,
    H2 : planet_scan_state_148 ?p2 ?m ?pos2 |- _ =>
      pose proof (planet_scan_state_148_final p1 m pos1 H1 ltac:(lia));
      pose proof (planet_scan_state_148_final p2 m pos2 H2 ltac:(lia))
  end.

Ltac assert_min_max_148 :=
  match goal with
  | Hgt : ?pos1 > ?pos2,
    Hpos1 : ?pos1 = planet_index_z_148 ?p1,
    Hpos2 : ?pos2 = planet_index_z_148 ?p2 |- _ =>
      assert (pos2 =
        planet_min_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_min_index_148; destruct (Z.leb_spec0 pos1 pos2); lia);
      assert (pos1 =
        planet_max_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_max_index_148; destruct (Z.leb_spec0 pos1 pos2); lia)
  | Hle : ?pos1 <= ?pos2,
    Hpos1 : ?pos1 = planet_index_z_148 ?p1,
    Hpos2 : ?pos2 = planet_index_z_148 ?p2 |- _ =>
      assert (pos1 =
        planet_min_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_min_index_148; destruct (Z.leb_spec0 pos1 pos2); lia);
      assert (pos2 =
        planet_max_index_148 (planet_index_z_148 p1) (planet_index_z_148 p2))
        by (rewrite <- Hpos1, <- Hpos2;
            unfold planet_max_index_148; destruct (Z.leb_spec0 pos1 pos2); lia)
  end.

Lemma proof_of_bf_entail_wit_1_split_goal_1 : bf_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_2 : bf_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_3 : bf_entail_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_4 : bf_entail_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_5 : bf_entail_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_6 : bf_entail_wit_1_split_goal_6.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_7 : bf_entail_wit_1_split_goal_7.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_8 : bf_entail_wit_1_split_goal_8.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1_split_goal_spatial : bf_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_1 : bf_entail_wit_1.
Proof.
  right.
  pre_process_default.
  pose proof planet_payloads_string_safe_148_proof as Hplanet_payloads_string_safe_148.
  sep_apply_l_atomic (GlobalStrings_split LitMap neptune_literal_148).
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (neptune_literal_148 :: nil) uranus_literal_148).
  { entailer!. vm_compute. intros [H|[]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (uranus_literal_148 :: neptune_literal_148 :: nil) saturn_literal_148).
  { entailer!. vm_compute. intros [H|[H|[]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) jupiter_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) mars_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[]]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (mars_literal_148 :: jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) earth_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (earth_literal_148 :: mars_literal_148 :: jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) venus_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[H|[H|[]]]]]]]; discriminate H. }
  sep_apply_l_atomic (GlobalStrings_missing_split LitMap (venus_literal_148 :: earth_literal_148 :: mars_literal_148 :: jupiter_literal_148 :: saturn_literal_148 :: uranus_literal_148 :: neptune_literal_148 :: nil) mercury_literal_148).
  { entailer!. vm_compute. intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; discriminate H. }
  unfold planet_literals_heap_148.
  sep_apply_l_atomic (mercury_lit_to_store_148 LitMap).
  sep_apply_l_atomic (venus_lit_to_store_148 LitMap).
  sep_apply_l_atomic (earth_lit_to_store_148 LitMap).
  sep_apply_l_atomic (mars_lit_to_store_148 LitMap).
  sep_apply_l_atomic (jupiter_lit_to_store_148 LitMap).
  sep_apply_l_atomic (saturn_lit_to_store_148 LitMap).
  sep_apply_l_atomic (uranus_lit_to_store_148 LitMap).
  sep_apply_l_atomic (neptune_lit_to_store_148 LitMap).
  unfold all_planet_literals_148.
  unfold planet_ptr_148, planet_literal_148.
  unfold mercury_literal_148, venus_literal_148, earth_literal_148, mars_literal_148.
  unfold jupiter_literal_148, saturn_literal_148, uranus_literal_148, neptune_literal_148.
  simpl.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_2_split_goal_1 : bf_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_bf_entail_wit_2_split_goal_2 : bf_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_bf_entail_wit_2_split_goal_spatial : bf_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_2 : bf_entail_wit_2.
Proof.
  right.
  pre_process_default.
  entailer!;
    apply planet_scan_state_148_init.
Qed.

Lemma proof_of_bf_entail_wit_3_split_goal_spatial : bf_entail_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_3 : bf_entail_wit_3.
Proof.
  left.
  pre_process_default.
  pose proof planet_payloads_string_safe_148_proof as Hplanet_payloads_string_safe_148.
  subst mercury venus earth mars jupiter saturn uranus neptune.
  unfold planet_literals_heap_148.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_4_1_split_goal_spatial : bf_entail_wit_4_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_1 : bf_entail_wit_4_1.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_2_split_goal_spatial : bf_entail_wit_4_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_2 : bf_entail_wit_4_2.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_3_split_goal_spatial : bf_entail_wit_4_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_3 : bf_entail_wit_4_3.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_4_split_goal_spatial : bf_entail_wit_4_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_4 : bf_entail_wit_4_4.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_5_split_goal_spatial : bf_entail_wit_4_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_5 : bf_entail_wit_4_5.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_6_split_goal_spatial : bf_entail_wit_4_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_6 : bf_entail_wit_4_6.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_7_split_goal_spatial : bf_entail_wit_4_7_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_7 : bf_entail_wit_4_7.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_8_split_goal_spatial : bf_entail_wit_4_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_8 : bf_entail_wit_4_8.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_9_split_goal_spatial : bf_entail_wit_4_9_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_9 : bf_entail_wit_4_9.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_10_split_goal_spatial : bf_entail_wit_4_10_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_10 : bf_entail_wit_4_10.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_11_split_goal_spatial : bf_entail_wit_4_11_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_11 : bf_entail_wit_4_11.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_12_split_goal_spatial : bf_entail_wit_4_12_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_12 : bf_entail_wit_4_12.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_13_split_goal_spatial : bf_entail_wit_4_13_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_13 : bf_entail_wit_4_13.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_14_split_goal_spatial : bf_entail_wit_4_14_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_14 : bf_entail_wit_4_14.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_15_split_goal_spatial : bf_entail_wit_4_15_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_15 : bf_entail_wit_4_15.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_16_split_goal_spatial : bf_entail_wit_4_16_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_16 : bf_entail_wit_4_16.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_17_split_goal_spatial : bf_entail_wit_4_17_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_17 : bf_entail_wit_4_17.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_18_split_goal_spatial : bf_entail_wit_4_18_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_18 : bf_entail_wit_4_18.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_19_split_goal_spatial : bf_entail_wit_4_19_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_19 : bf_entail_wit_4_19.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_20_split_goal_spatial : bf_entail_wit_4_20_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_20 : bf_entail_wit_4_20.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_21_split_goal_spatial : bf_entail_wit_4_21_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_21 : bf_entail_wit_4_21.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_22_split_goal_spatial : bf_entail_wit_4_22_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_22 : bf_entail_wit_4_22.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_23_split_goal_spatial : bf_entail_wit_4_23_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_23 : bf_entail_wit_4_23.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_24_split_goal_spatial : bf_entail_wit_4_24_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_24 : bf_entail_wit_4_24.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_25_split_goal_spatial : bf_entail_wit_4_25_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_25 : bf_entail_wit_4_25.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_26_split_goal_spatial : bf_entail_wit_4_26_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_26 : bf_entail_wit_4_26.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_27_split_goal_spatial : bf_entail_wit_4_27_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_27 : bf_entail_wit_4_27.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_28_split_goal_spatial : bf_entail_wit_4_28_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_28 : bf_entail_wit_4_28.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_29_split_goal_spatial : bf_entail_wit_4_29_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_29 : bf_entail_wit_4_29.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_30_split_goal_spatial : bf_entail_wit_4_30_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_30 : bf_entail_wit_4_30.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_31_split_goal_spatial : bf_entail_wit_4_31_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_31 : bf_entail_wit_4_31.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_4_32_split_goal_spatial : bf_entail_wit_4_32_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_entail_wit_4_32 : bf_entail_wit_4_32.
Proof. solve_planet_literals_heap_148. Qed.

Lemma proof_of_bf_entail_wit_6_1 : bf_entail_wit_6_1.
Proof.
  left.
  pre_process_default.
  pose_scan_finals_148.
  assert_min_max_148.
  Exists (@nil (list Z)) (@nil Z).
  subst out_size.
  replace (pos2 + 1 - 1) with pos2 by lia.
  assert (Hstate : output_state_148 LitMap pos2 pos1 pos2 (@nil (list Z)) (@nil Z)).
  { apply output_state_148_at_lower_empty; lia. }
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data 6).
  rewrite PtrArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_6_2 : bf_entail_wit_6_2.
Proof.
  left.
  pre_process_default.
  pose_scan_finals_148.
  assert_min_max_148.
  Exists (@nil (list Z)) (@nil Z).
  subst out_size.
  replace (pos1 + 1 - 1) with pos1 by lia.
  assert (Hstate : output_state_148 LitMap pos1 pos2 pos1 (@nil (list Z)) (@nil Z)).
  { apply output_state_148_at_lower_empty; lia. }
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data 6).
  rewrite PtrArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_1 : bf_entail_wit_7_1.
Proof.
  left.
  pre_process_default.
  assert (m = 1) by lia.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 1)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_2 : bf_entail_wit_7_2.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 2)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_3 : bf_entail_wit_7_3.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 3)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_4 : bf_entail_wit_7_4.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 4)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_5 : bf_entail_wit_7_5.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 5)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_7_6 : bf_entail_wit_7_6.
Proof.
  left.
  pre_process_default.
  subst m.
  assert (Hlen : Zlength output_ptrs_2 < 6).
  {
    eapply output_state_148_ptrs_length_before_lt_6
      with (LM := LitMap) (lo := lo) (hi := hi) (m := 6)
           (rows := output_rows_2);
      [lia | lia | match goal with H : output_state_148 _ _ _ _ _ _ |- _ => exact H end].
  }
  Exists output_rows_2 output_ptrs_2.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_8 : bf_entail_wit_8.
Proof.
  left.
  pre_process_default.
  Exists (output_rows_2 ++ (planet_payload_148 m :: nil))
         (output_ptrs_2 ++ (cur :: nil)).
  assert (Hstate :
    output_state_148 LitMap lo hi m
      (output_rows_2 ++ (planet_payload_148 m :: nil))
      (output_ptrs_2 ++ (cur :: nil))).
  {
    match goal with
    | Hcur : cur = planet_ptr_148 LitMap m |- _ => rewrite Hcur
    end.
    eapply output_state_148_step; try lia; eassumption.
  }
  assert (Hlen : out_size + 1 = Zlength (output_ptrs_2 ++ (cur :: nil))).
  {
    match goal with
    | Hout : out_size = Zlength output_ptrs_2 |- _ => rewrite Hout
    end.
    rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  }
  unfold store_string, string_lib.store_string.
  entailer!.
Qed.

Lemma proof_of_bf_entail_wit_9 : bf_entail_wit_9.
Proof.
  left.
  pre_process_default.
  Exists output_rows_2 output_ptrs_2.
  replace (m + 1 - 1) with m by lia.
  entailer!.
Qed.

Lemma proof_of_bf_return_wit_1_split_goal_1 : bf_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_2 : bf_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_3 : bf_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_4 : bf_return_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_5 : bf_return_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_6 : bf_return_wit_1_split_goal_6.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_7 : bf_return_wit_1_split_goal_7.
Proof. Abort.

Lemma proof_of_bf_return_wit_1_split_goal_spatial : bf_return_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_return_wit_1 : bf_return_wit_1.
Proof.
  right.
  pre_process_default.
  assert (Hidx1 : 0 <= planet_index_z_148 p1 <= 7).
  {
    destruct (planet_index_z_148_range p1) as [Hbad | Hok]; [| exact Hok].
    rewrite Hbad in *.
    unfold planet_min_index_148 in *.
    destruct (Z.leb_spec0 (-1) (planet_index_z_148 p2)); lia.
  }
  assert (Hidx2 : 0 <= planet_index_z_148 p2 <= 7).
  {
    destruct (planet_index_z_148_range p2) as [Hbad | Hok]; [| exact Hok].
    rewrite Hbad in *.
    unfold planet_min_index_148 in *.
    destruct (Z.leb_spec0 (planet_index_z_148 p1) (-1)); lia.
  }
  assert (Hle : lo <= hi).
  {
    match goal with
    | Hlo : lo = planet_min_index_148 _ _,
      Hhi : hi = planet_max_index_148 _ _ |- _ =>
        rewrite Hlo, Hhi;
        unfold planet_min_index_148, planet_max_index_148;
        destruct (Z.leb_spec0 (planet_index_z_148 p1) (planet_index_z_148 p2)); lia
    end.
  }
  pose proof (output_state_148_done_le LitMap p1 p2 lo hi m
    output_rows_2 output_ptrs_2 Hidx1 Hidx2 ltac:(lia) ltac:(lia) Hle
    ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(lia)
    ltac:(eassumption)) as [Hrows Hptrs].
  assert (Hout_rows :
    out_size =
    Zlength (planet_between_rows_148 (planet_index_z_148 p1) (planet_index_z_148 p2))).
  {
    match goal with
    | Hsize : out_size = Zlength output_ptrs_2 |- _ => rewrite Hsize
    end.
    rewrite Hptrs.
    rewrite <- planet_between_rows_ptrs_Zlength_148.
    reflexivity.
  }
  rewrite Hout_rows.
  rewrite Hptrs.
  entailer!;
    try solve
      [ apply problem_148_spec_z_between_valid_148; assumption
      | apply planet_between_rows_ptrs_Zlength_148
      | apply planet_between_rows_Zlength_bound_148
      | rewrite Hout_rows; reflexivity
      | lia ].
Qed.

Lemma proof_of_bf_return_wit_2_split_goal_1 : bf_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_2 : bf_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_3 : bf_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_4 : bf_return_wit_2_split_goal_4.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_5 : bf_return_wit_2_split_goal_5.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_6 : bf_return_wit_2_split_goal_6.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_7 : bf_return_wit_2_split_goal_7.
Proof. Abort.

Lemma proof_of_bf_return_wit_2_split_goal_spatial : bf_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_return_wit_2 : bf_return_wit_2.
Proof.
  right.
  pre_process_default.
  assert (Hbad : planet_index_z_148 p1 = -1).
  {
    eapply planet_scan_state_148_invalid; eauto; lia.
  }
  pose proof (planet_between_rows_invalid_left_148 p1 (planet_index_z_148 p2) Hbad)
    as [Hrows Hptrs].
  rewrite Hrows, Hptrs.
  simpl.
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data_2 6).
  rewrite PtrArray.seg_empty.
  entailer!;
    try solve
      [ apply problem_148_spec_z_invalid_left_148; exact Hbad
      | apply planet_between_rows_ptrs_Zlength_148
      | apply planet_between_rows_Zlength_bound_148
      | rewrite Zlength_nil; lia
      | lia ].
Qed.

Lemma proof_of_bf_return_wit_3_split_goal_1 : bf_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_2 : bf_return_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_3 : bf_return_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_4 : bf_return_wit_3_split_goal_4.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_5 : bf_return_wit_3_split_goal_5.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_6 : bf_return_wit_3_split_goal_6.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_7 : bf_return_wit_3_split_goal_7.
Proof. Abort.

Lemma proof_of_bf_return_wit_3_split_goal_spatial : bf_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_bf_return_wit_3 : bf_return_wit_3.
Proof.
  right.
  pre_process_default.
  assert (Hbad : planet_index_z_148 p2 = -1).
  {
    eapply planet_scan_state_148_invalid; eauto; lia.
  }
  pose proof (planet_between_rows_invalid_right_148 (planet_index_z_148 p1) p2 Hbad)
    as [Hrows Hptrs].
  rewrite Hrows, Hptrs.
  simpl.
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg data_2 6).
  rewrite PtrArray.seg_empty.
  entailer!;
    try solve
      [ apply problem_148_spec_z_invalid_right_148; exact Hbad
      | apply planet_between_rows_ptrs_Zlength_148
      | apply planet_between_rows_Zlength_bound_148
      | rewrite Zlength_nil; lia
      | lia ].
Qed.

Ltac solve_bf_string_pure_148 :=
  left;
  pre_process_default;
  unfold planet_payloads_string_safe_148 in *;
  entailer!.

Lemma proof_of_bf_partial_solve_wit_3_pure : bf_partial_solve_wit_3_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_4_pure : bf_partial_solve_wit_4_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_5_pure : bf_partial_solve_wit_5_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_6_pure : bf_partial_solve_wit_6_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_7_pure : bf_partial_solve_wit_7_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_8_pure : bf_partial_solve_wit_8_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_9_pure : bf_partial_solve_wit_9_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_10_pure : bf_partial_solve_wit_10_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_11_pure : bf_partial_solve_wit_11_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_12_pure : bf_partial_solve_wit_12_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_13_pure : bf_partial_solve_wit_13_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_14_pure : bf_partial_solve_wit_14_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_15_pure : bf_partial_solve_wit_15_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_16_pure : bf_partial_solve_wit_16_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_17_pure : bf_partial_solve_wit_17_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_18_pure : bf_partial_solve_wit_18_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_19_pure : bf_partial_solve_wit_19_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_20_pure : bf_partial_solve_wit_20_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_21_pure : bf_partial_solve_wit_21_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_22_pure : bf_partial_solve_wit_22_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_23_pure : bf_partial_solve_wit_23_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_24_pure : bf_partial_solve_wit_24_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_25_pure : bf_partial_solve_wit_25_pure.
Proof. solve_bf_string_pure_148. Qed.

Lemma proof_of_bf_partial_solve_wit_26_pure : bf_partial_solve_wit_26_pure.
Proof. solve_bf_string_pure_148. Qed.
