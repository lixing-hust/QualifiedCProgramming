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
Require Import C_79_goal.
Require Import C_79_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_79.
Local Open Scope sac.

Ltac normalize_79 :=
  repeat match goal with
  | |- context[?x ÷ ?y] =>
      rewrite (Z.quot_div_nonneg x y) by lia
  | H : context[?x ÷ ?y] |- _ =>
      rewrite (Z.quot_div_nonneg x y) in H by lia
  | |- context[signed_last_nbits ?x 8] =>
      rewrite (signed_last_nbits_eq x 8) by
        (try change (2 ^ (8 - 1)) with 128; lia)
  | H : context[signed_last_nbits ?x 8] |- _ =>
      rewrite (signed_last_nbits_eq x 8) in H by
        (try change (2 ^ (8 - 1)) with 128; lia)
  | |- context[signed_last_nbits ?x 32] =>
      rewrite (signed_last_nbits_eq x 32) by
        (try change (2 ^ (32 - 1)) with 2147483648; lia)
  | H : context[signed_last_nbits ?x 32] |- _ =>
      rewrite (signed_last_nbits_eq x 32) in H by
        (try change (2 ^ (32 - 1)) with 2147483648; lia)
  end.

Ltac expose_79 :=
  repeat match goal with
  | H : binary_safe_79 _ |- _ => unfold binary_safe_79 in H
  end;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac unfold_states_79 :=
  repeat match goal with
  | H : binary_count_state_z_79 _ _ _ |- _ =>
      unfold binary_count_state_z_79 in H
  | H : binary_divisor_state_z_79 _ _ _ |- _ =>
      unfold binary_divisor_state_z_79 in H
  | H : binary_write_state_z_79 _ _ _ _ _ |- _ =>
      unfold binary_write_state_z_79 in H
  end;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac use_safe_steps_79 :=
  match goal with
  | Hstep : forall x bits,
      binary_count_state_z_79 ?d x bits ->
      0 < x ->
      binary_count_state_z_79 ?d (x / 2) (bits + 1),
    Hst : binary_count_state_z_79 ?d ?x ?bits,
    Hpos : 0 < ?x
    |- binary_count_state_z_79 ?d (?x / 2) (?bits + 1) =>
      eapply Hstep; eauto
  | Hdone : forall bits,
      0 < ?d ->
      binary_count_state_z_79 ?d 0 bits ->
      bits = binary_length_z_79 ?d,
    Hst : binary_count_state_z_79 ?d 0 ?bits,
    Hpos : 0 < ?d
    |- ?bits = binary_length_z_79 ?d =>
      eapply Hdone; eauto
  | Hstep : forall i divisor,
      binary_divisor_state_z_79 ?d i divisor ->
      i < binary_length_z_79 ?d ->
      divisor * 2 <= INT_MAX /\
      binary_divisor_state_z_79 ?d (i + 1) (divisor * 2),
    Hst : binary_divisor_state_z_79 ?d ?i ?divisor,
    Hbits : ?bits = binary_length_z_79 ?d,
    Hlt : ?i < ?bits
    |- ?divisor * 2 <= INT_MAX =>
      destruct (Hstep i divisor Hst ltac:(lia)) as [? _]; lia
  | Hstep : forall i divisor,
      binary_divisor_state_z_79 ?d i divisor ->
      i < binary_length_z_79 ?d ->
      divisor * 2 <= INT_MAX /\
      binary_divisor_state_z_79 ?d (i + 1) (divisor * 2),
    Hst : binary_divisor_state_z_79 ?d ?i ?divisor,
    Hbits : ?bits = binary_length_z_79 ?d,
    Hlt : ?i < ?bits
    |- binary_divisor_state_z_79 ?d (?i + 1) (?divisor * 2) =>
      destruct (Hstep i divisor Hst ltac:(lia)) as [_ ?]; auto
  end.

Ltac use_write_one_79 :=
  match goal with
  | Hsafe : binary_safe_79 ?d,
    Hst : binary_write_state_z_79 ?d ?rem ?divisor ?pos ?out_l,
    Hpos : 0 < ?divisor,
    Hle : ?divisor <= ?rem
    |- binary_write_state_z_79 ?d (?rem - ?divisor) (?divisor / 2)
         (?pos + 1) (?out_l ++ [49]) =>
      let Hcopy := fresh "Hsafe_copy" in
      pose proof Hsafe as Hcopy;
      unfold binary_safe_79 in Hcopy;
      destruct Hcopy as [_ [_ [_ [_ [_ [_ [_ [Hone _]]]]]]]];
      destruct (Hone rem divisor pos out_l Hst Hpos Hle) as [_ Hnext];
      exact Hnext
  | Hsafe : binary_safe_79 ?d,
    Hst : binary_write_state_z_79 ?d ?rem ?divisor ?pos ?out_l,
    Hpos : 0 < ?divisor,
    Hlt : ?rem < ?divisor
    |- binary_write_state_z_79 ?d ?rem (?divisor / 2)
         (?pos + 1) (?out_l ++ [48]) =>
      let Hcopy := fresh "Hsafe_copy" in
      pose proof Hsafe as Hcopy;
      unfold binary_safe_79 in Hcopy;
      destruct Hcopy as [_ [_ [_ [_ [_ [_ [_ [_ [Hzero _]]]]]]]]];
      destruct (Hzero rem divisor pos out_l Hst Hpos Hlt) as [_ Hnext];
      exact Hnext
  | Hsafe : binary_safe_79 ?d,
    Hst : binary_write_state_z_79 ?d ?rem ?divisor ?pos ?out_l,
    Hpos : 0 < ?divisor,
    Hle : ?divisor <= ?rem
    |- (?pos + 1) <= ?bits + 2 =>
      let Hcopy := fresh "Hsafe_copy" in
      pose proof Hsafe as Hcopy;
      unfold binary_safe_79 in Hcopy;
      destruct Hcopy as [_ [_ [_ [_ [_ [_ [_ [Hone _]]]]]]]];
      destruct (Hone rem divisor pos out_l Hst Hpos Hle) as [_ Hnext];
      unfold binary_write_state_z_79 in Hnext; intuition lia
  | Hsafe : binary_safe_79 ?d,
    Hst : binary_write_state_z_79 ?d ?rem ?divisor ?pos ?out_l,
    Hpos : 0 < ?divisor,
    Hlt : ?rem < ?divisor
    |- (?pos + 1) <= ?bits + 2 =>
      let Hcopy := fresh "Hsafe_copy" in
      pose proof Hsafe as Hcopy;
      unfold binary_safe_79 in Hcopy;
      destruct Hcopy as [_ [_ [_ [_ [_ [_ [_ [_ [Hzero _]]]]]]]]];
      destruct (Hzero rem divisor pos out_l Hst Hpos Hlt) as [_ Hnext];
      unfold binary_write_state_z_79 in Hnext; intuition lia
  end.

Ltac solve_79_core :=
  pre_process;
  subst;
  simpl in *;
  normalize_79;
  try solve [entailer!; eauto; subst; simpl in *; normalize_79; lia];
  expose_79;
  subst;
  simpl in *;
  normalize_79;
  try solve [entailer!; normalize_79; use_safe_steps_79];
  try solve [
    entailer!;
    try rewrite Zlength_app;
    try rewrite Zlength_cons;
    try rewrite Zlength_nil;
    normalize_79;
    try use_write_one_79;
    lia
  ];
  try solve [entailer!; eauto; subst; simpl in *; normalize_79; lia];
  unfold_states_79;
  subst;
  simpl in *;
  normalize_79;
  try solve [entailer!; eauto; subst; simpl in *; normalize_79; lia];
  try solve [entailer!; eauto; subst; simpl in *; normalize_79; cancel].

Ltac solve_79 :=
  first [
    solve [left; solve_79_core] |
    solve [right; solve_79_core] |
    solve [solve_79_core]
  ].

Lemma binary_safe_append_tail_79 :
  forall decimal out_l,
    binary_safe_79 decimal ->
    out_l = app (cons 100 (cons 98 nil)) (binary_payload_z_79 decimal) ->
    app out_l (cons 100 (cons 98 nil)) =
    decorated_binary_output_z_79 decimal.
Proof.
  intros decimal out_l Hsafe Hout.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Happend _]]]]]]]]]]].
  exact (Happend out_l Hout).
Qed.

Lemma binary_safe_decorated_length_79 :
  forall decimal,
    binary_safe_79 decimal ->
    0 < decimal ->
    Zlength (decorated_binary_output_z_79 decimal) =
    binary_length_z_79 decimal + 4.
Proof.
  intros decimal Hsafe Hpos.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]]]]]]].
  exact (Hlen (decorated_binary_output_z_79 decimal) Hpos eq_refl).
Qed.

Lemma binary_safe_decorated_spec_79 :
  forall decimal,
    binary_safe_79 decimal ->
    problem_79_spec_z decimal (decorated_binary_output_z_79 decimal).
Proof.
  intros decimal Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hspec]]]]]]]]]]]]].
  exact (Hspec (decorated_binary_output_z_79 decimal) eq_refl).
Qed.

Lemma append_tail_with_zero_79 :
  forall out_l decorated,
    app out_l (cons 100 (cons 98 nil)) = decorated ->
    app (app (app out_l (cons 100 nil)) (cons 98 nil)) (cons 0 nil) =
    app decorated (cons 0 nil).
Proof.
  intros out_l decorated Htail.
  subst decorated.
  induction out_l; simpl; congruence.
Qed.

Lemma proof_of_decimal_to_binary_safety_wit_21_split_goal_1 : decimal_to_binary_safety_wit_21_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_21_split_goal_2 : decimal_to_binary_safety_wit_21_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_21 : decimal_to_binary_safety_wit_21.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_39_split_goal_1 : decimal_to_binary_safety_wit_39_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_39_split_goal_2 : decimal_to_binary_safety_wit_39_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_39 : decimal_to_binary_safety_wit_39.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_44_split_goal_1 : decimal_to_binary_safety_wit_44_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_44_split_goal_2 : decimal_to_binary_safety_wit_44_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_44 : decimal_to_binary_safety_wit_44.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_49_split_goal_1 : decimal_to_binary_safety_wit_49_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_49_split_goal_2 : decimal_to_binary_safety_wit_49_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_49 : decimal_to_binary_safety_wit_49.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_safety_wit_52_split_goal_1 : decimal_to_binary_safety_wit_52_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_52_split_goal_2 : decimal_to_binary_safety_wit_52_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_safety_wit_52 : decimal_to_binary_safety_wit_52.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_1_split_goal_1 : decimal_to_binary_entail_wit_1_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_1 : decimal_to_binary_entail_wit_1.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_2_split_goal_1 : decimal_to_binary_entail_wit_2_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_2_split_goal_1.
  intros. pre_process. normalize_79. entailer!.
  unfold binary_safe_79 in PreH11.
  destruct PreH11 as [_ [Hstep _]].
  eapply Hstep; eauto.
  lia.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_2_split_goal_2 : decimal_to_binary_entail_wit_2_split_goal_2.
Proof.
  unfold decimal_to_binary_entail_wit_2_split_goal_2.
  intros. pre_process.
  replace (x ÷ 2) with (x / 2).
  - entailer!. apply Z.div_pos; lia.
  - symmetry. apply Z.quot_div_nonneg; lia.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_2 : decimal_to_binary_entail_wit_2.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_2.
  intros. pre_process. normalize_79. entailer!.
  - unfold binary_safe_79 in PreH11.
    destruct PreH11 as [_ [Hstep _]].
    eapply Hstep; eauto. lia.
  - replace (x ÷ 2) with (x / 2).
    + apply Z.div_pos; lia.
    + symmetry. apply Z.quot_div_nonneg; lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_3_split_goal_1 : decimal_to_binary_entail_wit_3_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_3_split_goal_1.
  intros. pre_process. entailer!.
  assert (Hx0 : x = 0) by lia. subst x.
  unfold binary_safe_79 in PreH11.
  destruct PreH11 as [_ [_ [Hdone _]]].
  eapply Hdone; eauto.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_3 : decimal_to_binary_entail_wit_3.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_3.
  intros. pre_process. entailer!.
  assert (Hx0 : x = 0) by lia. subst x.
  unfold binary_safe_79 in PreH11.
  destruct PreH11 as [_ [_ [Hdone _]]].
  eapply Hdone; eauto.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_4_split_goal_1 : decimal_to_binary_entail_wit_4_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_4_split_goal_2 : decimal_to_binary_entail_wit_4_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_4 : decimal_to_binary_entail_wit_4.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_6_split_goal_1 : decimal_to_binary_entail_wit_6_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_6_split_goal_1.
  intros. pre_process. entailer!.
  unfold binary_safe_79 in PreH14.
  destruct PreH14 as [_ [_ [_ [_ [_ [Hstep _]]]]]].
  destruct (Hstep i divisor PreH16 ltac:(lia)) as [Hbound _].
  exact Hbound.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_6 : decimal_to_binary_entail_wit_6.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_6.
  intros. pre_process. entailer!.
  unfold binary_safe_79 in PreH14.
  destruct PreH14 as [_ [_ [_ [_ [_ [Hstep _]]]]]].
  destruct (Hstep i divisor PreH16 ltac:(lia)) as [Hbound _].
  exact Hbound.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_7_split_goal_1 : decimal_to_binary_entail_wit_7_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_7_split_goal_1.
  intros. pre_process. entailer!.
  unfold binary_safe_79 in PreH14.
  destruct PreH14 as [_ [_ [_ [_ [_ [Hstep _]]]]]].
  destruct (Hstep i divisor PreH16 ltac:(lia)) as [_ Hnext].
  exact Hnext.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_7 : decimal_to_binary_entail_wit_7.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_7.
  intros. pre_process. entailer!.
  unfold binary_safe_79 in PreH14.
  destruct PreH14 as [_ [_ [_ [_ [_ [Hstep _]]]]]].
  destruct (Hstep i divisor PreH16 ltac:(lia)) as [_ Hnext].
  exact Hnext.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_8_split_goal_1 : decimal_to_binary_entail_wit_8_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_8_split_goal_1.
  intros. pre_process. entailer!.
  replace i with bits in PreH16 by lia.
  exact PreH16.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_8 : decimal_to_binary_entail_wit_8.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_8.
  intros. pre_process. entailer!.
  replace i with bits in PreH16 by lia.
  exact PreH16.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_10 : decimal_to_binary_entail_wit_10.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_10.
  intros. pre_process.
  Exists (100 :: 98 :: nil).
  pose proof PreH16 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [Hwrite _]]]]]]].
  rewrite PreH4 in PreH9.
  pose proof (Hwrite divisor PreH1 PreH9) as Hwrite_state.
  rewrite (CharArray.full_unfold out 2 (98 :: nil) 100).
  rewrite (CharArray.seg_unfold out 1 2 nil 98).
  rewrite (CharArray.seg_empty out 2 2).
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_11_split_goal_1 : decimal_to_binary_entail_wit_11_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_11_split_goal_2 : decimal_to_binary_entail_wit_11_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_11 : decimal_to_binary_entail_wit_11.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_13_split_goal_1 : decimal_to_binary_entail_wit_13_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_13_split_goal_1.
  intros. pre_process.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_13_split_goal_2 : decimal_to_binary_entail_wit_13_split_goal_2.
Proof.
  unfold decimal_to_binary_entail_wit_13_split_goal_2.
  intros. pre_process. normalize_79. entailer!.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [Hone _]]]]]]]].
  destruct (Hone decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
  exact Hnext.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_13_split_goal_3 : decimal_to_binary_entail_wit_13_split_goal_3.
Proof.
  unfold decimal_to_binary_entail_wit_13_split_goal_3.
  intros. pre_process. normalize_79. entailer!.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [Hone _]]]]]]]].
  destruct (Hone decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
  unfold binary_write_state_z_79 in Hnext. intuition lia.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_13 : decimal_to_binary_entail_wit_13.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_13.
  intros. pre_process. normalize_79.
  Exists (app out_l_2 (cons 49 nil)).
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - pose proof PreH14 as Hsafe.
    unfold binary_safe_79 in Hsafe.
    destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [Hone _]]]]]]]].
    destruct (Hone decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
    exact Hnext.
  - pose proof PreH14 as Hsafe.
    unfold binary_safe_79 in Hsafe.
    destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [Hone _]]]]]]]].
    destruct (Hone decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
    unfold binary_write_state_z_79 in Hnext. intuition lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_15_split_goal_1 : decimal_to_binary_entail_wit_15_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_15_split_goal_1.
  intros. pre_process.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_15_split_goal_2 : decimal_to_binary_entail_wit_15_split_goal_2.
Proof.
  unfold decimal_to_binary_entail_wit_15_split_goal_2.
  intros. pre_process. normalize_79. entailer!.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [Hzero _]]]]]]]]].
  destruct (Hzero decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
  exact Hnext.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_15_split_goal_3 : decimal_to_binary_entail_wit_15_split_goal_3.
Proof.
  unfold decimal_to_binary_entail_wit_15_split_goal_3.
  intros. pre_process. normalize_79. entailer!.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [Hzero _]]]]]]]]].
  destruct (Hzero decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
  unfold binary_write_state_z_79 in Hnext. intuition lia.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_15_split_goal_4 : decimal_to_binary_entail_wit_15_split_goal_4.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_15 : decimal_to_binary_entail_wit_15.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_15.
  intros. pre_process. normalize_79.
  Exists (app out_l_2 (cons 48 nil)).
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - pose proof PreH14 as Hsafe.
    unfold binary_safe_79 in Hsafe.
    destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [Hzero _]]]]]]]]].
    destruct (Hzero decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
    replace (divisor ÷ 2) with (divisor / 2).
    + exact Hnext.
    + symmetry. apply Z.quot_div_nonneg; lia.
  - pose proof PreH14 as Hsafe.
    unfold binary_safe_79 in Hsafe.
    destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [Hzero _]]]]]]]]].
    destruct (Hzero decimal divisor pos out_l_2 PreH15 PreH3 PreH2) as [_ Hnext].
    unfold binary_write_state_z_79 in Hnext. intuition lia.
  - unfold binary_write_state_z_79 in PreH15. intuition lia.
Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_16_1_split_goal_1 : decimal_to_binary_entail_wit_16_1_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_16_1_split_goal_2 : decimal_to_binary_entail_wit_16_1_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_16_1_split_goal_3 : decimal_to_binary_entail_wit_16_1_split_goal_3.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_16_1 : decimal_to_binary_entail_wit_16_1.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_16_2_split_goal_1 : decimal_to_binary_entail_wit_16_2_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_16_2_split_goal_2 : decimal_to_binary_entail_wit_16_2_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_16_2_split_goal_3 : decimal_to_binary_entail_wit_16_2_split_goal_3.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_entail_wit_16_2 : decimal_to_binary_entail_wit_16_2.
Proof. solve_79. Qed. 

Lemma proof_of_decimal_to_binary_entail_wit_17_split_goal_1 : decimal_to_binary_entail_wit_17_split_goal_1.
Proof.
  unfold decimal_to_binary_entail_wit_17_split_goal_1.
  intros. pre_process. normalize_79. entailer!.
  assert (Hdiv0 : divisor = 0) by lia. subst divisor.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hdone _]]]]]]]]]].
  destruct (Hdone decimal pos out_l_2 PreH16) as [Hout _].
  rewrite <- Hout. exact PreH17.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_17_split_goal_2 : decimal_to_binary_entail_wit_17_split_goal_2.
Proof.
  unfold decimal_to_binary_entail_wit_17_split_goal_2.
  intros. pre_process. normalize_79. entailer!.
  assert (Hdiv0 : divisor = 0) by lia. subst divisor.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hdone _]]]]]]]]]].
  destruct (Hdone decimal pos out_l_2 PreH16) as [Hout _].
  rewrite <- Hout. exact PreH16.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_17_split_goal_3 : decimal_to_binary_entail_wit_17_split_goal_3.
Proof.
  unfold decimal_to_binary_entail_wit_17_split_goal_3.
  intros. pre_process. normalize_79. entailer!.
  assert (Hdiv0 : divisor = 0) by lia. subst divisor.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hdone _]]]]]]]]]].
  destruct (Hdone decimal pos out_l_2 PreH16) as [_ Hpos].
  rewrite PreH7. exact Hpos.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_17_split_goal_4 : decimal_to_binary_entail_wit_17_split_goal_4.
Proof.
  unfold decimal_to_binary_entail_wit_17_split_goal_4.
  intros. pre_process. normalize_79. entailer!.
  assert (Hdiv0 : divisor = 0) by lia. subst divisor.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hdone _]]]]]]]]]].
  destruct (Hdone decimal pos out_l_2 PreH16) as [Hout _].
  exact Hout.
Qed.

Lemma proof_of_decimal_to_binary_entail_wit_17 : decimal_to_binary_entail_wit_17.
Proof.
  left.
  unfold decimal_to_binary_entail_wit_17.
  intros. pre_process. normalize_79.
  assert (Hdiv0 : divisor = 0) by lia. subst divisor.
  pose proof PreH14 as Hsafe.
  unfold binary_safe_79 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hdone _]]]]]]]]]].
  destruct (Hdone decimal pos out_l_2 PreH16) as [Hout Hpos].
  subst out_l_2.
  Exists (app (cons 100 (cons 98 nil)) (binary_payload_z_79 decimal_pre)).
  entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_return_wit_1_split_goal_1 : decimal_to_binary_return_wit_1_split_goal_1.
Proof.
  unfold decimal_to_binary_return_wit_1_split_goal_1.
  intros. pre_process. entailer!.
  apply binary_safe_decorated_spec_79; auto.
Qed.

Lemma proof_of_decimal_to_binary_return_wit_1_split_goal_2 : decimal_to_binary_return_wit_1_split_goal_2.
Proof.
  unfold decimal_to_binary_return_wit_1_split_goal_2.
  intros. pre_process. entailer!.
  apply binary_safe_decorated_length_79; auto.
  unfold binary_write_state_z_79 in PreH15. intuition lia.
Qed.

Lemma proof_of_decimal_to_binary_return_wit_1_split_goal_spatial : decimal_to_binary_return_wit_1_split_goal_spatial.
Proof.
  unfold decimal_to_binary_return_wit_1_split_goal_spatial.
  intros. pre_process. normalize_79.
  pose proof (binary_safe_append_tail_79 decimal_pre out_l_2 PreH14 PreH11) as Htail.
  assert (Hpos_decimal : 0 < decimal_pre).
  { unfold binary_write_state_z_79 in PreH15. intuition lia. }
  pose proof (binary_safe_decorated_length_79 decimal_pre PreH14 Hpos_decimal) as Hlen.
  replace (((pos + 1) + 1) + 1)
    with (Zlength (decorated_binary_output_z_79 decimal_pre) + 1).
  2: { rewrite Hlen, PreH12, PreH9. lia. }
  replace (app (app (app out_l_2 (cons 100 nil)) (cons 98 nil)) (cons 0 nil))
    with (app (decorated_binary_output_z_79 decimal_pre) (cons 0 nil)).
  2: { symmetry. apply append_tail_with_zero_79. exact Htail. }
  entailer!.
Qed.

Lemma proof_of_decimal_to_binary_return_wit_1 : decimal_to_binary_return_wit_1.
Proof.
  left.
  unfold decimal_to_binary_return_wit_1.
  intros. pre_process. normalize_79.
  pose proof (binary_safe_append_tail_79 decimal_pre out_l_2 PreH13 PreH10) as Htail.
  assert (Hpos_decimal : 0 < decimal_pre).
  { unfold binary_write_state_z_79 in PreH14. intuition lia. }
  pose proof (binary_safe_decorated_length_79 decimal_pre PreH13 Hpos_decimal) as Hlen.
  pose proof (binary_safe_decorated_spec_79 decimal_pre PreH13) as Hspec.
  replace (((pos + 1) + 1) + 1)
    with (Zlength (decorated_binary_output_z_79 decimal_pre) + 1).
  2: { rewrite Hlen, PreH11, PreH8. lia. }
  replace (app (app (app out_l_2 (cons 100 nil)) (cons 98 nil)) (cons 0 nil))
    with (app (decorated_binary_output_z_79 decimal_pre) (cons 0 nil)).
  2: { symmetry. apply append_tail_with_zero_79. exact Htail. }
  replace (bits + 5)
    with (Zlength (decorated_binary_output_z_79 decimal_pre) + 1).
  2: { rewrite Hlen, PreH8. lia. }
  Exists (decorated_binary_output_z_79 decimal_pre)
         (Zlength (decorated_binary_output_z_79 decimal_pre)).
  entailer!.
  - rewrite CharArray.undef_seg_empty. entailer!.
Qed. 

Lemma proof_of_decimal_to_binary_return_wit_2_split_goal_1 : decimal_to_binary_return_wit_2_split_goal_1.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_return_wit_2_split_goal_2 : decimal_to_binary_return_wit_2_split_goal_2.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_return_wit_2_split_goal_spatial : decimal_to_binary_return_wit_2_split_goal_spatial.
Proof. solve_79. Qed.

Lemma proof_of_decimal_to_binary_return_wit_2 : decimal_to_binary_return_wit_2.
Proof. solve_79. Qed. 
