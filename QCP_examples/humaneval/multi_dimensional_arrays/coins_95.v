Load "../spec/95".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z c) (string_of_list_z rest)
  end.

Definition bool_of_z (z : Z) : bool :=
  Z.eqb z 1.

Definition row_payload_z (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition rows_to_dictionary_z (rows : list (list Z)) : dictionary :=
  map (fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString)) rows.

Definition problem_95_pre_z (rows : list (list Z)) : Prop :=
  problem_95_pre (rows_to_dictionary_z rows).

Definition lower_char_z (c : Z) : Prop :=
  97 <= c <= 122.

Definition upper_char_z (c : Z) : Prop :=
  65 <= c <= 90.

Definition letter_char_z (c : Z) : Prop :=
  upper_char_z c \/ lower_char_z c.

Definition payload_index_z (row : list Z) (i : Z) : Prop :=
  0 <= i < Zlength row - 1.

Definition row_all_lower_z (row : list Z) : Prop :=
  forall i, payload_index_z row i -> lower_char_z (Znth i row 0).

Definition row_all_upper_z (row : list Z) : Prop :=
  forall i, payload_index_z row i -> upper_char_z (Znth i row 0).

Definition row_all_letters_z (row : list Z) : Prop :=
  forall i, payload_index_z row i -> letter_char_z (Znth i row 0).

Definition rows_all_lower_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_lower_z (Znth k rows nil).

Definition rows_all_upper_z (rows : list (list Z)) : Prop :=
  forall k, 0 <= k < Zlength rows -> row_all_upper_z (Znth k rows nil).

Definition rows_have_uniform_case_z (rows : list (list Z)) : Prop :=
  rows_all_lower_z rows \/ rows_all_upper_z rows.

Definition scanned_position_z (k i r j : Z) : Prop :=
  (0 <= r < k /\ 0 <= j) \/ (r = k /\ 0 <= j < i).

Definition scanned_char_z (rows : list (list Z)) (k i r j : Z) : Prop :=
  0 <= r < Zlength rows /\
  scanned_position_z k i r j /\
  j < Zlength (Znth r rows nil) - 1.

Definition scanned_all_letters_z (rows : list (list Z)) (k i : Z) : Prop :=
  forall r j,
    scanned_char_z rows k i r j ->
    letter_char_z (Znth j (Znth r rows nil) 0).

Definition scanned_has_lower_z (rows : list (list Z)) (k i : Z) : Prop :=
  exists r j,
    scanned_char_z rows k i r j /\
    lower_char_z (Znth j (Znth r rows nil) 0).

Definition scanned_has_upper_z (rows : list (list Z)) (k i : Z) : Prop :=
  exists r j,
    scanned_char_z rows k i r j /\
    upper_char_z (Znth j (Znth r rows nil) 0).

Definition scan_state_z (rows : list (list Z)) (k i islower isupper : Z) : Prop :=
  scanned_all_letters_z rows k i /\
  (islower = 1 <-> scanned_has_lower_z rows k i) /\
  (isupper = 1 <-> scanned_has_upper_z rows k i) /\
  0 <= islower <= 1 /\
  0 <= isupper <= 1 /\
  islower + isupper <= 1.

Definition invalid_char_seen_z (rows : list (list Z)) (k i : Z) : Prop :=
  0 <= k < Zlength rows /\
  payload_index_z (Znth k rows nil) i /\
  ~ letter_char_z (Znth i (Znth k rows nil) 0).

Definition mixed_case_seen_z (rows : list (list Z)) (k i : Z) : Prop :=
  scanned_has_lower_z rows k i /\ scanned_has_upper_z rows k i.

Definition problem_95_spec_z (rows : list (list Z)) (ret : Z) : Prop :=
  problem_95_spec (rows_to_dictionary_z rows) (bool_of_z ret).

Definition rows_well_formed_z (rows : list (list Z)) (dict_size : Z) : Prop :=
  Zlength rows = dict_size /\
  forall k,
    0 <= k < dict_size ->
    0 < Zlength (Znth k rows nil) <= 101 /\
    Znth (Zlength (Znth k rows nil) - 1) (Znth k rows nil) 0 = 0 /\
    (forall i, payload_index_z (Znth k rows nil) i ->
       0 <= Znth i (Znth k rows nil) 0 <= 127 /\
       Znth i (Znth k rows nil) 0 <> 0).

Definition dictionary_all_lower_z (rows : list (list Z)) : Prop :=
  forall k v,
    In (k, v) (rows_to_dictionary_z rows) ->
    match k with
    | KeyString s => is_lowercase s
    | KeyOther => False
    end.

Definition dictionary_all_upper_z (rows : list (list Z)) : Prop :=
  forall k v,
    In (k, v) (rows_to_dictionary_z rows) ->
    match k with
    | KeyString s => is_uppercase s
    | KeyOther => False
    end.

Lemma list_ascii_of_string_string_of_list_z_95 : forall l,
  list_ascii_of_string (string_of_list_z l) = map ascii_of_z l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma nat_of_ascii_ascii_of_z_95 : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_leb_true_to_Z_le_95 : forall a b,
  (a <=? b)%char = true ->
  Z.of_nat (nat_of_ascii a) <= Z.of_nat (nat_of_ascii b).
Proof.
  intros a b Hleb.
  unfold Ascii.leb, Ascii.compare in Hleb.
  destruct (N_of_ascii a ?= N_of_ascii b)%N eqn:Hcmp; try discriminate.
  - apply N.compare_eq_iff in Hcmp.
    unfold nat_of_ascii.
    rewrite Hcmp.
    lia.
  - apply N.compare_lt_iff in Hcmp.
    apply N2Z.inj_lt in Hcmp.
    unfold nat_of_ascii.
    rewrite !N_nat_Z.
    lia.
Qed.

Lemma ascii_leb_true_of_Z_le_95 : forall a b,
  Z.of_nat (nat_of_ascii a) <= Z.of_nat (nat_of_ascii b) ->
  (a <=? b)%char = true.
Proof.
  intros a b Hle.
  unfold Ascii.leb, Ascii.compare.
  destruct (N_of_ascii a ?= N_of_ascii b)%N eqn:Hcmp; auto.
  apply N.compare_gt_iff in Hcmp.
  apply N2Z.inj_lt in Hcmp.
  unfold nat_of_ascii in Hle.
  rewrite !N_nat_Z in Hle.
  lia.
Qed.

Lemma lower_ascii_of_z_95 : forall c,
  lower_char_z c ->
  (("a" <=? ascii_of_z c)%char && (ascii_of_z c <=? "z")%char) = true.
Proof.
  intros c Hc.
  unfold lower_char_z in Hc.
  apply andb_true_iff.
  split; apply ascii_leb_true_of_Z_le_95;
    rewrite nat_of_ascii_ascii_of_z_95 by lia;
    rewrite Z2Nat.id by lia;
    change (Z.of_nat (nat_of_ascii "a"%char)) with 97;
    change (Z.of_nat (nat_of_ascii "z"%char)) with 122;
    lia.
Qed.

Lemma upper_ascii_of_z_95 : forall c,
  upper_char_z c ->
  (("A" <=? ascii_of_z c)%char && (ascii_of_z c <=? "Z")%char) = true.
Proof.
  intros c Hc.
  unfold upper_char_z in Hc.
  apply andb_true_iff.
  split; apply ascii_leb_true_of_Z_le_95;
    rewrite nat_of_ascii_ascii_of_z_95 by lia;
    rewrite Z2Nat.id by lia;
    change (Z.of_nat (nat_of_ascii "A"%char)) with 65;
    change (Z.of_nat (nat_of_ascii "Z"%char)) with 90;
    lia.
Qed.

Lemma lower_ascii_of_z_inv_95 : forall c,
  0 <= c < 256 ->
  (("a" <=? ascii_of_z c)%char && (ascii_of_z c <=? "z")%char) = true ->
  lower_char_z c.
Proof.
  intros c Hrange Hbool.
  apply andb_true_iff in Hbool as [Hlo Hhi].
  pose proof (ascii_leb_true_to_Z_le_95 _ _ Hlo) as Hlo'.
  pose proof (ascii_leb_true_to_Z_le_95 _ _ Hhi) as Hhi'.
  rewrite nat_of_ascii_ascii_of_z_95 in Hlo' by lia.
  rewrite nat_of_ascii_ascii_of_z_95 in Hhi' by lia.
  rewrite Z2Nat.id in Hlo' by lia.
  rewrite Z2Nat.id in Hhi' by lia.
  change (Z.of_nat (nat_of_ascii "a"%char)) with 97 in Hlo'.
  change (Z.of_nat (nat_of_ascii "z"%char)) with 122 in Hhi'.
  unfold lower_char_z.
  lia.
Qed.

Lemma upper_ascii_of_z_inv_95 : forall c,
  0 <= c < 256 ->
  (("A" <=? ascii_of_z c)%char && (ascii_of_z c <=? "Z")%char) = true ->
  upper_char_z c.
Proof.
  intros c Hrange Hbool.
  apply andb_true_iff in Hbool as [Hlo Hhi].
  pose proof (ascii_leb_true_to_Z_le_95 _ _ Hlo) as Hlo'.
  pose proof (ascii_leb_true_to_Z_le_95 _ _ Hhi) as Hhi'.
  rewrite nat_of_ascii_ascii_of_z_95 in Hlo' by lia.
  rewrite nat_of_ascii_ascii_of_z_95 in Hhi' by lia.
  rewrite Z2Nat.id in Hlo' by lia.
  rewrite Z2Nat.id in Hhi' by lia.
  change (Z.of_nat (nat_of_ascii "A"%char)) with 65 in Hlo'.
  change (Z.of_nat (nat_of_ascii "Z"%char)) with 90 in Hhi'.
  unfold upper_char_z.
  lia.
Qed.

Lemma Znth_In_range_95 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists_95 : forall {A : Type} (x : A) l d,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A x l d Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < List.length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := d) in Hn.
    exact Hn.
Qed.

Lemma Znth_firstn_95 : forall {A : Type} n (l : list A) i d,
  0 <= i ->
  i < Z.of_nat n ->
  Znth i (firstn n l) d = Znth i l d.
Proof.
  intros A n l i d Hi Hlt.
  unfold Znth.
  rewrite List.nth_firstn.
  destruct (Z.to_nat i <? n)%nat eqn:Hcmp.
  - reflexivity.
  - apply Nat.ltb_ge in Hcmp.
    lia.
Qed.

Lemma Zlength_row_payload_z_95 : forall row,
  0 < Zlength row ->
  Zlength (row_payload_z row) = Zlength row - 1.
Proof.
  intros row Hlen.
  unfold row_payload_z.
  rewrite Zlength_correct, firstn_length.
  rewrite Nat.min_l.
  - rewrite Z2Nat.id by lia.
    reflexivity.
  - apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia.
    rewrite Zlength_correct.
    lia.
Qed.

Lemma row_payload_index_z_95 : forall row i,
  0 <= i < Zlength (row_payload_z row) ->
  payload_index_z row i.
Proof.
  intros row i Hi.
  unfold row_payload_z, payload_index_z in *.
  split; [lia |].
  rewrite Zlength_correct, firstn_length in Hi.
  lia.
Qed.

Lemma Znth_row_payload_z_95 : forall row i,
  0 <= i < Zlength (row_payload_z row) ->
  Znth i (row_payload_z row) 0 = Znth i row 0.
Proof.
  intros row i Hi.
  unfold row_payload_z in *.
  apply Znth_firstn_95; [lia |].
  rewrite Zlength_correct, firstn_length in Hi.
  lia.
Qed.

Lemma row_all_lower_is_lowercase_95 : forall row,
  row_all_lower_z row ->
  is_lowercase (string_of_list_z (row_payload_z row)).
Proof.
  intros row Hlower.
  unfold is_lowercase.
  rewrite list_ascii_of_string_string_of_list_z_95.
  apply Forall_forall.
  intros a Hin.
  apply in_map_iff in Hin.
  destruct Hin as [z [Ha HzIn]].
  destruct (In_Znth_exists_95 z (row_payload_z row) 0 HzIn)
    as [i [Hi Hz]].
  subst a.
  rewrite <- Hz.
  rewrite Znth_row_payload_z_95 by exact Hi.
  apply lower_ascii_of_z_95.
  apply Hlower.
  apply row_payload_index_z_95.
  exact Hi.
Qed.

Lemma row_all_upper_is_uppercase_95 : forall row,
  row_all_upper_z row ->
  is_uppercase (string_of_list_z (row_payload_z row)).
Proof.
  intros row Hupper.
  unfold is_uppercase.
  rewrite list_ascii_of_string_string_of_list_z_95.
  apply Forall_forall.
  intros a Hin.
  apply in_map_iff in Hin.
  destruct Hin as [z [Ha HzIn]].
  destruct (In_Znth_exists_95 z (row_payload_z row) 0 HzIn)
    as [i [Hi Hz]].
  subst a.
  rewrite <- Hz.
  rewrite Znth_row_payload_z_95 by exact Hi.
  apply upper_ascii_of_z_95.
  apply Hupper.
  apply row_payload_index_z_95.
  exact Hi.
Qed.

Lemma dictionary_all_lower_from_rows_95 : forall rows,
  rows_all_lower_z rows ->
  dictionary_all_lower_z rows.
Proof.
  intros rows Hrows k v Hin.
  unfold rows_to_dictionary_z in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [row [Hpair HrowIn]].
  inversion Hpair; subst; clear Hpair.
  apply row_all_lower_is_lowercase_95.
  destruct (In_Znth_exists_95 row rows nil HrowIn) as [idx [Hidx Hrow]].
  specialize (Hrows idx Hidx).
  rewrite Hrow in Hrows.
  exact Hrows.
Qed.

Lemma dictionary_all_upper_from_rows_95 : forall rows,
  rows_all_upper_z rows ->
  dictionary_all_upper_z rows.
Proof.
  intros rows Hrows k v Hin.
  unfold rows_to_dictionary_z in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [row [Hpair HrowIn]].
  inversion Hpair; subst; clear Hpair.
  apply row_all_upper_is_uppercase_95.
  destruct (In_Znth_exists_95 row rows nil HrowIn) as [idx [Hidx Hrow]].
  specialize (Hrows idx Hidx).
  rewrite Hrow in Hrows.
  exact Hrows.
Qed.

Lemma dictionary_all_lower_char_95 : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  payload_index_z (Znth k rows nil) i ->
  dictionary_all_lower_z rows ->
  lower_char_z (Znth i (Znth k rows nil) 0).
Proof.
  intros rows dict_size k i [Hlen Hrow] Hk Hi Hall.
  specialize (Hrow k Hk) as [Hrowlen [_ Hrange]].
  pose proof (Hrange i Hi) as [Hc_range _].
  assert (HinRow : In (Znth k rows nil) rows).
  { apply Znth_In_range_95. rewrite Hlen. lia. }
  assert (HinPair :
    In (KeyString (string_of_list_z (row_payload_z (Znth k rows nil))), EmptyString)
       (rows_to_dictionary_z rows)).
  { unfold rows_to_dictionary_z.
    change (In ((fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString))
                  (Znth k rows nil))
               (map (fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString)) rows)).
    apply in_map. exact HinRow. }
  specialize (Hall _ _ HinPair).
  simpl in Hall.
  unfold is_lowercase in Hall.
  rewrite list_ascii_of_string_string_of_list_z_95 in Hall.
  apply Forall_forall with
    (x := ascii_of_z (Znth i (Znth k rows nil) 0)) in Hall.
  - apply lower_ascii_of_z_inv_95; [lia | exact Hall].
  - assert (Hidx_payload :
      0 <= i < Zlength (row_payload_z (Znth k rows nil))).
    { split; [apply Hi |].
      rewrite Zlength_row_payload_z_95 by lia.
      destruct Hi as [_ Hi].
      lia. }
    replace (Znth i (Znth k rows nil) 0)
      with (Znth i (row_payload_z (Znth k rows nil)) 0)
      by (rewrite Znth_row_payload_z_95 by exact Hidx_payload; reflexivity).
    apply in_map.
    apply Znth_In_range_95.
    exact Hidx_payload.
Qed.

Lemma dictionary_all_upper_char_95 : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  payload_index_z (Znth k rows nil) i ->
  dictionary_all_upper_z rows ->
  upper_char_z (Znth i (Znth k rows nil) 0).
Proof.
  intros rows dict_size k i [Hlen Hrow] Hk Hi Hall.
  specialize (Hrow k Hk) as [Hrowlen [_ Hrange]].
  pose proof (Hrange i Hi) as [Hc_range _].
  assert (HinRow : In (Znth k rows nil) rows).
  { apply Znth_In_range_95. rewrite Hlen. lia. }
  assert (HinPair :
    In (KeyString (string_of_list_z (row_payload_z (Znth k rows nil))), EmptyString)
       (rows_to_dictionary_z rows)).
  { unfold rows_to_dictionary_z.
    change (In ((fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString))
                  (Znth k rows nil))
               (map (fun row => (KeyString (string_of_list_z (row_payload_z row)), EmptyString)) rows)).
    apply in_map. exact HinRow. }
  specialize (Hall _ _ HinPair).
  simpl in Hall.
  unfold is_uppercase in Hall.
  rewrite list_ascii_of_string_string_of_list_z_95 in Hall.
  apply Forall_forall with
    (x := ascii_of_z (Znth i (Znth k rows nil) 0)) in Hall.
  - apply upper_ascii_of_z_inv_95; [lia | exact Hall].
  - assert (Hidx_payload :
      0 <= i < Zlength (row_payload_z (Znth k rows nil))).
    { split; [apply Hi |].
      rewrite Zlength_row_payload_z_95 by lia.
      destruct Hi as [_ Hi].
      lia. }
    replace (Znth i (Znth k rows nil) 0)
      with (Znth i (row_payload_z (Znth k rows nil)) 0)
      by (rewrite Znth_row_payload_z_95 by exact Hidx_payload; reflexivity).
    apply in_map.
    apply Znth_In_range_95.
    exact Hidx_payload.
Qed.

Lemma problem_95_pre_z_intro : forall rows,
  problem_95_pre_z rows.
Proof.
  intros rows.
  unfold problem_95_pre_z, problem_95_pre.
  exact I.
Qed.

Lemma problem_95_spec_z_empty : forall rows dict_size,
  dict_size = 0 ->
  rows_well_formed_z rows dict_size ->
  problem_95_spec_z rows 0.
Proof.
  intros rows dict_size Hsize [Hlen _].
  subst dict_size.
  apply Zlength_nil_inv in Hlen.
  subst rows.
  unfold problem_95_spec_z, bool_of_z.
  reflexivity.
Qed.

Lemma problem_95_spec_z_invalid : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  invalid_char_seen_z rows k i ->
  problem_95_spec_z rows 0.
Proof.
  intros rows dict_size k i Hwf Hbad.
  destruct Hbad as [HkRows [Hpayload Hnot_letter]].
  pose proof Hwf as [Hlen _].
  assert (Hk : 0 <= k < dict_size) by (rewrite <- Hlen; exact HkRows).
  unfold problem_95_spec_z, problem_95_spec, bool_of_z.
  destruct (rows_to_dictionary_z rows) as [| entry rest] eqn:Hdict.
  - unfold rows_to_dictionary_z in Hdict.
    apply map_eq_nil in Hdict.
    subst rows.
    rewrite Zlength_nil in HkRows.
    lia.
  - split.
    + intros [Hall_lower | Hall_upper].
      * exfalso.
        apply Hnot_letter.
        right.
        assert (Hall_lower_rows : dictionary_all_lower_z rows).
        { unfold dictionary_all_lower_z.
          intros key v Hin.
          rewrite Hdict in Hin.
          exact (Hall_lower key v Hin). }
        eapply dictionary_all_lower_char_95 with (dict_size := dict_size); eauto.
      * exfalso.
        apply Hnot_letter.
        left.
        assert (Hall_upper_rows : dictionary_all_upper_z rows).
        { unfold dictionary_all_upper_z.
          intros key v Hin.
          rewrite Hdict in Hin.
          exact (Hall_upper key v Hin). }
        eapply dictionary_all_upper_char_95 with (dict_size := dict_size); eauto.
    + discriminate.
Qed.

Lemma problem_95_spec_z_mixed : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  mixed_case_seen_z rows k i ->
  problem_95_spec_z rows 0.
Proof.
  intros rows dict_size k i Hwf Hmix.
  destruct Hmix as [[rl [jl [Hscan_lower Hlower]]]
                    [ru [ju [Hscan_upper Hupper]]]].
  destruct Hscan_lower as [Hrl [Hpos_lower Hjl]].
  destruct Hscan_upper as [Hru [Hpos_upper Hju]].
  pose proof Hwf as [Hlen _].
  assert (Hrl_size : 0 <= rl < dict_size) by (rewrite <- Hlen; exact Hrl).
  assert (Hru_size : 0 <= ru < dict_size) by (rewrite <- Hlen; exact Hru).
  assert (Hpayload_lower : payload_index_z (Znth rl rows nil) jl).
  { unfold payload_index_z, scanned_position_z in *.
    destruct Hpos_lower as [[_ Hj_nonneg] | [_ [Hj_nonneg _]]]; lia. }
  assert (Hpayload_upper : payload_index_z (Znth ru rows nil) ju).
  { unfold payload_index_z, scanned_position_z in *.
    destruct Hpos_upper as [[_ Hj_nonneg] | [_ [Hj_nonneg _]]]; lia. }
  unfold problem_95_spec_z, problem_95_spec, bool_of_z.
  destruct (rows_to_dictionary_z rows) as [| entry rest] eqn:Hdict.
  - unfold rows_to_dictionary_z in Hdict.
    apply map_eq_nil in Hdict.
    subst rows.
    rewrite Zlength_nil in Hrl.
    lia.
  - split.
    + intros [Hall_lower | Hall_upper].
      * exfalso.
        assert (Hall_lower_rows : dictionary_all_lower_z rows).
        { unfold dictionary_all_lower_z.
          intros key v Hin.
          rewrite Hdict in Hin.
          exact (Hall_lower key v Hin). }
        pose proof (dictionary_all_lower_char_95 rows dict_size ru ju
            Hwf Hru_size Hpayload_upper Hall_lower_rows) as Hlower_bad.
        unfold lower_char_z, upper_char_z in *.
        lia.
      * exfalso.
        assert (Hall_upper_rows : dictionary_all_upper_z rows).
        { unfold dictionary_all_upper_z.
          intros key v Hin.
          rewrite Hdict in Hin.
          exact (Hall_upper key v Hin). }
        pose proof (dictionary_all_upper_char_95 rows dict_size rl jl
            Hwf Hrl_size Hpayload_lower Hall_upper_rows) as Hupper_bad.
        unfold lower_char_z, upper_char_z in *.
        lia.
    + discriminate.
Qed.

Lemma problem_95_spec_z_success : forall rows dict_size,
  0 < dict_size ->
  rows_well_formed_z rows dict_size ->
  rows_have_uniform_case_z rows ->
  problem_95_spec_z rows 1.
Proof.
  intros rows dict_size Hpos [Hlen _] Huniform.
  unfold problem_95_spec_z, problem_95_spec, bool_of_z.
  destruct (rows_to_dictionary_z rows) as [| entry rest] eqn:Hdict.
  - unfold rows_to_dictionary_z in Hdict.
    apply map_eq_nil in Hdict.
    subst rows.
    rewrite Zlength_nil in Hlen.
    lia.
  - split.
    + intros _. reflexivity.
    + intros _.
      destruct Huniform as [Hlower | Hupper].
      * left.
        intros key v Hin.
        apply (dictionary_all_lower_from_rows_95 rows Hlower key v).
        rewrite Hdict.
        exact Hin.
      * right.
        intros key v Hin.
        apply (dictionary_all_upper_from_rows_95 rows Hupper key v).
        rewrite Hdict.
        exact Hin.
Qed.

Lemma invalid_char_seen_intro : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 <> 0 ->
  ~ letter_char_z (Znth i (Znth k rows nil) 0) ->
  invalid_char_seen_z rows k i.
Proof.
  intros rows dict_size k i [Hlen Hrow] Hk Hi Hnz Hnot.
  specialize (Hrow k Hk) as [Hrowlen [Hlast _]].
  unfold invalid_char_seen_z, payload_index_z.
  split.
  - rewrite Hlen. lia.
  - split.
    + split; [lia |].
      assert (i <> Zlength (Znth k rows nil) - 1).
      { intro Heq. rewrite Heq in Hnz. contradiction. }
      lia.
    + exact Hnot.
Qed.

Lemma scan_state_z_initial : forall rows,
  scan_state_z rows 0 0 0 0.
Proof.
  intros rows.
  unfold scan_state_z, scanned_all_letters_z, scanned_has_lower_z,
         scanned_has_upper_z, scanned_char_z, scanned_position_z.
  split.
  - intros r j [_ [Hpos _]].
    destruct Hpos as [[Hr0 Hr] | [_ [Hj0 Hj]]]; lia.
  - split.
    + split; intros H;
        [discriminate
        | destruct H as [r [j [[_ [Hpos _]] _]]];
          destruct Hpos as [[Hr0 Hr] | [_ [Hj0 Hj]]]; lia].
    + split.
      * split; intros H;
          [discriminate
          | destruct H as [r [j [[_ [Hpos _]] _]]];
            destruct Hpos as [[Hr0 Hr] | [_ [Hj0 Hj]]]; lia].
      * repeat split; lia.
Qed.

Lemma payload_index_from_nonzero : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 <> 0 ->
  payload_index_z (Znth k rows nil) i.
Proof.
  intros rows dict_size k i [_ Hrow] Hk Hi Hnz.
  specialize (Hrow k Hk) as [_ [Hlast _]].
  unfold payload_index_z.
  split; [lia |].
  assert (i <> Zlength (Znth k rows nil) - 1).
  { intro Heq. rewrite Heq in Hnz. contradiction. }
  lia.
Qed.

Lemma scanned_char_step_inv : forall rows k i r j,
  scanned_char_z rows k (i + 1) r j ->
  scanned_char_z rows k i r j \/ (r = k /\ j = i /\ 0 <= i /\ j < Zlength (Znth r rows nil) - 1).
Proof.
  intros rows k i r j [Hr [Hpos Hj]].
  unfold scanned_char_z, scanned_position_z in *.
  destruct Hpos as [[Hr0 Hrk] | [Hr_eq [Hj0 Hji]]].
  - left. split; [assumption |].
    split; [left; lia | assumption].
  - destruct (Z.eq_dec j i) as [Heq | Hneq].
    + right. subst. repeat split; auto; lia.
    + left. split; [assumption |].
      split; [right; split; [assumption | lia] | assumption].
Qed.

Lemma scanned_char_step_old : forall rows k i r j,
  scanned_char_z rows k i r j ->
  scanned_char_z rows k (i + 1) r j.
Proof.
  intros rows k i r j [Hr [Hpos Hj]].
  unfold scanned_char_z, scanned_position_z in *.
  split; [assumption |].
  split; [| assumption].
  destruct Hpos as [[Hr0 Hrk] | [Hr_eq [Hj0 Hji]]].
  - left; lia.
  - right; split; [assumption | lia].
Qed.

Lemma scanned_char_step_current : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  payload_index_z (Znth k rows nil) i ->
  scanned_char_z rows k (i + 1) k i.
Proof.
  intros rows dict_size k i [Hlen _] Hk Hpayload.
  unfold scanned_char_z, scanned_position_z, payload_index_z in *.
  split.
  - rewrite Hlen; lia.
  - split.
    + right; lia.
    + lia.
Qed.

Lemma scan_state_z_lower_step : forall rows dict_size k i islower isupper,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 <> 0 ->
  lower_char_z (Znth i (Znth k rows nil) 0) ->
  isupper + 1 <> 2 ->
  scan_state_z rows k i islower isupper ->
  scan_state_z rows k (i + 1) 1 isupper.
Proof.
  intros rows dict_size k i islower isupper Hwf Hk Hi Hnz Hlower Hnot2
         [Hall [Hlower_iff [Hupper_iff [Hislower [Hisupper Hsum]]]]].
  assert (Hpayload := payload_index_from_nonzero rows dict_size k i Hwf Hk Hi Hnz).
  assert (Hisupper0 : isupper = 0) by lia.
  subst isupper.
  unfold scan_state_z.
  split.
  - intros r j Hscan.
    destruct (scanned_char_step_inv rows k i r j Hscan) as [Hold | [Hr_eq [Hj_eq [_ _]]]].
    + apply Hall; assumption.
    + subst r j. right; assumption.
  - split.
    + split; intros _.
      * exists k, i. split.
        -- apply scanned_char_step_current with (dict_size := dict_size); assumption.
        -- assumption.
      * reflexivity.
    + split.
      * split; intros H.
        -- discriminate.
        -- destruct H as [r [j [Hscan Hupper]]].
           destruct (scanned_char_step_inv rows k i r j Hscan) as [Hold | [Hr_eq [Hj_eq [_ _]]]].
           ++ pose proof (proj2 Hupper_iff (ex_intro _ r (ex_intro _ j (conj Hold Hupper)))) as Hbad.
              discriminate.
           ++ subst r j. unfold lower_char_z, upper_char_z in *; lia.
      * repeat split; lia.
Qed.

Lemma scan_state_z_upper_step : forall rows dict_size k i islower isupper,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 <> 0 ->
  upper_char_z (Znth i (Znth k rows nil) 0) ->
  1 + islower <> 2 ->
  scan_state_z rows k i islower isupper ->
  scan_state_z rows k (i + 1) islower 1.
Proof.
  intros rows dict_size k i islower isupper Hwf Hk Hi Hnz Hupper Hnot2
         [Hall [Hlower_iff [Hupper_iff [Hislower [Hisupper Hsum]]]]].
  assert (Hpayload := payload_index_from_nonzero rows dict_size k i Hwf Hk Hi Hnz).
  assert (Hislower0 : islower = 0) by lia.
  subst islower.
  unfold scan_state_z.
  split.
  - intros r j Hscan.
    destruct (scanned_char_step_inv rows k i r j Hscan) as [Hold | [Hr_eq [Hj_eq [_ _]]]].
    + apply Hall; assumption.
    + subst r j. left; assumption.
  - split.
    + split; intros H.
      * discriminate.
      * destruct H as [r [j [Hscan Hlower]]].
        destruct (scanned_char_step_inv rows k i r j Hscan) as [Hold | [Hr_eq [Hj_eq [_ _]]]].
        -- pose proof (proj2 Hlower_iff (ex_intro _ r (ex_intro _ j (conj Hold Hlower)))) as Hbad.
           discriminate.
        -- subst r j. unfold lower_char_z, upper_char_z in *; lia.
    + split.
      * split; intros _.
        -- exists k, i. split.
           ++ apply scanned_char_step_current with (dict_size := dict_size); assumption.
           ++ assumption.
        -- reflexivity.
      * repeat split; lia.
Qed.

Lemma mixed_case_seen_lower_intro : forall rows dict_size k i islower isupper,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 <> 0 ->
  lower_char_z (Znth i (Znth k rows nil) 0) ->
  isupper + 1 = 2 ->
  scan_state_z rows k i islower isupper ->
  mixed_case_seen_z rows k (i + 1).
Proof.
  intros rows dict_size k i islower isupper Hwf Hk Hi Hnz Hlower Hmix
         [_ [_ [Hupper_iff _]]].
  assert (Hpayload := payload_index_from_nonzero rows dict_size k i Hwf Hk Hi Hnz).
  split.
  - exists k, i. split.
    + apply scanned_char_step_current with (dict_size := dict_size); assumption.
    + assumption.
  - destruct (proj1 Hupper_iff ltac:(lia)) as [r [j [Hscan Hupper]]].
    exists r, j. split; [apply scanned_char_step_old; assumption | assumption].
Qed.

Lemma mixed_case_seen_upper_intro : forall rows dict_size k i islower isupper,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 <> 0 ->
  upper_char_z (Znth i (Znth k rows nil) 0) ->
  1 + islower = 2 ->
  scan_state_z rows k i islower isupper ->
  mixed_case_seen_z rows k (i + 1).
Proof.
  intros rows dict_size k i islower isupper Hwf Hk Hi Hnz Hupper Hmix
         [_ [Hlower_iff _]].
  split.
  - destruct (proj1 Hlower_iff ltac:(lia)) as [r [j [Hscan Hlower]]].
    exists r, j. split; [apply scanned_char_step_old; assumption | assumption].
  - exists k, i. split.
    + assert (Hpayload := payload_index_from_nonzero rows dict_size k i Hwf Hk Hi Hnz).
      apply scanned_char_step_current with (dict_size := dict_size); assumption.
    + assumption.
Qed.

Lemma row_zero_index_is_last : forall rows dict_size k i,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 = 0 ->
  i = Zlength (Znth k rows nil) - 1.
Proof.
  intros rows dict_size k i [_ Hrow] Hk Hi Hz.
  specialize (Hrow k Hk) as [_ [Hlast Hnonzero]].
  destruct (Z.eq_dec i (Zlength (Znth k rows nil) - 1)) as [Heq | Hneq]; [assumption |].
  exfalso.
  assert (payload_index_z (Znth k rows nil) i).
  { unfold payload_index_z. split; [lia | lia]. }
  specialize (Hnonzero i H).
  lia.
Qed.

Lemma scanned_char_finish_old_to_new : forall rows k i r j,
  scanned_char_z rows k i r j ->
  scanned_char_z rows (k + 1) 0 r j.
Proof.
  intros rows k i r j [Hr [Hpos Hj]].
  unfold scanned_char_z, scanned_position_z in *.
  split; [assumption |].
  split; [| assumption].
  destruct Hpos as [[Hr0 Hrk] | [Hr_eq [Hj0 Hji]]].
  - left; lia.
  - left; lia.
Qed.

Lemma scanned_char_finish_new_to_old : forall rows k i r j,
  i = Zlength (Znth k rows nil) - 1 ->
  scanned_char_z rows (k + 1) 0 r j ->
  scanned_char_z rows k i r j.
Proof.
  intros rows k i r j Hi [Hr [Hpos Hj]].
  unfold scanned_char_z, scanned_position_z in *.
  split; [assumption |].
  split; [| assumption].
  destruct Hpos as [[Hr0 Hrk1] | [Hr_eq [Hj_ge Hj_lt]]].
  - destruct (Z.eq_dec r k) as [Heq | Hneq].
    + subst r. right. split; [reflexivity | lia].
    + left; lia.
  - lia.
Qed.

Lemma scan_state_z_finish_row : forall rows dict_size k i islower isupper,
  rows_well_formed_z rows dict_size ->
  0 <= k < dict_size ->
  0 <= i < Zlength (Znth k rows nil) ->
  Znth i (Znth k rows nil) 0 = 0 ->
  scan_state_z rows k i islower isupper ->
  scan_state_z rows (k + 1) 0 islower isupper.
Proof.
  intros rows dict_size k i islower isupper Hwf Hk Hi Hz
         [Hall [Hlower_iff [Hupper_iff [Hislower [Hisupper Hsum]]]]].
  pose proof (row_zero_index_is_last rows dict_size k i Hwf Hk Hi Hz) as Hlast.
  unfold scan_state_z.
  split.
  - intros r j Hscan.
    apply Hall.
    eapply scanned_char_finish_new_to_old; eauto.
  - split.
    + split; intros H.
      * destruct (proj1 Hlower_iff H) as [r [j [Hscan Hlower]]].
        exists r, j. split; [eapply scanned_char_finish_old_to_new; eauto | assumption].
      * apply (proj2 Hlower_iff).
        destruct H as [r [j [Hscan Hlower]]].
        exists r, j. split; [eapply scanned_char_finish_new_to_old; eauto | assumption].
    + split.
      * split; intros H.
        -- destruct (proj1 Hupper_iff H) as [r [j [Hscan Hupper]]].
           exists r, j. split; [eapply scanned_char_finish_old_to_new; eauto | assumption].
        -- apply (proj2 Hupper_iff).
           destruct H as [r [j [Hscan Hupper]]].
           exists r, j. split; [eapply scanned_char_finish_new_to_old; eauto | assumption].
      * repeat split; lia.
Qed.

Lemma scan_state_z_done_uniform : forall rows dict_size islower isupper,
  rows_well_formed_z rows dict_size ->
  scan_state_z rows dict_size 0 islower isupper ->
  rows_have_uniform_case_z rows.
Proof.
  intros rows dict_size islower isupper [Hlen _]
         [Hall [Hlower_iff [Hupper_iff [Hislower [Hisupper Hsum]]]]].
  unfold rows_have_uniform_case_z, rows_all_lower_z, rows_all_upper_z,
         row_all_lower_z, row_all_upper_z.
  destruct (Z.eq_dec isupper 0) as [Hupper0 | Hupper_not0].
  - left. intros k Hk i Hpayload.
    assert (Hscan : scanned_char_z rows dict_size 0 k i).
    { unfold scanned_char_z, scanned_position_z, payload_index_z in *.
      split; [rewrite Hlen in Hk; lia |].
      split; [left; rewrite Hlen in Hk; lia | lia]. }
    specialize (Hall k i Hscan) as Hletter.
    destruct Hletter as [Hupper | Hlower]; [| assumption].
    exfalso.
    pose proof (proj2 Hupper_iff (ex_intro _ k (ex_intro _ i (conj Hscan Hupper)))) as Hbad.
    lia.
  - assert (Hisupper1 : isupper = 1) by lia.
    assert (Hislower0 : islower = 0) by lia.
    right. intros k Hk i Hpayload.
    assert (Hscan : scanned_char_z rows dict_size 0 k i).
    { unfold scanned_char_z, scanned_position_z, payload_index_z in *.
      split; [rewrite Hlen in Hk; lia |].
      split; [left; rewrite Hlen in Hk; lia | lia]. }
    specialize (Hall k i Hscan) as Hletter.
    destruct Hletter as [Hupper | Hlower]; [assumption |].
    exfalso.
    pose proof (proj2 Hlower_iff (ex_intro _ k (ex_intro _ i (conj Hscan Hlower)))) as Hbad.
    lia.
Qed.
