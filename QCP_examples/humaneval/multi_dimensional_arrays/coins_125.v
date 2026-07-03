Load "../spec/125".

Definition spec_contains_125 := contains.
Definition spec_split_125 := split.
Definition spec_count_odd_lowercase_125 := count_odd_lowercase.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_125 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_125 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_125 c) (string_of_list_z_125 rest)
  end.

Definition row_payload_z_125 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_125 (row : list Z) : string :=
  string_of_list_z_125 (row_payload_z_125 row).

Definition rows_to_strings_z_125 (rows : list (list Z)) : list string :=
  map row_string_z_125 rows.

Fixpoint contains_zb_125 (s : list Z) (c : Z) : bool :=
  match s with
  | [] => false
  | x :: xs => if Z.eqb x c then true else contains_zb_125 xs c
  end.

Definition contains_z_125 (s : list Z) (c : Z) : Prop :=
  exists i, 0 <= i < Zlength s /\ Znth i s 0 = c.

Lemma contains_zb_125_true_of_Znth : forall s c i,
  0 <= i < Zlength s ->
  Znth i s 0 = c ->
  contains_zb_125 s c = true.
Proof.
  induction s as [|a s IH]; intros c i Hi Hnth.
  - rewrite Zlength_nil in Hi; lia.
  - simpl.
    destruct (Z.eqb_spec a c); [reflexivity|].
    rewrite Zlength_cons in Hi.
    assert (0 < i).
    {
      destruct (Z.eq_dec i 0) as [Hz | Hz].
      - subst i. unfold Znth in Hnth. simpl in Hnth. congruence.
      - lia.
    }
    apply IH with (i := i - 1).
    + lia.
    + rewrite Znth_cons in Hnth by lia.
      exact Hnth.
Qed.

Lemma contains_zb_125_false_of_forall : forall s c,
  (forall k, 0 <= k < Zlength s -> Znth k s 0 <> c) ->
  contains_zb_125 s c = false.
Proof.
  induction s as [|a s IH]; intros c Hnone.
  - reflexivity.
  - simpl.
    destruct (Z.eqb_spec a c) as [Heq | Hneq].
    + specialize (Hnone 0).
      unfold Znth in Hnone. simpl in Hnone.
      exfalso; apply Hnone.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg s). lia.
      * exact Heq.
    + apply IH.
      intros k Hk.
      specialize (Hnone (k + 1)).
      rewrite Znth_cons in Hnone by lia.
      replace (k + 1 - 1) with k in Hnone by lia.
      apply Hnone.
      rewrite Zlength_cons in *.
      pose proof (Zlength_nonneg s). lia.
Qed.

Lemma strchr_result_nonzero_contains_zb_125 : forall s c ret p,
  c <> 0 ->
  ret <> 0 ->
  strchr_result s c ret p ->
  contains_zb_125 s c = true.
Proof.
  intros s c ret p Hc Hret Hres.
  destruct Hres as [[i [Hi [Hnth [_ [_ _]]]]] | [Hnone [[Hz _] | [_ Hzero]]]].
  - apply contains_zb_125_true_of_Znth with (i := i); auto.
  - contradiction.
  - contradiction.
Qed.

Lemma strchr_result_zero_contains_zb_125 : forall s c p,
  c <> 0 ->
  strchr_result s c 0 p ->
  contains_zb_125 s c = false.
Proof.
  intros s c p Hc Hres.
  destruct Hres as [[i [_ [_ [_ [_ Hnz]]]]] | [Hnone [[Hz _] | [_ Hzero]]]].
  - contradiction.
  - contradiction.
  - apply contains_zb_125_false_of_forall.
    unfold string_length in Hnone.
    exact Hnone.
Qed.

Definition is_odd_lower_z_125 (c : Z) : bool :=
  Z.leb 97 c && Z.leb c 122 && Z.eqb (Z.rem c 2) 0.

Fixpoint odd_lower_count_payload_125 (s : list Z) : Z :=
  match s with
  | [] => 0
  | c :: rest =>
      (if is_odd_lower_z_125 c then 1 else 0) +
      odd_lower_count_payload_125 rest
  end.

Definition odd_lower_prefix_125 (s : list Z) (i : Z) : Z :=
  odd_lower_count_payload_125 (sublist 0 i s).

Definition odd_lower_count_125 (s : list Z) : Z :=
  odd_lower_count_payload_125 s.

Definition decimal_write_state_125
    (value _tmp pos digits : Z) (done : list Z) : Prop :=
  0 <= value /\
  Zlength done = digits - pos - 1.

Definition problem_125_pre_z (s : list Z) : Prop :=
  problem_125_pre (string_of_list_z_125 s).

Definition output_sum_z_125
    (s : list Z) (rows : list (list Z))
    : Datatypes.sum (list string) nat :=
  let l := list_ascii_of_string (string_of_list_z_125 s) in
  if spec_contains_125 l " "%char then
    inl (map string_of_list_ascii (spec_split_125 " "%char l))
  else if spec_contains_125 l ","%char then
    inl (map string_of_list_ascii (spec_split_125 ","%char l))
  else
    inr (spec_count_odd_lowercase_125 l).

Definition problem_125_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_125_spec (string_of_list_z_125 s) (output_sum_z_125 s rows).

Lemma problem_125_spec_z_any : forall s rows,
  problem_125_spec_z s rows.
Proof.
  intros s rows.
  unfold problem_125_spec_z, problem_125_spec, output_sum_z_125,
    spec_contains_125, spec_split_125, spec_count_odd_lowercase_125.
  destruct (contains (list_ascii_of_string (string_of_list_z_125 s)) " "%char);
    [reflexivity|].
  destruct (contains (list_ascii_of_string (string_of_list_z_125 s)) ","%char);
    reflexivity.
Qed.

Definition valid_split_words_input_125 (_s : list Z) : Prop := True.

Definition word_payload_125 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition word_row_125 (s : list Z) (start stop : Z) : list Z :=
  c_string (word_payload_125 s start stop).

Definition split_step_125
    (sep : Z) (st : list (list Z) * list Z) (c : Z)
    : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if Z.eqb c sep then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint split_state_nat_125 (n : nat) (s : list Z) (sep : Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      split_step_125
        sep
        (split_state_nat_125 n' s sep)
        (Znth (Z.of_nat n') s 0)
  end.

Definition split_completed_payloads_125
    (s : list Z) (i sep : Z) : list (list Z) :=
  fst (split_state_nat_125 (Z.to_nat i) s sep).

Definition split_scan_current_125 (s : list Z) (i sep : Z) : list Z :=
  snd (split_state_nat_125 (Z.to_nat i) s sep).

Definition split_completed_rows_125
    (s : list Z) (i sep : Z) : list (list Z) :=
  map c_string (split_completed_payloads_125 s i sep).

Definition split_payloads_125 (s : list Z) (sep : Z) : list (list Z) :=
  let '(rows, cur) := split_state_nat_125 (Z.to_nat (Zlength s)) s sep in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.

Definition split_output_rows_125 (s : list Z) (sep : Z) : list (list Z) :=
  map c_string (split_payloads_125 s sep).

Definition split_scan_state_125
    (s : list Z) (i start sep : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = split_completed_rows_125 s i sep /\
  ((split_scan_current_125 s i sep = [] /\ start = -1) \/
   (0 <= start < i /\
    split_scan_current_125 s i sep = word_payload_125 s start i)).

Fixpoint split_words_rows_heap_125
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row **
      split_words_rows_heap_125 ps rs
  | _, _ => emp
  end.

Lemma split_words_rows_heap_125_nil :
  emp |-- split_words_rows_heap_125 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma split_words_rows_heap_125_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  split_words_rows_heap_125 ptrs rows ** CharArray.full p (Zlength row) row
  |-- split_words_rows_heap_125 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  intros ptrs rows p row Hlen.
  revert rows Hlen.
  induction ptrs as [| p0 ptrs IH]; intros rows Hlen;
    destruct rows as [| row0 rows]; simpl in *.
  - rewrite derivable1_sepcon_comm.
    entailer!.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rows).
    lia.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ptrs).
    lia.
  - rewrite Zlength_cons in Hlen.
    rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength rows) by lia.
    sep_apply (IH rows Htail).
    cancel.
Qed.

Lemma Zlength_map_125 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  induction l as [| x xs IH].
  - reflexivity.
  - simpl.
    rewrite !Zlength_cons.
    lia.
Qed.

Lemma split_state_nat_125_step : forall i s sep,
  0 <= i ->
  split_state_nat_125 (Z.to_nat (i + 1)) s sep =
  split_step_125 sep (split_state_nat_125 (Z.to_nat i) s sep) (Znth i s 0).
Proof.
  intros i s sep Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma c_string_Znth_before_125 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma all_ascii_c_string_Znth_125 : forall s i,
  all_ascii s ->
  0 <= i < Zlength s ->
  0 <= Znth i (c_string s) 0 <= 127.
Proof.
  intros s i Hascii Hi.
  rewrite c_string_Znth_before_125 by lia.
  apply Hascii.
  exact Hi.
Qed.

Lemma word_payload_125_step : forall s start i,
  0 <= start /\ start <= i /\ i < Zlength s ->
  word_payload_125 s start (i + 1) =
  word_payload_125 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds.
  unfold word_payload_125.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry.
    apply sublist_single.
    lia.
Qed.

Lemma Zlength_word_payload_125 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (word_payload_125 s start stop) = stop - start.
Proof.
  intros s start stop Hbounds Hstop.
  unfold word_payload_125.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma word_payload_125_empty : forall s start,
  word_payload_125 s start start = [].
Proof.
  intros s start.
  unfold word_payload_125.
  apply sublist_nil.
  lia.
Qed.

Lemma word_payload_125_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  word_payload_125 s start (start + (k + 1)) =
  word_payload_125 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite word_payload_125_step by lia.
  rewrite c_string_Znth_before_125 by lia.
  reflexivity.
Qed.

Lemma word_row_125_unfold : forall s start stop,
  word_row_125 s start stop =
  word_payload_125 s start stop ++ [0].
Proof.
  intros.
  unfold word_row_125, c_string.
  reflexivity.
Qed.

Lemma split_scan_state_125_step_delim_nonempty : forall s i start sep rows,
  split_scan_state_125 s i start sep rows ->
  0 <= start < i ->
  Znth i s 0 = sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) (-1) sep
    (rows ++ [word_row_125 s start i]).
Proof.
  intros s i start sep rows Hstate Hstart Hdelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart_bad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur as [| c cs].
    + simpl in Hcur.
      assert (Zlength (word_payload_125 s start i) = i - start).
      { apply Zlength_word_payload_125; lia. }
      rewrite <- Hcur in H.
      rewrite Zlength_nil in H.
      lia.
    + simpl.
      unfold word_row_125.
      rewrite map_app.
      rewrite Hcur.
      reflexivity.
  - left.
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur; split; reflexivity.
Qed.

Lemma split_scan_state_125_step_delim_empty : forall s i sep rows,
  split_scan_state_125 s i (-1) sep rows ->
  Znth i s 0 = sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) (-1) sep rows.
Proof.
  intros s i sep rows Hstate Hdelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur; [reflexivity|congruence].
  - left.
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur_empty.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur; [split; reflexivity|congruence].
Qed.

Lemma split_scan_state_125_step_nondelim_continue : forall s i start sep rows,
  split_scan_state_125 s i start sep rows ->
  0 <= start < i ->
  Znth i s 0 <> sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) start sep rows.
Proof.
  intros s i start sep rows Hstate Hstart Hnondelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    rewrite Hcur.
    rewrite word_payload_125_step by lia.
    reflexivity.
Qed.

Lemma split_scan_state_125_step_nondelim_start : forall s i sep rows,
  split_scan_state_125 s i (-1) sep rows ->
  Znth i s 0 <> sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) i sep rows.
Proof.
  intros s i sep rows Hstate Hnondelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  subst.
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur_empty.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    subst cur.
    simpl.
    unfold word_payload_125.
    replace (sublist i (i + 1) s) with [Znth i s 0].
    + reflexivity.
    + symmetry; apply sublist_single; lia.
Qed.

Lemma split_scan_state_125_final_empty : forall s sep rows,
  split_scan_state_125 s (Zlength s) (-1) sep rows ->
  rows = split_output_rows_125 s sep.
Proof.
  intros s sep rows Hstate.
  unfold split_scan_state_125 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur Hstart] | [Hbad _]]; [| lia].
  subst rows.
  unfold split_output_rows_125, split_payloads_125,
    split_completed_rows_125, split_completed_payloads_125 in *.
  unfold split_scan_current_125 in Hcur.
  destruct (split_state_nat_125 (Z.to_nat (Zlength s)) s sep) as [payloads cur].
  simpl in *.
  subst cur.
  reflexivity.
Qed.

Lemma split_scan_state_125_final_nonempty : forall s sep start rows,
  split_scan_state_125 s (Zlength s) start sep rows ->
  0 <= start < Zlength s ->
  rows ++ [word_row_125 s start (Zlength s)] = split_output_rows_125 s sep.
Proof.
  intros s sep start rows Hstate Hstart.
  unfold split_scan_state_125 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [_ Hcur]]; [lia|].
  subst rows.
  unfold split_output_rows_125, split_payloads_125,
    split_completed_rows_125, split_completed_payloads_125 in *.
  unfold split_scan_current_125 in Hcur.
  destruct (split_state_nat_125 (Z.to_nat (Zlength s)) s sep) as [payloads cur].
  simpl in *.
  destruct cur as [| c cs].
  - assert (Zlength (word_payload_125 s start (Zlength s)) =
      Zlength s - start).
    { apply Zlength_word_payload_125; lia. }
    rewrite <- Hcur in H.
    rewrite Zlength_nil in H.
    lia.
  - unfold word_row_125.
    rewrite <- Hcur.
    simpl.
    rewrite map_app.
    reflexivity.
Qed.

Lemma split_state_nat_125_rows_bound : forall n s sep rows cur,
  split_state_nat_125 n s sep = (rows, cur) ->
  Zlength rows <= Z.of_nat n.
Proof.
  induction n as [| n IH]; intros s sep rows cur Hst; simpl in Hst.
  - inversion Hst; subst. rewrite Zlength_nil. lia.
  - destruct (split_state_nat_125 n s sep) as [rows0 cur0] eqn:Hprev.
    unfold split_step_125 in Hst.
    destruct (Z.eqb (Znth (Z.of_nat n) s 0) sep).
    + destruct cur0 as [| c cs]; inversion Hst; subst.
      * specialize (IH s sep rows [] Hprev). lia.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        specialize (IH s sep rows0 (c :: cs) Hprev). lia.
    + inversion Hst; subst.
      specialize (IH s sep rows cur0 Hprev).
      lia.
Qed.

Lemma Zlength_split_output_rows_125_le : forall s sep,
  Zlength (split_output_rows_125 s sep) <= Zlength s + 1.
Proof.
  intros s sep.
  unfold split_output_rows_125, split_payloads_125.
  destruct (split_state_nat_125 (Z.to_nat (Zlength s)) s sep) as [rows cur] eqn:Hst.
  destruct cur as [| c cs].
  - rewrite Zlength_map_125.
    pose proof (split_state_nat_125_rows_bound _ _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
  - rewrite Zlength_map_125, Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (split_state_nat_125_rows_bound _ _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
Qed.

Lemma odd_lower_count_payload_125_nonneg : forall s,
  0 <= odd_lower_count_payload_125 s.
Proof.
  induction s as [|c rest IH]; simpl.
  - lia.
  - destruct (is_odd_lower_z_125 c); lia.
Qed.

Lemma odd_lower_count_payload_125_le_Zlength : forall s,
  odd_lower_count_payload_125 s <= Zlength s.
Proof.
  induction s as [|c rest IH]; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (is_odd_lower_z_125 c); lia.
Qed.

Lemma list_ascii_of_string_string_of_list_z_125 : forall l,
  list_ascii_of_string (string_of_list_z_125 l) = map ascii_of_z_125 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma nat_of_ascii_ascii_of_z_125 : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z_125 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_125.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_eqb_ascii_of_z_const_125 : forall z n,
  0 <= z < 256 ->
  (n < 256)%nat ->
  Ascii.eqb (ascii_of_z_125 z) (ascii_of_nat n) = Z.eqb z (Z.of_nat n).
Proof.
  intros z n Hz Hn.
  destruct (Ascii.eqb_spec (ascii_of_z_125 z) (ascii_of_nat n)) as [Heq | Hneq];
    destruct (Z.eqb_spec z (Z.of_nat n)) as [Hz' | Hnz]; try reflexivity.
  - exfalso.
    apply Hnz.
    apply (f_equal nat_of_ascii) in Heq.
    rewrite nat_of_ascii_ascii_of_z_125 in Heq by exact Hz.
    rewrite nat_ascii_embedding in Heq by lia.
    lia.
  - subst z.
    exfalso.
    apply Hneq.
    unfold ascii_of_z_125.
    rewrite Nat2Z.id.
    reflexivity.
Qed.

Lemma contains_zb_125_false_ascii : forall s c n,
  all_ascii s ->
  c = Z.of_nat n ->
  (n < 256)%nat ->
  contains_zb_125 s c = false ->
  contains (map ascii_of_z_125 s) (ascii_of_nat n) = false.
Proof.
  induction s as [|x xs IH]; intros c n Hascii Hc Hn Hcontains.
  - reflexivity.
  - simpl in Hcontains.
    simpl.
    assert (Hx : 0 <= x < 256).
    {
      specialize (Hascii 0).
      rewrite Znth0_cons in Hascii.
      assert (0 <= 0 < Zlength (x :: xs)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      specialize (Hascii H).
      lia.
    }
    assert (Htail : all_ascii xs).
    {
      intros i Hi.
      specialize (Hascii (i + 1)).
      rewrite Znth_cons in Hascii by lia.
      replace (i + 1 - 1) with i in Hascii by lia.
      apply Hascii.
      rewrite Zlength_cons. lia.
    }
    rewrite ascii_eqb_ascii_of_z_const_125 by assumption.
    subst c.
    destruct (Z.eqb_spec x (Z.of_nat n)); [discriminate|].
    apply IH with (c := Z.of_nat n); auto.
Qed.

Lemma odd_lower_count_payload_125_app_single : forall s c,
  odd_lower_count_payload_125 (s ++ [c]) =
  odd_lower_count_payload_125 s + (if is_odd_lower_z_125 c then 1 else 0).
Proof.
  induction s as [|x xs IH]; intros c; simpl.
  - lia.
  - rewrite IH.
    destruct (is_odd_lower_z_125 x);
      destruct (is_odd_lower_z_125 c); lia.
Qed.

Lemma odd_lower_prefix_125_step_hit : forall s i,
  0 <= i < Zlength s ->
  97 <= Znth i (c_string s) 0 ->
  Znth i (c_string s) 0 <= 122 ->
  Z.rem (Znth i (c_string s) 0) 2 = 0 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i + 1.
Proof.
  intros s i Hi Hlo Hhi Hrem.
  unfold odd_lower_prefix_125.
  rewrite (sublist_split 0 (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0]
    by (symmetry; apply sublist_single; lia).
  rewrite odd_lower_count_payload_125_app_single.
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hlo, Hhi, Hrem by lia.
  replace (Z.leb 97 (Znth i s 0)) with true
    by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i s 0) 122) with true
    by (symmetry; apply Z.leb_le; lia).
  rewrite Hrem, Z.eqb_refl.
  simpl.
  lia.
Qed.

Lemma odd_lower_prefix_125_step_skip : forall s i,
  0 <= i < Zlength s ->
  is_odd_lower_z_125 (Znth i s 0) = false ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hskip.
  unfold odd_lower_prefix_125.
  rewrite (sublist_split 0 (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0]
    by (symmetry; apply sublist_single; lia).
  rewrite odd_lower_count_payload_125_app_single.
  rewrite Hskip.
  lia.
Qed.

Lemma odd_lower_prefix_125_step_high : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 > 122 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hhi.
  apply odd_lower_prefix_125_step_skip; [exact Hi|].
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hhi by lia.
  replace (Z.leb (Znth i s 0) 122) with false
    by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.leb 97 (Znth i s 0)); reflexivity.
Qed.

Lemma odd_lower_prefix_125_step_low : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 < 97 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hlo.
  apply odd_lower_prefix_125_step_skip; [exact Hi|].
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hlo by lia.
  replace (Z.leb 97 (Znth i s 0)) with false
    by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma odd_lower_prefix_125_step_rem_nonzero : forall s i,
  0 <= i < Zlength s ->
  97 <= Znth i (c_string s) 0 ->
  Znth i (c_string s) 0 <= 122 ->
  Z.rem (Znth i (c_string s) 0) 2 <> 0 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hlo Hhi Hrem.
  apply odd_lower_prefix_125_step_skip; [exact Hi|].
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hlo, Hhi, Hrem by lia.
  replace (Z.leb 97 (Znth i s 0)) with true
    by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i s 0) 122) with true
    by (symmetry; apply Z.leb_le; lia).
  destruct (Z.eqb_spec (Z.rem (Znth i s 0) 2) 0); [contradiction|].
  reflexivity.
Qed.

Lemma odd_lower_prefix_125_final : forall s i,
  i = Zlength s ->
  odd_lower_prefix_125 s i = odd_lower_count_125 s.
Proof.
  intros s i Hi.
  subst i.
  unfold odd_lower_prefix_125, odd_lower_count_125.
  rewrite (sublist_self s (Zlength s) eq_refl).
  reflexivity.
Qed.
