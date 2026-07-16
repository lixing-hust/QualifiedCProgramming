Load "../spec/87".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_87_pre_z (rows : list (list Z)) (x : Z) : Prop :=
  problem_87_pre rows x.

Definition problem_87_spec_z (rows : list (list Z)) (x : Z)
  (coords : list (Z * Z)) : Prop :=
  problem_87_spec rows x coords.

Definition coords_flat_87 (coords : list (Z * Z)) : list Z :=
  flat_map (fun p => [fst p; snd p]) coords.

Lemma coords_flat_87_app_single : forall coords i j,
  coords_flat_87 (coords ++ [(i, j)]) = coords_flat_87 coords ++ [i; j].
Proof.
  intros coords i j.
  unfold coords_flat_87.
  rewrite flat_map_app; reflexivity.
Qed.

Lemma Zlength_coords_flat_87 : forall coords,
  Zlength (coords_flat_87 coords) = 2 * Zlength coords.
Proof.
  intros coords; induction coords as [|[i j] coords IH].
  - reflexivity.
  - change (Zlength ([i; j] ++ coords_flat_87 coords) =
      2 * Zlength ((i, j) :: coords)).
    rewrite Zlength_app, !Zlength_cons, Zlength_nil, IH; lia.
Qed.

Definition row_sizes_87 (rows : list (list Z)) : list Z :=
  map (fun row => Zlength row) rows.

Definition matrix_cells_87 (rows : list (list Z)) : Z :=
  fold_right (fun row acc => Zlength row + acc) 0 rows.

Definition outer_seen_87 (i : Z) (p : Z * Z) : Prop := fst p < i.

Definition inner_seen_87 (i j : Z) (p : Z * Z) : Prop :=
  fst p < i \/ (fst p = i /\ j < snd p).

Definition coords_state_87
  (rows : list (list Z)) (x : Z) (seen : Z * Z -> Prop)
  (coords : list (Z * Z)) : Prop :=
  NoDup coords /\
  (forall p, In p coords <-> coord_hits rows x p /\ seen p).

Definition count_scan_outer_87
  (rows : list (list Z)) (x i count : Z) : Prop :=
  exists coords,
    Zlength coords = count /\
    coords_state_87 rows x (outer_seen_87 i) coords.

Definition count_scan_inner_87
  (rows : list (list Z)) (x i j count : Z) : Prop :=
  exists coords,
    Zlength coords = count /\
    coords_state_87 rows x (inner_seen_87 i j) coords.

Definition get_row_safe_87 (rows : list (list Z)) : Prop :=
  (forall row, In row rows -> 0 <= Zlength row < INT_MAX) /\
  (forall x i j count,
      count_scan_inner_87 rows x i j count ->
      2 * (count + 1) < INT_MAX) /\
  (forall x i count,
      count_scan_outer_87 rows x i count ->
      2 * count < INT_MAX).

Lemma row_length_safe_87 : forall rows i,
  get_row_safe_87 rows ->
  0 <= i < Zlength rows ->
  0 <= Zlength (Znth i rows nil) < INT_MAX.
Proof.
  intros rows i Hsafe Hi.
  destruct Hsafe as [Hrows [Hinner Houter]].
  apply Hrows.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi; lia.
Qed.

Definition fill_scan_outer_87
  (rows : list (list Z)) (x i : Z) (coords : list (Z * Z)) : Prop :=
  coords_state_87 rows x (outer_seen_87 i) coords /\
  StronglySorted coord_order coords.

Definition fill_scan_inner_87
  (rows : list (list Z)) (x i j : Z) (coords : list (Z * Z)) : Prop :=
  coords_state_87 rows x (inner_seen_87 i j) coords /\
  StronglySorted coord_order coords.

Definition get_row_finished_87
  (rows : list (list Z)) (x : Z) (coords : list (Z * Z)) : Prop :=
  problem_87_spec_z rows x coords.

Lemma Znth_map_87 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
  0 <= i < Zlength l ->
  Znth i (map f l) d' = f (Znth i l d).
Proof.
  intros A B f l i d d' Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f d)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l d (Z.to_nat i)).
    reflexivity.
Qed.

Lemma row_sizes_87_Znth : forall rows i d,
  0 <= i < Zlength rows ->
  Znth i (row_sizes_87 rows) d = Zlength (Znth i rows nil).
Proof.
  intros rows i d Hi.
  unfold row_sizes_87.
  rewrite (Znth_map_87 (fun row => Zlength row) rows i nil d) by exact Hi.
  reflexivity.
Qed.

Lemma coord_hits_current_87 : forall rows x i j,
  0 <= i < Zlength rows ->
  0 <= j < Zlength (Znth i rows nil) ->
  Znth j (Znth i rows nil) 0 = x ->
  coord_hits rows x (i, j).
Proof.
  intros rows x i j Hi Hj Hx.
  unfold coord_hits; cbn.
  exists (Znth i rows nil).
  split.
  - unfold Znth in *.
    apply nth_error_nth'.
    rewrite Zlength_correct in Hi.
    lia.
  - split.
    + unfold Znth in *.
      rewrite (nth_error_nth' (nth (Z.to_nat i) rows []) 0).
      * now f_equal.
      * rewrite Zlength_correct in Hj.
        lia.
    + split; lia.
Qed.

Lemma coord_hits_current_inv_87 : forall rows x i j,
  0 <= i < Zlength rows ->
  0 <= j < Zlength (Znth i rows nil) ->
  coord_hits rows x (i, j) ->
  Znth j (Znth i rows nil) 0 = x.
Proof.
  intros rows x i j Hi Hj [row [Hrow [Hcell _]]].
  cbn in Hrow; cbn in Hcell.
  unfold Znth.
  pose proof (nth_error_nth rows (Z.to_nat i) nil Hrow) as Hrow'.
  pose proof (nth_error_nth row (Z.to_nat j) 0 Hcell) as Hcell'.
  rewrite <- Hrow' in Hcell'.
  exact Hcell'.
Qed.

Lemma inner_seen_start_87 : forall rows x i p,
  0 <= i < Zlength rows ->
  coord_hits rows x p ->
  (inner_seen_87 i (Zlength (Znth i rows nil) - 1) p <-> outer_seen_87 i p).
Proof.
  intros rows x i [r c] Hi Hhit; simpl in *.
  destruct Hhit as [row [Hrow [Hcell [Hr Hc]]]].
  cbn in Hrow; cbn in Hcell; cbn in Hr; cbn in Hc.
  assert (HcLt : c < Zlength row).
  { rewrite Zlength_correct.
    apply (proj2 (Z2Nat.inj_lt c (Z.of_nat (length row)) Hc ltac:(lia))).
    rewrite Nat2Z.id.
    apply (proj1 (nth_error_Some row (Z.to_nat c))).
    rewrite Hcell; discriminate. }
  unfold inner_seen_87, outer_seen_87; simpl.
  split; intro H.
  - destruct H as [H|[Heq Hgt]]; [exact H|].
    subst r.
    cbn in Hgt.
    unfold Znth in Hgt.
    pose proof (nth_error_nth rows (Z.to_nat i) nil Hrow) as HrowEq.
    rewrite <- HrowEq in HcLt.
    exfalso; lia.
  - left; exact H.
Qed.

Lemma inner_seen_end_87 : forall rows x i p,
  coord_hits rows x p ->
  (inner_seen_87 i (-1) p <-> outer_seen_87 (i + 1) p).
Proof.
  intros rows x i [r c] Hhit; simpl in *.
  destruct Hhit as [row [_ [_ [Hr Hc]]]].
  cbn in Hr; cbn in Hc.
  unfold inner_seen_87, outer_seen_87; simpl.
  split; intros H.
  - destruct H as [H|[Heq Hcgt]]; lia.
  - destruct (Z_lt_ge_dec r i) as [Hlt|Hge].
    + left; exact Hlt.
    + right; split; lia.
Qed.

Lemma inner_seen_step_87 : forall rows x i j p,
  coord_hits rows x p ->
  (inner_seen_87 i (j - 1) p <->
   inner_seen_87 i j p \/ p = (i, j)).
Proof.
  intros rows x i j [r c] Hhit; simpl in *.
  destruct Hhit as [row [_ [_ [Hr Hc]]]].
  unfold inner_seen_87; simpl.
  split; intros H.
  - destruct H as [H|[Heq Hgt]]; [left; left; exact H|].
    destruct (Z_lt_ge_dec j c) as [Hjc|Hcj].
    + left; right; split; [exact Heq|exact Hjc].
    + right. subst r. assert (c = j) by lia. subst c. reflexivity.
  - destruct H as [[H|[Heq Hgt]]|Heq].
    + left; exact H.
    + right; split; [exact Heq|lia].
    + inversion Heq; right; split; reflexivity || lia.
Qed.

Lemma coords_state_outer_0_87 : forall rows x,
  coords_state_87 rows x (outer_seen_87 0) [].
Proof.
  intros rows x; split; [constructor|].
  intros [r c]; simpl; split; intro H; [contradiction|].
  destruct H as [[row [_ [_ [Hr _]]]] Hseen].
  cbn in Hr.
  unfold outer_seen_87 in Hseen; simpl in Hseen; lia.
Qed.

Lemma coords_state_outer_to_inner_87 : forall rows x i coords,
  0 <= i < Zlength rows ->
  coords_state_87 rows x (outer_seen_87 i) coords ->
  coords_state_87 rows x (inner_seen_87 i (Zlength (Znth i rows nil) - 1)) coords.
Proof.
  intros rows x i coords Hi [Hnd Hmem]; split; [exact Hnd|].
  intros p; rewrite Hmem.
  split; intro H.
  - destruct H as [Hhit Hseen]; split; [exact Hhit|].
    apply (proj2 (inner_seen_start_87 rows x i p Hi Hhit)); exact Hseen.
  - destruct H as [Hhit Hseen]; split; [exact Hhit|].
    apply (proj1 (inner_seen_start_87 rows x i p Hi Hhit)); exact Hseen.
Qed.

Lemma coords_state_inner_to_outer_87 : forall rows x i coords,
  coords_state_87 rows x (inner_seen_87 i (-1)) coords ->
  coords_state_87 rows x (outer_seen_87 (i + 1)) coords.
Proof.
  intros rows x i coords [Hnd Hmem]; split; [exact Hnd|].
  intros p; rewrite Hmem.
  split; intro H.
  - destruct H as [Hhit Hseen]; split; [exact Hhit|].
    apply (proj1 (inner_seen_end_87 rows x i p Hhit)); exact Hseen.
  - destruct H as [Hhit Hseen]; split; [exact Hhit|].
    apply (proj2 (inner_seen_end_87 rows x i p Hhit)); exact Hseen.
Qed.

Lemma coords_state_inner_hit_87 : forall rows x i j coords,
  coord_hits rows x (i, j) ->
  coords_state_87 rows x (inner_seen_87 i j) coords ->
  coords_state_87 rows x (inner_seen_87 i (j - 1)) (coords ++ [(i, j)]).
Proof.
  intros rows x i j coords Hcur [Hnd Hmem]; split.
  - apply NoDup_app.
    + exact Hnd.
    + constructor; [simpl; tauto|constructor].
    +
    intros p Hp Hpj.
    simpl in Hpj; destruct Hpj as [Hpj|Hpj]; [subst p|contradiction].
    apply Hmem in Hp; destruct Hp as [_ Hseen].
    unfold inner_seen_87 in Hseen; cbn in Hseen; lia.
  - intro p; rewrite in_app_iff; simpl.
    split; intro H.
    + destruct H as [H|H].
      * apply Hmem in H; destruct H as [Hhit Hseen].
        split; [exact Hhit|].
        apply (proj2 (inner_seen_step_87 rows x i j p Hhit)).
        left; exact Hseen.
      * destruct (@in_inv (Z * Z) (i, j) p nil H) as [Heq|Hnil].
        -- destruct p as [r c]; injection Heq as Hr Hc; subst r; subst c.
           split; [exact Hcur|].
           unfold inner_seen_87; cbn; right; split; lia.
        -- contradiction.
    + destruct H as [Hhit Hseen].
      apply (proj1 (inner_seen_step_87 rows x i j p Hhit)) in Hseen.
      destruct Hseen as [Hseen|Hp].
      * left; apply Hmem; split; assumption.
      * right; left; symmetry; exact Hp.
Qed.

Lemma coords_state_inner_miss_87 : forall rows x i j coords,
  ~ coord_hits rows x (i, j) ->
  coords_state_87 rows x (inner_seen_87 i j) coords ->
  coords_state_87 rows x (inner_seen_87 i (j - 1)) coords.
Proof.
  intros rows x i j coords Hmiss [Hnd Hmem]; split; [exact Hnd|].
  intro p; rewrite Hmem; split; intro H.
  - destruct H as [Hhit Hseen].
    split; [exact Hhit|].
    apply (proj2 (inner_seen_step_87 rows x i j p Hhit)).
    left; exact Hseen.
  - destruct H as [Hhit Hseen].
    split; [exact Hhit|].
    apply (proj1 (inner_seen_step_87 rows x i j p Hhit)) in Hseen.
    destruct Hseen as [Hseen|Hp]; [exact Hseen|].
    subst p; contradiction.
Qed.

Lemma count_outer_0_87 : forall rows x,
  count_scan_outer_87 rows x 0 0.
Proof.
  intros; exists []; split; [reflexivity|apply coords_state_outer_0_87].
Qed.

Lemma count_outer_to_inner_87 : forall rows x i count,
  0 <= i < Zlength rows ->
  count_scan_outer_87 rows x i count ->
  count_scan_inner_87 rows x i (Zlength (Znth i rows nil) - 1) count.
Proof.
  intros rows x i count Hi [coords [Hlen Hstate]].
  exists coords; split; [exact Hlen|].
  apply coords_state_outer_to_inner_87; assumption.
Qed.

Lemma count_inner_hit_87 : forall rows x i j count,
  coord_hits rows x (i, j) ->
  count_scan_inner_87 rows x i j count ->
  count_scan_inner_87 rows x i (j - 1) (count + 1).
Proof.
  intros rows x i j count Hhit [coords [Hlen Hstate]].
  exists (coords ++ [(i, j)]); split.
  - rewrite Zlength_correct, app_length; simpl.
    rewrite Zlength_correct in Hlen; lia.
  - apply coords_state_inner_hit_87; assumption.
Qed.

Lemma count_inner_miss_87 : forall rows x i j count,
  ~ coord_hits rows x (i, j) ->
  count_scan_inner_87 rows x i j count ->
  count_scan_inner_87 rows x i (j - 1) count.
Proof.
  intros rows x i j count Hmiss [coords [Hlen Hstate]].
  exists coords; split; [exact Hlen|].
  apply coords_state_inner_miss_87; assumption.
Qed.

Lemma count_inner_to_outer_87 : forall rows x i count,
  count_scan_inner_87 rows x i (-1) count ->
  count_scan_outer_87 rows x (i + 1) count.
Proof.
  intros rows x i count [coords [Hlen Hstate]].
  exists coords; split; [exact Hlen|].
  apply coords_state_inner_to_outer_87; exact Hstate.
Qed.

Lemma strongly_sorted_snoc_87 : forall {A} (R : A -> A -> Prop) l a,
  StronglySorted R l -> Forall (fun b => R b a) l ->
  StronglySorted R (l ++ [a]).
Proof.
  intros A R l; induction l as [|b l IH]; intros a Hsort Hall.
  - simpl; apply SSorted_cons; constructor.
  - inversion Hsort as [|? ? Htail Hbefore]; subst.
    inversion Hall as [|? ? Hba Hrest]; subst.
    simpl; apply SSorted_cons.
    + apply IH; assumption.
    + apply Forall_app; split.
      * exact Hbefore.
      * constructor; [exact Hba|constructor].
Qed.

Lemma seen_before_current_87 : forall rows x i j p,
  coord_hits rows x p ->
  inner_seen_87 i j p ->
  coord_hits rows x (i, j) ->
  coord_order p (i, j).
Proof.
  intros rows x i j [r c] Hhit Hseen Hcur.
  unfold inner_seen_87 in Hseen; cbn in Hseen.
  unfold coord_order; cbn.
  destruct Hseen as [Hlt|[Heq Hgt]]; [left; exact Hlt|].
  right; split; [exact Heq|lia].
Qed.

Lemma fill_outer_0_87 : forall rows x,
  fill_scan_outer_87 rows x 0 [].
Proof.
  intros; split; [apply coords_state_outer_0_87|constructor].
Qed.

Lemma fill_outer_to_inner_87 : forall rows x i coords,
  0 <= i < Zlength rows ->
  fill_scan_outer_87 rows x i coords ->
  fill_scan_inner_87 rows x i (Zlength (Znth i rows nil) - 1) coords.
Proof.
  intros rows x i coords Hi [Hstate Hsort]; split; [|exact Hsort].
  apply coords_state_outer_to_inner_87; assumption.
Qed.

Lemma fill_inner_hit_87 : forall rows x i j coords,
  coord_hits rows x (i, j) ->
  fill_scan_inner_87 rows x i j coords ->
  fill_scan_inner_87 rows x i (j - 1) (coords ++ [(i, j)]).
Proof.
  intros rows x i j coords Hcur [Hstate Hsort]; split.
  - apply coords_state_inner_hit_87; assumption.
  - apply strongly_sorted_snoc_87; [exact Hsort|].
    apply Forall_forall; intros p Hp.
    apply Hstate in Hp; destruct Hp as [Hhit Hseen].
    apply seen_before_current_87 with (rows := rows) (x := x); assumption.
Qed.

Lemma fill_inner_miss_87 : forall rows x i j coords,
  ~ coord_hits rows x (i, j) ->
  fill_scan_inner_87 rows x i j coords ->
  fill_scan_inner_87 rows x i (j - 1) coords.
Proof.
  intros rows x i j coords Hmiss [Hstate Hsort]; split; [|exact Hsort].
  apply coords_state_inner_miss_87; assumption.
Qed.

Lemma fill_inner_to_outer_87 : forall rows x i coords,
  fill_scan_inner_87 rows x i (-1) coords ->
  fill_scan_outer_87 rows x (i + 1) coords.
Proof.
  intros rows x i coords [Hstate Hsort]; split; [|exact Hsort].
  apply coords_state_inner_to_outer_87; exact Hstate.
Qed.

Lemma fill_finished_87 : forall rows x coords,
  fill_scan_outer_87 rows x (Zlength rows) coords ->
  get_row_finished_87 rows x coords.
Proof.
  intros rows x coords [Hstate Hsort].
  unfold get_row_finished_87, problem_87_spec_z, problem_87_spec.
  destruct Hstate as [_ Hmem].
  split.
  - intro p; specialize (Hmem p).
    split; intro H.
    + apply Hmem in H; destruct H as [Hhit Hseen]; exact Hhit.
    + apply Hmem; split; [exact H|].
      unfold outer_seen_87; destruct H as [row [Hrow [_ [Hr _]]]].
      assert (Hlt : (Z.to_nat (fst p) < length rows)%nat).
      { apply (proj1 (nth_error_Some rows (Z.to_nat (fst p)))).
        rewrite Hrow; discriminate. }
      rewrite Zlength_correct.
      apply (proj2 (Z2Nat.inj_lt (fst p) (Z.of_nat (length rows)) Hr ltac:(lia))).
      rewrite Nat2Z.id; exact Hlt.
  - apply StronglySorted_Sorted; exact Hsort.
Qed.

Lemma count_fill_length_87 : forall rows x count coords,
  count_scan_outer_87 rows x (Zlength rows) count ->
  fill_scan_outer_87 rows x (Zlength rows) coords ->
  Zlength coords = count.
Proof.
  intros rows x count coords [count_coords [Hcount Hcount_state]]
    [Hfill_state Hfill_sort].
  destruct Hcount_state as [Hcount_nd Hcount_mem].
  destruct Hfill_state as [Hfill_nd Hfill_mem].
  assert (Hperm : Permutation coords count_coords).
  { apply NoDup_Permutation; try assumption.
    intro p; rewrite Hfill_mem, Hcount_mem; tauto. }
  rewrite <- Hcount.
  rewrite !Zlength_correct.
  f_equal; apply Permutation_length; exact Hperm.
Qed.

Lemma fill_inner_room_87 : forall rows x i j count coords,
  i < Zlength rows ->
  coord_hits rows x (i, j) ->
  count_scan_outer_87 rows x (Zlength rows) count ->
  fill_scan_inner_87 rows x i j coords ->
  Zlength coords < count.
Proof.
  intros rows x i j count coords Hi Hcur
    [count_coords [Hcount Hcount_state]] [Hfill_state Hfill_sort].
  destruct Hcount_state as [Hcount_nd Hcount_mem].
  destruct Hfill_state as [Hfill_nd Hfill_mem].
  assert (Hnext_nd : NoDup (coords ++ [(i, j)])).
  { pose proof (coords_state_inner_hit_87 rows x i j coords Hcur
      (conj Hfill_nd Hfill_mem)) as Hnext.
    exact (proj1 Hnext). }
  assert (Hincl : incl (coords ++ [(i, j)]) count_coords).
  { intros [r c] Hp.
    apply Hcount_mem; split.
    - apply in_app_iff in Hp; destruct Hp as [Hp|Hp].
      + apply Hfill_mem in Hp; exact (proj1 Hp).
      + simpl in Hp; destruct Hp as [Hp|Hp].
        * inversion Hp; subst; exact Hcur.
        * contradiction.
    - unfold outer_seen_87; simpl.
      apply in_app_iff in Hp; destruct Hp as [Hp|Hp].
      + apply Hfill_mem in Hp; destruct Hp as [_ Hseen].
        unfold inner_seen_87 in Hseen; simpl in Hseen.
        destruct Hseen as [Hlt|[Heq Hgt]]; lia.
      + simpl in Hp; destruct Hp as [Hp|Hp].
        * inversion Hp; subst; lia.
        * contradiction. }
  pose proof (NoDup_incl_length Hnext_nd Hincl) as Hlen.
  rewrite app_length in Hlen; simpl in Hlen.
  rewrite !Zlength_correct in Hcount |- *.
  lia.
Qed.
