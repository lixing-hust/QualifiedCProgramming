Load "../spec/129".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.

Definition nat_row_of_z_129 (row : list Z) : list nat :=
  map Z.to_nat row.

Definition nat_grid_of_z_129 (rows : list (list Z)) : list (list nat) :=
  map nat_row_of_z_129 rows.

Definition nat_list_of_z_129 (xs : list Z) : list nat :=
  map Z.to_nat xs.

Definition problem_129_pre_z (rows : list (list Z)) (k : Z) : Prop :=
  0 <= k /\ problem_129_pre (nat_grid_of_z_129 rows) (Z.to_nat k).

Definition problem_129_spec_z (rows : list (list Z)) (k : Z) (output : list Z) : Prop :=
  0 <= k /\ problem_129_spec (nat_grid_of_z_129 rows) (Z.to_nat k) (nat_list_of_z_129 output).

Definition cell_value_z_129 (rows : list (list Z)) (x y v : Z) : Prop :=
  0 <= x /\ 0 <= y /\
  cell_value (nat_grid_of_z_129 rows) (Z.to_nat x, Z.to_nat y) (Z.to_nat v).

Definition one_pos_z_129 (rows : list (list Z)) (x y : Z) : Prop :=
  0 <= x /\ 0 <= y /\ Znth y (Znth x rows nil) 0 = 1.

Definition scanned_before_129 (n i j r c : Z) : Prop :=
  0 <= r < n /\
  0 <= c < n /\
  (r < i \/ (r = i /\ c < j)).

Definition no_one_before_129 (rows : list (list Z)) (n i j : Z) : Prop :=
  forall r c,
    scanned_before_129 n i j r c ->
    Znth c (Znth r rows nil) 0 <> 1.

Definition find_one_scan_state_129
    (rows : list (list Z)) (n i j x y : Z) : Prop :=
  0 <= i <= n /\
  0 <= j <= n /\
  0 <= x < n /\
  0 <= y < n /\
  (one_pos_z_129 rows x y \/ no_one_before_129 rows n i j).

Definition neighbor_min_z_129 (rows : list (list Z)) (x y minv : Z) : Prop :=
  0 <= x /\ 0 <= y /\ 0 <= minv /\
  cell_value (nat_grid_of_z_129 rows) (Z.to_nat x, Z.to_nat y) 1 /\
  is_neighbor_min_of_one (nat_grid_of_z_129 rows) (Z.to_nat minv).

Definition output_value_129 (i minv : Z) : Z :=
  if Z.even i then 1 else minv.

Definition output_prefix_129 (k minv i : Z) (output : list Z) : Prop :=
  0 <= i <= k /\
  Zlength output = i /\
  forall t, 0 <= t < i -> Znth t output 0 = output_value_129 t minv.

Lemma output_prefix_snoc_129 :
  forall k minv i output v,
    output_prefix_129 k minv i output ->
    0 <= i < k ->
    v = output_value_129 i minv ->
    output_prefix_129 k minv (i + 1) (output ++ v :: nil).
Proof.
  intros k minv i output v Hprefix Hi Hv.
  unfold output_prefix_129 in *.
  destruct Hprefix as [Hi_b [Hlen Hnth]].
  split; [lia |].
  split.
  - rewrite Zlength_app. rewrite Hlen. change (Zlength (v :: nil)) with 1. lia.
  - intros t Ht.
    assert (t < i \/ t = i) as [Htlt | ->] by lia.
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hnth; lia.
    + rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen.
      replace (i - i) with 0 by lia.
      change (Znth 0 (v :: nil) 0) with v.
      exact Hv.
Qed.

Definition dir_neighbor_value_129
    (rows : list (list Z)) (n x y d v : Z) : Prop :=
  (d = 0 /\ 0 < x /\ x < n /\ 0 <= y < n /\
     v = Znth y (Znth (x - 1) rows nil) 0) \/
  (d = 1 /\ 0 <= x /\ x + 1 < n /\ 0 <= y < n /\
     v = Znth y (Znth (x + 1) rows nil) 0) \/
  (d = 2 /\ 0 <= x < n /\ 0 < y /\ y < n /\
     v = Znth (y - 1) (Znth x rows nil) 0) \/
  (d = 3 /\ 0 <= x < n /\ 0 <= y /\ y + 1 < n /\
     v = Znth (y + 1) (Znth x rows nil) 0).

Definition checked_neighbor_min_129
    (rows : list (list Z)) (n x y stage minv : Z) : Prop :=
  0 <= stage <= 4 /\
  0 <= x < n /\
  0 <= y < n /\
  1 <= minv <= n * n /\
  (forall d v,
      0 <= d < stage ->
      dir_neighbor_value_129 rows n x y d v ->
      minv <= v) /\
  (minv = n * n \/
   exists d v,
     0 <= d < stage /\
     dir_neighbor_value_129 rows n x y d v /\
     minv = v).

Definition find_one_state_129 (rows : list (list Z)) (n i j x y : Z) : Prop :=
  0 <= i <= n /\
  0 <= j <= n /\
  0 <= x < n /\
  0 <= y < n /\
  one_pos_z_129 rows x y.

Lemma find_one_scan_state_step_not_one_129 :
  forall rows n i j x y,
    0 <= i < n ->
    0 <= j < n ->
    find_one_scan_state_129 rows n i j x y ->
    Znth j (Znth i rows nil) 0 <> 1 ->
    find_one_scan_state_129 rows n i (j + 1) x y.
Proof.
  intros rows n i j x y Hi Hj Hscan Hneq.
  unfold find_one_scan_state_129 in *.
  destruct Hscan as [Hi_b [Hj_b [Hx_b [Hy_b Hcase]]]].
  repeat split; try lia.
  destruct Hcase as [Hfound | Hnone].
  - left; exact Hfound.
  - right.
    unfold no_one_before_129 in *.
    intros r c Hbefore.
    unfold scanned_before_129 in Hbefore.
    destruct Hbefore as [[Hr0 Hrn] [[Hc0 Hcn] Hpos]].
    destruct Hpos as [Hri | [Hri Hcj]].
    + apply Hnone.
      unfold scanned_before_129.
      repeat split; lia.
    + subst r.
      assert (c < j \/ c = j) as [Hclt | Hceq] by lia.
      * apply Hnone.
        unfold scanned_before_129.
        repeat split; lia.
      * subst c; exact Hneq.
Qed.

Lemma find_one_scan_state_finish_row_129 :
  forall rows n i j x y,
    0 <= i < n ->
    j >= n ->
    j <= n ->
    find_one_scan_state_129 rows n i j x y ->
    find_one_scan_state_129 rows n (i + 1) 0 x y.
Proof.
  intros rows n i j x y Hi Hj_ge Hj_le Hscan.
  unfold find_one_scan_state_129 in *.
  destruct Hscan as [Hi_b [Hj_b [Hx_b [Hy_b Hcase]]]].
  repeat split; try lia.
  destruct Hcase as [Hfound | Hnone].
  - left; exact Hfound.
  - right.
    unfold no_one_before_129 in *.
    intros r c Hbefore.
    apply Hnone.
    unfold scanned_before_129 in *.
    destruct Hbefore as [[Hr0 Hrn] [[Hc0 Hcn] Hpos]].
    repeat split; try lia.
Qed.

Lemma find_one_scan_state_found_129 :
  forall rows n i x y one_x one_y row_default,
    Zlength rows = n ->
    (forall r, 0 <= r < n -> Zlength (Znth r rows row_default) = n) ->
    0 <= one_x < n ->
    0 <= one_y < n ->
    Znth one_y (Znth one_x rows row_default) 0 = 1 ->
    i >= n ->
    i <= n ->
    find_one_scan_state_129 rows n i 0 x y ->
    find_one_state_129 rows n n 0 x y.
Proof.
  intros rows n i x y one_x one_y row_default Hlen Hrow Hox Hoy Hone Hi_ge Hi_le Hscan.
  unfold find_one_scan_state_129 in Hscan.
  unfold find_one_state_129, one_pos_z_129 in *.
  destruct Hscan as [Hi_b [_ [Hx_b [Hy_b Hcase]]]].
  repeat split; try lia.
  destruct Hcase as [Hfound | Hnone].
  - destruct Hfound as [_ [_ Heq]].
    exact Heq.
  - exfalso.
    assert (Hone_nil : Znth one_y (Znth one_x rows nil) 0 = 1).
    {
      rewrite (Znth_indep rows one_x nil row_default) by lia.
      exact Hone.
    }
    apply (Hnone one_x one_y).
    + unfold scanned_before_129.
      repeat split; try lia.
    + exact Hone_nil.
Qed.

Lemma checked_neighbor_min_init_129 :
  forall rows n x y,
    2 <= n ->
    find_one_state_129 rows n n 0 x y ->
    checked_neighbor_min_129 rows n x y 0 (n * n).
Proof.
  intros rows n x y Hn Hfind.
  unfold checked_neighbor_min_129.
  unfold find_one_state_129 in Hfind.
  destruct Hfind as [_ [_ [Hx [Hy _]]]].
  repeat split; try lia.
Qed.

Lemma checked_neighbor_min_step_absent_129 :
  forall rows n x y stage minv,
    0 <= stage < 4 ->
    checked_neighbor_min_129 rows n x y stage minv ->
    (forall v, ~ dir_neighbor_value_129 rows n x y stage v) ->
    checked_neighbor_min_129 rows n x y (stage + 1) minv.
Proof.
  intros rows n x y stage minv Hstage Hchecked Habsent.
  unfold checked_neighbor_min_129 in *.
  destruct Hchecked as [Hstage_b [Hx [Hy [Hmin [Hle Hex]]]]].
  repeat split; try lia.
  - intros d v Hd Hdir.
    assert (d < stage \/ d = stage) as [Hdlt | ->] by lia.
    + apply (Hle d v); try lia; exact Hdir.
    + exfalso; apply (Habsent v); exact Hdir.
  - destruct Hex as [Hinit | [d [v [Hd [Hdir Heq]]]]].
    + left; exact Hinit.
    + right; exists d, v; repeat split; try lia; assumption.
Qed.

Lemma checked_neighbor_min_step_keep_129 :
  forall rows n x y stage minv v,
    0 <= stage < 4 ->
    checked_neighbor_min_129 rows n x y stage minv ->
    dir_neighbor_value_129 rows n x y stage v ->
    minv <= v ->
    checked_neighbor_min_129 rows n x y (stage + 1) minv.
Proof.
  intros rows n x y stage minv v Hstage Hchecked Hdir_stage Hcmp.
  unfold checked_neighbor_min_129 in *.
  destruct Hchecked as [Hstage_b [Hx [Hy [Hmin [Hle Hex]]]]].
  repeat split; try lia.
  - intros d w Hd Hdir.
    assert (d < stage \/ d = stage) as [Hdlt | ->] by lia.
    + apply (Hle d w); try lia; exact Hdir.
    + assert (w = v).
      {
        unfold dir_neighbor_value_129 in Hdir_stage, Hdir.
        repeat
          match goal with
          | H : _ \/ _ |- _ => destruct H as [H | H]
          | H : _ /\ _ |- _ => destruct H as [? H]
          end; try lia.
      }
      subst w; exact Hcmp.
  - destruct Hex as [Hinit | [d [w [Hd [Hdir Heq]]]]].
    + left; exact Hinit.
    + right; exists d, w; repeat split; try lia; assumption.
Qed.

Lemma checked_neighbor_min_step_update_129 :
  forall rows n x y stage minv v,
    0 <= stage < 4 ->
    checked_neighbor_min_129 rows n x y stage minv ->
    dir_neighbor_value_129 rows n x y stage v ->
    v < minv ->
    1 <= v <= n * n ->
    checked_neighbor_min_129 rows n x y (stage + 1) v.
Proof.
  intros rows n x y stage minv v Hstage Hchecked Hdir_stage Hcmp Hv.
  unfold checked_neighbor_min_129 in *.
  destruct Hchecked as [Hstage_b [Hx [Hy [Hmin [Hle Hex]]]]].
  repeat split; try lia.
  - intros d w Hd Hdir.
    assert (d < stage \/ d = stage) as [Hdlt | ->] by lia.
    + assert (minv <= w) by (apply (Hle d w); try lia; exact Hdir).
      lia.
    + assert (w = v).
      {
        unfold dir_neighbor_value_129 in Hdir_stage, Hdir.
        repeat
          match goal with
          | H : _ \/ _ |- _ => destruct H as [H | H]
          | H : _ /\ _ |- _ => destruct H as [? H]
          end; try lia.
      }
      subst w; lia.
  - right.
    exists stage, v.
    repeat split; try lia; assumption.
Qed.

Lemma Zlength_map_129 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma length_of_Zlength_129 : forall {A : Type} (l : list A) n,
  0 <= n ->
  Zlength l = n ->
  length l = Z.to_nat n.
Proof.
  intros A l n Hn Hlen.
  apply Nat2Z.inj.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma nth_map_Znth_129 :
  forall {A B : Type} (f : A -> B) (l : list A) i da db,
    0 <= i < Zlength l ->
    nth (Z.to_nat i) (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l da (Z.to_nat i)).
    reflexivity.
Qed.

Lemma nth_error_Znth_129 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_error_nth'.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma nat_grid_length_129 : forall rows n,
  Zlength rows = n ->
  length (nat_grid_of_z_129 rows) = Z.to_nat n.
Proof.
  intros rows n Hlen.
  unfold nat_grid_of_z_129.
  rewrite map_length.
  apply length_of_Zlength_129.
  - rewrite <- Hlen. apply Zlength_nonneg.
  - exact Hlen.
Qed.

Lemma nat_grid_row_lengths_129 : forall rows n,
  (forall r, 0 <= r < Zlength rows -> Zlength (Znth r rows nil) = n) ->
  Forall (fun row : list nat => length row = Z.to_nat n)
         (nat_grid_of_z_129 rows).
Proof.
  induction rows as [| row rows IH]; intros n Hrow.
  - constructor.
  - unfold nat_grid_of_z_129; simpl.
    constructor.
    + unfold nat_row_of_z_129.
      rewrite map_length.
      assert (Hidx0 : 0 <= 0 < Zlength (row :: rows)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg rows). lia. }
      pose proof (Hrow 0 Hidx0) as Hrow0.
      change (Znth 0 (row :: rows) nil) with row in Hrow0.
      apply length_of_Zlength_129.
      * rewrite <- Hrow0. apply Zlength_nonneg.
      * exact Hrow0.
    + fold nat_grid_of_z_129.
      apply IH.
      intros r Hr.
      specialize (Hrow (r + 1)).
      assert (0 <= r + 1 < Zlength (row :: rows)) by (rewrite Zlength_cons; lia).
      specialize (Hrow H).
      rewrite Znth_cons in Hrow by lia.
      replace (r + 1 - 1) with r in Hrow by lia.
      exact Hrow.
Qed.

Lemma nat_grid_cell_129 :
  forall rows n r c,
    Zlength rows = n ->
    (forall r0, 0 <= r0 < n -> Zlength (Znth r0 rows nil) = n) ->
    0 <= r < n ->
    0 <= c < n ->
    grid_cell (nat_grid_of_z_129 rows) (Z.to_nat r) (Z.to_nat c) =
      Z.to_nat (Znth c (Znth r rows nil) 0).
Proof.
  intros rows n r c Hlen Hrow Hr Hc.
  unfold grid_cell, nat_grid_of_z_129, nat_row_of_z_129.
  rewrite (nth_map_Znth_129 (fun row => map Z.to_nat row) rows r nil nil).
  - rewrite (nth_map_Znth_129 Z.to_nat (Znth r rows nil) c 0 0%nat).
    + reflexivity.
    + rewrite Hrow by lia; lia.
  - rewrite Hlen; lia.
Qed.

Lemma Z_to_nat_pred_129 : forall x,
  0 < x ->
  (Z.to_nat x - 1)%nat = Z.to_nat (x - 1).
Proof.
  intros x Hx.
  rewrite Z2Nat.inj_sub by lia.
  simpl.
  reflexivity.
Qed.

Lemma Z_to_nat_succ_129 : forall x,
  0 <= x ->
  S (Z.to_nat x) = Z.to_nat (x + 1).
Proof.
  intros x Hx.
  replace (x + 1) with (Z.succ x) by lia.
  rewrite Z2Nat.inj_succ by lia.
  reflexivity.
Qed.

Lemma checked_neighbor_min_to_spec_129 :
  forall rows n x y minv,
    2 <= n ->
    Zlength rows = n ->
    (forall r, 0 <= r < n -> Zlength (Znth r rows nil) = n) ->
    (forall r c,
        0 <= r < n ->
        0 <= c < n ->
        1 <= Znth c (Znth r rows nil) 0 <= n * n) ->
    find_one_state_129 rows n n 0 x y ->
    checked_neighbor_min_129 rows n x y 4 minv ->
    is_neighbor_min_of_one (nat_grid_of_z_129 rows) (Z.to_nat minv).
Proof.
  intros rows n x y minv Hn Hlen Hrow Hrange Hfind Hchecked.
  unfold find_one_state_129, one_pos_z_129 in Hfind.
  destruct Hfind as [_ [_ [Hx [Hy [_ [_ Hone]]]]]].
  unfold checked_neighbor_min_129 in Hchecked.
  destruct Hchecked as [_ [_ [_ [Hmin [Hle Hex]]]]].
  exists (Z.to_nat n), (Z.to_nat x), (Z.to_nat y).
  repeat split.
  - apply nat_grid_length_129; exact Hlen.
  - apply nat_grid_row_lengths_129.
    intros r Hr.
    apply Hrow.
    rewrite Hlen in Hr.
    lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    lia.
  - rewrite (nat_grid_cell_129 rows n x y Hlen Hrow Hx Hy).
    rewrite Hone.
    reflexivity.
  - destruct Hex as [Hinit | [d [v [Hd [Hdir Heq]]]]].
    + destruct (Z_lt_le_dec 0 x) as [Hxpos | Hxzero].
      * left.
        split.
        -- apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
        -- rewrite (Z_to_nat_pred_129 x Hxpos).
           rewrite (nat_grid_cell_129 rows n (x - 1) y Hlen Hrow ltac:(lia) Hy).
           assert (Hdir0 : dir_neighbor_value_129 rows n x y 0
                        (Znth y (Znth (x - 1) rows nil) 0)).
           { unfold dir_neighbor_value_129; left; repeat split; lia. }
           assert (minv <= Znth y (Znth (x - 1) rows nil) 0)
             by (apply (Hle 0); try lia; exact Hdir0).
           pose proof (Hrange (x - 1) y ltac:(lia) Hy).
           apply Nat2Z.inj.
           rewrite !Z2Nat.id by lia.
           lia.
      * right; left.
        split.
        -- apply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_succ.
           rewrite !Z2Nat.id by lia.
           lia.
        -- rewrite (Z_to_nat_succ_129 x ltac:(lia)).
           rewrite (nat_grid_cell_129 rows n (x + 1) y Hlen Hrow ltac:(lia) Hy).
           assert (Hdir1 : dir_neighbor_value_129 rows n x y 1
                        (Znth y (Znth (x + 1) rows nil) 0)).
           { unfold dir_neighbor_value_129; right; left; repeat split; lia. }
           assert (minv <= Znth y (Znth (x + 1) rows nil) 0)
             by (apply (Hle 1); try lia; exact Hdir1).
           pose proof (Hrange (x + 1) y ltac:(lia) Hy).
           apply Nat2Z.inj.
           rewrite !Z2Nat.id by lia.
           lia.
    + unfold dir_neighbor_value_129 in Hdir.
      destruct Hdir as [[Hd0 [Hr0 [Hr1 [Hc Heqv]]]] |
        [[Hd0 [Hr0 [Hr1 [Hc Heqv]]]] |
        [[Hd0 [Hr0 [Hc0 [Hc1 Heqv]]]] |
         [Hd0 [Hr0 [Hc0 [Hc1 Heqv]]]]]]]; subst d minv.
      all: subst v.
      * left.
        split.
        -- apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
        -- rewrite (Z_to_nat_pred_129 x Hr0).
           rewrite (nat_grid_cell_129 rows n (x - 1) y Hlen Hrow ltac:(lia) Hc).
           reflexivity.
      * right; left.
        split.
        -- apply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_succ.
           rewrite !Z2Nat.id by lia.
           lia.
        -- rewrite (Z_to_nat_succ_129 x Hr0).
           rewrite (nat_grid_cell_129 rows n (x + 1) y Hlen Hrow ltac:(lia) Hc).
           reflexivity.
      * right; right; left.
        split.
        -- apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
        -- rewrite (Z_to_nat_pred_129 y Hc0).
           rewrite (nat_grid_cell_129 rows n x (y - 1) Hlen Hrow Hr0 ltac:(lia)).
           reflexivity.
      * right; right; right.
        split.
        -- apply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_succ.
           rewrite !Z2Nat.id by lia.
           lia.
        -- rewrite (Z_to_nat_succ_129 y Hc0).
           rewrite (nat_grid_cell_129 rows n x (y + 1) Hlen Hrow Hr0 ltac:(lia)).
           reflexivity.
  - intros Hxpos.
    assert (0 < x).
    { apply Nat2Z.inj_lt in Hxpos.
      rewrite Z2Nat.id in Hxpos by lia; simpl in Hxpos; lia. }
    rewrite (Z_to_nat_pred_129 x H).
    rewrite (nat_grid_cell_129 rows n (x - 1) y Hlen Hrow ltac:(lia) Hy).
    assert (Hdir : dir_neighbor_value_129 rows n x y 0
                  (Znth y (Znth (x - 1) rows nil) 0)).
    { unfold dir_neighbor_value_129; left; repeat split; lia. }
    assert (Hval := Hrange (x - 1) y ltac:(lia) Hy).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 0); try lia; exact Hdir.
  - intros Hxsucc.
    assert (x + 1 < n).
    { apply Nat2Z.inj_lt in Hxsucc.
      rewrite Nat2Z.inj_succ in Hxsucc.
      rewrite !Z2Nat.id in Hxsucc by lia.
      lia. }
    rewrite (Z_to_nat_succ_129 x ltac:(lia)).
    rewrite (nat_grid_cell_129 rows n (x + 1) y Hlen Hrow ltac:(lia) Hy).
    assert (Hdir : dir_neighbor_value_129 rows n x y 1
                  (Znth y (Znth (x + 1) rows nil) 0)).
    { unfold dir_neighbor_value_129; right; left; repeat split; lia. }
    assert (Hval := Hrange (x + 1) y ltac:(lia) Hy).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 1); try lia; exact Hdir.
  - intros Hypos.
    assert (0 < y).
    { apply Nat2Z.inj_lt in Hypos.
      rewrite Z2Nat.id in Hypos by lia; simpl in Hypos; lia. }
    rewrite (Z_to_nat_pred_129 y H).
    rewrite (nat_grid_cell_129 rows n x (y - 1) Hlen Hrow Hx ltac:(lia)).
    assert (Hdir : dir_neighbor_value_129 rows n x y 2
                  (Znth (y - 1) (Znth x rows nil) 0)).
    { unfold dir_neighbor_value_129; right; right; left; repeat split; lia. }
    assert (Hval := Hrange x (y - 1) Hx ltac:(lia)).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 2); try lia; exact Hdir.
  - intros Hysucc.
    assert (y + 1 < n).
    { apply Nat2Z.inj_lt in Hysucc.
      rewrite Nat2Z.inj_succ in Hysucc.
      rewrite !Z2Nat.id in Hysucc by lia.
      lia. }
    rewrite (Z_to_nat_succ_129 y ltac:(lia)).
    rewrite (nat_grid_cell_129 rows n x (y + 1) Hlen Hrow Hx ltac:(lia)).
    assert (Hdir : dir_neighbor_value_129 rows n x y 3
                  (Znth (y + 1) (Znth x rows nil) 0)).
    { unfold dir_neighbor_value_129; right; right; right; repeat split; lia. }
    assert (Hval := Hrange x (y + 1) Hx ltac:(lia)).
    apply Z2Nat.inj_le; try lia.
    apply (Hle 3); try lia; exact Hdir.
Qed.

Definition min_neighbor_state_129 (rows : list (list Z)) (n x y minv : Z) : Prop :=
  checked_neighbor_min_129 rows n x y 4 minv /\
  is_neighbor_min_of_one (nat_grid_of_z_129 rows) (Z.to_nat minv).

Lemma Z_even_of_nat_129 : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n.
  - reflexivity.
  - rewrite Nat.even_succ.
    rewrite <- Nat.negb_even.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
    rewrite Z.even_add.
    simpl.
    rewrite IHn.
    destruct (Nat.even n); reflexivity.
Qed.

Lemma output_prefix_to_alternating_129 :
  forall k minv output,
    0 <= k ->
    output_prefix_129 k minv k output ->
    alternating_min_path_values (Z.to_nat k) (Z.to_nat minv)
      (nat_list_of_z_129 output).
Proof.
  intros k minv output Hk Hprefix.
  unfold output_prefix_129 in Hprefix.
  destruct Hprefix as [_ [Hlen Hnth]].
  unfold alternating_min_path_values, nat_list_of_z_129.
  split.
  - rewrite map_length.
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - intros i Hi.
    assert (Ht : 0 <= Z.of_nat i < k).
    {
      split; [lia|].
      apply Nat2Z.inj_lt in Hi.
      rewrite Z2Nat.id in Hi by lia.
      exact Hi.
    }
    specialize (Hnth (Z.of_nat i) Ht).
    rewrite nth_error_map.
    replace i with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite (nth_error_Znth_129 output (Z.of_nat i) 0).
    + rewrite Nat2Z.id.
      rewrite Hnth.
      unfold output_value_129.
      rewrite Z_even_of_nat_129.
      destruct (Nat.even i); reflexivity.
    + rewrite Hlen; exact Ht.
Qed.

Lemma min_neighbor_output_spec_129 :
  forall rows n x y minv k output,
    0 <= k ->
    min_neighbor_state_129 rows n x y minv ->
    output_prefix_129 k minv k output ->
    problem_129_spec_z rows k output.
Proof.
  intros rows n x y minv k output Hk Hstate Hprefix.
  unfold problem_129_spec_z.
  split; [exact Hk|].
  unfold problem_129_spec.
  destruct Hstate as [_ Hmin].
  exists (Z.to_nat minv).
  split.
  - exact Hmin.
  - apply output_prefix_to_alternating_129; assumption.
Qed.
