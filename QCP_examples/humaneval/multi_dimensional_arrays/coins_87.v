Load "../spec/87".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Fixpoint flatten_coords_87 (coords : list (Z * Z)) : list Z :=
  match coords with
  | [] => []
  | (r, c) :: rest => r :: c :: flatten_coords_87 rest
  end.

Definition problem_87_pre_z (rows : list (list Z)) (x : Z) : Prop :=
  problem_87_pre rows x.

Definition problem_87_spec_z
    (rows : list (list Z)) (x : Z) (output : list Z) : Prop :=
  exists coords,
    problem_87_spec rows x coords /\
    output = flatten_coords_87 coords.

Definition row_sizes_match_87
    (rows : list (list Z)) (sizes : list Z) : Prop :=
  Zlength sizes = Zlength rows /\
  forall i,
    0 <= i < Zlength rows ->
    Znth i sizes 0 = Zlength (Znth i rows nil).

Definition total_cells_prefix_87 (rows : list (list Z)) (i : Z) : Z :=
  fold_left Z.add
    (map (fun row => Zlength row) (firstn (Z.to_nat i) rows)) 0.

Definition coord_if_87 (row : list Z) (r x c : Z) : list (Z * Z) :=
  if Znth c row 0 =? x then [(r, c)] else [].

Definition desc_cols_after_87 (row : list Z) (j : Z) : list Z :=
  rev (map Z.of_nat
         (seq (Z.to_nat (j + 1))
              (Z.to_nat (Zlength row - (j + 1))))).

Fixpoint collect_coords_row_desc_87
    (row : list Z) (r c x : Z) : list (Z * Z) :=
  match row with
  | [] => []
  | h :: t =>
      collect_coords_row_desc_87 t r (Z.succ c) x ++
      if h =? x then [(r, c)] else []
  end.

Definition row_desc_after_87 (row : list Z) (r j x : Z) : list (Z * Z) :=
  collect_coords_row_desc_87 (skipn (Z.to_nat (j + 1)) row) r (j + 1) x.

Definition scan_coords_87
    (rows : list (list Z)) (x i j : Z) : list (Z * Z) :=
  sort_coords (collect_all_coords (firstn (Z.to_nat i) rows) 0 x) ++
  row_desc_after_87 (Znth i rows nil) i j x.

Definition scan_state_87
    (rows : list (list Z)) (x i j : Z) (output : list Z) : Prop :=
  if i <? Zlength rows then
    output = flatten_coords_87 (scan_coords_87 rows x i j)
  else
    output = flatten_coords_87 (get_row_impl rows x).

Definition prefix_state_87
    (rows : list (list Z)) (x i : Z) (output : list Z) : Prop :=
  output =
    flatten_coords_87
      (sort_coords (collect_all_coords (firstn (Z.to_nat i) rows) 0 x)).

Lemma flatten_coords_87_length : forall coords,
  Zlength (flatten_coords_87 coords) = 2 * Zlength coords.
Proof.
  induction coords as [| [r c] rest IH].
  - simpl. reflexivity.
  - simpl flatten_coords_87.
    repeat rewrite Zlength_cons.
    rewrite IH.
    lia.
Qed.

Lemma flatten_coords_87_app : forall a b,
  flatten_coords_87 (a ++ b) =
  flatten_coords_87 a ++ flatten_coords_87 b.
Proof.
  induction a as [| [r c] rest IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma total_cells_prefix_87_0 : forall rows,
  total_cells_prefix_87 rows 0 = 0.
Proof.
  intros rows. unfold total_cells_prefix_87. reflexivity.
Qed.

Lemma fold_left_Zadd_app_87 : forall l x,
  fold_left Z.add l x = x + fold_left Z.add l 0.
Proof.
  induction l as [| a l IH]; intros x; simpl.
  - repeat rewrite Zlength_correct. simpl. lia.
  - rewrite IH. rewrite (IH a). lia.
Qed.

Lemma fold_left_Zadd_nonneg_87 : forall l x,
  0 <= x ->
  (forall z, In z l -> 0 <= z) ->
  0 <= fold_left Z.add l x.
Proof.
  induction l as [| a l IH]; intros x Hx Hall; simpl.
  - exact Hx.
  - apply IH.
    + specialize (Hall a ltac:(left; reflexivity)). lia.
    + intros z Hz. apply Hall. right; exact Hz.
Qed.

Lemma fold_left_Zadd_app_nonneg_le_87 : forall a b,
  (forall z, In z b -> 0 <= z) ->
  fold_left Z.add a 0 <= fold_left Z.add (a ++ b) 0.
Proof.
  intros a b Hb.
  rewrite fold_left_app.
  rewrite (fold_left_Zadd_app_87 b (fold_left Z.add a 0)).
  assert (0 <= fold_left Z.add b 0).
  { apply fold_left_Zadd_nonneg_87; [lia | exact Hb]. }
  lia.
Qed.

Lemma firstn_succ_Z_87 : forall {A : Type} (rows : list A) k d,
  0 <= k < Zlength rows ->
  firstn (Z.to_nat (k + 1)) rows =
  firstn (Z.to_nat k) rows ++ [Znth k rows d].
Proof.
  assert (Hnth: forall {A : Type} (rows : list A) n d,
    (n < List.length rows)%nat ->
    firstn (S n) rows = firstn n rows ++ [nth n rows d]).
  {
    intros A rows.
    induction rows as [| row rest IH]; intros [| n] d Hlt; simpl in *; try lia.
    - reflexivity.
    - rewrite (IH n d) by lia. reflexivity.
  }
  intros A rows k d Hk.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite (Hnth A rows (Z.to_nat k) d) by (rewrite Zlength_correct in Hk; lia).
  unfold Znth. reflexivity.
Qed.

Lemma total_cells_prefix_87_step : forall rows i,
  0 <= i < Zlength rows ->
  total_cells_prefix_87 rows (i + 1) =
  total_cells_prefix_87 rows i + Zlength (Znth i rows nil).
Proof.
  intros rows i Hi.
  unfold total_cells_prefix_87.
  rewrite firstn_succ_Z_87 with (d := nil) by exact Hi.
  rewrite map_app. simpl.
  rewrite fold_left_app. simpl.
  rewrite fold_left_Zadd_app_87. lia.
Qed.

Lemma total_cells_prefix_87_nonneg_monotone : forall rows i,
  0 <= i <= Zlength rows ->
  0 <= total_cells_prefix_87 rows i <= total_cells_prefix_87 rows (Zlength rows).
Proof.
  intros rows i Hi.
  unfold total_cells_prefix_87.
  remember (Z.to_nat i) as n.
  assert (Hnlen : (n <= length rows)%nat).
  { subst n.
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia. }
  split.
  - apply fold_left_Zadd_nonneg_87; [lia |].
    intros z Hz.
    apply in_map_iff in Hz.
    destruct Hz as [row [<- _]].
    apply Zlength_nonneg.
  - replace (Z.to_nat (Zlength rows)) with (length rows).
    2:{ rewrite Zlength_correct. symmetry. apply Nat2Z.id. }
    rewrite firstn_all.
    rewrite <- (firstn_skipn n rows) at 2.
    rewrite map_app.
    apply fold_left_Zadd_app_nonneg_le_87.
    intros z Hz.
    apply in_map_iff in Hz.
    destruct Hz as [row [<- _]].
    apply Zlength_nonneg.
Qed.

Lemma desc_cols_after_87_end : forall row,
  desc_cols_after_87 row (Zlength row - 1) = nil.
Proof.
  intros row.
  unfold desc_cols_after_87.
  replace (Zlength row - 1 + 1) with (Zlength row) by lia.
  replace (Z.to_nat (Zlength row - Zlength row)) with O by lia.
  reflexivity.
Qed.

Lemma row_desc_after_87_end : forall row r x,
  row_desc_after_87 row r (Zlength row - 1) x = nil.
Proof.
  intros row r x.
  unfold row_desc_after_87.
  replace (Zlength row - 1 + 1) with (Zlength row) by lia.
  replace (Z.to_nat (Zlength row)) with (length row).
  - rewrite skipn_all. reflexivity.
  - rewrite Zlength_correct. symmetry. apply Nat2Z.id.
Qed.

Lemma skipn_Znth_cons_87 : forall {A : Type} (row : list A) j d,
  0 <= j < Zlength row ->
  skipn (Z.to_nat j) row =
  Znth j row d :: skipn (Z.to_nat (j + 1)) row.
Proof.
  assert (Hskip: forall {A : Type} (row : list A) n d,
    (n < length row)%nat ->
    skipn n row = nth n row d :: skipn (S n) row).
  {
    intros A row.
    induction row as [| h t IH]; intros [| n] d Hn; simpl in *; try lia.
    - reflexivity.
    - apply IH. lia.
  }
  intros A row j d Hj.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  rewrite (Hskip A row (Z.to_nat j) d).
  - unfold Znth. reflexivity.
  - rewrite Zlength_correct in Hj. lia.
Qed.

Lemma scan_state_87_start : forall rows sizes x i out,
  row_sizes_match_87 rows sizes ->
  0 <= i < Zlength rows ->
  prefix_state_87 rows x i out ->
  scan_state_87 rows x i (Znth i sizes 0 - 1) out.
Proof.
  intros rows sizes x i out Hmatch Hi Hprefix.
  unfold scan_state_87.
  destruct (i <? Zlength rows) eqn:Hlt.
  - unfold scan_coords_87.
    destruct Hmatch as [_ Hsizes].
    rewrite Hsizes by lia.
    rewrite row_desc_after_87_end.
    rewrite app_nil_r.
    exact Hprefix.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma desc_cols_after_87_step : forall row j,
  0 <= j < Zlength row ->
  desc_cols_after_87 row (j - 1) = desc_cols_after_87 row j ++ [j].
Proof.
  intros row j Hj.
  unfold desc_cols_after_87.
  replace (j - 1 + 1) with j by lia.
  replace (Z.to_nat (Zlength row - j))
    with (S (Z.to_nat (Zlength row - (j + 1)))) by lia.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  simpl.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma row_desc_after_87_match_step : forall row r j x,
  0 <= j < Zlength row ->
  Znth j row 0 = x ->
  row_desc_after_87 row r (j - 1) x =
  row_desc_after_87 row r j x ++ [(r, j)].
Proof.
  intros row r j x Hj Hx.
  unfold row_desc_after_87.
  replace (j - 1 + 1) with j by lia.
  rewrite skipn_Znth_cons_87 with (d := 0) by lia.
  simpl.
  rewrite Hx, Z.eqb_refl.
  replace (j + 1) with (Z.succ j) by lia.
  reflexivity.
Qed.

Lemma scan_state_87_match_step : forall rows x i j out,
  0 <= i < Zlength rows ->
  0 <= j < Zlength (Znth i rows nil) ->
  Znth j (Znth i rows nil) 0 = x ->
  scan_state_87 rows x i j out ->
  scan_state_87 rows x i (j - 1) (out ++ [i; j]).
Proof.
  intros rows x i j out Hi Hj Hx Hscan.
  unfold scan_state_87 in *.
  destruct (i <? Zlength rows) eqn:Hlt.
  - unfold scan_coords_87 in *.
    rewrite Hscan.
    rewrite row_desc_after_87_match_step by lia.
    repeat rewrite flatten_coords_87_app.
    simpl.
    rewrite app_assoc.
    reflexivity.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma row_desc_after_87_nomatch_step : forall row r j x,
  0 <= j < Zlength row ->
  Znth j row 0 <> x ->
  row_desc_after_87 row r (j - 1) x =
  row_desc_after_87 row r j x.
Proof.
  intros row r j x Hj Hx.
  unfold row_desc_after_87.
  replace (j - 1 + 1) with j by lia.
  rewrite skipn_Znth_cons_87 with (d := 0) by lia.
  simpl.
  destruct (Znth j row 0 =? x) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - replace (j + 1) with (Z.succ j) by lia.
    rewrite app_nil_r. reflexivity.
Qed.

Lemma scan_state_87_nomatch_step : forall rows x i j out,
  0 <= i < Zlength rows ->
  0 <= j < Zlength (Znth i rows nil) ->
  Znth j (Znth i rows nil) 0 <> x ->
  scan_state_87 rows x i j out ->
  scan_state_87 rows x i (j - 1) out.
Proof.
  intros rows x i j out Hi Hj Hx Hscan.
  unfold scan_state_87 in *.
  destruct (i <? Zlength rows) eqn:Hlt.
  - unfold scan_coords_87 in *.
    rewrite Hscan.
    rewrite row_desc_after_87_nomatch_step by lia.
    reflexivity.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma insert_coord_87_length : forall coord coords,
  Zlength (insert_coord coord coords) = 1 + Zlength coords.
Proof.
  assert (Hlen: forall coord coords,
    length (insert_coord coord coords) = S (length coords)).
  {
    intros coord coords.
    induction coords as [| h t IH]; simpl.
    - reflexivity.
    - repeat destruct (_ <? _); repeat destruct (_ =? _); simpl;
        try rewrite IH; reflexivity.
  }
  intros coord coords.
  repeat rewrite Zlength_correct.
  rewrite Hlen.
  lia.
Qed.

Lemma sort_coords_87_length : forall coords,
  Zlength (sort_coords coords) = Zlength coords.
Proof.
  induction coords as [| h t IH]; simpl.
  - reflexivity.
  - rewrite insert_coord_87_length, IH.
    rewrite Zlength_cons. lia.
Qed.

Lemma insert_coord_87_between : forall left right r c,
  (forall p, In p left -> fst p = r /\ c < snd p) ->
  (forall p, In p right -> r < fst p) ->
  insert_coord (r, c) (left ++ right) = left ++ (r, c) :: right.
Proof.
  induction left as [| [hr hc] left IH]; intros right r c Hleft Hright.
  - destruct right as [| [rr rc] right].
    + reflexivity.
    + simpl.
      assert (r < fst (rr, rc)) as Hr by (apply Hright; left; reflexivity).
      simpl in Hr.
      replace (r <? rr) with true by (symmetry; apply Z.ltb_lt; lia).
      reflexivity.
  - simpl in *.
    assert (fst (hr, hc) = r /\ c < snd (hr, hc)) as Hhead.
    { apply Hleft. left; reflexivity. }
    simpl in Hhead.
    destruct Hhead as [-> Hc].
    rewrite Z.ltb_irrefl.
    rewrite Z.eqb_refl.
    replace (hc <? c) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite IH.
    + reflexivity.
    + intros p Hp. apply Hleft. right; exact Hp.
    + exact Hright.
Qed.

Lemma insert_coord_87_preserves_row_gt : forall coord coords r,
  r < fst coord ->
  (forall p, In p coords -> r < fst p) ->
  forall p, In p (insert_coord coord coords) -> r < fst p.
Proof.
  intros coord coords r Hcoord Hcoords.
  induction coords as [| h t IH]; simpl; intros p Hp.
  - destruct Hp as [<- | []]. exact Hcoord.
  - destruct (fst coord <? fst h) eqn:Hlt.
    + simpl in Hp.
      destruct Hp as [<- | Hp].
      * exact Hcoord.
      * apply Hcoords. exact Hp.
    + destruct (fst coord =? fst h) eqn:Heq.
      * destruct (snd h <? snd coord) eqn:Hcol.
        -- simpl in Hp.
           destruct Hp as [<- | Hp].
           ++ exact Hcoord.
           ++ apply Hcoords. exact Hp.
        -- simpl in Hp.
           destruct Hp as [<- | Hp].
           ++ apply Hcoords. left; reflexivity.
           ++ apply IH.
              ** intros q Hq. apply Hcoords. right; exact Hq.
              ** exact Hp.
      * simpl in Hp.
        destruct Hp as [<- | Hp].
        -- apply Hcoords. left; reflexivity.
        -- apply IH.
           ++ intros q Hq. apply Hcoords. right; exact Hq.
           ++ exact Hp.
Qed.

Lemma sort_coords_87_preserves_row_gt : forall coords r,
  (forall p, In p coords -> r < fst p) ->
  forall p, In p (sort_coords coords) -> r < fst p.
Proof.
  induction coords as [| coord rest IH]; intros r Hcoords p Hp; simpl in Hp.
  - contradiction.
  - apply insert_coord_87_preserves_row_gt with (coord := coord) (coords := sort_coords rest).
    + apply Hcoords. left; reflexivity.
    + intros q Hq. apply IH.
      * intros z Hz. apply Hcoords. right; exact Hz.
      * exact Hq.
    + exact Hp.
Qed.

Lemma collect_coords_row_87_fst : forall row r c x p,
  In p (collect_coords_row row r c x) ->
  fst p = r.
Proof.
  induction row as [| h t IH]; intros r c x p Hp; simpl in Hp.
  - contradiction.
  - destruct (h =? x) eqn:Heq.
    + destruct Hp as [Hp | Hp].
      * subst p. reflexivity.
      * apply IH in Hp. exact Hp.
    + apply IH in Hp. exact Hp.
Qed.

Lemma collect_all_coords_87_row_ge : forall rows r x p,
  In p (collect_all_coords rows r x) ->
  r <= fst p.
Proof.
  induction rows as [| row rest IH]; intros r x p Hp; simpl in Hp.
  - contradiction.
  - apply in_app_or in Hp. destruct Hp as [Hp | Hp].
    + apply collect_coords_row_87_fst in Hp. lia.
    + specialize (IH (Z.succ r) x p Hp). lia.
Qed.

Lemma collect_coords_row_desc_87_fst_ge : forall row r c x p,
  In p (collect_coords_row_desc_87 row r c x) ->
  fst p = r /\ c <= snd p.
Proof.
  induction row as [| h t IH]; intros r c x p Hp; simpl in Hp.
  - contradiction.
  - apply in_app_or in Hp. destruct Hp as [Hp | Hp].
    + specialize (IH r (Z.succ c) x p Hp). simpl in IH. lia.
    + destruct (h =? x); simpl in Hp.
      * destruct Hp as [<- | []]. simpl. lia.
      * contradiction.
Qed.

Lemma sort_coords_collect_row_app_87 : forall row tail r c x,
  (forall p, In p tail -> r < fst p) ->
  sort_coords (collect_coords_row row r c x ++ tail) =
  collect_coords_row_desc_87 row r c x ++ sort_coords tail.
Proof.
  induction row as [| h t IH]; intros tail r c x Htail.
  - reflexivity.
  - simpl collect_coords_row.
    simpl collect_coords_row_desc_87.
    destruct (h =? x) eqn:Heq.
    + simpl sort_coords.
      rewrite IH by exact Htail.
      rewrite insert_coord_87_between.
      * rewrite <- app_assoc. reflexivity.
      * intros p Hp.
        pose proof (collect_coords_row_desc_87_fst_ge t r (Z.succ c) x p Hp)
          as [Hfst Hsnd].
        simpl in Hsnd. lia.
      * apply sort_coords_87_preserves_row_gt. exact Htail.
    + rewrite IH by exact Htail.
      rewrite app_nil_r.
      reflexivity.
Qed.

Fixpoint collect_all_coords_desc_87
    (rows : list (list Z)) (r x : Z) : list (Z * Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      collect_coords_row_desc_87 row r 0 x ++
      collect_all_coords_desc_87 rest (Z.succ r) x
  end.

Lemma collect_all_coords_desc_87_app : forall left right r x,
  collect_all_coords_desc_87 (left ++ right) r x =
  collect_all_coords_desc_87 left r x ++
  collect_all_coords_desc_87 right (r + Zlength left) x.
Proof.
  induction left as [| row rest IH]; intros right r x; simpl.
  - replace (r + Zlength []) with r by (rewrite Zlength_nil; lia).
    reflexivity.
  - rewrite IH.
    rewrite app_assoc.
    replace (Z.succ r + Zlength rest)
      with (r + Zlength (row :: rest)) by (rewrite Zlength_cons; lia).
    reflexivity.
Qed.

Lemma sort_collect_all_coords_desc_87 : forall rows r x,
  sort_coords (collect_all_coords rows r x) =
  collect_all_coords_desc_87 rows r x.
Proof.
  induction rows as [| row rest IH]; intros r x; simpl.
  - reflexivity.
  - rewrite sort_coords_collect_row_app_87.
    + rewrite IH. reflexivity.
    + intros p Hp.
      pose proof (collect_all_coords_87_row_ge rest (Z.succ r) x p Hp).
      lia.
Qed.

Lemma Zlength_firstn_87 : forall {A : Type} (rows : list A) i,
  0 <= i <= Zlength rows ->
  Zlength (firstn (Z.to_nat i) rows) = i.
Proof.
  intros A rows i Hi.
  rewrite Zlength_correct.
  rewrite firstn_length.
  rewrite Nat.min_l.
  - rewrite Z2Nat.id by lia. reflexivity.
  - apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma row_desc_after_87_minus_one : forall row r x,
  row_desc_after_87 row r (-1) x = collect_coords_row_desc_87 row r 0 x.
Proof.
  intros row r x.
  unfold row_desc_after_87.
  replace (-1 + 1) with 0 by lia.
  reflexivity.
Qed.

Lemma scan_coords_87_row_done : forall rows x i,
  0 <= i < Zlength rows ->
  scan_coords_87 rows x i (-1) =
  sort_coords (collect_all_coords (firstn (Z.to_nat (i + 1)) rows) 0 x).
Proof.
  intros rows x i Hi.
  unfold scan_coords_87.
  rewrite row_desc_after_87_minus_one.
  repeat rewrite sort_collect_all_coords_desc_87.
  rewrite firstn_succ_Z_87 with (d := nil) by lia.
  rewrite collect_all_coords_desc_87_app.
  simpl.
  rewrite app_nil_r.
  rewrite Zlength_firstn_87 by lia.
  replace (0 + i) with i by lia.
  reflexivity.
Qed.

Lemma scan_state_87_done : forall rows x i j output,
  0 <= i < Zlength rows ->
  -1 <= j < 0 ->
  scan_state_87 rows x i j output ->
  prefix_state_87 rows x (i + 1) output.
Proof.
  intros rows x i j output Hi Hj Hscan.
  assert (j = -1) by lia. subst j.
  unfold scan_state_87 in Hscan.
  unfold prefix_state_87.
  destruct (i <? Zlength rows) eqn:Hlt.
  - rewrite Hscan.
    rewrite scan_coords_87_row_done by lia.
    reflexivity.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma prefix_state_87_complete : forall rows x i output,
  i = Zlength rows ->
  prefix_state_87 rows x i output ->
  problem_87_spec_z rows x output.
Proof.
  intros rows x i output Hi Hprefix.
  subst i.
  unfold prefix_state_87 in Hprefix.
  unfold problem_87_spec_z, problem_87_spec, get_row_impl.
  exists (sort_coords (collect_all_coords rows 0 x)).
  split; [reflexivity |].
  rewrite Hprefix.
  replace (Z.to_nat (Zlength rows)) with (length rows).
  - rewrite firstn_all. reflexivity.
  - rewrite Zlength_correct. symmetry. apply Nat2Z.id.
Qed.

Lemma collect_coords_row_87_length_le : forall row r c x,
  Zlength (collect_coords_row row r c x) <= Zlength row.
Proof.
  induction row as [| h t IH]; intros r c x.
  - repeat rewrite Zlength_correct. simpl. lia.
  - simpl collect_coords_row.
    destruct (h =? x); repeat rewrite Zlength_cons;
      specialize (IH r (Z.succ c) x); lia.
Qed.

Lemma collect_coords_row_desc_87_length_le : forall row r c x,
  Zlength (collect_coords_row_desc_87 row r c x) <= Zlength row.
Proof.
  induction row as [| h t IH]; intros r c x.
  - repeat rewrite Zlength_correct. simpl. lia.
  - simpl collect_coords_row_desc_87.
    rewrite Zlength_app.
    specialize (IH r (Z.succ c) x).
    destruct (h =? x); repeat rewrite Zlength_correct in *; simpl in *; lia.
Qed.

Lemma collect_all_coords_87_length_le_list : forall rows r x,
  Zlength (collect_all_coords rows r x) <=
  fold_left Z.add (map (fun row => Zlength row) rows) 0.
Proof.
  induction rows as [| row rest IH]; intros r x; simpl.
  - repeat rewrite Zlength_correct. simpl. lia.
  - rewrite Zlength_app.
    pose proof (collect_coords_row_87_length_le row r 0 x).
    specialize (IH (Z.succ r) x).
    rewrite (fold_left_Zadd_app_87 (map (fun row0 : list Z => Zlength row0) rest) (Zlength row)).
    lia.
Qed.

Lemma collect_all_coords_87_prefix_length_le : forall rows i x,
  0 <= i <= Zlength rows ->
  Zlength (collect_all_coords (firstn (Z.to_nat i) rows) 0 x) <=
  total_cells_prefix_87 rows i.
Proof.
  intros rows i x Hi.
  unfold total_cells_prefix_87.
  apply collect_all_coords_87_length_le_list.
Qed.

Lemma row_desc_after_87_length_le : forall row r j x,
  0 <= j < Zlength row ->
  Zlength (row_desc_after_87 row r j x) + 1 <= Zlength row.
Proof.
  intros row r j x Hj.
  unfold row_desc_after_87.
  pose proof (collect_coords_row_desc_87_length_le
    (skipn (Z.to_nat (j + 1)) row) r (j + 1) x) as Hlen.
  assert (Hskip: Zlength (skipn (Z.to_nat (j + 1)) row) =
                 Zlength row - (j + 1)).
  {
    repeat rewrite Zlength_correct.
    rewrite length_skipn.
    rewrite Nat2Z.inj_sub by
      (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia;
       rewrite <- Zlength_correct; lia).
    rewrite Z2Nat.id by lia.
    reflexivity.
  }
  rewrite Hskip in Hlen.
  lia.
Qed.

Lemma scan_state_87_match_room : forall rows x i j out,
  0 <= i < Zlength rows ->
  0 <= j < Zlength (Znth i rows nil) ->
  Znth j (Znth i rows nil) 0 = x ->
  scan_state_87 rows x i j out ->
  Zlength out + 2 <= total_cells_prefix_87 rows (Zlength rows) * 2.
Proof.
  intros rows x i j out Hi Hj Hx Hscan.
  unfold scan_state_87 in Hscan.
  destruct (i <? Zlength rows) eqn:Hlt.
  - unfold scan_coords_87 in Hscan.
    rewrite Hscan.
    rewrite flatten_coords_87_length.
    rewrite Zlength_app.
    rewrite sort_coords_87_length.
    pose proof (collect_all_coords_87_prefix_length_le rows i x ltac:(lia)).
    pose proof (row_desc_after_87_length_le (Znth i rows nil) i j x Hj).
    pose proof (total_cells_prefix_87_step rows i Hi).
    pose proof (total_cells_prefix_87_nonneg_monotone rows (i + 1) ltac:(lia)).
    lia.
  - apply Z.ltb_ge in Hlt. lia.
Qed.
