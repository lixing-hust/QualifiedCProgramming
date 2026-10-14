From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* Only implementation-derived finite-sequence mathematics; no old case imports. *)
Definition copy_lookup_count (xs : list Z) : Z := Z.of_nat (length xs).
Definition copy_lookup_at (xs : list Z) (slot : Z) : Z :=
  nth (Z.to_nat (slot - 17)) xs 0.
Definition copy_lookup_prefix_absent (xs : list Z) (key upto : Z) : Prop :=
  forall j, 17 <= j < upto -> copy_lookup_at xs j <> key.
Definition copy_lookup_first (xs : list Z) (key finish r : Z) : Prop :=
  17 <= r < finish /\ r < 17 + copy_lookup_count xs /\
  copy_lookup_at xs r = key /\ copy_lookup_prefix_absent xs key r.

(* This is a memory-safety domain, not an assumed output. An out-of-bounds
   endpoint is permitted whenever an earlier in-bounds match stops all reads. *)
Definition copy_lookup_read_safe (xs : list Z) (key finish : Z) : Prop :=
  0 <= finish <= 4294967295 /\ copy_lookup_count xs <= 238 /\
  (finish <= 17 + copy_lookup_count xs \/
   exists j, 17 <= j < finish /\ j < 17 + copy_lookup_count xs /\
             copy_lookup_at xs j = key).
Definition copy_lookup_search_result (xs : list Z) (key finish r : Z) : Prop :=
  copy_lookup_first xs key finish r \/
  (r = 0 /\ finish <= 17 + copy_lookup_count xs /\
   copy_lookup_prefix_absent xs key finish).
Definition copy_lookup_result
    (prio cspace finish key : Z) (xs : list Z) (r : Z) : Prop :=
  (63 <= prio /\ r = 42) \/
  (prio < 63 /\ cspace = 0 /\ r = 0) \/
  (prio < 63 /\ cspace <> 0 /\ copy_lookup_search_result xs key finish r).
Definition copy_lookup_input_safe
    (prio cspace finish key : Z) (xs : list Z) : Prop :=
  0 <= prio <= 255 /\
  (prio < 63 -> cspace <> 0 -> copy_lookup_read_safe xs key finish).

(* Loop assertion mathematics: all earlier inspected slots fail; immutable
   storage and the original safety domain will be carried spatially in C. *)
Definition copy_lookup_scan_inv (xs : list Z) (key finish i : Z) : Prop :=
  17 <= i /\ i <= Z.max 17 finish /\ i <= 17 + copy_lookup_count xs /\
  copy_lookup_prefix_absent xs key i /\ copy_lookup_read_safe xs key finish.

(* Pointer-field ownership, using the shared C layout's symbolic field names.
   This is a strided structure-field collection, not a second contiguous array
   model. Only the actually used union object pointer view is owned. *)
From Coq Require Import String.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope sac.
Definition copy_lookup_object_address (p stride i : Z) : Z :=
  let slots := eval_addr_expr
    (RE_addr_of
      (LE_dot_field (LE_arrow_field (RE_const p (FET_alias "cspace"))
                                    "cnode") "slots")) in
  eval_addr_expr
    (RE_addr_of
      (LE_dot_field
        (LE_dot_field
          (LE_dot_field
            (LE_arrow_field (RE_const (slots + i * stride) (FET_alias "slot"))
                            "capability") "cap_content") "object") "object_t")).
Fixpoint copy_lookup_cells (p stride lo : Z) (xs : list Z) : Assertion :=
  match xs with
  | nil => emp
  | x :: tail => store_ptr (copy_lookup_object_address p stride lo) x **
                 copy_lookup_cells p stride (lo + 1) tail
  end.
Fixpoint copy_lookup_cells_hole (p stride lo : Z) (xs : list Z) (skip : Z)
    : Assertion :=
  match xs with
  | nil => emp
  | x :: tail =>
      if Z.eq_dec lo skip then copy_lookup_cells p stride (lo + 1) tail
      else store_ptr (copy_lookup_object_address p stride lo) x **
           copy_lookup_cells_hole p stride (lo + 1) tail skip
  end.

From Coq Require Import Lia.
Lemma copy_lookup_active_bound__cells_scan xs key finish i :
  copy_lookup_scan_inv xs key finish i -> i < finish ->
  i < 17 + copy_lookup_count xs.
Proof.
  intros [Hlo [Hmax [Hbound [Habs [Hfinish [Hcount Hsafe]]]]]] Hlt.
  destruct Hsafe as [Hend | [j [[Hjlo Hjend] [Hjb Hmatch]]]]; [lia|].
  destruct (Z_lt_ge_dec j i); [exfalso; apply (Habs j); [lia|exact Hmatch]|lia].
Qed.
Lemma copy_lookup_cells_extract__cells_scan p stride lo xs i :
  lo <= i < lo + Z.of_nat (List.length xs) ->
  copy_lookup_cells p stride lo xs |--
  copy_lookup_cells_hole p stride lo xs i **
  store_ptr (copy_lookup_object_address p stride i) (nth (Z.to_nat (i-lo)) xs 0).
Proof.
  revert lo i. induction xs as [|x xs IH]; intros lo i Hb.
  - simpl in Hb. lia.
  - simpl List.length in Hb. rewrite Nat2Z.inj_succ in Hb.
    simpl copy_lookup_cells. simpl copy_lookup_cells_hole.
    destruct (Z.eq_dec lo i) as [Heq|Hne].
    + subst i. replace (lo-lo) with 0 by lia. simpl Z.to_nat. simpl nth. cancel.
    + assert (Ht : lo+1 <= i < lo+1+Z.of_nat(List.length xs)) by lia.
      assert (Hi : Z.to_nat(i-lo) = S (Z.to_nat(i-(lo+1)))).
      { replace (i-lo) with (Z.succ (i-(lo+1))) by lia.
        rewrite Z2Nat.inj_succ by lia. reflexivity. }
      rewrite Hi. simpl nth.
      sep_apply_l_atomic (IH (lo+1) i Ht). cancel.
Qed.
Lemma copy_lookup_cells_restore__cells_scan p stride lo xs i :
  lo <= i < lo + Z.of_nat (List.length xs) ->
  copy_lookup_cells_hole p stride lo xs i **
  store_ptr (copy_lookup_object_address p stride i) (nth (Z.to_nat (i-lo)) xs 0)
  |-- copy_lookup_cells p stride lo xs.
Proof.
  revert lo i. induction xs as [|x xs IH]; intros lo i Hb.
  - simpl in Hb. lia.
  - simpl List.length in Hb. rewrite Nat2Z.inj_succ in Hb.
    simpl copy_lookup_cells. simpl copy_lookup_cells_hole.
    destruct (Z.eq_dec lo i) as [Heq|Hne].
    + subst i. replace (lo-lo) with 0 by lia. simpl Z.to_nat. simpl nth. cancel.
    + assert (Ht : lo+1 <= i < lo+1+Z.of_nat(List.length xs)) by lia.
      assert (Hi : Z.to_nat(i-lo) = S (Z.to_nat(i-(lo+1)))).
      { replace (i-lo) with (Z.succ (i-(lo+1))) by lia.
        rewrite Z2Nat.inj_succ by lia. reflexivity. }
      rewrite Hi. simpl nth.
      sep_apply_l_atomic (IH (lo+1) i Ht). cancel.
Qed.
