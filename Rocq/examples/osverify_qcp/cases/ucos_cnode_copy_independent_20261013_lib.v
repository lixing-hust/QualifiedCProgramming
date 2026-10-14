(* Independently derived from the two frozen original implementation extracts.
   This is an unverified first mathematical candidate, not an OS-intent spec. *)
From Coq Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Record copy_cap := {
  copy_tag : Z;
  copy_word0 : Z;
  copy_word1 : Z;
  copy_pointer : Z
}.
Record copy_state := {
  copy_table : Z -> Z;
  copy_counter : Z -> Z;
  copy_slots : Z -> Z -> copy_cap
}.

(* Address-indexed maps identify aliases; they do not duplicate ownership. *)
Definition copy_state_same (a b : copy_state) : Prop :=
  (forall p, copy_table b p = copy_table a p) /\
  (forall p, copy_counter b p = copy_counter a p) /\
  (forall p i, copy_slots b p i = copy_slots a p i).
Definition copy_first_match (a : copy_state) (p obj e k : Z) : Prop :=
  17 <= k < e /\ copy_pointer (copy_slots a p k) = obj /\
  (forall j, 17 <= j < k -> copy_pointer (copy_slots a p j) <> obj).
Definition copy_no_match (a : copy_state) (p obj e : Z) : Prop :=
  forall j, 17 <= j < e -> copy_pointer (copy_slots a p j) <> obj.
Definition copy_lookup (a : copy_state) (prio obj r : Z) : Prop :=
  (63 <= prio /\ r = 42) \/
  (prio < 63 /\
   ((copy_table a prio = 0 /\ r = 0) \/
    (copy_table a prio <> 0 /\
     ((r = 0 /\ copy_no_match a (copy_table a prio) obj (copy_counter a prio)) \/
      copy_first_match a (copy_table a prio) obj (copy_counter a prio) r)))).

(* Safety is a first-hit property, not a blanket bound on the counter. *)
Definition copy_lookup_safe (a : copy_state) (prio obj : Z) : Prop :=
  prio < 63 -> copy_table a prio <> 0 ->
  copy_counter a prio <= 255 \/
  exists k, k < 255 /\
    copy_first_match a (copy_table a prio) obj (copy_counter a prio) k.

Definition copy_category_effect (a b : copy_state) (d s f : Z) : Prop :=
  (forall p, copy_table b p = copy_table a p) /\
  (forall p, copy_counter b p = copy_counter a p) /\
  (forall p i,
    copy_slots b p i =
    if Z.eq_dec p (copy_table a d) then
      if Z.eq_dec i f then
        {| copy_tag := 1;
           copy_word0 := copy_word0 (copy_slots a (copy_table a s) f);
           copy_word1 := copy_word1 (copy_slots a (copy_table a s) f);
           copy_pointer := copy_pointer (copy_slots a p i) |}
      else copy_slots a p i
    else copy_slots a p i).
Definition copy_object_effect (a b : copy_state) (d s f k inc : Z) : Prop :=
  (forall p, copy_table b p = copy_table a p) /\
  (forall p, copy_counter b p =
    if Z.eq_dec p d then copy_counter a p + inc else copy_counter a p) /\
  (forall p i,
    copy_slots b p i =
    if Z.eq_dec p (copy_table a d) then
      if Z.eq_dec i k then
        {| copy_tag := 2;
           copy_word0 := copy_word0 (copy_slots a (copy_table a s) f);
           copy_word1 := copy_word1 (copy_slots a p i);
           copy_pointer := copy_pointer (copy_slots a (copy_table a s) f) |}
      else copy_slots a p i
    else copy_slots a p i).

(* Complete disjoint priority-ordered return relation. Writes preserve all
   unmentioned fields; scalar C ownership must connect this relation to memory. *)
Definition copy_result (a b : copy_state) (d s f ret : Z) : Prop :=
  ((255 <= f \/ 64 <= d \/ 64 <= s) /\ ret = 6 /\ copy_state_same a b) \/
  (f < 255 /\ d < 64 /\ s < 64 /\
    (((copy_table a d = 0 \/ copy_table a s = 0) /\ ret = 6 /\ copy_state_same a b) \/
     (copy_table a d <> 0 /\ copy_table a s <> 0 /\
       ((copy_tag (copy_slots a (copy_table a s) f) = 1 /\
          ret = 0 /\ copy_category_effect a b d s f) \/
        (copy_tag (copy_slots a (copy_table a s) f) <> 1 /\
         copy_tag (copy_slots a (copy_table a s) f) <> 2 /\
          ret = 6 /\ copy_state_same a b) \/
        (copy_tag (copy_slots a (copy_table a s) f) = 2 /\
         exists r, copy_lookup a d (copy_pointer (copy_slots a (copy_table a s) f)) r /\
          ((r = 0 /\ 255 <= copy_counter a d /\ ret = 2 /\ copy_state_same a b) \/
           (r = 0 /\ copy_counter a d < 255 /\ ret = 0 /\
             copy_object_effect a b d s f (copy_counter a d) 1) \/
           (r <> 0 /\ ret = 0 /\ copy_object_effect a b d s f r 0))))))).

Definition copy_scalar_domain (d s f : Z) : Prop :=
  0 <= d <= 255 /\ 0 <= s <= 255 /\ 0 <= f <= 4294967295.
Definition copy_semantic_safe (a : copy_state) (d s f : Z) : Prop :=
  copy_scalar_domain d s f /\
  (f < 255 -> d < 64 -> s < 64 ->
   copy_table a d <> 0 -> copy_table a s <> 0 ->
   copy_tag (copy_slots a (copy_table a s) f) = 2 ->
   copy_lookup_safe a d (copy_pointer (copy_slots a (copy_table a s) f))).

From Coq Require Import String.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope sac.

(* A finite resource map: one typed view per physical scalar cell. None owns
   writable uninitialized storage; Some v additionally records initialization. *)
Record copy_cell := { copy_cell_addr : Z; copy_cell_ptr : bool;
                      copy_cell_value : option Z }.
Definition copy_cell_heap (c : copy_cell) : Assertion :=
  match copy_cell_ptr c, copy_cell_value c with
  | true, Some v => store_ptr (copy_cell_addr c) v
  | true, None => undef_store_ptr (copy_cell_addr c)
  | false, Some v => store_uint (copy_cell_addr c) v
  | false, None => undef_store_uint (copy_cell_addr c)
  end.
Fixpoint copy_heap (h : list copy_cell) : Assertion :=
  match h with nil => emp | c :: t => copy_cell_heap c ** copy_heap t end.
Definition copy_read (h : list copy_cell) (addr : Z) (ptr : bool) (v : Z) : Prop :=
  In {|copy_cell_addr := addr; copy_cell_ptr := ptr; copy_cell_value := Some v|} h.
Definition copy_writable (h : list copy_cell) (addr : Z) (ptr : bool) : Prop :=
  exists v, In {|copy_cell_addr := addr; copy_cell_ptr := ptr; copy_cell_value := v|} h.
Definition copy_slot_lvalue (p stride i : Z) : lvalue_expr :=
  let slots := eval_addr_expr (RE_addr_of
    (LE_dot_field (LE_arrow_field (RE_const p (FET_alias "cspace")) "cnode") "slots")) in
  LE_arrow_field (RE_const (slots+i*stride) (FET_alias "slot")) "capability".
Definition copy_cap_address (p stride i : Z) : Z :=
  eval_addr_expr (RE_addr_of (copy_slot_lvalue p stride i)).
Definition copy_tag_address (p stride i : Z) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field (copy_slot_lvalue p stride i) "cap_type")).
Definition copy_content_address (p stride i : Z) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field (copy_slot_lvalue p stride i) "cap_content")).
Definition copy_category_address (p stride i : Z) (name : string) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field
    (LE_dot_field (copy_slot_lvalue p stride i) "cap_content") "category") name)).
Definition copy_object_address (p stride i : Z) (name : string) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field
    (LE_dot_field (copy_slot_lvalue p stride i) "cap_content") "object") name)).
Definition copy_component_address (p stride i k : Z) : Z :=
  if Z.eq_dec k 0 then copy_tag_address p stride i else
  if Z.eq_dec k 1 then copy_category_address p stride i "category_content" else
  if Z.eq_dec k 2 then copy_category_address p stride i "category_right" else
  copy_object_address p stride i "object_t".
Definition copy_typed_layout (a : copy_state) (tb nb ptrsize stride d s : Z) : Prop :=
  (forall p i, (p = copy_table a d \/ p = copy_table a s) -> 0 <= i < 255 ->
    copy_category_address p stride i "category_content" = copy_object_address p stride i "object_right" /\
    copy_category_address p stride i "category_right" = copy_object_address p stride i "Dummy_int" /\
    copy_category_address p stride i "Dummy_ptr" = copy_object_address p stride i "object_t") /\
  (forall p q i j k l,
    (p = copy_table a d \/ p = copy_table a s) ->
    (q = copy_table a d \/ q = copy_table a s) ->
    0 <= i < 255 -> 0 <= j < 255 -> 0 <= k < 4 -> 0 <= l < 4 ->
    copy_component_address p stride i k = copy_component_address q stride j l ->
    p = q /\ i = j /\ k = l) /\
  (forall p i k prio,
    (p = copy_table a d \/ p = copy_table a s) ->
    0 <= i < 255 -> 0 <= k < 4 -> 0 <= prio < 64 ->
    copy_component_address p stride i k <> tb+ptrsize*prio /\
    copy_component_address p stride i k <> nb+4*prio) /\
  (forall i j, 0 <= i < 64 -> 0 <= j < 64 -> tb+ptrsize*i <> nb+4*j).
Definition copy_live (a : copy_state) (d s f : Z) : Prop :=
  f < 255 /\ d < 64 /\ s < 64 /\ copy_table a d <> 0 /\ copy_table a s <> 0.
Definition copy_scan_reads (h : list copy_cell) (a : copy_state)
    (nb stride d obj : Z) : Prop :=
  d < 63 ->
  copy_read h (nb + 4*d) false (copy_counter a d) /\
  forall j, 17 <= j < copy_counter a d ->
    (forall k, 17 <= k < j -> copy_pointer (copy_slots a (copy_table a d) k) <> obj) ->
    j < 255 /\
    copy_read h (copy_object_address (copy_table a d) stride j "object_t") true
      (copy_pointer (copy_slots a (copy_table a d) j)).
Definition copy_object_writes_available (h : list copy_cell) (a : copy_state)
    (stride d s f k : Z) : Prop :=
  0 <= k < 255 /\
  copy_read h (copy_object_address (copy_table a s) stride f "object_right") false
    (copy_word0 (copy_slots a (copy_table a s) f)) /\
  copy_writable h (copy_tag_address (copy_table a d) stride k) false /\
  copy_writable h (copy_object_address (copy_table a d) stride k "object_right") false /\
  copy_writable h (copy_object_address (copy_table a d) stride k "object_t") true.
Definition copy_pre (h : list copy_cell) (a : copy_state)
    (tb nb ptrsize stride d s f : Z) : Prop :=
  copy_semantic_safe a d s f /\ NoDup (map copy_cell_addr h) /\
  (copy_live a d s f -> copy_typed_layout a tb nb ptrsize stride d s) /\
  (f < 255 -> d < 64 -> s < 64 ->
    copy_read h (tb + ptrsize*d) true (copy_table a d) /\
    copy_read h (tb + ptrsize*s) true (copy_table a s)) /\
  (copy_live a d s f ->
    copy_read h (copy_tag_address (copy_table a s) stride f) false
      (copy_tag (copy_slots a (copy_table a s) f))) /\
  (copy_live a d s f -> copy_tag (copy_slots a (copy_table a s) f) = 1 ->
    copy_read h (copy_category_address (copy_table a s) stride f "category_content") false
      (copy_word0 (copy_slots a (copy_table a s) f)) /\
    copy_read h (copy_category_address (copy_table a s) stride f "category_right") false
      (copy_word1 (copy_slots a (copy_table a s) f)) /\
    copy_writable h (copy_tag_address (copy_table a d) stride f) false /\
    copy_writable h (copy_category_address (copy_table a d) stride f "category_content") false /\
    copy_writable h (copy_category_address (copy_table a d) stride f "category_right") false) /\
  (copy_live a d s f -> copy_tag (copy_slots a (copy_table a s) f) = 2 ->
    copy_read h (copy_object_address (copy_table a s) stride f "object_t") true
      (copy_pointer (copy_slots a (copy_table a s) f)) /\
    copy_scan_reads h a nb stride d (copy_pointer (copy_slots a (copy_table a s) f)) /\
    (forall r, copy_lookup a d (copy_pointer (copy_slots a (copy_table a s) f)) r ->
      (r = 0 -> copy_read h (nb+4*d) false (copy_counter a d)) /\
      (r = 0 -> copy_counter a d < 255 ->
        copy_writable h (nb+4*d) false /\
        copy_object_writes_available h a stride d s f (copy_counter a d)) /\
      (r <> 0 -> copy_object_writes_available h a stride d s f r))).

Definition copy_write (h : list copy_cell) (w : Z * Z) : list copy_cell :=
  map (fun c => if Z.eq_dec (copy_cell_addr c) (fst w) then
       {|copy_cell_addr := copy_cell_addr c; copy_cell_ptr := copy_cell_ptr c;
         copy_cell_value := Some (snd w)|} else c) h.
Definition copy_write_all (h : list copy_cell) (ws : list (Z * Z)) : list copy_cell :=
  fold_left copy_write ws h.
Definition copy_category_delta (a : copy_state) (stride d s f : Z) : list (Z*Z) :=
  [(copy_tag_address (copy_table a d) stride f, 1);
   (copy_category_address (copy_table a d) stride f "category_content",
       copy_word0 (copy_slots a (copy_table a s) f));
   (copy_category_address (copy_table a d) stride f "category_right",
       copy_word1 (copy_slots a (copy_table a s) f))].
Definition copy_object_delta (a : copy_state) (stride d s f k : Z) : list (Z*Z) :=
  [(copy_tag_address (copy_table a d) stride k, 2);
   (copy_object_address (copy_table a d) stride k "object_right",
       copy_word0 (copy_slots a (copy_table a s) f));
   (copy_object_address (copy_table a d) stride k "object_t",
       copy_pointer (copy_slots a (copy_table a s) f))].
Definition copy_delta (a : copy_state) (nb stride d s f ret : Z)
    (ws : list (Z*Z)) : Prop :=
  (ret <> 0 /\ ws = []) \/
  (ret = 0 /\ copy_tag (copy_slots a (copy_table a s) f) = 1 /\
    ws = copy_category_delta a stride d s f) \/
  (ret = 0 /\ copy_tag (copy_slots a (copy_table a s) f) = 2 /\
    exists r, copy_lookup a d (copy_pointer (copy_slots a (copy_table a s) f)) r /\
      ((r = 0 /\ ws = (nb+4*d,copy_counter a d+1) ::
                           copy_object_delta a stride d s f (copy_counter a d)) \/
       (r <> 0 /\ ws = copy_object_delta a stride d s f r))).
Definition copy_post (h h' : list copy_cell) (a : copy_state)
    (nb stride d s f ret : Z) : Prop :=
  exists b ws, copy_result a b d s f ret /\ copy_delta a nb stride d s f ret ws /\
    h' = copy_write_all h ws.

Definition copy_hole (h : list copy_cell) (addr : Z) : Assertion :=
  copy_heap (filter (fun c => negb (Z.eqb (copy_cell_addr c) addr)) h).
Definition copy_two_holes (h : list copy_cell) (x y : Z) : Assertion :=
  copy_heap (filter (fun c => (negb (Z.eqb (copy_cell_addr c) x) &&
                              negb (Z.eqb (copy_cell_addr c) y))%bool) h).
Definition copy_put (h : list copy_cell) (addr value : Z) : list copy_cell :=
  copy_write h (addr,value).

From SimpleC.EE.osverify_qcp.cases Require Import ucos_get_obj_slot_copy_independent_20261013_lib.
Definition copy_lookup_agrees (a : copy_state) (d : Z) (xs : list Z) : Prop :=
  forall j, 17 <= j < 17 + Z.of_nat (List.length xs) ->
    copy_lookup_at xs j = copy_pointer (copy_slots a (copy_table a d) j).
Definition copy_call_frame (h : list copy_cell)
    (tb nb ptrsize stride d p : Z) (xs : list Z) : Assertion :=
  copy_heap (filter (fun c => (
    negb (Z.eqb (copy_cell_addr c) (tb+ptrsize*d)) &&
    negb (Z.eqb (copy_cell_addr c) (nb+4*d)) &&
    negb (existsb (fun n => Z.eqb (copy_cell_addr c)
      (copy_object_address p stride (17+Z.of_nat n) "object_t"))
      (seq 0 (List.length xs))))%bool) h).
Definition copy_allocation_state (h hc : list copy_cell) (a : copy_state)
    (nb d key idx : Z) : Prop :=
  (copy_lookup a d key 0 /\ idx = copy_counter a d /\ 0 <= idx < 255 /\
   hc = copy_put h (nb+4*d) (copy_counter a d+1)) \/
  (copy_lookup a d key idx /\ idx <> 0 /\ 0 <= idx < 255 /\ hc = h).

Definition copy_lookup_resources (tb nb ptrsize stride prio p finish : Z)
    (xs : list Z) : Assertion :=
  ((“63 <= prio” && emp) ||
   (“prio < 63” &&
    store_uint (nb+prio*4) finish ** store_ptr (tb+prio*ptrsize) p **
    ((“p = 0” && emp) || (“p <> 0” && copy_lookup_cells p stride 17 xs)))).
Definition copy_call_rest (h : list copy_cell)
    (tb nb ptrsize stride d p : Z) (xs : list Z) : Assertion :=
  if Z_lt_dec d 63 then copy_call_frame h tb nb ptrsize stride d p xs else copy_heap h.
Lemma copy_lookup_resources_equivalent tb nb ptrsize stride prio p finish xs :
  copy_lookup_resources tb nb ptrsize stride prio p finish xs --||--
  ((“63 <= prio” && emp) ||
   (“prio < 63” &&
    store_uint (nb+prio*4) finish ** store_ptr (tb+prio*ptrsize) p **
    ((“p = 0” && emp) || (“p <> 0” && copy_lookup_cells p stride 17 xs)))).
Proof. unfold copy_lookup_resources; split; cancel. Qed.

(* Call-local provenance of every cell removed from h. This fact is derived
   when selecting xs, never assumed in the function's entry precondition. *)
Definition copy_call_records (h : list copy_cell)
    (tb nb ptrsize stride d p finish : Z) (xs : list Z) : Prop :=
  d < 63 ->
  copy_read h (tb+ptrsize*d) true p /\
  copy_read h (nb+4*d) false finish /\
  (forall j, 17 <= j < 17 + Z.of_nat (List.length xs) ->
    copy_read h (copy_object_address p stride j "object_t") true (copy_lookup_at xs j)).

From Coq Require Import Sorting.Permutation.
From Coq Require Import Bool.
Lemma copy_heap_focus__access h c :
  NoDup (map copy_cell_addr h) -> In c h ->
  copy_heap h --||-- copy_cell_heap c ** copy_hole h (copy_cell_addr c).
Proof.
  intros ND IN. unfold copy_hole.
  induction h as [|x t IH]; simpl in IN; [contradiction|].
  inversion ND as [|? ? NX NT]; subst.
  destruct IN as [E|IN].
  - subst x. simpl. rewrite Z.eqb_refl. simpl.
    assert (F : filter (fun x => negb (copy_cell_addr x =? copy_cell_addr c)) t = t).
    { assert (AllKeep : forall y, In y t -> negb (copy_cell_addr y =? copy_cell_addr c) = true).
      { intros y HY. apply Bool.negb_true_iff, Z.eqb_neq.
        intro E. apply NX. rewrite <- E. apply in_map. exact HY. }
      clear IH ND NX NT. induction t as [|y u IH]; [reflexivity|].
      simpl. rewrite AllKeep by (left; reflexivity). f_equal. apply IH.
      intros z HZ. apply AllKeep. right; exact HZ. }
    rewrite F. split; cancel.
  - assert (NE : copy_cell_addr x <> copy_cell_addr c).
    { intro E. apply NX. rewrite E. apply in_map. exact IN. }
    specialize (IH NT IN).
    simpl. apply Z.eqb_neq in NE. rewrite NE. simpl.
    destruct IH as [L R]. split.
    + sep_apply_l_atomic L. cancel.
    + sep_apply_r_atomic R. cancel. cancel (copy_cell_heap c).
Qed.
Lemma copy_read_focus__access h addr ptr v :
  NoDup (map copy_cell_addr h) -> copy_read h addr ptr v ->
  copy_heap h |-- copy_hole h addr **
    (if ptr then store_ptr addr v else store_uint addr v).
Proof.
  intros ND IN.
  pose proof (proj1 (copy_heap_focus__access h
    {|copy_cell_addr:=addr;copy_cell_ptr:=ptr;copy_cell_value:=Some v|} ND IN)) as L.
  sep_apply_l_atomic L. destruct ptr; unfold copy_cell_heap; simpl; cancel.
Qed.
Lemma copy_read_restore__access h addr ptr v :
  NoDup (map copy_cell_addr h) -> copy_read h addr ptr v ->
  copy_hole h addr ** (if ptr then store_ptr addr v else store_uint addr v)
  |-- copy_heap h.
Proof.
  intros ND IN.
  pose proof (proj2 (copy_heap_focus__access h
    {|copy_cell_addr:=addr;copy_cell_ptr:=ptr;copy_cell_value:=Some v|} ND IN)) as R.
  sep_apply_r_atomic R. destruct ptr; unfold copy_cell_heap; simpl; cancel.
Qed.
Lemma copy_tag_cap_address__access p stride i :
 copy_tag_address p stride i =
 eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_type")).
Proof. unfold copy_tag_address, copy_cap_address. csimpl. reflexivity. Qed.
Lemma copy_object_cap_address__access p stride i name :
 copy_object_address p stride i name =
 eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_content") "object") name)).
Proof. unfold copy_object_address, copy_cap_address. csimpl. reflexivity. Qed.
Lemma copy_heap_focus__category_steps h c :
 NoDup (map copy_cell_addr h) -> In c h ->
 copy_heap h --||-- copy_cell_heap c ** copy_hole h (copy_cell_addr c).
Proof.
 intros Hnd Hin; unfold copy_hole.
 induction h as [|a h IH]; simpl in *; [contradiction|].
 inversion Hnd as [|? ? Hnot Htail]; subst.
 destruct Hin as [Heq|Hin].
 - subst a. rewrite Z.eqb_refl; simpl.
   assert (filter (fun c0 => negb (copy_cell_addr c0 =? copy_cell_addr c)) h = h) as E.
   { clear IH Htail Hnd. revert Hnot. induction h as [|x t IH]; simpl; intros Hnot; auto.
     assert (copy_cell_addr x <> copy_cell_addr c) as Hx.
     { intro E; apply Hnot; left; exact E. }
     apply Z.eqb_neq in Hx; rewrite Hx; simpl; f_equal.
     apply IH. intro H; apply Hnot; right; exact H. }
   rewrite E. split; cancel.
 - assert (copy_cell_addr a <> copy_cell_addr c) as Hneq.
   { intro E; apply Hnot; rewrite E; apply in_map; exact Hin. }
   apply Z.eqb_neq in Hneq. rewrite Hneq; simpl.
   specialize (IH Htail Hin). destruct IH as [IH1 IH2]. split.
   + sep_apply_l_atomic IH1. cancel.
   + sep_apply_r_atomic IH2. cancel.
all: cancel (copy_cell_heap c).
Qed.
Lemma copy_put_preserves__category_steps h x v :
 map copy_cell_addr (copy_put h x v) = map copy_cell_addr h.
Proof.
 unfold copy_put, copy_write; simpl. induction h as [|c h IH]; simpl; auto.
 destruct (Z.eq_dec (copy_cell_addr c) x); simpl; f_equal; auto.
Qed.
Lemma copy_put_read__category_steps h x v y t w : x <> y ->
 copy_read h y t w -> copy_read (copy_put h x v) y t w.
Proof.
 intros Hneq Hin. unfold copy_read, copy_put, copy_write in *; simpl.
 apply in_map_iff. exists {| copy_cell_addr := y; copy_cell_ptr := t; copy_cell_value := Some w |}.
 split; auto. simpl; destruct (Z.eq_dec y x); congruence.
Qed.
Lemma copy_put_writable__category_steps h x v y t :
 copy_writable h y t -> copy_writable (copy_put h x v) y t.
Proof.
 intros [w Hw]. unfold copy_writable, copy_put, copy_write; simpl.
 destruct (Z.eq_dec y x) as [E|E].
 - exists (Some v). apply in_map_iff. exists {| copy_cell_addr:=y;copy_cell_ptr:=t;copy_cell_value:=w |}.
   split; auto. simpl; destruct (Z.eq_dec y x); congruence.
 - exists w. apply in_map_iff. exists {| copy_cell_addr:=y;copy_cell_ptr:=t;copy_cell_value:=w |}.
   split; auto. simpl; destruct (Z.eq_dec y x); congruence.
Qed.
Lemma copy_heap_put__category_steps h x t w v :
 NoDup (map copy_cell_addr h) ->
 In {|copy_cell_addr:=x;copy_cell_ptr:=t;copy_cell_value:=w|} h ->
 copy_hole h x ** copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=t;copy_cell_value:=Some v|}
 |-- copy_heap (copy_put h x v).
Proof.
 intros Hnd Hin. unfold copy_hole, copy_put, copy_write; simpl.
 induction h as [|c h IH]; simpl in *; [contradiction|].
 inversion Hnd as [|? ? Hnot Htail]; subst.
 destruct Hin as [E|Hin].
 - subst c; simpl. rewrite Z.eqb_refl. destruct (Z.eq_dec x x); [|contradiction]. simpl.
   assert (filter (fun c => negb (copy_cell_addr c =? x)) h = h) as Ef.
   { clear IH Hnd Htail. revert Hnot. induction h as [|c h IH]; simpl; intros Hnot; auto.
     assert (copy_cell_addr c <> x) as E by (intro E; apply Hnot; auto).
     apply Z.eqb_neq in E; rewrite E; simpl; f_equal; apply IH; tauto. }
   assert (map (fun c => if Z.eq_dec (copy_cell_addr c) x then
      {|copy_cell_addr:=copy_cell_addr c;copy_cell_ptr:=copy_cell_ptr c;copy_cell_value:=Some v|} else c) h = h) as Em.
   { clear IH Hnd Htail Ef. revert Hnot. induction h as [|c h IH]; simpl; intros Hnot; auto.
     destruct (Z.eq_dec (copy_cell_addr c) x); [exfalso; apply Hnot; auto|].
     f_equal; apply IH; tauto. }
   rewrite Ef, Em; cancel.
 - assert (copy_cell_addr c <> x) as E.
   { intro E; apply Hnot; rewrite E; apply in_map with (f:=copy_cell_addr) in Hin; exact Hin. }
   assert (copy_cell_addr c =? x = false) as Eb by (apply Z.eqb_neq; exact E).
   rewrite Eb; simpl. destruct (Z.eq_dec (copy_cell_addr c) x); [contradiction|].
   specialize (IH Htail Hin). sep_apply_r_atomic IH. cancel.
all: cancel (copy_cell_heap c).
all: cancel (copy_heap (filter (fun c => negb (copy_cell_addr c =? x)) h)).
all: cancel (copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=t;copy_cell_value:=Some v|}).
Qed.
Lemma copy_filter_nodup__category_steps h (f : copy_cell -> bool) :
 NoDup (map copy_cell_addr h) -> NoDup (map copy_cell_addr (filter f h)).
Proof.
 induction h as [|c h IH]; simpl; intros H; [constructor|].
 inversion H; subst. destruct (f c); simpl; auto. constructor; auto.
 intro Hin; apply H2. apply in_map_iff in Hin as [x [E Hin]].
 apply filter_In in Hin as [Hin _]. apply in_map_iff; exists x; auto.
Qed.
Lemma copy_hole_twice__category_steps h x y :
 copy_hole (filter (fun c => negb (copy_cell_addr c =? y)) h) x = copy_two_holes h x y.
Proof.
 unfold copy_hole, copy_two_holes; f_equal.
 induction h as [|c h IH]; simpl; auto.
 destruct (copy_cell_addr c =? x) eqn:Ex, (copy_cell_addr c =? y) eqn:Ey; simpl; rewrite ?Ex, ?Ey; simpl; try exact IH; f_equal; exact IH.
Qed.
Lemma copy_heap_two_focus__category_steps h x y v :
 NoDup (map copy_cell_addr h) -> x <> y ->
 copy_writable h x false -> copy_read h y false v ->
 copy_heap h |-- copy_two_holes h x y ** store_uint y v ** undef_store_uint x.
Proof.
 intros Hnd Hneq [w Hw] Hr.
 pose proof (copy_heap_focus__category_steps h _ Hnd Hr) as [Hf _].
 cbn [copy_cell_heap copy_cell_addr copy_cell_ptr copy_cell_value] in Hf.
 sep_apply_l_atomic Hf.
 assert (Hwf : In {|copy_cell_addr:=x;copy_cell_ptr:=false;copy_cell_value:=w|}
 (filter (fun c => negb (copy_cell_addr c =? y)) h)).
 { apply filter_In; split; auto. simpl; apply Bool.negb_true_iff, Z.eqb_neq; auto. }
 pose proof (copy_heap_focus__category_steps _ _ (copy_filter_nodup__category_steps h _ Hnd) Hwf) as [Hff _].
 cbn [copy_cell_addr] in Hff.
 rewrite copy_hole_twice__category_steps in Hff.
 unfold copy_hole at 1.
 sep_apply_l_atomic Hff.
 destruct w; cbn [copy_cell_heap copy_cell_addr copy_cell_ptr copy_cell_value].
 - sep_apply store_uint_undef_store_uint. cancel.
 - cancel.
Qed.
Lemma copy_layout_separation__category_steps h a tb nb ptrsize stride d s f p q k l :
 copy_pre h a tb nb ptrsize stride d s f -> copy_live a d s f ->
 (p = copy_table a d \/ p = copy_table a s) ->
 (q = copy_table a d \/ q = copy_table a s) ->
 0 <= k < 4 -> 0 <= l < 4 -> k <> l ->
 copy_component_address p stride f k <> copy_component_address q stride f l.
Proof.
 intros [Hsafe [_ [Hlayout _]]] Hl Hp Hq Hk Hl0 Hneq Heq.
 destruct Hsafe as [[Hd [Hs Hf]] _].
 pose proof Hl as [Hf0 _].
 destruct (Hlayout Hl) as [_ [Hi _]].
 specialize (Hi p q f f k l Hp Hq ltac:(lia) ltac:(lia) Hk Hl0 Heq).
 tauto.
Qed.
Lemma copy_heap_read__category_steps h x v :
 NoDup (map copy_cell_addr h) -> copy_read h x false v ->
 copy_heap h |-- copy_hole h x ** store_uint x v.
Proof.
 intros Hn Hr. pose proof (proj1 (copy_heap_focus__category_steps h _ Hn Hr)) as Hf.
 cbn [copy_cell_heap copy_cell_addr copy_cell_ptr copy_cell_value] in Hf.
 sep_apply_l_atomic Hf. cancel.
Qed.
Lemma copy_restore_uint__category_steps h x v :
 NoDup (map copy_cell_addr h) -> copy_writable h x false ->
 copy_hole h x ** store_uint x v |-- copy_heap (copy_put h x v).
Proof.
 intros Hn [w Hw].
 exact (copy_heap_put__category_steps h x false w v Hn Hw).
Qed.
Lemma copy_filter_put__category_steps h x y v :
 filter (fun c => negb (copy_cell_addr c =? y)) (copy_put h x v) =
 copy_put (filter (fun c => negb (copy_cell_addr c =? y)) h) x v.
Proof.
 unfold copy_put, copy_write; simpl. induction h as [|c h IH]; simpl; auto.
 destruct (Z.eq_dec (copy_cell_addr c) x) eqn:Ex;
 destruct (copy_cell_addr c =? y) eqn:Ey; simpl;
 rewrite ?Ey, ?Ex; simpl; try exact IH; f_equal; exact IH.
Qed.
Lemma copy_two_restore__category_steps h x y u v :
 NoDup (map copy_cell_addr h) -> x <> y ->
 copy_writable h x false -> copy_read h y false u ->
 copy_two_holes h x y ** store_uint y u ** store_uint x v |-- copy_heap (copy_put h x v).
Proof.
 intros Hnd Hneq [w Hw] Hr.
 assert (Hwf : In {|copy_cell_addr:=x;copy_cell_ptr:=false;copy_cell_value:=w|}
 (filter (fun c => negb (copy_cell_addr c =? y)) h)).
 { apply filter_In; split; auto. simpl; apply Bool.negb_true_iff, Z.eqb_neq; auto. }
 pose proof (copy_heap_put__category_steps _ x false w v (copy_filter_nodup__category_steps h _ Hnd) Hwf) as Hput.
 rewrite copy_hole_twice__category_steps in Hput.
 rewrite <- copy_filter_put__category_steps in Hput.
 change (copy_two_holes h x y ** store_uint x v |-- copy_hole (copy_put h x v) y) in Hput.
 sep_apply_l_atomic Hput.
 pose proof (copy_put_read__category_steps h x v y false u Hneq Hr) as Hru.
 assert (Hnu : NoDup (map copy_cell_addr (copy_put h x v))) by (rewrite copy_put_preserves__category_steps; exact Hnd).
 pose proof (proj2 (copy_heap_focus__category_steps _ _ Hnu Hru)) as Hback.
 cbn [copy_cell_heap copy_cell_addr copy_cell_ptr copy_cell_value] in Hback.
 sep_apply_l_atomic Hback. cancel (copy_heap (copy_put h x v)).
Qed.
Lemma copy_lookup_refines__lookup a d xs key r :
  copy_lookup_agrees a d xs ->
  copy_lookup_result d (copy_table a d) (copy_counter a d) key xs r ->
  copy_lookup a d key r.
Proof.
  intros Hag Hr. unfold copy_lookup_result in Hr.
  destruct Hr as [[Hd Hr]|[[Hd [Hp Hr]]|[Hd [Hp Hr]]]].
  - left; auto.
  - right; split; [assumption|left; auto].
  - right; split; [assumption|right; split; [assumption|]].
    destruct Hr as [Hfirst|[Hr [Hend Habs]]].
    + right. destruct Hfirst as [Hb [Hcount [Heq Habs]]].
      unfold copy_first_match. split; [exact Hb|]. split.
      * rewrite <- Hag; [exact Heq|unfold copy_lookup_count in Hcount; lia].
      * intros j Hj. rewrite <- Hag; [apply Habs; exact Hj|unfold copy_lookup_count in Hcount; lia].
    + left; split; [exact Hr|]. intros j Hj.
      rewrite <- Hag; [apply Habs; exact Hj|unfold copy_lookup_count in Hend; lia].
Qed.
Lemma copy_filter_away__lookup h addr :
  ~ In addr (map copy_cell_addr h) ->
  filter (fun c => negb (Z.eqb (copy_cell_addr c) addr)) h = h.
Proof.
  induction h as [|c h IH]; intros H; simpl; [reflexivity|].
  assert (Hc : copy_cell_addr c <> addr) by (intro E; apply H; simpl; auto).
  apply Z.eqb_neq in Hc. rewrite Hc. simpl. f_equal. apply IH.
  intro Hin; apply H; simpl; auto.
Qed.
Lemma copy_heap_focus__lookup h c :
  NoDup (map copy_cell_addr h) -> In c h ->
  copy_heap h --||-- copy_cell_heap c ** copy_hole h (copy_cell_addr c).
Proof.
  induction h as [|x h IH]; intros Hnd Hin; [contradiction|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  destruct Hin as [Heq|Hin].
  - subst x. unfold copy_hole. simpl filter.
    rewrite Z.eqb_refl. simpl.
    rewrite copy_filter_away__lookup by exact Hnot. simpl copy_heap. split; cancel.
  - assert (Hne : copy_cell_addr x <> copy_cell_addr c).
    { intro Heq; apply Hnot. rewrite Heq. apply in_map; exact Hin. }
    unfold copy_hole at 1. simpl filter.
    apply Z.eqb_neq in Hne. rewrite Hne. simpl.
    destruct (IH Htail Hin) as [Hout Hback]. split.
    + simpl copy_heap. sep_apply_l_atomic Hout. unfold copy_hole. cancel.
    + sep_apply_r_atomic Hback. unfold copy_hole. cancel.
  cancel (copy_cell_heap c).
Qed.
Lemma copy_heap_app__lookup l r :
  copy_heap (l ++ r) --||-- copy_heap l ** copy_heap r.
Proof.
  induction l as [|c l [IH1 IH2]]; simpl copy_heap; simpl app.
  - split; cancel (copy_heap r); cancel.
  - split.
    + sep_apply_l_atomic IH1. cancel (copy_cell_heap c). cancel.
    + sep_apply_r_atomic IH2. cancel (copy_cell_heap c). cancel.
Qed.
Lemma copy_heap_perm__lookup l r :
  Permutation l r -> copy_heap l |-- copy_heap r.
Proof.
  intro H; induction H; simpl copy_heap.
  - cancel.
  - sep_apply_l_atomic IHPermutation. cancel (copy_cell_heap x). cancel (copy_heap l'); cancel.
  - cancel (copy_cell_heap x). cancel (copy_cell_heap y). cancel (copy_heap l); cancel.
  - sep_apply_l_atomic IHPermutation1. exact IHPermutation2.
Qed.
Lemma copy_nodup_cells__lookup h :
  NoDup (map copy_cell_addr h) -> NoDup h.
Proof.
  induction h as [|c h IH]; intros H; [constructor|].
  inversion H; subst. constructor; [|auto].
  intro Hin. apply H2. apply in_map; exact Hin.
Qed.
Lemma copy_addr_unique__lookup h c c' :
  NoDup (map copy_cell_addr h) -> In c h -> In c' h ->
  copy_cell_addr c = copy_cell_addr c' -> c = c'.
Proof.
  induction h as [|x h IH]; intros Hnd Hc Hd Heq; [contradiction|].
  inversion Hnd as [|? ? Hnot Htail]; subst.
  destruct Hc as [Hc|Hc], Hd as [Hd|Hd]; subst; auto.
  - exfalso; apply Hnot. rewrite Heq. apply in_map; exact Hd.
  - exfalso; apply Hnot. rewrite <- Heq. apply in_map; exact Hc.
Qed.
Lemma copy_partition__lookup h cs :
  NoDup (map copy_cell_addr h) -> NoDup (map copy_cell_addr cs) ->
  (forall c, In c cs -> In c h) ->
  copy_heap h --||-- copy_heap cs **
  copy_heap (filter (fun c => negb (existsb (fun x => Z.eqb (copy_cell_addr c) (copy_cell_addr x)) cs)) h).
Proof.
  intros Hh Hcs Hin.
  set (F := fun c => negb (existsb (fun x => Z.eqb (copy_cell_addr c) (copy_cell_addr x)) cs)).
  assert (HF : forall c, In c h -> (F c = true <-> ~ In c cs)).
  { intros c Hc. unfold F. rewrite Bool.negb_true_iff.
    split.
    - intros He Hinc. assert (Ht : existsb (fun x => Z.eqb (copy_cell_addr c) (copy_cell_addr x)) cs = true).
      { apply existsb_exists. exists c. split; [exact Hinc|apply Z.eqb_refl]. } congruence.
    - intro Hnot. destruct (existsb (fun x => Z.eqb (copy_cell_addr c) (copy_cell_addr x)) cs) eqn:E; [|reflexivity].
      apply existsb_exists in E. destruct E as [x [Hx He]]. apply Z.eqb_eq in He.
      exfalso; apply Hnot. assert (c=x) by (exact (copy_addr_unique__lookup h c x Hh Hc (Hin x Hx) He)). subst; exact Hx.
  }
  assert (Hperm : Permutation h (cs ++ filter F h)).
  { apply NoDup_Permutation.
    - apply copy_nodup_cells__lookup; exact Hh.
    - apply NoDup_app. repeat split.
      + apply copy_nodup_cells__lookup; exact Hcs.
      + apply NoDup_filter. apply copy_nodup_cells__lookup; exact Hh.
      + intros c Hc Hf. apply filter_In in Hf. destruct Hf as [Hch Hcf]. apply (proj1 (HF c Hch) Hcf); exact Hc.
    - intro c. rewrite in_app_iff, filter_In. split.
      + intro Hc. destruct (existsb (fun x => Z.eqb (copy_cell_addr c) (copy_cell_addr x)) cs) eqn:E.
        * apply existsb_exists in E. destruct E as [x [Hx He]]. apply Z.eqb_eq in He.
          assert (c=x) by (exact (copy_addr_unique__lookup h c x Hh Hc (Hin x Hx) He)). subst; auto.
        * right; split; [exact Hc|unfold F; rewrite E; reflexivity].
      + intros [Hc|[Hc _]]; auto.
  }
  destruct (copy_heap_app__lookup cs (filter F h)) as [Ha Hb]. split.
  - sep_apply_l_atomic (copy_heap_perm__lookup h _ Hperm). exact Ha.
  - sep_apply_r_atomic (copy_heap_perm__lookup _ h (Permutation_sym Hperm)). exact Hb.
Qed.
Lemma copy_bounded_first__lookup (v : Z -> Z) key lo (n : nat) :
  (exists k, lo <= k < lo+Z.of_nat n /\ v k = key /\
    forall j, lo <= j < k -> v j <> key) \/
  (forall j, lo <= j < lo+Z.of_nat n -> v j <> key).
Proof.
  revert lo. induction n as [|n IH]; intro lo.
  - right; intros j Hj; simpl in Hj; lia.
  - destruct (Z.eq_dec (v lo) key) as [Heq|Hne].
    + left; exists lo. split; [rewrite Nat2Z.inj_succ; lia|].
      split; [exact Heq|]. intros j Hj; lia.
    + destruct (IH (lo+1)) as [[k [Hk [Heq Habs]]]|Habs].
      * left; exists k. rewrite Nat2Z.inj_succ. split; [lia|]. split; [exact Heq|].
        intros j Hj. destruct (Z.eq_dec j lo); [subst; exact Hne|apply Habs; lia].
      * right. rewrite Nat2Z.inj_succ. intros j Hj.
        destruct (Z.eq_dec j lo); [subst; exact Hne|apply Habs; lia].
Qed.
Lemma copy_prefix_endpoint__lookup a d key :
  copy_lookup_safe a d key -> d < 63 -> copy_table a d <> 0 ->
  exists e, 17 <= e <= 255 /\
    (copy_counter a d <= e \/ exists k, 17 <= k < e /\
       k < copy_counter a d /\ copy_pointer (copy_slots a (copy_table a d) k) = key) /\
    (forall j, 17 <= j < e -> j < copy_counter a d /\
       forall k, 17 <= k < j -> copy_pointer (copy_slots a (copy_table a d) k) <> key).
Proof.
  intros Hsafe Hd Hp. specialize (Hsafe Hd Hp).
  destruct (Z_le_gt_dec (copy_counter a d) 17) as [Hsmall|Hbig].
  - exists 17. split; [lia|]. split; [left; exact Hsmall|]. intros j Hj; lia.
  - set (bound := Z.min (copy_counter a d) 255).
    assert (Hb : 17 < bound <= 255) by (unfold bound; lia).
    destruct (copy_bounded_first__lookup
      (fun j => copy_pointer (copy_slots a (copy_table a d) j)) key 17 (Z.to_nat (bound-17)))
      as [[k [Hk [Heq Habs]]]|Habs]; rewrite Z2Nat.id in * by lia.
    + exists (k+1). split; [lia|]. split.
      * right; exists k. repeat split; try assumption; unfold bound in *; lia.
      * intros j Hj. split; [unfold bound in *; lia|]. intros x Hx. apply Habs; lia.
    + assert (Hend : copy_counter a d <= 255).
      { destruct Hsafe as [Hend|[k [Hk [Hke [Heq Hprior]]]]]; [exact Hend|].
        exfalso. apply (Habs k); [unfold bound; lia|exact Heq]. }
      exists (copy_counter a d). split; [lia|]. split; [left; lia|].
      intros j Hj. split; [lia|]. intros k Hk. apply Habs. unfold bound; lia.
Qed.
Lemma copy_prefix_values__lookup (v : Z -> Z) e :
  17 <= e ->
  let xs := map (fun n => v (17+Z.of_nat n)) (seq 0 (Z.to_nat (e-17))) in
  Z.of_nat (List.length xs) = e-17 /\
  (forall j, 17 <= j < e -> copy_lookup_at xs j = v j).
Proof.
  intros He xs. split.
  - unfold xs. rewrite length_map, length_seq, Z2Nat.id; lia.
  - intros j Hj. unfold copy_lookup_at, xs.
    rewrite (@nth_indep Z _ (Z.to_nat (j-17)) 0 (v (17+Z.of_nat 0))).
    2: rewrite length_map, length_seq; apply Z2Nat.inj_lt; lia.
    rewrite (map_nth (fun n => v (17+Z.of_nat n)) (seq 0 (Z.to_nat (e-17))) 0%nat (Z.to_nat (j-17))), seq_nth.
    2: apply Z2Nat.inj_lt; lia.
    simpl Nat.add. rewrite Z2Nat.id by lia. f_equal; lia.
Qed.
Lemma copy_cells_map__lookup p stride lo xs :
  copy_heap (map (fun n =>
    {| copy_cell_addr := copy_object_address p stride (lo+Z.of_nat n) "object_t";
       copy_cell_ptr := true; copy_cell_value := Some (nth n xs 0) |})
    (seq 0 (List.length xs))) --||-- copy_lookup_cells p stride lo xs.
Proof.
  revert lo. induction xs as [|x xs IH]; intro lo; [simpl; split; cancel|].
  simpl List.length. simpl seq. simpl map. simpl nth.
  rewrite <- seq_shift, map_map.
  assert (Heq : map (fun n : nat =>
      {| copy_cell_addr := copy_object_address p stride (lo + Z.of_nat (S n)) "object_t";
         copy_cell_ptr := true; copy_cell_value := Some (nth n xs 0) |}) (seq 0 (List.length xs)) =
    map (fun n : nat =>
      {| copy_cell_addr := copy_object_address p stride (lo+1+Z.of_nat n) "object_t";
         copy_cell_ptr := true; copy_cell_value := Some (nth n xs 0) |}) (seq 0 (List.length xs))).
  { apply map_ext. intro n. rewrite Nat2Z.inj_succ. f_equal. f_equal. lia. }
  simpl nth. rewrite Heq. simpl copy_heap. cbn [copy_cell_heap copy_cell_ptr copy_cell_addr copy_cell_value]. simpl copy_lookup_cells.
  replace (lo+0) with lo by lia.
  change (copy_object_address p stride lo "object_t") with (copy_lookup_object_address p stride lo).
  destruct (IH (lo+1)) as [Hout Hback]. split.
  - sep_apply_l_atomic Hout. cancel (copy_lookup_cells p stride (lo+1) xs); cancel.
  - sep_apply_r_atomic Hback. cancel.
Qed.
Lemma copy_map_nodup__lookup {A B} (f : A -> B) l :
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x=y) -> NoDup (map f l).
Proof.
  intros H; induction H as [|x l Hnot Hnd IH]; intro Hinj; simpl; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    apply Hnot. assert (x=y) by (apply Hinj; simpl; auto). subst; exact Hy.
  - apply IH. intros u v Hu Hv Heq. apply Hinj; simpl; auto.
Qed.
Lemma copy_existsb_map__lookup {A B} (f : A -> B) (p : B -> bool) l :
  existsb p (map f l) = existsb (fun x => p (f x)) l.
Proof. induction l; simpl; congruence. Qed.
Lemma copy_lookup_partition__lookup h a tb nb ps stride d s f xs :
  copy_pre h a tb nb ps stride d s f -> copy_live a d s f -> d < 63 ->
  Z.of_nat (List.length xs) <= 238 ->
  copy_call_records h tb nb ps stride d (copy_table a d) (copy_counter a d) xs ->
  copy_heap h --||--
    store_ptr (tb+ps*d) (copy_table a d) ** store_uint (nb+4*d) (copy_counter a d) **
    copy_lookup_cells (copy_table a d) stride 17 xs **
    copy_call_frame h tb nb ps stride d (copy_table a d) xs.
Proof.
  intros Hpre Hlive Hd Hlen Hrecords.
  destruct Hpre as [[Hdomain Hsafe] [Hnd [Hlayout Hother]]].
  destruct Hdomain as [Hdb [Hsb Hfb]].
  specialize (Hlayout Hlive). destruct Hlayout as [Hunion [Hinject [Haway Htab]]].
  specialize (Hrecords Hd). destruct Hrecords as [Htr [Hnr Hrs]].
  set (mk := fun n => {| copy_cell_addr := copy_object_address (copy_table a d) stride (17+Z.of_nat n) "object_t";
    copy_cell_ptr := true; copy_cell_value := Some (nth n xs 0) |}).
  set (cs := {| copy_cell_addr := tb+ps*d; copy_cell_ptr := true; copy_cell_value := Some (copy_table a d)|} ::
    {| copy_cell_addr := nb+4*d; copy_cell_ptr := false; copy_cell_value := Some (copy_counter a d)|} ::
    map mk (seq 0 (List.length xs))).
  assert (Hix : forall n, In n (seq 0 (List.length xs)) -> 0 <= 17+Z.of_nat n < 255).
  { intros n Hn. apply in_seq in Hn. lia. }
  assert (Haway' : forall n, In n (seq 0 (List.length xs)) ->
      copy_cell_addr (mk n) <> tb+ps*d /\ copy_cell_addr (mk n) <> nb+4*d).
  { intros n Hn. specialize (Haway (copy_table a d) (17+Z.of_nat n) 3 d (or_introl eq_refl) (Hix n Hn)).
    unfold mk. simpl copy_cell_addr. apply Haway; lia. }
  assert (Hcs : NoDup (map copy_cell_addr cs)).
  { unfold cs. simpl map. constructor.
    - intro Hi. destruct Hi as [Hi|Hi].
      + apply (Htab d d); try lia. symmetry; exact Hi.
      + rewrite map_map in Hi. apply in_map_iff in Hi. destruct Hi as [n [He Hn]].
        apply (proj1 (Haway' n Hn)); exact He.
    - constructor.
      + intro Hi. rewrite map_map in Hi. apply in_map_iff in Hi. destruct Hi as [n [He Hn]].
        apply (proj2 (Haway' n Hn)); exact He.
      + rewrite map_map. apply copy_map_nodup__lookup; [apply seq_NoDup|].
        intros n m Hn Hm He. unfold mk in He; simpl in He.
        assert (Hi : 17+Z.of_nat n = 17+Z.of_nat m).
        { apply (proj1 (proj2 (Hinject (copy_table a d) (copy_table a d)
            (17+Z.of_nat n) (17+Z.of_nat m) 3 3 (or_introl eq_refl) (or_introl eq_refl)
            (Hix n Hn) (Hix m Hm) ltac:(lia) ltac:(lia) He))). }
        lia.
  }
  assert (Hinc : forall c, In c cs -> In c h).
  { intros c Hc. unfold cs in Hc. destruct Hc as [Hc|[Hc|Hc]]; subst; try assumption.
    apply in_map_iff in Hc. destruct Hc as [n [Hc Hn]]. subst c. apply in_seq in Hn.
    assert (Hb : 17 <= 17+Z.of_nat n < 17+Z.of_nat (List.length xs)) by lia.
    specialize (Hrs (17+Z.of_nat n) Hb). unfold copy_lookup_at in Hrs.
    replace (17+Z.of_nat n-17) with (Z.of_nat n) in Hrs by lia.
    rewrite Nat2Z.id in Hrs. exact Hrs.
  }
  destruct (copy_partition__lookup h cs Hnd Hcs Hinc) as [Hout Hback].
  assert (HF : copy_heap (filter (fun c => negb (existsb (fun x => Z.eqb (copy_cell_addr c) (copy_cell_addr x)) cs)) h) =
    copy_call_frame h tb nb ps stride d (copy_table a d) xs).
  { unfold copy_call_frame, cs. f_equal. apply filter_ext. intro c. simpl existsb.
    rewrite copy_existsb_map__lookup. unfold mk. simpl copy_cell_addr.
    repeat rewrite Bool.negb_orb. rewrite Bool.andb_assoc. reflexivity. }
  rewrite HF in Hout, Hback. unfold cs in Hout, Hback. simpl copy_heap in Hout, Hback.
  cbn [copy_cell_heap copy_cell_ptr copy_cell_addr copy_cell_value] in Hout, Hback.
  fold (4*d) in Hout, Hback.
  unfold mk in Hout, Hback.
  destruct (copy_cells_map__lookup (copy_table a d) stride 17 xs) as [Hco Hcb]. split.
  - sep_apply_l_atomic Hout. sep_apply_l_atomic Hco. cancel (copy_call_frame h tb nb ps stride d (copy_table a d) xs). cancel (copy_lookup_cells (copy_table a d) stride 17 xs); cancel.
    change (store_uint (nb+4*d) (copy_counter a d) |-- store_uint (nb+4*d) (copy_counter a d)). cancel.
  - sep_apply_l_atomic Hcb. sep_apply_r_atomic Hback. cancel (copy_call_frame h tb nb ps stride d (copy_table a d) xs). fold mk. cancel (copy_heap (map mk (seq 0 (List.length xs)))); cancel.
    change (store_uint (nb+4*d) (copy_counter a d) |-- store_uint (nb+4*d) (copy_counter a d)). cancel.
Qed.
Lemma copy_resources_active__lookup tb nb ps stride d p finish xs :
  d < 63 -> p <> 0 ->
  copy_lookup_resources tb nb ps stride d p finish xs --||--
  store_ptr (tb+ps*d) p ** store_uint (nb+4*d) finish ** copy_lookup_cells p stride 17 xs.
Proof.
  intros Hd Hp. unfold copy_lookup_resources.
  replace (d*4) with (4*d) by lia. replace (d*ps) with (ps*d) by nia.
  split.
  - Split.
    + Intros_p H; lia.
    + Intros_p H. Split.
      * Intros_p E; contradiction.
      * Intros_p Hnz. cancel (copy_lookup_cells p stride 17 xs); cancel.
  - Right. Right. split_pure_spatial.
    + cancel (copy_lookup_cells p stride 17 xs); cancel.
    + split_pures; dump_pre_spatial; assumption.
Qed.
Lemma copy_resources_sentinel__lookup tb nb ps stride d p finish xs :
  63 <= d -> copy_lookup_resources tb nb ps stride d p finish xs --||-- emp.
Proof.
  intro Hd. unfold copy_lookup_resources. split.
  - Split; Intros_p H; [cancel|lia].
  - Left. split_pure_spatial; [cancel|dump_pre_spatial; exact Hd].
Qed.
Lemma copy_heap_uint_range__lookup h addr value :
  NoDup (map copy_cell_addr h) -> copy_read h addr false value ->
  copy_heap h |-- “ 0 <= value <= 4294967295 ”.
Proof.
  intros Hnd Hread.
  sep_apply_l_atomic (proj1 (copy_heap_focus__lookup h
    {|copy_cell_addr:=addr;copy_cell_ptr:=false;copy_cell_value:=Some value|} Hnd Hread)).
  cbn [copy_cell_heap copy_cell_ptr copy_cell_addr copy_cell_value].
  prop_apply_p (store_uint_range addr value).
  Intros_p Hr. dump_pre_spatial. exact Hr.
Qed.
Lemma copy_lookup_prefix__lookup h a tb nb ps stride d s f :
  copy_pre h a tb nb ps stride d s f -> copy_live a d s f ->
  copy_tag (copy_slots a (copy_table a s) f) = 2 -> d < 63 ->
  0 <= copy_counter a d <= 4294967295 ->
  exists xs, copy_lookup_agrees a d xs /\
    copy_lookup_input_safe d (copy_table a d) (copy_counter a d)
      (copy_pointer (copy_slots a (copy_table a s) f)) xs /\
    copy_call_records h tb nb ps stride d (copy_table a d) (copy_counter a d) xs.
Proof.
  intros Hpre Hlive Htag Hd Hrange.
  destruct Hpre as [[Hdomain Hsafe] [Hnd [Hlayout [Htabs [Htagread [Hcat Hobj]]]]]].
  pose proof Hlive as [Hf [Hdb [Hsb [Hdp Hsp]]]].
  specialize (Hsafe Hf Hdb Hsb Hdp Hsp Htag).
  specialize (Hobj Hlive Htag). destruct Hobj as [Hsrc [Hscan Hwrite]].
  specialize (Hscan Hd). destruct Hscan as [Hnr Hrs].
  destruct (copy_prefix_endpoint__lookup a d _ Hsafe Hd Hdp) as [e [He [Hcover Hbefore]]].
  set (v := fun j => copy_pointer (copy_slots a (copy_table a d) j)).
  set (xs := map (fun n => v (17+Z.of_nat n)) (seq 0 (Z.to_nat (e-17)))).
  destruct (copy_prefix_values__lookup v e ltac:(lia)) as [Hlen Hvalues].
  change (Z.of_nat (List.length xs) = e-17) in Hlen.
  change (forall j, 17 <= j < e -> copy_lookup_at xs j = v j) in Hvalues.
  exists xs. split.
  - intros j Hj. apply Hvalues; lia.
  - split.
    + split; [exact (proj1 Hdomain)|]. intros _ _. unfold copy_lookup_read_safe, copy_lookup_count.
      split; [exact Hrange|]. split; [lia|]. destruct Hcover as [Hend|[k [Hk [Hkf Hmatch]]]].
      * left; lia.
      * right; exists k. split; [lia|]. split; [lia|]. rewrite Hvalues by lia. exact Hmatch.
    + intros _. split; [exact (proj1 (Htabs Hf Hdb Hsb))|]. split; [exact Hnr|].
      intros j Hj. assert (Hje : 17 <= j < e) by lia.
      destruct (Hbefore j Hje) as [Hjf Habs].
      rewrite Hvalues by exact Hje. exact (proj2 (Hrs j ltac:(lia) Habs)).
Qed.
Lemma copy_heap_ptr_restore__lookup h addr value :
  NoDup (map copy_cell_addr h) -> copy_read h addr true value ->
  copy_hole h addr ** store_ptr addr value |-- copy_heap h.
Proof.
  intros Hnd Hread.
  pose proof (proj2 (copy_heap_focus__lookup h
    {|copy_cell_addr:=addr;copy_cell_ptr:=true;copy_cell_value:=Some value|} Hnd Hread)) as Hback.
  cbn [copy_cell_heap copy_cell_ptr copy_cell_addr copy_cell_value] in Hback.
  sep_apply_r_atomic Hback. cancel (copy_hole h addr); cancel.
Qed.
Lemma copy_source_object_address__lookup p stride i :
  eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_content") "object") "object_t")) =
  copy_object_address p stride i "object_t".
Proof.
  unfold copy_cap_address, copy_object_address, copy_slot_lvalue.
  csimpl. reflexivity.
Qed.
Lemma copy_filter_id__allocation {A} (f : A -> bool) l :
 (forall x, In x l -> f x = true) -> filter f l = l.
Proof. induction l as [|x t IH]; intros H; simpl; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros y HY. apply H. right; exact HY. Qed.
Lemma copy_map_id__allocation {A} (f : A -> A) l :
 (forall x, In x l -> f x = x) -> map f l = l.
Proof. induction l as [|x t IH]; intros H; simpl; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros y HY. apply H. right; exact HY. Qed.
Lemma copy_heap_focus__allocation h c :
 NoDup (map copy_cell_addr h) -> In c h ->
 copy_heap h |-- copy_cell_heap c ** copy_hole h (copy_cell_addr c).
Proof.
 intros ND IN. unfold copy_hole. induction h as [|b t IH]; simpl in *; [contradiction|].
 inversion ND as [|? ? NB NT]; subst. destruct IN as [E|IN].
 - subst b. rewrite Z.eqb_refl. simpl.
   assert (F : filter (fun c0 => negb (copy_cell_addr c0 =? copy_cell_addr c)) t = t).
   { apply copy_filter_id__allocation. intros x HX. apply Bool.negb_true_iff, Z.eqb_neq. intro EQ.
     apply NB. rewrite <- EQ. apply in_map. exact HX. }
   rewrite F. cancel.
 - assert (NE : copy_cell_addr b <> copy_cell_addr c).
   { intro E. apply NB. rewrite E. apply in_map. exact IN. }
   apply Z.eqb_neq in NE. rewrite NE. simpl.
   specialize (IH NT IN). sep_apply_l_atomic IH. cancel.
Qed.
Lemma copy_heap_put__allocation h x v :
 NoDup (map copy_cell_addr h) -> copy_writable h x false ->
 copy_hole h x ** store_uint x v |-- copy_heap (copy_put h x v).
Proof.
 intros ND [old IN]. unfold copy_hole, copy_put, copy_write.
 induction h as [|c t IH]; simpl in *; [contradiction|].
 inversion ND as [|? ? NC NT]; subst.
 destruct IN as [E|IN].
 - subst c. simpl. rewrite Z.eqb_refl. destruct (Z.eq_dec x x); [|contradiction]. simpl.
   assert (F : filter (fun c => negb (copy_cell_addr c =? x)) t = t).
   { apply copy_filter_id__allocation. intros c HC. apply Bool.negb_true_iff, Z.eqb_neq. intro E.
     apply NC. simpl. rewrite <- E. apply in_map. exact HC. }
   assert (M : map (fun c => if Z.eq_dec (copy_cell_addr c) x then
     {|copy_cell_addr:=copy_cell_addr c;copy_cell_ptr:=copy_cell_ptr c;copy_cell_value:=Some v|} else c) t = t).
   { apply copy_map_id__allocation. intros c HC. destruct (Z.eq_dec (copy_cell_addr c) x) as [E|E]; [|reflexivity].
     exfalso. apply NC. simpl. rewrite <- E. apply in_map. exact HC. }
   rewrite F, M. unfold copy_cell_heap. simpl. cancel.
 - assert (NE : copy_cell_addr c <> x).
   { intro E. apply NC. rewrite E. change (In (copy_cell_addr {|copy_cell_addr:=x;copy_cell_ptr:=false;copy_cell_value:=old|}) (map copy_cell_addr t)). apply in_map. exact IN. }
   assert (EB : (copy_cell_addr c =? x) = false) by (apply Z.eqb_neq; exact NE).
   rewrite EB. destruct (Z.eq_dec (copy_cell_addr c) x); [contradiction|]. simpl.
   specialize (IH NT IN). sep_apply_l_atomic IH. cancel.
Qed.
Lemma copy_put_addresses__allocation h x v :
 map copy_cell_addr (copy_put h x v) = map copy_cell_addr h.
Proof. unfold copy_put, copy_write. rewrite map_map. apply map_ext. intros c. simpl. destruct (Z.eq_dec (copy_cell_addr c) x); reflexivity. Qed.
Lemma copy_put_preserves__allocation h x v y ptr :
 x <> y -> copy_writable h y ptr -> copy_writable (copy_put h x v) y ptr.
Proof.
 intros NE [old IN]. exists old. unfold copy_put, copy_write.
 apply in_map_iff. exists {|copy_cell_addr:=y;copy_cell_ptr:=ptr;copy_cell_value:=old|}.
 split; [simpl; destruct (Z.eq_dec y x); [congruence|reflexivity]|exact IN].
Qed.
Lemma copy_heap_writable__allocation h x :
 NoDup (map copy_cell_addr h) -> copy_writable h x false ->
 copy_heap h |-- copy_hole h x ** undef_store_uint x.
Proof.
 intros ND [old IN]. sep_apply_l_atomic (copy_heap_focus__allocation h
 {|copy_cell_addr:=x;copy_cell_ptr:=false;copy_cell_value:=old|} ND IN).
 destruct old as [v|]; unfold copy_cell_heap; simpl; cancel.
 apply store_uint_undef_store_uint.
Qed.
Lemma copy_available__allocation h a tb nb ps st d s f r :
 copy_pre h a tb nb ps st d s f -> copy_live a d s f ->
 copy_tag (copy_slots a (copy_table a s) f) = 2 ->
 copy_lookup a d (copy_pointer (copy_slots a (copy_table a s) f)) r ->
 (r = 0 -> copy_counter a d < 255 -> copy_writable h (nb+4*d) false /\ copy_object_writes_available h a st d s f (copy_counter a d)) /\
 (r <> 0 -> copy_object_writes_available h a st d s f r).
Proof. intros (_&_&_&_&_&_&H) L T R. specialize (H L T). destruct H as (_&_&H). specialize (H r R). tauto. Qed.
Lemma copy_allocation_tag__allocation h hc a tb nb ps st d s f key idx :
 copy_pre h a tb nb ps st d s f -> copy_live a d s f ->
 copy_tag (copy_slots a (copy_table a s) f) = 2 ->
 key = copy_pointer (copy_slots a (copy_table a s) f) ->
 copy_allocation_state h hc a nb d key idx ->
 NoDup (map copy_cell_addr hc) /\ copy_writable hc (copy_tag_address (copy_table a d) st idx) false.
Proof.
 intros P L T K A. subst key.
 pose proof P as (SAFE&ND&LAY&_).
 destruct A as [(LOOK&E&B&HC)|(LOOK&NE&B&HC)]; subst hc.
 - subst idx. split; [rewrite copy_put_addresses__allocation; exact ND|].
   destruct (copy_available__allocation h a tb nb ps st d s f 0 P L T LOOK) as [W _].
   specialize (W eq_refl (proj2 B)). destruct W as [_ (_&_&W&_)].
   apply copy_put_preserves__allocation; [|exact W].
   specialize (LAY L). destruct LAY as (_&_&SEP&_).
   destruct SAFE as [(D&S&F) _].
   specialize (SEP (copy_table a d) (copy_counter a d) 0 d (or_introl eq_refl) B ltac:(lia) ltac:(unfold copy_live in L; lia)).
   unfold copy_component_address in SEP. simpl in SEP. intro E. apply (proj2 SEP). symmetry. exact E.
 - split; [exact ND|].
   destruct (copy_available__allocation h a tb nb ps st d s f idx P L T LOOK) as [_ W].
   specialize (W NE). destruct W as (_&_&W&_). exact W.
Qed.
Lemma copy_filter_absent__object_steps h x :
  ~ In x (map copy_cell_addr h) ->
  filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h = h.
Proof.
  induction h as [|c t IH]; simpl; intros H; auto.
  assert (copy_cell_addr c <> x) by (intro E; apply H; auto).
  apply Z.eqb_neq in H0. rewrite H0; simpl; f_equal.
  apply IH; tauto.
Qed.
Lemma copy_heap_focus__object_steps h c :
  NoDup (map copy_cell_addr h) -> In c h ->
  copy_heap h --||-- copy_cell_heap c ** copy_hole h (copy_cell_addr c).
Proof.
  induction h as [|b t IH]; simpl; intros ND IN; [contradiction|].
  inversion ND as [|? ? NOT ND']; subst.
  destruct IN as [E|IN].
  - subst b. unfold copy_hole; simpl. rewrite Z.eqb_refl; simpl.
    rewrite copy_filter_absent__object_steps by exact NOT. split; cancel.
  - assert (NE : copy_cell_addr b <> copy_cell_addr c).
    { intro E; apply NOT; rewrite E; apply in_map; exact IN. }
    assert (EB : (copy_cell_addr b =? copy_cell_addr c) = false)
      by (apply Z.eqb_neq; exact NE).
    specialize (IH ND' IN). unfold copy_hole; simpl. rewrite EB; simpl.
    split.
    + sep_apply_l_atomic (proj1 IH). unfold copy_hole. cancel.
    + sep_apply_r_atomic (proj2 IH). unfold copy_hole. cancel. cancel (copy_cell_heap c).
Qed.
Lemma copy_put_absent__object_steps h x v :
  ~ In x (map copy_cell_addr h) -> copy_put h x v = h.
Proof.
  unfold copy_put, copy_write; simpl.
  induction h as [|c t IH]; simpl; intros H; auto.
  destruct (Z.eq_dec (copy_cell_addr c) x) as [E|E].
  - exfalso; apply H; auto.
  - f_equal; apply IH; tauto.
Qed.
Lemma copy_heap_put__object_steps h x b old v :
  NoDup (map copy_cell_addr h) ->
  In {| copy_cell_addr := x; copy_cell_ptr := b; copy_cell_value := old |} h ->
  copy_hole h x ** copy_cell_heap
    {| copy_cell_addr := x; copy_cell_ptr := b; copy_cell_value := Some v |}
  |-- copy_heap (copy_put h x v).
Proof.
  induction h as [|c t IH]; simpl; intros ND IN; [contradiction|].
  inversion ND as [|? ? NOT ND']; subst.
  destruct IN as [E|IN].
  - subst c. unfold copy_hole; simpl. rewrite Z.eqb_refl; simpl.
    rewrite copy_filter_absent__object_steps by exact NOT.
    unfold copy_put, copy_write; simpl.
    destruct (Z.eq_dec x x); [|contradiction].
    change (copy_heap t ** copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=Some v|}
      |-- copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=Some v|} ** copy_heap (copy_put t x v)). rewrite copy_put_absent__object_steps by exact NOT. cancel.
  - assert (NE : copy_cell_addr c <> x).
    { intro E; apply NOT; rewrite E; apply in_map_iff.
      exists {|copy_cell_addr := x; copy_cell_ptr := b; copy_cell_value := old|}; auto. }
    unfold copy_hole; simpl.
    assert (EB : (copy_cell_addr c =? x) = false) by (apply Z.eqb_neq; exact NE).
    rewrite EB; simpl.
    unfold copy_put, copy_write; simpl.
    destruct (Z.eq_dec (copy_cell_addr c) x); [contradiction|].
    change (copy_cell_heap c ** copy_hole t x ** copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=Some v|}
      |-- copy_cell_heap c ** copy_heap (copy_put t x v)).
    sep_apply_r_atomic (IH ND' IN). unfold copy_hole. cancel.
    cancel (copy_cell_heap c).
    cancel (copy_heap (filter (fun c0 => negb (Z.eqb (copy_cell_addr c0) x)) t)).
    cancel (copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=Some v|}).
Qed.
Lemma copy_put_preserves__object_steps h x v :
  map copy_cell_addr (copy_put h x v) = map copy_cell_addr h.
Proof.
  unfold copy_put, copy_write; simpl; rewrite map_map.
  apply map_ext; intros c; destruct (Z.eq_dec (copy_cell_addr c) x); reflexivity.
Qed.
Lemma copy_read_put_other__object_steps h x y b w v :
  x <> y -> copy_read h y b w -> copy_read (copy_put h x v) y b w.
Proof.
  unfold copy_read, copy_put, copy_write; simpl; intros NE IN.
  apply in_map_iff; exists {|copy_cell_addr:=y; copy_cell_ptr:=b; copy_cell_value:=Some w|}.
  split; auto; simpl; destruct (Z.eq_dec y x); [congruence|reflexivity].
Qed.
Lemma copy_writable_put__object_steps h x y b v :
  copy_writable h y b -> copy_writable (copy_put h x v) y b.
Proof.
  unfold copy_writable, copy_put, copy_write; simpl; intros [w IN].
  destruct (Z.eq_dec y x) as [E|NE].
  - exists (Some v); apply in_map_iff.
    exists {|copy_cell_addr:=y; copy_cell_ptr:=b; copy_cell_value:=w|}.
    split; auto; simpl; destruct (Z.eq_dec y x); [reflexivity|contradiction].
  - exists w; apply in_map_iff.
    exists {|copy_cell_addr:=y; copy_cell_ptr:=b; copy_cell_value:=w|}.
    split; auto; simpl; destruct (Z.eq_dec y x); [contradiction|reflexivity].
Qed.
Lemma copy_filter_nodup__object_steps h x :
  NoDup (map copy_cell_addr h) ->
  NoDup (map copy_cell_addr (filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h)).
Proof.
  induction h as [|c t IH]; simpl; intros ND; [constructor|].
  inversion ND as [|? ? HN HT]; subst.
  destruct (negb (copy_cell_addr c =? x)); simpl; auto.
  constructor; auto. intro H; apply HN.
  apply in_map_iff in H as [z [E IN]]. apply filter_In in IN as [IN _].
  apply in_map_iff; exists z; auto.
Qed.
Lemma copy_two_filters__object_steps h x y :
  filter (fun c => negb (Z.eqb (copy_cell_addr c) y))
    (filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h) =
  filter (fun c => (negb (Z.eqb (copy_cell_addr c) x) &&
                   negb (Z.eqb (copy_cell_addr c) y))%bool) h.
Proof.
  induction h as [|c t IH]; simpl; auto.
  destruct (negb (copy_cell_addr c =? x)) eqn:E1;
    destruct (negb (copy_cell_addr c =? y)) eqn:E2; simpl;
    rewrite ?E2, ?IH; reflexivity.
Qed.
Lemma copy_heap_two_focus__object_steps h c d :
  NoDup (map copy_cell_addr h) -> In c h -> In d h ->
  copy_cell_addr c <> copy_cell_addr d ->
  copy_heap h --||-- copy_cell_heap c ** copy_cell_heap d **
    copy_two_holes h (copy_cell_addr c) (copy_cell_addr d).
Proof.
  intros ND IC ID NE.
  assert (ID' : In d (filter (fun z => negb (Z.eqb (copy_cell_addr z) (copy_cell_addr c))) h)).
  { apply filter_In; split; auto. apply Bool.negb_true_iff, Z.eqb_neq; congruence. }
  pose proof (copy_heap_focus__object_steps h c ND IC) as HC.
  pose proof (copy_heap_focus__object_steps _ d
    (copy_filter_nodup__object_steps h (copy_cell_addr c) ND) ID') as HD.
  unfold copy_hole in HD. rewrite copy_two_filters__object_steps in HD.
  fold (copy_two_holes h (copy_cell_addr c) (copy_cell_addr d)) in HD.
  split.
  - sep_apply_l_atomic (proj1 HC). unfold copy_hole.
    sep_apply_l_atomic (proj1 HD). cancel.
  - sep_apply_r_atomic (proj2 HC). unfold copy_hole.
    sep_apply_r_atomic (proj2 HD). cancel.
    cancel (copy_cell_heap c). cancel (copy_cell_heap d).
    cancel (copy_two_holes h (copy_cell_addr c) (copy_cell_addr d)).
Qed.
Lemma copy_cell_forget__object_steps x b old :
  copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=old|}
  |-- copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=None|}.
Proof.
  destruct b, old; simpl; try apply store_ptr_undef_store_ptr;
    try apply store_uint_undef_store_uint; cancel.
Qed.
Lemma copy_heap_prepare__object_steps h x y b v :
  NoDup (map copy_cell_addr h) -> copy_read h y b v -> copy_writable h x b ->
  x <> y ->
  copy_heap h |-- copy_two_holes h x y **
    copy_cell_heap {|copy_cell_addr:=y;copy_cell_ptr:=b;copy_cell_value:=Some v|} **
    copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=None|}.
Proof.
  intros ND R [old W] NE.
  sep_apply_l_atomic (proj1 (copy_heap_two_focus__object_steps h
    {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=old|}
    {|copy_cell_addr:=y;copy_cell_ptr:=b;copy_cell_value:=Some v|}
    ND W R NE)).
  sep_apply_l_atomic (copy_cell_forget__object_steps x b old). simpl.
  cancel (copy_two_holes h x y).
  cancel (copy_cell_heap {|copy_cell_addr:=y;copy_cell_ptr:=b;copy_cell_value:=Some v|}).
  cancel (copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=None|}).
Qed.
Lemma copy_filter_put_other__object_steps h x y v :
  x <> y ->
  filter (fun c => negb (Z.eqb (copy_cell_addr c) y)) (copy_put h x v) =
  copy_put (filter (fun c => negb (Z.eqb (copy_cell_addr c) y)) h) x v.
Proof.
  intros NE; unfold copy_put, copy_write; simpl.
  induction h as [|c t IH]; simpl; auto.
  destruct (Z.eq_dec (copy_cell_addr c) x) eqn:E1; simpl;
    destruct (negb (copy_cell_addr c =? y)); simpl; rewrite ?E1, ?IH; reflexivity.
Qed.
Lemma copy_read_put_here__object_steps h x b old v :
  In {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=old|} h ->
  copy_read (copy_put h x v) x b v.
Proof.
  intros IN; unfold copy_read, copy_put, copy_write; simpl.
  apply in_map_iff; exists {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=old|}.
  split; auto; simpl; destruct (Z.eq_dec x x); [reflexivity|contradiction].
Qed.
Lemma copy_heap_two_put__object_steps h x y b old w v :
  NoDup (map copy_cell_addr h) ->
  In {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=old|} h ->
  copy_read h y b w -> x <> y ->
  copy_two_holes h x y **
    copy_cell_heap {|copy_cell_addr:=y;copy_cell_ptr:=b;copy_cell_value:=Some w|} **
    copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=Some v|}
  |-- copy_heap (copy_put h x v).
Proof.
  intros ND WX RY NE.
  assert (RX : In {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=old|}
    (filter (fun c => negb (Z.eqb (copy_cell_addr c) y)) h)).
  { apply filter_In; split; auto. simpl; apply Bool.negb_true_iff, Z.eqb_neq; exact NE. }
  pose proof (copy_read_put_other__object_steps h x y b w v NE RY) as RY'.
  assert (ND' : NoDup (map copy_cell_addr (copy_put h x v)))
    by (rewrite copy_put_preserves__object_steps; exact ND).
  sep_apply_r_atomic (proj2 (copy_heap_focus__object_steps (copy_put h x v)
    {|copy_cell_addr:=y;copy_cell_ptr:=b;copy_cell_value:=Some w|} ND' RY')).
  unfold copy_hole; simpl. rewrite copy_filter_put_other__object_steps by exact NE.
  sep_apply_r_atomic (copy_heap_put__object_steps _ x b old v
    (copy_filter_nodup__object_steps h y ND) RX).
  unfold copy_hole. rewrite copy_two_filters__object_steps.
  assert (E : copy_heap
    (filter (fun c => (negb (copy_cell_addr c =? y) && negb (copy_cell_addr c =? x))%bool) h)
    = copy_two_holes h x y).
  { unfold copy_two_holes; f_equal; apply filter_ext; intro c; apply Bool.andb_comm. }
  rewrite E.
  cancel (copy_two_holes h x y).
  cancel (copy_cell_heap {|copy_cell_addr:=y;copy_cell_ptr:=b;copy_cell_value:=Some w|}).
  cancel (copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=b;copy_cell_value:=Some v|}).
Qed.
Lemma copy_layout_separation__object_steps a tb nb ps st d s f k :
  copy_typed_layout a tb nb ps st d s ->
  0 <= f < 255 -> 0 <= k < 255 -> 0 <= d < 64 ->
  copy_tag_address (copy_table a d) st k <>
    copy_object_address (copy_table a s) st f "object_right" /\
  copy_tag_address (copy_table a d) st k <>
    copy_object_address (copy_table a s) st f "object_t" /\
  copy_object_address (copy_table a d) st k "object_right" <>
    copy_object_address (copy_table a s) st f "object_t" /\
  nb+4*d <> copy_object_address (copy_table a s) st f "object_right" /\
  nb+4*d <> copy_object_address (copy_table a s) st f "object_t".
Proof.
  intros [OV [SEP [CNT TAB]]] BF BK BD.
  pose proof (OV (copy_table a s) f (or_intror eq_refl) BF) as [OS _].
  pose proof (OV (copy_table a d) k (or_introl eq_refl) BK) as [OD _].
  assert (N01 : copy_component_address (copy_table a d) st k 0 <>
    copy_component_address (copy_table a s) st f 1).
  { intro E; pose proof (SEP _ _ _ _ 0 1 (or_introl eq_refl)
      (or_intror eq_refl) BK BF ltac:(lia) ltac:(lia) E); lia. }
  assert (N03 : copy_component_address (copy_table a d) st k 0 <>
    copy_component_address (copy_table a s) st f 3).
  { intro E; pose proof (SEP _ _ _ _ 0 3 (or_introl eq_refl)
      (or_intror eq_refl) BK BF ltac:(lia) ltac:(lia) E); lia. }
  assert (N13 : copy_component_address (copy_table a d) st k 1 <>
    copy_component_address (copy_table a s) st f 3).
  { intro E; pose proof (SEP _ _ _ _ 1 3 (or_introl eq_refl)
      (or_intror eq_refl) BK BF ltac:(lia) ltac:(lia) E); lia. }
  pose proof (CNT (copy_table a s) f 1 d (or_intror eq_refl) BF ltac:(lia) BD) as [_ C1].
  pose proof (CNT (copy_table a s) f 3 d (or_intror eq_refl) BF ltac:(lia) BD) as [_ C3].
  unfold copy_component_address in N01, N03, N13, C1, C3.
  simpl in N01, N03, N13, C1, C3.
  rewrite OS in N01, C1. rewrite OD in N13.
  repeat split; auto; congruence.
Qed.
Lemma copy_object_resources__object_steps h hc a tb nb ps st d s f idx :
  copy_pre h a tb nb ps st d s f -> copy_live a d s f ->
  copy_tag (copy_slots a (copy_table a s) f) = 2 ->
  copy_allocation_state h hc a nb d
    (copy_pointer (copy_slots a (copy_table a s) f)) idx ->
  NoDup (map copy_cell_addr hc) /\
  copy_writable hc (copy_tag_address (copy_table a d) st idx) false /\
  copy_read hc (copy_object_address (copy_table a s) st f "object_right") false
    (copy_word0 (copy_slots a (copy_table a s) f)) /\
  copy_writable hc (copy_object_address (copy_table a d) st idx "object_right") false /\
  copy_read hc (copy_object_address (copy_table a s) st f "object_t") true
    (copy_pointer (copy_slots a (copy_table a s) f)) /\
  copy_writable hc (copy_object_address (copy_table a d) st idx "object_t") true /\
  copy_tag_address (copy_table a d) st idx <>
    copy_object_address (copy_table a s) st f "object_right" /\
  copy_tag_address (copy_table a d) st idx <>
    copy_object_address (copy_table a s) st f "object_t" /\
  copy_object_address (copy_table a d) st idx "object_right" <>
    copy_object_address (copy_table a s) st f "object_t".
Proof.
  intros PRE LIVE TAG AL.
  destruct PRE as [[DOM SAFE] [ND [LAY [TAB [ST [CAT OBJ]]]]]].
  specialize (LAY LIVE). specialize (OBJ LIVE TAG).
  destruct OBJ as [RP [SCAN AV]].
  destruct DOM as [BD [BS BF]].
  pose proof LIVE as [UF [UD [US _]]].
  destruct AL as [[LK [EI [BI HC]]]|[LK [NZ [BI HC]]]]; subst hc.
  - specialize (AV 0 LK). destruct AV as [_ [AV _]].
    specialize (AV eq_refl ltac:(lia)). destruct AV as [_ WA].
    unfold copy_object_writes_available in WA.
    destruct WA as [_ [RW [WT [WW WP]]]].
    subst idx.
    pose proof (copy_layout_separation__object_steps a tb nb ps st d s f
      (copy_counter a d) LAY ltac:(lia) BI ltac:(lia)) as [N1 [N2 [N3 [C1 C3]]]].
    repeat split; auto.
    + rewrite copy_put_preserves__object_steps; exact ND.
    + apply copy_writable_put__object_steps; exact WT.
    + apply copy_read_put_other__object_steps; assumption.
    + apply copy_writable_put__object_steps; exact WW.
    + apply copy_read_put_other__object_steps; assumption.
    + apply copy_writable_put__object_steps; exact WP.
  - specialize (AV idx LK). destruct AV as [_ [_ AV]].
    specialize (AV NZ). unfold copy_object_writes_available in AV.
    destruct AV as [_ [RW [WT [WW WP]]]].
    pose proof (copy_layout_separation__object_steps a tb nb ps st d s f idx
      LAY ltac:(lia) BI ltac:(lia)) as [N1 [N2 [N3 _]]].
    repeat split; auto.
Qed.
Lemma copy_category_post__category_result h a nb stride d s f :
 copy_live a d s f -> copy_tag (copy_slots a (copy_table a s) f) = 1 ->
 copy_post h (copy_write_all h (copy_category_delta a stride d s f)) a nb stride d s f 0.
Proof.
 intros [Hf [Hd [Hs [HD HS]]]] HT.
 unfold copy_post.
 exists {| copy_table := copy_table a; copy_counter := copy_counter a;
 copy_slots := fun p i => if Z.eq_dec p (copy_table a d) then
 if Z.eq_dec i f then {|copy_tag:=1; copy_word0:=copy_word0 (copy_slots a (copy_table a s) f); copy_word1:=copy_word1 (copy_slots a (copy_table a s) f); copy_pointer:=copy_pointer (copy_slots a p i)|} else copy_slots a p i else copy_slots a p i |}.
 exists (copy_category_delta a stride d s f).
 split.
 - unfold copy_result. right. repeat split; try assumption.
   right. repeat split; try assumption. left. repeat split; try assumption; reflexivity.
 - split; [unfold copy_delta; right; left; auto|reflexivity].
Qed.
Lemma copy_put_addresses__category_result h x v :
 map copy_cell_addr (copy_put h x v) = map copy_cell_addr h.
Proof.
 unfold copy_put, copy_write. induction h as [|c t IH]; simpl; auto.
 destruct (Z.eq_dec (copy_cell_addr c) x); simpl; simpl in IH; rewrite IH; reflexivity.
Qed.
Lemma copy_put_writable__category_result h x v y ty :
 copy_writable h y ty -> copy_writable (copy_put h x v) y ty.
Proof.
 intros [old Hin]. unfold copy_writable, copy_put, copy_write.
 destruct (Z.eq_dec y x) as [E|N].
 - exists (Some v). apply in_map_iff. exists {|copy_cell_addr:=y;copy_cell_ptr:=ty;copy_cell_value:=old|}. simpl.
   destruct (Z.eq_dec y x); auto; contradiction.
 - exists old. apply in_map_iff. exists {|copy_cell_addr:=y;copy_cell_ptr:=ty;copy_cell_value:=old|}. simpl.
   destruct (Z.eq_dec y x); auto; contradiction.
Qed.
Lemma copy_heap_put__category_result h x v :
 NoDup (map copy_cell_addr h) -> copy_writable h x false ->
 store_uint x v ** copy_hole h x |-- copy_heap (copy_put h x v).
Proof.
 induction h as [|[a ty old] t IH]; intros ND [ov Hin]; simpl in Hin; [contradiction|].
 inversion ND as [|? ? NA NT]; subst.
 unfold copy_hole, copy_put, copy_write in *; simpl in *.
 destruct (Z.eq_dec a x) as [E|N].
 - subst a. assert (HT: ty = false).
   { destruct Hin as [E|E]; [inversion E; reflexivity|]. exfalso. apply NA. apply in_map with (f:=copy_cell_addr) in E. exact E. }
   subst ty. rewrite Z.eqb_refl. simpl.
   assert (F: filter (fun c => negb (copy_cell_addr c =? x)) t = t).
   { clear IH Hin NT ND. induction t as [|c t IH]; simpl in *; auto. assert (B: (copy_cell_addr c =? x) = false) by (apply Z.eqb_neq; intro E; apply NA; auto). rewrite B. simpl. f_equal. apply IH. intro E; apply NA; auto. }
   assert (M: map (fun c => if Z.eq_dec (copy_cell_addr c) x then {|copy_cell_addr:=copy_cell_addr c;copy_cell_ptr:=copy_cell_ptr c;copy_cell_value:=Some v|} else c) t = t).
   { clear IH Hin NT ND F. induction t as [|c t IH]; simpl in *; auto. destruct (Z.eq_dec (copy_cell_addr c) x) as [E|E]; [exfalso; apply NA; auto|]. f_equal. apply IH. intro H; apply NA; auto. }
   rewrite F, M. simpl. unfold copy_cell_heap; simpl. cancel.
 - assert (B: (a =? x) = false) by (apply Z.eqb_neq; exact N).
   rewrite B. simpl. destruct Hin as [E|E]; [inversion E; contradiction|].
   sep_apply_l_atomic (IH NT (ex_intro _ ov E)). cancel.
Qed.
Lemma copy_put_read__category_result h x v y w :
 x <> y -> copy_read h y false w -> copy_read (copy_put h x v) y false w.
Proof.
 intros N H. unfold copy_read, copy_put, copy_write in *. apply in_map_iff.
 exists {|copy_cell_addr:=y;copy_cell_ptr:=false;copy_cell_value:=Some w|}.
 simpl. destruct (Z.eq_dec y x); [congruence|auto].
Qed.
Lemma copy_put_same__category_result h x v :
 NoDup (map copy_cell_addr h) -> copy_read h x false v -> copy_put h x v = h.
Proof.
 unfold copy_read, copy_put, copy_write. induction h as [|[a ty old] t IH]; intros ND HR; [contradiction|].
 inversion ND as [|? ? NA NT]; subst. simpl in *.
 destruct (Z.eq_dec a x) as [E|N].
 - subst a. destruct HR as [E|E].
   + inversion E; subst. f_equal. clear IH ND NT E.
     induction t as [|c t IH]; simpl in *; auto.
     destruct (Z.eq_dec (copy_cell_addr c) x); [exfalso; apply NA; auto|].
     f_equal. apply IH. intro H; apply NA; auto.
   + exfalso. apply NA. apply in_map with (f:=copy_cell_addr) in E; exact E.
 - f_equal. apply IH; auto. destruct HR as [E|E]; [inversion E; contradiction|auto].
Qed.
Lemma copy_heap_two_focus__category_result h x y v w :
 NoDup (map copy_cell_addr h) -> x <> y ->
 copy_writable h x false -> copy_read h y false w ->
 copy_two_holes h x y ** store_uint y w ** store_uint x v |-- copy_heap (copy_put h x v).
Proof.
 intros ND N WX RY.
 set (hf := filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h).
 assert (NDf: NoDup (map copy_cell_addr hf)).
 { unfold hf. clear WX RY hf. induction h as [|c t IH]; simpl; [constructor|]. inversion ND as [|? ? NA NT]; subst. destruct (negb (copy_cell_addr c =? x)); simpl; auto. constructor; auto. intro H. apply NA. apply in_map_iff in H. destruct H as [q [E H]]. apply filter_In in H. rewrite <- E. apply in_map; tauto. }
 assert (RYf: copy_read hf y false w).
 { unfold copy_read, hf. apply filter_In. split; auto. simpl. apply Bool.negb_true_iff. apply Z.eqb_neq. congruence. }
 assert (E: copy_two_holes h x y = copy_hole hf y).
 { unfold copy_two_holes, copy_hole, hf. f_equal. clear ND N WX RY NDf RYf hf. induction h as [|c t IH]; simpl; auto. destruct (negb (copy_cell_addr c =? x)) eqn:Hx; destruct (negb (copy_cell_addr c =? y)) eqn:Hy; simpl; rewrite ?Hy, ?IH; reflexivity. }
 rewrite E.
 sep_apply_l_atomic (copy_heap_put__category_result hf y w NDf (ex_intro _ (Some w) RYf)).
 rewrite (copy_put_same__category_result hf y w NDf RYf).
 change (copy_heap hf) with (copy_hole h x).
 sep_apply_l_atomic (copy_heap_put__category_result h x v ND WX). cancel.
Qed.
Lemma copy_category_address_bridge__category_result p stride i name :
 eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field
 (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_content") "category") name)) = copy_category_address p stride i name.
Proof.
 unfold copy_category_address, copy_cap_address. csimpl. reflexivity.
Qed.
Lemma copy_tag_address_bridge__category_result p stride i :
 eval_addr_expr (RE_addr_of
 (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_type")) = copy_tag_address p stride i.
Proof.
 unfold copy_tag_address, copy_cap_address. csimpl. reflexivity.
Qed.
Lemma copy_put_addrs__object_result h x v :
 map copy_cell_addr (copy_put h x v) = map copy_cell_addr h.
Proof. unfold copy_put, copy_write. rewrite map_map. induction h as [|c h IH]; simpl; auto.
 destruct (Z.eq_dec (copy_cell_addr c) x); simpl; f_equal; auto. Qed.
Lemma copy_put_read_other__object_result h x v y ptr w :
 x <> y -> copy_read h y ptr w -> copy_read (copy_put h x v) y ptr w.
Proof. intros Hxy H. unfold copy_read, copy_put, copy_write in *.
 apply in_map_iff. exists {|copy_cell_addr:=y;copy_cell_ptr:=ptr;copy_cell_value:=Some w|}.
 split; auto. simpl. destruct (Z.eq_dec y x); congruence. Qed.
Lemma copy_put_writable__object_result h x v y ptr :
 copy_writable h y ptr -> copy_writable (copy_put h x v) y ptr.
Proof. intros [w H]. unfold copy_writable, copy_put, copy_write.
 destruct (Z.eq_dec y x) as [E|E].
 - exists (Some v). apply in_map_iff.
   exists {|copy_cell_addr:=y;copy_cell_ptr:=ptr;copy_cell_value:=w|}; split; auto.
   simpl. destruct (Z.eq_dec y x); congruence.
 - exists w. apply in_map_iff.
   exists {|copy_cell_addr:=y;copy_cell_ptr:=ptr;copy_cell_value:=w|}; split; auto.
   simpl. destruct (Z.eq_dec y x); congruence.
Qed.
Lemma copy_put_absent__object_result h x v :
 ~ In x (map copy_cell_addr h) -> copy_put h x v = h.
Proof. unfold copy_put, copy_write. induction h as [|c h IH]; simpl; auto.
 intros H. destruct (Z.eq_dec (copy_cell_addr c) x); [exfalso; apply H; auto|].
 f_equal. apply IH. tauto. Qed.
Lemma copy_filter_absent__object_result h x :
 ~ In x (map copy_cell_addr h) ->
 filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h = h.
Proof. induction h as [|c h IH]; simpl; auto. intros H.
 assert (copy_cell_addr c <> x) by tauto. apply Z.eqb_neq in H0. rewrite H0; simpl.
 f_equal. apply IH. tauto. Qed.
Lemma copy_heap_put__object_result h x ptr v :
 NoDup (map copy_cell_addr h) -> copy_writable h x ptr ->
 copy_hole h x ** copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=Some v|}
 |-- copy_heap (copy_put h x v).
Proof.
 intros Hnd Hw. unfold copy_hole. revert Hnd Hw.
 induction h as [|[y q w] h IH]; intros Hnd [old Hin]; simpl in Hin; [contradiction|].
 inversion Hnd as [|? ? Hnot Htail]; subst. simpl in *.
 destruct (Z.eq_dec y x) as [E|E].
 - subst y. assert (q=ptr) as Eq.
   { destruct Hin as [Hin|Hin]; [inversion Hin; reflexivity|].
     exfalso. apply Hnot. apply in_map_iff. exists {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=old|}; split; [reflexivity|exact Hin]. }
   subst q. unfold copy_put, copy_write; simpl.
   destruct (Z.eq_dec x x); [|contradiction]. rewrite Z.eqb_refl; simpl.
   rewrite copy_filter_absent__object_result by exact Hnot.
   change (copy_heap h ** copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=Some v|}
     |-- copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=Some v|} ** copy_heap (copy_put h x v)).
   rewrite copy_put_absent__object_result by exact Hnot. cancel.
 - assert (Hin' : In {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=old|} h).
   { destruct Hin; [inversion H; contradiction|assumption]. }
   assert (Z.eqb y x = false) as Eb by (apply Z.eqb_neq; exact E).
   unfold copy_put, copy_write; simpl. destruct (Z.eq_dec y x); [contradiction|].
   rewrite Eb; simpl. fold (copy_put h x v).
   sep_apply_l_atomic (IH Htail (ex_intro _ old Hin')). unfold copy_put, copy_write. simpl. cancel.
Qed.
Lemma copy_put_same__object_result h x ptr v :
 NoDup (map copy_cell_addr h) -> copy_read h x ptr v -> copy_put h x v = h.
Proof. intros Hnd Hr. unfold copy_read in Hr. induction h as [|[y q w] h IH]; [contradiction|].
 inversion Hnd as [|? ? Hnot Htail]; subst. simpl in Hr.
 destruct Hr as [E|Hin].
 - inversion E; subst. unfold copy_put, copy_write; simpl.
   destruct (Z.eq_dec x x); [|contradiction]. f_equal.
   change (copy_put h x v = h). apply copy_put_absent__object_result; exact Hnot.
 - assert (y <> x) as E.
   { intro E; subst. apply Hnot. apply in_map_iff.
     exists {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=Some v|}; auto. }
   unfold copy_put, copy_write; simpl. destruct (Z.eq_dec y x); [contradiction|].
   f_equal. apply IH; auto.
Qed.
Lemma copy_filter_nodup__object_result h (f:copy_cell->bool) :
 NoDup (map copy_cell_addr h) -> NoDup (map copy_cell_addr (filter f h)).
Proof. induction h as [|c h IH]; simpl; intros H; [constructor|].
 inversion H; subst. destruct (f c); simpl; auto. constructor; auto.
 intro Hin. apply H2. apply in_map_iff in Hin as [z [E Hin]].
 apply filter_In in Hin as [Hin _]. apply in_map_iff. exists z; auto.
Qed.
Lemma copy_heap_restore__object_result h x ptr v :
 NoDup (map copy_cell_addr h) -> copy_read h x ptr v ->
 copy_hole h x ** copy_cell_heap {|copy_cell_addr:=x;copy_cell_ptr:=ptr;copy_cell_value:=Some v|}
 |-- copy_heap h.
Proof. intros Hnd Hr. pose proof (copy_heap_put__object_result h x ptr v Hnd (ex_intro _ (Some v) Hr)) as H.
 rewrite (copy_put_same__object_result h x ptr v Hnd Hr) in H. exact H. Qed.
Lemma copy_heap_two_focus__object_result h x y v w :
 NoDup (map copy_cell_addr h) -> x <> y -> copy_writable h x true -> copy_read h y true w ->
 copy_two_holes h x y ** store_ptr y w ** store_ptr x v |-- copy_heap (copy_put h x v).
Proof. intros Hnd Hxy Hx Hy.
 assert (Hfilter : copy_read (filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h) y true w).
 { unfold copy_read in *. apply filter_In. split; auto. simpl.
   apply negb_true_iff. apply Z.eqb_neq. congruence. }
 assert (E : copy_two_holes h x y = copy_hole (filter (fun c => negb (Z.eqb (copy_cell_addr c) x)) h) y).
 { unfold copy_two_holes, copy_hole. f_equal. clear Hnd Hx Hy Hfilter.
   induction h as [|c h IH]; simpl; auto. destruct (Z.eqb (copy_cell_addr c) x) eqn:Ex, (Z.eqb (copy_cell_addr c) y) eqn:Ey; simpl; rewrite ?Ex, ?Ey, ?IH; auto. }
 rewrite E.
 sep_apply_l_atomic (copy_heap_restore__object_result _ y true w (copy_filter_nodup__object_result _ _ Hnd) Hfilter).
 sep_apply_l_atomic (copy_heap_put__object_result h x true v Hnd Hx). cancel.
Qed.
Lemma copy_object_post__object_result h hc a nb stride d s f key idx :
 copy_live a d s f -> copy_tag (copy_slots a (copy_table a s) f) = 2 ->
 key = copy_pointer (copy_slots a (copy_table a s) f) ->
 copy_allocation_state h hc a nb d key idx ->
 copy_post h (copy_write_all hc (copy_object_delta a stride d s f idx)) a nb stride d s f 0.
Proof.
 intros Live Tag Key Alloc. subst key. destruct Live as [F [D [S [Td Ts]]]].
 destruct Alloc as [[Look [Idx [Bound HC]]]|[Look [Nz [Bound HC]]]].
 - subst idx hc. unfold copy_post.
   exists {|copy_table:=copy_table a;
     copy_counter:=fun p => if Z.eq_dec p d then copy_counter a p + 1 else copy_counter a p;
     copy_slots:=fun p i => if Z.eq_dec p (copy_table a d) then
       if Z.eq_dec i (copy_counter a d) then
         {|copy_tag:=2;copy_word0:=copy_word0 (copy_slots a (copy_table a s) f);
           copy_word1:=copy_word1 (copy_slots a p i);copy_pointer:=copy_pointer (copy_slots a (copy_table a s) f)|}
       else copy_slots a p i else copy_slots a p i|}.
   exists ((nb+4*d,copy_counter a d+1)::copy_object_delta a stride d s f (copy_counter a d)).
   split.
   + unfold copy_result. right. repeat split; auto. right. repeat split; auto.
     right; right. split; auto. exists 0. split; auto. right; left.
     repeat split; auto; try lia.
   + split.
     * unfold copy_delta. right; right. repeat split; auto. exists 0. split; auto.
     * reflexivity.
 - subst hc. unfold copy_post.
   exists {|copy_table:=copy_table a;
     copy_counter:=fun p => if Z.eq_dec p d then copy_counter a p + 0 else copy_counter a p;
     copy_slots:=fun p i => if Z.eq_dec p (copy_table a d) then
       if Z.eq_dec i idx then
         {|copy_tag:=2;copy_word0:=copy_word0 (copy_slots a (copy_table a s) f);
           copy_word1:=copy_word1 (copy_slots a p i);copy_pointer:=copy_pointer (copy_slots a (copy_table a s) f)|}
       else copy_slots a p i else copy_slots a p i|}.
   exists (copy_object_delta a stride d s f idx). split.
   + unfold copy_result. right. repeat split; auto. right. repeat split; auto.
     right; right. split; auto. exists idx. split; auto. right; right.
     repeat split; auto.
   + split; [|reflexivity]. unfold copy_delta. right; right. repeat split; auto.
     exists idx. split; auto.
Qed.
Lemma copy_object_ready__object_result h hc a tb nb ps stride d s f key idx :
 copy_pre h a tb nb ps stride d s f -> copy_live a d s f ->
 copy_tag (copy_slots a (copy_table a s) f) = 2 ->
 key = copy_pointer (copy_slots a (copy_table a s) f) ->
 copy_allocation_state h hc a nb d key idx ->
 let h2 := copy_put (copy_put hc (copy_tag_address (copy_table a d) stride idx) 2)
   (copy_object_address (copy_table a d) stride idx "object_right")
   (copy_word0 (copy_slots a (copy_table a s) f)) in
 NoDup (map copy_cell_addr h2) /\
 copy_writable h2 (copy_object_address (copy_table a d) stride idx "object_t") true /\
 copy_read h2 (copy_object_address (copy_table a s) stride f "object_t") true
   (copy_pointer (copy_slots a (copy_table a s) f)).
Proof.
 intros Pre Live Tag Key Alloc. subst key. cbn zeta.
 destruct Pre as [Safe [ND [Layout [Tables [Tags [Cat Obj]]]]]].
 specialize (Layout Live). specialize (Obj Live Tag).
 destruct Obj as [Src [Scan Avail]].
 destruct Safe as [[D0 [S0 F0]] Safe].
 pose proof Live as [F [D [S [Td Ts]]]].
 assert (Bi : 0 <= idx < 255) by (destruct Alloc as [[? [? [? ?]]]|[? [? [? ?]]]]; auto).
 destruct Layout as [Union [Inject [Separate TablesSep]]].
 assert (U : copy_category_address (copy_table a d) stride idx "category_content" =
             copy_object_address (copy_table a d) stride idx "object_right").
 { specialize (Union (copy_table a d) idx (or_introl eq_refl) Bi). tauto. }
 assert (Nt : copy_tag_address (copy_table a d) stride idx <>
              copy_object_address (copy_table a s) stride f "object_t").
 { intro E. assert (Ec : copy_component_address (copy_table a d) stride idx 0 =
                        copy_component_address (copy_table a s) stride f 3).
   { unfold copy_component_address; simpl. exact E. }
   specialize (Inject (copy_table a d) (copy_table a s) idx f 0 3
      (or_introl eq_refl) (or_intror eq_refl) Bi ltac:(lia) ltac:(lia) ltac:(lia) Ec). lia. }
 assert (Nr : copy_object_address (copy_table a d) stride idx "object_right" <>
              copy_object_address (copy_table a s) stride f "object_t").
 { intro E. assert (Ec : copy_component_address (copy_table a d) stride idx 1 =
                        copy_component_address (copy_table a s) stride f 3).
   { unfold copy_component_address; simpl. rewrite U. exact E. }
   specialize (Inject (copy_table a d) (copy_table a s) idx f 1 3
      (or_introl eq_refl) (or_intror eq_refl) Bi ltac:(lia) ltac:(lia) ltac:(lia) Ec). lia. }
 assert (Nc : nb+4*d <> copy_object_address (copy_table a s) stride f "object_t").
 { specialize (Separate (copy_table a s) f 3 d (or_intror eq_refl) ltac:(lia) ltac:(lia) ltac:(lia)).
   change (copy_object_address (copy_table a s) stride f "object_t" <> tb+ps*d /\ copy_object_address (copy_table a s) stride f "object_t" <> nb+4*d) in Separate. destruct Separate. congruence. }
 assert (Base : NoDup (map copy_cell_addr hc) /\
   copy_writable hc (copy_object_address (copy_table a d) stride idx "object_t") true /\
   copy_read hc (copy_object_address (copy_table a s) stride f "object_t") true
      (copy_pointer (copy_slots a (copy_table a s) f))).
 { destruct Alloc as [[Look [Idx [Bound HC]]]|[Look [Nz [Bound HC]]]].
   - subst idx hc. specialize (Avail 0 Look). destruct Avail as [_ [A _]].
     specialize (A eq_refl ltac:(lia)). destruct A as [_ [_ [_ [_ [_ W]]]]].
     split; [rewrite copy_put_addrs__object_result; exact ND|]. split.
     + apply copy_put_writable__object_result; exact W.
     + apply copy_put_read_other__object_result; auto.
   - subst hc. specialize (Avail idx Look). destruct Avail as [_ [_ A]].
     specialize (A Nz). destruct A as [_ [_ [_ [_ W]]]]. auto. }
 destruct Base as [NDc [Wc Rc]]. split.
 - repeat rewrite copy_put_addrs__object_result. exact NDc.
 - split.
   + repeat apply copy_put_writable__object_result. exact Wc.
   + apply copy_put_read_other__object_result; auto.
     apply copy_put_read_other__object_result; auto.
Qed.
Lemma copy_tag_concrete__object_result p stride i :
 eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_type")) =
 copy_tag_address p stride i.
Proof. unfold copy_cap_address, copy_tag_address. rewrite (eval_addr (RE_addr_of (copy_slot_lvalue p stride i)) (FET_alias "cap")). rewrite <- addr_of_arrow_field. reflexivity. Qed.
Lemma copy_object_concrete__object_result p stride i name :
 eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field
  (LE_arrow_field (RE_const (copy_cap_address p stride i) (FET_alias "cap")) "cap_content") "object") name)) =
 copy_object_address p stride i name.
Proof. unfold copy_cap_address, copy_object_address. csimpl. reflexivity. Qed.
Lemma copy_heap_focus__unchanged_result h c :
 NoDup (map copy_cell_addr h) -> In c h ->
 copy_heap h --||-- copy_cell_heap c ** copy_hole h (copy_cell_addr c).
Proof.
 intros ND IN. unfold copy_hole.
 induction h as [|x t IH]; simpl in IN; [contradiction|].
 inversion ND as [|? ? Hnot Hnd]; subst.
 destruct IN as [E|IN].
 - subst x. simpl. rewrite Z.eqb_refl. simpl.
   assert (F : filter (fun c0 => negb (copy_cell_addr c0 =? copy_cell_addr c)) t = t).
   { clear IH Hnd ND. induction t as [|z t IT]; [reflexivity|].
     simpl in *. assert (NE : copy_cell_addr z <> copy_cell_addr c) by intuition.
     apply Z.eqb_neq in NE. rewrite NE. simpl. f_equal. apply IT. intuition. }
   rewrite F. split; cancel.
 - assert (NE : copy_cell_addr x <> copy_cell_addr c).
   { intro E. apply Hnot. rewrite E. apply in_map. exact IN. }
   simpl. apply Z.eqb_neq in NE. rewrite NE. simpl.
   specialize (IH Hnd IN). rewrite IH. split; cancel.
Qed.
Lemma copy_unchanged_post__unchanged_result h a nb stride d s f ret :
 copy_result a a d s f ret -> ret <> 0 -> copy_post h h a nb stride d s f ret.
Proof. intros HR HN. exists a, nil. split; [exact HR|]. split.
 - left. split; auto.
 - reflexivity.
Qed.
