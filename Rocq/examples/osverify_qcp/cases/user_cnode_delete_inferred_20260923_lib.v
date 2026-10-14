From Coq Require Import ZArith List String.
From SimpleC.SL Require Import SeparationLogic.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* Independently inferred finite physical-cell state; no kernel model imports. *)
Inductive DKind := DUInt | DPtr | DUChar.
Record DCell := { dkind : DKind; daddr : Z; dcontents : option Z }.
Definition DMemory := list DCell.
Definition DLookup (m : DMemory) (a : Z) : option Z :=
  match find (fun c => Z.eqb (daddr c) a) m with
  | Some c => dcontents c | None => None end.
Definition DVal (m : DMemory) (a : Z) : Z :=
  match DLookup m a with Some v => v | None => 0 end.
Definition DReadable (m : DMemory) (a : Z) : Prop :=
  exists v, DLookup m a = Some v.
Definition DHasKind (m : DMemory) (a : Z) (k : DKind) : Prop :=
  forall c, In c m -> daddr c = a -> dkind c = k.
Definition DReadAs (m : DMemory) (a : Z) (k : DKind) : Prop :=
  DReadable m a /\ DHasKind m a k.
Definition DWritable (m : DMemory) (a : Z) (k : DKind) : Prop :=
  exists c, In c m /\ daddr c = a /\ dkind c = k.
Definition DReadUInt m a := DReadAs m a DUInt.
Definition DReadPtr m a := DReadAs m a DPtr.
Definition DReadByte m a := DReadAs m a DUChar.
Definition DWriteUInt m a := DWritable m a DUInt.
Definition DWritePtr m a := DWritable m a DPtr.
Definition DWrite (m : DMemory) (a v : Z) : DMemory :=
  map (fun c => if Z.eqb (daddr c) a
       then {| dkind := dkind c; daddr := daddr c; dcontents := Some v |}
       else c) m.
Definition DCellHeap (c : DCell) : expr :=
  match dkind c, dcontents c with
  | DUInt, Some v => store_uint (daddr c) v
  | DUInt, None => undef_store_uint (daddr c)
  | DPtr, Some v => store_ptr (daddr c) v
  | DPtr, None => undef_store_ptr (daddr c)
  | DUChar, Some v => store_uchar (daddr c) v
  | DUChar, None => undef_store_uchar (daddr c)
  end.
Fixpoint DHeap (m : DMemory) : expr :=
  match m with [] => emp | c :: cs => sepcon (DCellHeap c) (DHeap cs) end.
(* One physical cell is extracted at a time. It is never owned twice. *)
Definition DWithout (m : DMemory) (a : Z) : DMemory :=
  filter (fun c => negb (Z.eqb (daddr c) a)) m.
Definition DHeapRest (m : DMemory) (a : Z) : expr := DHeap (DWithout m a).
Definition DHeapRest2 (m : DMemory) (a b : Z) : expr :=
  DHeap (DWithout (DWithout m a) b).
Definition DHeapRest3 (m : DMemory) (a b c : Z) : expr :=
  DHeap (DWithout (DWithout (DWithout m a) b) c).
Definition DHeapRest4 (m : DMemory) (a b c d : Z) : expr :=
  DHeap (DWithout (DWithout (DWithout (DWithout m a) b) c) d).

Definition DGlobal (s : string) : Z := eval_addr_expr (RE_addr_of (LE_var s)).
Definition DIndex (s : string) (i : Z) : Z :=
  eval_addr_expr (RE_addr_of (LE_array_subst (LE_var s) i)).
Definition DField (p : Z) (ty field : string) : Z :=
  eval_addr_expr (RE_addr_of (LE_arrow_field (RE_const p (FET_struct ty)) field)).
Definition DSlot (p i : Z) : lvalue_expr :=
  LE_array_subst (LE_dot_field
    (LE_arrow_field (RE_const p (FET_struct "cspace")) "cnode") "slots") i.
Definition DSField (p i : Z) (f : string) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field (DSlot p i) f)).
Definition DCapField (p i : Z) (f : string) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field
    (LE_dot_field (DSlot p i) "capability") f)).
Definition DUnionField (p i : Z) (view f : string) : Z :=
  eval_addr_expr (RE_addr_of (LE_dot_field (LE_dot_field
    (LE_dot_field (LE_dot_field (DSlot p i) "capability") "cap_content") view) f)).
Definition DW0 p i := DUnionField p i "category" "category_content".
Definition DW1 p i := DUnionField p i "category" "category_right".
Definition DObj p i := DUnionField p i "object" "object_t".
Definition DSpace m p := DVal m (DIndex "OSCSpacePrioTbl" p).
Definition DEnd m p := DVal m (DIndex "OSCSpaceObjectPointer" p).
Definition DCurrent m := DVal m (DGlobal "OSTCBCur").
Definition DPrioAddress m := DField (DCurrent m) "os_tcb" "OSTCBPrio".
Definition DPrio m := DVal m (DPrioAddress m).
Definition DRightAddress m := DW1 (DSpace m (DPrio m)) 11.
Definition DRightBits m := Z.land (DVal m (DRightAddress m)) 16.
Definition DEvtAddress (t c : Z) : Z :=
  let name := if Z.eqb t 2 then "Sem_info"
              else if Z.eqb t 3 then "Pthread_Mutex" else "Mq_Attr" in
  eval_addr_expr (RE_addr_of (LE_dot_field (LE_array_subst (LE_var name) c) "pevent")).
Definition DEvent m t c := DVal m (DEvtAddress t c).
Definition DTask m c := DVal m (DIndex "OSTCBPrioTbl" c).
(* The source configuration is a parameter, not a readable mutable cell. *)
Definition DConfiguration (max_events : Z) : Prop := 19 <= max_events <= 255.
Definition DLimit (max_events : Z) : Z := max_events - 16.
Definition DUnionLayout : Prop := forall p i,
  DUnionField p i "object" "object_right" = DW0 p i /\
  DUnionField p i "object" "Dummy_int" = DW1 p i /\
  DUnionField p i "category" "Dummy_ptr" = DObj p i.
Definition DTyped (m : DMemory) : Prop :=
  NoDup (map daddr m) /\
  (forall c, In c m -> match dcontents c with
   | None => True
   | Some v => match dkind c with
     | DUChar => 0 <= v <= 255
     | _ => 0 <= v <= 4294967295 end end).

(* Search specifies the least match, not an executable search recurrence. *)
Definition DAbsent m p obj lo hi : Prop :=
  forall j, lo <= j < hi -> DVal m (DObj p j) <> obj.
Definition DFirst m p obj hi r : Prop :=
  (r = 0 /\ DAbsent m p obj 17 hi) \/
  (17 <= r < hi /\ DVal m (DObj p r) = obj /\ DAbsent m p obj 17 r).
Definition DGetResult m prio obj r : Prop :=
  (63 <= prio /\ r = 42) \/
  (prio < 63 /\
   ((DSpace m prio = 0 /\ r = 0) \/
    (DSpace m prio <> 0 /\ DFirst m (DSpace m prio) obj (DEnd m prio) r))).
Definition DGetSafe m prio obj : Prop :=
  0 <= prio <= 255 /\ (prio < 63 ->
  DReadAs m (DIndex "OSCSpacePrioTbl" prio) DPtr /\
  DReadAs m (DIndex "OSCSpaceObjectPointer" prio) DUInt /\
  (DSpace m prio <> 0 -> 0 <= DEnd m prio <= 4294967295 /\
    forall i, 17 <= i < DEnd m prio -> DAbsent m (DSpace m prio) obj 17 i ->
      i < 255 /\ DReadAs m (DObj (DSpace m prio) i) DPtr)).
Definition DObjectRequest m max_events typ cap obj : Prop :=
  ((typ = 2 \/ typ = 3 \/ typ = 4) /\ cap < DLimit max_events / 3 /\ obj = DEvent m typ cap) \/
  (typ = 5 /\ 0 < cap < 62 /\ obj = DTask m cap).
Definition DValidObjectRequest max_events typ cap : Prop :=
  ((typ = 2 \/ typ = 3 \/ typ = 4) /\ cap < DLimit max_events / 3) \/
  (typ = 5 /\ 0 < cap < 62).
Definition DCheckResult m max_events cap typ prio r : Prop :=
  (typ = 1 /\ ((cap <= 16 /\ r = cap) \/ (16 < cap /\ r = 255))) \/
  (typ <> 1 /\
    ((~ DValidObjectRequest max_events typ cap /\ r = 255) \/
     (exists obj, DObjectRequest m max_events typ cap obj /\
       ((obj = 0 /\ r = 255) \/
        (obj <> 0 /\ exists s, DGetResult m prio obj s /\
           ((s = 0 /\ r = 255) \/ (s <> 0 /\ r = s))))))).
Definition DCheckSafe m max_events cap typ prio : Prop :=
  0 <= cap <= 4294967295 /\ 0 <= typ <= 255 /\ 0 <= prio <= 255 /\
  DConfiguration max_events /\
  (((typ = 2 \/ typ = 3 \/ typ = 4) /\ cap < DLimit max_events / 3) ->
    DReadAs m (DEvtAddress typ cap) DPtr /\ (DEvent m typ cap <> 0 -> DGetSafe m prio (DEvent m typ cap))) /\
  ((typ = 5 /\ 0 < cap < 62) -> DReadAs m (DIndex "OSTCBPrioTbl" cap) DPtr /\
     (DTask m cap <> 0 -> DGetSafe m prio (DTask m cap))).

Definition DCoreEligible m prio slot : Prop :=
  0 <= slot < 255 /\ 0 <= prio < 64 /\ DSpace m prio <> 0.
Definition DCapType m prio slot := DVal m (DCapField (DSpace m prio) slot "cap_type").
Definition DCanDelete m prio slot : Prop :=
  DCoreEligible m prio slot /\ (DCapType m prio slot = 1 \/ DCapType m prio slot = 2).
Definition DPayloadDeleted m prio slot : DMemory :=
  let p := DSpace m prio in
  let m1 := DWrite (DWrite m (DCapField p slot "cap_type") 0) (DW0 p slot) 0 in
  if Z.eqb (DCapType m prio slot) 1
  then DWrite m1 (DW1 p slot) 0 else DWrite m1 (DObj p slot) 0.
Definition DDeleted m prio slot : DMemory :=
  DWrite (DPayloadDeleted m prio slot)
         (DSField (DSpace m prio) slot "slot_type") 0.
Definition DCoreResult m prio slot r m' : Prop :=
  (DCanDelete m prio slot /\ r = 0 /\ m' = DDeleted m prio slot) \/
  (~ DCanDelete m prio slot /\ r = 9 /\ m' = m).
Definition DCoreSafe m prio slot : Prop :=
  0 <= prio <= 255 /\ 0 <= slot <= 4294967295 /\
  ((slot < 255 /\ prio < 64) -> DReadAs m (DIndex "OSCSpacePrioTbl" prio) DPtr /\
    (DSpace m prio <> 0 -> DReadAs m (DCapField (DSpace m prio) slot "cap_type") DUInt /\
     ((DCapType m prio slot = 1 \/ DCapType m prio slot = 2) ->
       DWritable m (DSField (DSpace m prio) slot "slot_type") DUInt /\
       DWritable m (DW0 (DSpace m prio) slot) DUInt /\
       (DCapType m prio slot = 1 -> DWritable m (DW1 (DSpace m prio) slot) DUInt) /\
       (DCapType m prio slot = 2 -> DWritable m (DObj (DSpace m prio) slot) DPtr)))).
(* Read footprint of the unchanged short-circuit authorization expression. *)
Definition DAuthFootprint m prio : Prop :=
  DReadUInt m (DRightAddress m) /\
  (DRightBits m <> 0 ->
   DReadPtr m (DGlobal "OSTCBCur") /\ DReadByte m (DPrioAddress m) /\
   DReadByte m (DIndex "CapParent" prio)).
Definition DAuthorized m prio : Prop :=
  Z.land (DVal m (DW1 (DSpace m (DPrio m)) 11)) 16 <> 0 /\
  (DVal m (DIndex "CapParent" prio) = DPrio m \/ prio = DPrio m).
Definition DUserResult m max_events prio typ cap r m' : Prop :=
  (63 <= prio /\ r = 42 /\ m' = m) \/
  (prio < 63 /\ 5 < typ /\ r = 30 /\ m' = m) \/
  (prio < 63 /\ typ <= 5 /\ exists slot, DCheckResult m max_events cap typ prio slot /\
   ((slot = 255 /\ r = 30 /\ m' = m) \/
    (slot <> 255 /\
     ((DSpace m (DPrio m) = 0 /\ r = 9 /\ m' = m) \/
      (DSpace m (DPrio m) <> 0 /\
       ((~ DAuthorized m prio /\ r = 252 /\ m' = m) \/
        (DAuthorized m prio /\ DCoreResult m prio slot r m'))))))).
Definition DUserSafe m max_events prio typ cap : Prop :=
  DConfiguration max_events /\ 0 <= prio <= 255 /\ 0 <= typ <= 255 /\ 0 <= cap <= 4294967295 /\
  ((prio < 63 /\ typ <= 5) -> DCheckSafe m max_events cap typ prio /\
   forall slot, DCheckResult m max_events cap typ prio slot -> slot <> 255 ->
     DReadAs m (DGlobal "OSTCBCur") DPtr /\ DCurrent m <> 0 /\
     DReadAs m (DField (DCurrent m) "os_tcb" "OSTCBPrio") DUChar /\
     0 <= DPrio m < 64 /\ DReadAs m (DIndex "OSCSpacePrioTbl" (DPrio m)) DPtr /\
     (DSpace m (DPrio m) <> 0 ->
       DReadAs m (DW1 (DSpace m (DPrio m)) 11) DUInt /\
       (Z.land (DVal m (DW1 (DSpace m (DPrio m)) 11)) 16 <> 0 ->
         DReadAs m (DIndex "CapParent" prio) DUChar) /\
       (DAuthorized m prio -> DCoreSafe m prio slot))).
