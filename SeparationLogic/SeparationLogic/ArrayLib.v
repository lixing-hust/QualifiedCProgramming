Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux.
Require Export ArrayLibCore.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type ArrayLibSig (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig CRules) (SLibSig : StoreLibSig CRules DePredSig).

Include ArrayLibCoreSig CRules DePredSig SLibSig.

Import CRules.
Import DePredSig.
Import SLibSig.
Local Open Scope sac.

Module StoreCharAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(CHAR)) # Char |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(CHAR)) # Char |->_ .
  Definition sizeA := sizeof(CHAR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_char_undef_store_char.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(CHAR) + lo * sizeof(CHAR)) with (x + (lo + n) * sizeof(CHAR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(CHAR) + lo * sizeof(CHAR)) with (x + (lo + n) * sizeof(CHAR)) by lia.
    entailer!.
  Qed.

End StoreCharAsElement.

Module CharArray := ArrayLib (StoreCharAsElement).

Module StoreUCharAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UCHAR)) # UChar |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UCHAR)) # UChar |->_ .
  Definition sizeA := sizeof(UCHAR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uchar_undef_store_uchar.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UCHAR) + lo * sizeof(UCHAR)) with (x + (lo + n) * sizeof(UCHAR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UCHAR) + lo * sizeof(UCHAR)) with (x + (lo + n) * sizeof(UCHAR)) by lia.
    entailer!.
  Qed.

End StoreUCharAsElement.

Module UCharArray := ArrayLib (StoreUCharAsElement).

Module StoreShortAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(SHORT)) # Short |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(SHORT)) # Short |->_ .
  Definition sizeA := sizeof(SHORT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_short_undef_store_short.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(SHORT) + lo * sizeof(SHORT)) with (x + (lo + n) * sizeof(SHORT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(SHORT) + lo * sizeof(SHORT)) with (x + (lo + n) * sizeof(SHORT)) by lia.
    entailer!.
  Qed.

End StoreShortAsElement.

Module ShortArray := ArrayLib (StoreShortAsElement).

Module StoreUShortAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(USHORT)) # UShort |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(USHORT)) # UShort |->_ .
  Definition sizeA := sizeof(USHORT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_ushort_undef_store_ushort.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(USHORT) + lo * sizeof(USHORT)) with (x + (lo + n) * sizeof(USHORT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(USHORT) + lo * sizeof(USHORT)) with (x + (lo + n) * sizeof(USHORT)) by lia.
    entailer!.
  Qed.

End StoreUShortAsElement.

Module UShortArray := ArrayLib (StoreUShortAsElement).

Module StoreIntAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(INT)) # Int |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(INT)) # Int |->_ .
  Definition sizeA := sizeof(INT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_int_undef_store_int.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(INT) + lo * sizeof(INT)) with (x + (lo + n) * sizeof(INT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(INT) + lo * sizeof(INT)) with (x + (lo + n) * sizeof(INT)) by lia.
    entailer!.
  Qed.

End StoreIntAsElement.

Module IntArray := ArrayLib (StoreIntAsElement).

Module StoreUIntAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UINT)) # UInt |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UINT)) # UInt |->_ .
  Definition sizeA := sizeof(UINT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uint_undef_store_uint.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UINT) + lo * sizeof(UINT)) with (x + (lo + n) * sizeof(UINT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UINT) + lo * sizeof(UINT)) with (x + (lo + n) * sizeof(UINT)) by lia.
    entailer!.
  Qed.

End StoreUIntAsElement.

Module UIntArray := ArrayLib (StoreUIntAsElement).

Module StoreInt64AsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(INT64)) # Int64 |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(INT64)) # Int64 |->_ .
  Definition sizeA := sizeof(INT64).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_int64_undef_store_int64.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(INT64) + lo * sizeof(INT64)) with (x + (lo + n) * sizeof(INT64)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(INT64) + lo * sizeof(INT64)) with (x + (lo + n) * sizeof(INT64)) by lia.
    entailer!.
  Qed.

End StoreInt64AsElement.

Module Int64Array := ArrayLib (StoreInt64AsElement).

Module StoreUInt64AsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UINT64)) # UInt64 |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UINT64)) # UInt64 |->_ .
  Definition sizeA := sizeof(UINT64).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uint64_undef_store_uint64.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UINT64) + lo * sizeof(UINT64)) with (x + (lo + n) * sizeof(UINT64)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UINT64) + lo * sizeof(UINT64)) with (x + (lo + n) * sizeof(UINT64)) by lia.
    entailer!.
  Qed.

End StoreUInt64AsElement.

Module UInt64Array := ArrayLib (StoreUInt64AsElement).

Module StorePtrAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(PTR)) # Ptr |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(PTR)) # Ptr |->_ .
  Definition sizeA := sizeof(PTR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_ptr_undef_store_ptr.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(PTR) + lo * sizeof(PTR)) with (x + (lo + n) * sizeof(PTR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(PTR) + lo * sizeof(PTR)) with (x + (lo + n) * sizeof(PTR)) by lia.
    entailer!.
  Qed.

End StorePtrAsElement.

Module PtrArray := ArrayLib (StorePtrAsElement).

End ArrayLibSig.
