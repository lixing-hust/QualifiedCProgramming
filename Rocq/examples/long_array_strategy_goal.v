Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Module LongArray.

Definition storeA (x lo a : Z) : Assertion :=
  (x + lo * sizeof(INT64)) # Int64 |-> a.

Definition undefstoreA (x lo : Z) : Assertion :=
  (x + lo * sizeof(INT64)) # Int64 |->_.

Definition full (p n : Z) (l : list Z) : Assertion :=
  store_array storeA p n l.

Definition seg (p lo hi : Z) (l : list Z) : Assertion :=
  store_array_rec storeA p lo hi l.

Definition missing_i (p i lo hi : Z) (l : list Z) : Assertion :=
  store_array_missing_i_rec storeA p i lo hi l.

Definition undef_full (p n : Z) : Assertion :=
  store_undef_array undefstoreA p n.

Definition undef_seg (p lo hi : Z) : Assertion :=
  store_undef_array_rec undefstoreA p lo hi (Z.to_nat (hi - lo)).

Definition undef_missing_i (p i lo hi : Z) : Assertion :=
  store_undef_array_missing_i_rec undefstoreA p i lo hi (Z.to_nat (hi - lo)).

Definition full_shape (p n : Z) : Assertion := undef_full p n.
Definition seg_shape (p lo hi : Z) : Assertion := undef_seg p lo hi.
Definition missing_i_shape (p i lo hi : Z) : Assertion := undef_missing_i p i lo hi.

End LongArray.

Definition long_array_strategy1 :=
  forall (i n p : Z) (l : list Z),
    TT && [| 0 <= i |] && [| i < n |] && emp ** LongArray.full p n l
    |--
    (TT && emp ** LongArray.missing_i p i 0 n l) **
    (ALL (v : Z),
      TT && [| v = Znth i l 0 |] && emp -*
      TT && emp ** poly_store FET_int64 (p + i * sizeof(INT64)) v).

Definition long_array_strategy2 :=
  forall (i n : Z) (l : list Z) (p : Z),
    TT && [| 0 <= i |] && [| i < n |] && emp **
    LongArray.missing_i p i 0 n l **
    poly_store FET_int64 (p + i * sizeof(INT64)) (Znth i l 0)
    |--
    (TT && emp ** LongArray.full p n l) **
    (TT && emp -* TT && emp).

Definition long_array_strategy3 :=
  forall (i n : Z) (l : list Z) (v p : Z),
    TT && [| 0 <= i |] && [| i < n |] && emp **
    LongArray.missing_i p i 0 n l **
    poly_store FET_int64 (p + i * sizeof(INT64)) v
    |--
    (TT && emp ** LongArray.full p n (replace_Znth i v l)) **
    (TT && emp -* TT && emp).

Definition long_array_strategy4 :=
  forall (p : Z) (l1 : list Z) (n : Z),
    TT && emp ** LongArray.full p n l1
    |--
    (TT && emp) **
    (ALL (l2 : list Z),
      TT && [| l1 = l2 |] && emp -*
      TT && emp ** LongArray.full p n l2).

Definition long_array_strategy5 :=
  forall (p v : Z) (l : list Z) (n i : Z),
    TT && emp ** LongArray.missing_i p i v n l
    |--
    (TT && emp) **
    (TT && emp -* TT && emp ** LongArray.missing_i p i v n l).

Definition long_array_strategy6 :=
  forall (p y : Z) (l1 : list Z) (x : Z),
    TT && emp ** LongArray.seg p x y l1
    |--
    (TT && emp) **
    (ALL (l2 : list Z),
      TT && [| l1 = l2 |] && emp -*
      TT && emp ** LongArray.seg p x y l2).

Definition long_array_strategy7 :=
  forall (i y x p : Z) (l : list Z),
    TT && [| x <= i |] && [| i < y |] && emp ** LongArray.seg p x y l
    |--
    (TT && emp ** LongArray.missing_i p i x y l) **
    (ALL (v : Z),
      TT && [| v = Znth (i - x) l 0 |] && emp -*
      TT && emp ** poly_store FET_int64 (p + i * sizeof(INT64)) v).

Definition long_array_strategy8 :=
  forall (x y z : Z) (l1 : list Z) (p : Z) (l2 : list Z),
    TT && [| y <= z |] && [| x <= y |] && emp **
    LongArray.seg p x y l1 ** LongArray.seg p y z l2
    |--
    (TT && emp) **
    (ALL (l3 : list Z),
      TT && [| l3 = @app Z l1 l2 |] && emp -*
      TT && emp ** LongArray.seg p x z l3).

Definition long_array_strategy9 :=
  forall (x y z p : Z) (l3 : list Z),
    TT && [| y <= z |] && [| x <= y |] && emp ** LongArray.seg p x z l3
    |--
    (TT && emp) **
    (ALL (l1 l2 : list Z),
      TT && [| l3 = @app Z l1 l2 |] && [| Zlength l1 = y - x |] && emp -*
      TT && emp ** LongArray.seg p x y l1 ** LongArray.seg p y z l2).

Definition long_array_strategy10 :=
  TT && emp
  |--
  (TT && emp) **
  (ALL (l : list Z) (p x : Z),
    TT && [| l = nil |] && emp -*
    TT && emp ** LongArray.seg p x x l).

Definition long_array_strategy11 :=
  forall (i y x : Z) (l : list Z) (p : Z),
    TT && [| x <= i |] && [| i < y |] && emp **
    LongArray.missing_i p i x y l **
    poly_store FET_int64 (p + i * sizeof(INT64)) (Znth (i - x) l 0)
    |--
    (TT && emp ** LongArray.seg p x y l) **
    (TT && emp -* TT && emp).

Definition long_array_strategy12 :=
  forall (i y x : Z) (l : list Z) (v p : Z),
    TT && [| x <= i |] && [| i < y |] && emp **
    LongArray.missing_i p i x y l **
    poly_store FET_int64 (p + i * sizeof(INT64)) v
    |--
    (TT && emp ** LongArray.seg p x y (replace_Znth (i - x) v l)) **
    (TT && emp -* TT && emp).

Module Type long_array_Strategy_Correct.

  Axiom long_array_strategy1_correctness : long_array_strategy1.
  Axiom long_array_strategy2_correctness : long_array_strategy2.
  Axiom long_array_strategy3_correctness : long_array_strategy3.
  Axiom long_array_strategy4_correctness : long_array_strategy4.
  Axiom long_array_strategy5_correctness : long_array_strategy5.
  Axiom long_array_strategy6_correctness : long_array_strategy6.
  Axiom long_array_strategy7_correctness : long_array_strategy7.
  Axiom long_array_strategy8_correctness : long_array_strategy8.
  Axiom long_array_strategy9_correctness : long_array_strategy9.
  Axiom long_array_strategy10_correctness : long_array_strategy10.
  Axiom long_array_strategy11_correctness : long_array_strategy11.
  Axiom long_array_strategy12_correctness : long_array_strategy12.

End long_array_Strategy_Correct.
