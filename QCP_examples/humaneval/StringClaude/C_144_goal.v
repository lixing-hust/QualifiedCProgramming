Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_144.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function simplify -----*)

Definition simplify_safety_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) ,
  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) ,
  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) ,
  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_4 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) ,
  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_5 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) ,
  [| (retval = lenx) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x_len" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "c" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_6 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (47 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 47) |]
.

Definition simplify_safety_wit_7 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (((a * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((a * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) )) |]
.

Definition simplify_safety_wit_8 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition simplify_safety_wit_9 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((a * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (a * 10 )) |]
.

Definition simplify_safety_wit_10 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition simplify_safety_wit_11 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition simplify_safety_wit_12 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ((a * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition simplify_safety_wit_13 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (b: Z) (c: Z) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> sx)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((sx + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sx + 1 )) |]
.

Definition simplify_safety_wit_14 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (b: Z) (c: Z) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> sx)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition simplify_safety_wit_15 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (((b * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((b * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) )) |]
.

Definition simplify_safety_wit_16 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition simplify_safety_wit_17 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((b * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (b * 10 )) |]
.

Definition simplify_safety_wit_18 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition simplify_safety_wit_19 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition simplify_safety_wit_20 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> ((b * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition simplify_safety_wit_21 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (c: Z) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> lenx)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_22 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (47 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 47) |]
.

Definition simplify_safety_wit_23 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (((c * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((c * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) )) |]
.

Definition simplify_safety_wit_24 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition simplify_safety_wit_25 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((c * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (c * 10 )) |]
.

Definition simplify_safety_wit_26 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition simplify_safety_wit_27 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition simplify_safety_wit_28 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> ((c * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ))
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition simplify_safety_wit_29 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> sn)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((sn + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sn + 1 )) |]
.

Definition simplify_safety_wit_30 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> sn)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition simplify_safety_wit_31 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (0 <= (lenx + 1 )) |] 
  &&  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (((d * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((d * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) )) |]
.

Definition simplify_safety_wit_32 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (0 <= (lenx + 1 )) |] 
  &&  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 )) |]
.

Definition simplify_safety_wit_33 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((d * 10 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d * 10 )) |]
.

Definition simplify_safety_wit_34 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition simplify_safety_wit_35 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (0 <= (lenx + 1 )) |] 
  &&  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| (48 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 48) |]
.

Definition simplify_safety_wit_36 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (0 <= (lenx + 1 )) |] 
  &&  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> ((d * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ))
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition simplify_safety_wit_37 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "product_num" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((ax * cn ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ax * cn )) |]
.

Definition simplify_safety_wit_38 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "product_den" ) )) # Int  |->_)
  **  ((( &( "product_num" ) )) # Int  |-> (ax * cn ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((bx * d ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (bx * d )) |]
.

Definition simplify_safety_wit_39 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "product_den" ) )) # Int  |-> (bx * d ))
  **  ((( &( "product_num" ) )) # Int  |-> (ax * cn ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (((ax * cn ) <> (INT_MIN)) \/ ((bx * d ) <> (-1))) |] 
  &&  [| ((bx * d ) <> 0) |]
.

Definition simplify_safety_wit_40 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "product_den" ) )) # Int  |-> (bx * d ))
  **  ((( &( "product_num" ) )) # Int  |-> (ax * cn ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_safety_wit_41 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (((ax * cn ) % ( (bx * d ) ) ) = 0) |] 
  &&  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "product_den" ) )) # Int  |-> (bx * d ))
  **  ((( &( "product_num" ) )) # Int  |-> (ax * cn ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition simplify_safety_wit_42 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (((ax * cn ) % ( (bx * d ) ) ) <> 0) |] 
  &&  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  ((( &( "product_den" ) )) # Int  |-> (bx * d ))
  **  ((( &( "product_num" ) )) # Int  |-> (ax * cn ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition simplify_entail_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (retval: Z) ,
  [| (retval = lenx) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "x_len" ) )) # Int  |-> retval)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= sx) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= ax) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = (parse_digits_z ((sublist (0) (0) (lx))))) |]
  &&  ((( &( "x_len" ) )) # Int  |-> lenx)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= sx) |] 
  &&  [| (0 <= ((a * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) )) |] 
  &&  [| (((a * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ) <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (((a * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ) = (parse_digits_z ((sublist (0) ((i + 1 )) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) = 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "i" ) )) # Int  |-> sx)
  **  ((( &( "a" ) )) # Int  |-> ax)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_4 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (b: Z) (c: Z) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= (sx + 1 )) |] 
  &&  [| ((sx + 1 ) <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) ((sx + 1 )) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_5 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lenx) |] 
  &&  [| (0 <= ((b * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) )) |] 
  &&  [| (((b * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ) <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (((b * 10 ) + ((Znth i (app (lx) ((cons (0) (nil)))) 0) - 48 ) ) = (parse_digits_z ((sublist ((sx + 1 )) ((i + 1 )) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_6 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (i >= lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "i" ) )) # Int  |-> lenx)
  **  ((( &( "b" ) )) # Int  |-> bx)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_7 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (c: Z) (d: Z) (retval: Z) ,
  [| (retval = lenn) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "n_len" ) )) # Int  |-> retval)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "n_len" ) )) # Int  |-> lenn)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_8 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (c: Z) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (0) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_9 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= sn) |] 
  &&  [| (0 <= ((c * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) )) |] 
  &&  [| (((c * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ) <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (((c * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ) = (parse_digits_z ((sublist (0) ((i + 1 )) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_10 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) = 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (d = 0) |]
  &&  ((( &( "i" ) )) # Int  |-> sn)
  **  ((( &( "c" ) )) # Int  |-> cn)
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_11 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (d = 0) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= (sn + 1 )) |] 
  &&  [| ((sn + 1 ) <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) ((sn + 1 )) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_entail_wit_12 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (0 <= (lenx + 1 )) |] 
  &&  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= lenn) |] 
  &&  [| (0 <= ((d * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) )) |] 
  &&  [| (((d * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ) <= dn) |] 
  &&  [| (((d * 10 ) + ((Znth i (app (ln) ((cons (0) (nil)))) 0) - 48 ) ) = (parse_digits_z ((sublist ((sn + 1 )) ((i + 1 )) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_return_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (((ax * cn ) % ( (bx * d ) ) ) <> 0) |] 
  &&  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (problem_144_spec_z lx ln 0 ) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_return_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (((ax * cn ) % ( (bx * d ) ) ) = 0) |] 
  &&  [| (i >= lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (problem_144_spec_z lx ln 1 ) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) ,
  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (0 <= lenx) |] 
  &&  [| (lenx < INT_MAX) |] 
  &&  [| (0 <= lenn) |] 
  &&  [| (lenn < INT_MAX) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (((x_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lx) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i x_pre i 0 (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (lx) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenn + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sx) |] 
  &&  [| (0 <= a) |] 
  &&  [| (a <= ax) |] 
  &&  [| (b = 0) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (a = (parse_digits_z ((sublist (0) (i) (lx))))) |]
  &&  (((x_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lx) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i x_pre i 0 (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_4 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (b: Z) (i: Z) ,
  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= (lenn + 1 )) |] 
  &&  [| (i < lenx) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sx + 1 ) <= i) |] 
  &&  [| (i <= lenx) |] 
  &&  [| (0 <= b) |] 
  &&  [| (b <= bx) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |] 
  &&  [| (b = (parse_digits_z ((sublist ((sx + 1 )) (i) (lx))))) |]
  &&  (((x_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lx) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i x_pre i 0 (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_5 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (c: Z) (d: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (c = 0) |] 
  &&  [| (d = 0) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_6 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (((n_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (ln) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i n_pre i 0 (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_7 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (c: Z) (i: Z) ,
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
|--
  [| ((Znth i (app (ln) ((cons (0) (nil)))) 0) <> 47) |] 
  &&  [| (0 <= (lenx + 1 )) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= sn) |] 
  &&  [| (0 <= c) |] 
  &&  [| (c <= cn) |] 
  &&  [| (d = 0) |] 
  &&  [| (c = (parse_digits_z ((sublist (0) (i) (ln))))) |]
  &&  (((n_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (ln) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i n_pre i 0 (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
.

Definition simplify_partial_solve_wit_8 := 
forall (n_pre: Z) (x_pre: Z) (dn: Z) (cn: Z) (bx: Z) (ax: Z) (sn: Z) (sx: Z) (lenn: Z) (lenx: Z) (ln: (@list Z)) (lx: (@list Z)) (d: Z) (i: Z) ,
  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
  **  (CharArray.full n_pre (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
|--
  [| (0 <= (lenx + 1 )) |] 
  &&  [| (i < lenn) |] 
  &&  [| ((Zlength (lx)) = lenx) |] 
  &&  [| ((Zlength (ln)) = lenn) |] 
  &&  [| (problem_144_pre_z lx ln ) |] 
  &&  [| (ascii_range_z lx ) |] 
  &&  [| (ascii_range_z ln ) |] 
  &&  [| (fraction_parts_z lx sx ax bx ) |] 
  &&  [| (fraction_parts_z ln sn cn dn ) |] 
  &&  [| (fraction_values_safe_z ax bx cn dn ) |] 
  &&  [| (0 < sx) |] 
  &&  [| (sx < lenx) |] 
  &&  [| (0 < sn) |] 
  &&  [| (sn < lenn) |] 
  &&  [| ((sn + 1 ) <= i) |] 
  &&  [| (i <= lenn) |] 
  &&  [| (0 <= d) |] 
  &&  [| (d <= dn) |] 
  &&  [| (d = (parse_digits_z ((sublist ((sn + 1 )) (i) (ln))))) |]
  &&  (((n_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (ln) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i n_pre i 0 (lenn + 1 ) (app (ln) ((cons (0) (nil)))) )
  **  (CharArray.full x_pre (lenx + 1 ) (app (lx) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_simplify_safety_wit_1 : simplify_safety_wit_1.
Axiom proof_of_simplify_safety_wit_2 : simplify_safety_wit_2.
Axiom proof_of_simplify_safety_wit_3 : simplify_safety_wit_3.
Axiom proof_of_simplify_safety_wit_4 : simplify_safety_wit_4.
Axiom proof_of_simplify_safety_wit_5 : simplify_safety_wit_5.
Axiom proof_of_simplify_safety_wit_6 : simplify_safety_wit_6.
Axiom proof_of_simplify_safety_wit_7 : simplify_safety_wit_7.
Axiom proof_of_simplify_safety_wit_8 : simplify_safety_wit_8.
Axiom proof_of_simplify_safety_wit_9 : simplify_safety_wit_9.
Axiom proof_of_simplify_safety_wit_10 : simplify_safety_wit_10.
Axiom proof_of_simplify_safety_wit_11 : simplify_safety_wit_11.
Axiom proof_of_simplify_safety_wit_12 : simplify_safety_wit_12.
Axiom proof_of_simplify_safety_wit_13 : simplify_safety_wit_13.
Axiom proof_of_simplify_safety_wit_14 : simplify_safety_wit_14.
Axiom proof_of_simplify_safety_wit_15 : simplify_safety_wit_15.
Axiom proof_of_simplify_safety_wit_16 : simplify_safety_wit_16.
Axiom proof_of_simplify_safety_wit_17 : simplify_safety_wit_17.
Axiom proof_of_simplify_safety_wit_18 : simplify_safety_wit_18.
Axiom proof_of_simplify_safety_wit_19 : simplify_safety_wit_19.
Axiom proof_of_simplify_safety_wit_20 : simplify_safety_wit_20.
Axiom proof_of_simplify_safety_wit_21 : simplify_safety_wit_21.
Axiom proof_of_simplify_safety_wit_22 : simplify_safety_wit_22.
Axiom proof_of_simplify_safety_wit_23 : simplify_safety_wit_23.
Axiom proof_of_simplify_safety_wit_24 : simplify_safety_wit_24.
Axiom proof_of_simplify_safety_wit_25 : simplify_safety_wit_25.
Axiom proof_of_simplify_safety_wit_26 : simplify_safety_wit_26.
Axiom proof_of_simplify_safety_wit_27 : simplify_safety_wit_27.
Axiom proof_of_simplify_safety_wit_28 : simplify_safety_wit_28.
Axiom proof_of_simplify_safety_wit_29 : simplify_safety_wit_29.
Axiom proof_of_simplify_safety_wit_30 : simplify_safety_wit_30.
Axiom proof_of_simplify_safety_wit_31 : simplify_safety_wit_31.
Axiom proof_of_simplify_safety_wit_32 : simplify_safety_wit_32.
Axiom proof_of_simplify_safety_wit_33 : simplify_safety_wit_33.
Axiom proof_of_simplify_safety_wit_34 : simplify_safety_wit_34.
Axiom proof_of_simplify_safety_wit_35 : simplify_safety_wit_35.
Axiom proof_of_simplify_safety_wit_36 : simplify_safety_wit_36.
Axiom proof_of_simplify_safety_wit_37 : simplify_safety_wit_37.
Axiom proof_of_simplify_safety_wit_38 : simplify_safety_wit_38.
Axiom proof_of_simplify_safety_wit_39 : simplify_safety_wit_39.
Axiom proof_of_simplify_safety_wit_40 : simplify_safety_wit_40.
Axiom proof_of_simplify_safety_wit_41 : simplify_safety_wit_41.
Axiom proof_of_simplify_safety_wit_42 : simplify_safety_wit_42.
Axiom proof_of_simplify_entail_wit_1 : simplify_entail_wit_1.
Axiom proof_of_simplify_entail_wit_2 : simplify_entail_wit_2.
Axiom proof_of_simplify_entail_wit_3 : simplify_entail_wit_3.
Axiom proof_of_simplify_entail_wit_4 : simplify_entail_wit_4.
Axiom proof_of_simplify_entail_wit_5 : simplify_entail_wit_5.
Axiom proof_of_simplify_entail_wit_6 : simplify_entail_wit_6.
Axiom proof_of_simplify_entail_wit_7 : simplify_entail_wit_7.
Axiom proof_of_simplify_entail_wit_8 : simplify_entail_wit_8.
Axiom proof_of_simplify_entail_wit_9 : simplify_entail_wit_9.
Axiom proof_of_simplify_entail_wit_10 : simplify_entail_wit_10.
Axiom proof_of_simplify_entail_wit_11 : simplify_entail_wit_11.
Axiom proof_of_simplify_entail_wit_12 : simplify_entail_wit_12.
Axiom proof_of_simplify_return_wit_1 : simplify_return_wit_1.
Axiom proof_of_simplify_return_wit_2 : simplify_return_wit_2.
Axiom proof_of_simplify_partial_solve_wit_1 : simplify_partial_solve_wit_1.
Axiom proof_of_simplify_partial_solve_wit_2 : simplify_partial_solve_wit_2.
Axiom proof_of_simplify_partial_solve_wit_3 : simplify_partial_solve_wit_3.
Axiom proof_of_simplify_partial_solve_wit_4 : simplify_partial_solve_wit_4.
Axiom proof_of_simplify_partial_solve_wit_5 : simplify_partial_solve_wit_5.
Axiom proof_of_simplify_partial_solve_wit_6 : simplify_partial_solve_wit_6.
Axiom proof_of_simplify_partial_solve_wit_7 : simplify_partial_solve_wit_7.
Axiom proof_of_simplify_partial_solve_wit_8 : simplify_partial_solve_wit_8.

End VC_Correct.
