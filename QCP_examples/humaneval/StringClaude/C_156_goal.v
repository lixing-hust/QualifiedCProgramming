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
Require Import coins_156.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function append_roman_digit -----*)

Definition append_roman_digit_safety_wit_1 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition append_roman_digit_safety_wit_2 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_3 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_4 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_5 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_6 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_7 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_8 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_9 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_10 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition append_roman_digit_safety_wit_11 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_12 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_13 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_14 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_15 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 3 )) |]
.

Definition append_roman_digit_safety_wit_16 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition append_roman_digit_safety_wit_17 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition append_roman_digit_safety_wit_18 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_19 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_20 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_21 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_22 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (5 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 5) |]
.

Definition append_roman_digit_safety_wit_23 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_24 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_25 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (6 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 6) |]
.

Definition append_roman_digit_safety_wit_26 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_27 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_28 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_29 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_30 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition append_roman_digit_safety_wit_31 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_32 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_33 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_34 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_35 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 3 )) |]
.

Definition append_roman_digit_safety_wit_36 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition append_roman_digit_safety_wit_37 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition append_roman_digit_safety_wit_38 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_39 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_40 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_41 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_safety_wit_42 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 3 )) |]
.

Definition append_roman_digit_safety_wit_43 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition append_roman_digit_safety_wit_44 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (((pos_pre + 1 ) + 1 ) + 1 )) |] 
  &&  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((((pos_pre + 1 ) + 1 ) + 1 ) + 1 ) (app ((app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 3 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 4 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 4 )) |]
.

Definition append_roman_digit_safety_wit_45 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (((pos_pre + 1 ) + 1 ) + 1 )) |] 
  &&  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((((pos_pre + 1 ) + 1 ) + 1 ) + 1 ) (app ((app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 3 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (4 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4) |]
.

Definition append_roman_digit_safety_wit_46 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 1 )) |]
.

Definition append_roman_digit_safety_wit_47 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition append_roman_digit_safety_wit_48 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (ten_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| ((pos_pre + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (pos_pre + 2 )) |]
.

Definition append_roman_digit_safety_wit_49 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (ten_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
  **  ((( &( "digit" ) )) # Int  |-> digit_pre)
  **  ((( &( "five" ) )) # Int  |-> five_pre)
  **  ((( &( "ten" ) )) # Int  |-> ten_pre)
  **  ((( &( "one" ) )) # Int  |-> one_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition append_roman_digit_return_wit_1 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (ten_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 2 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 2 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 2 ) cap )
.

Definition append_roman_digit_return_wit_2 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (((pos_pre + 1 ) + 1 ) + 1 )) |] 
  &&  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((((pos_pre + 1 ) + 1 ) + 1 ) + 1 ) (app ((app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 3 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 4 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 4 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 4 ) cap )
.

Definition append_roman_digit_return_wit_3 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 3 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 3 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 3 ) cap )
.

Definition append_roman_digit_return_wit_4 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 2 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 2 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 2 ) cap )
.

Definition append_roman_digit_return_wit_5 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 1 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
.

Definition append_roman_digit_return_wit_6 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 2 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 2 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 2 ) cap )
.

Definition append_roman_digit_return_wit_7 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 3 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 3 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 3 ) cap )
.

Definition append_roman_digit_return_wit_8 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 2 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 2 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 2 ) cap )
.

Definition append_roman_digit_return_wit_9 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| ((pos_pre + 1 ) = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
.

Definition append_roman_digit_return_wit_10 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  EX (chunk: (@list Z)) ,
  [| (roman_digit_z one_pre ten_pre five_pre digit_pre chunk ) |] 
  &&  [| (pos_pre = (pos_pre + (Zlength (chunk)) )) |]
  &&  (CharArray.full out_pre pos_pre (app (prefix) (chunk)) )
  **  (CharArray.undef_seg out_pre pos_pre cap )
.

Definition append_roman_digit_partial_solve_wit_1 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_2 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_3 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_4 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_5 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_6 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 2 ) ((pos_pre + 1 ) + 1 ) cap )
  **  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_7 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_8 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_9 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_10 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_11 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_12 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_13 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_14 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 2 ) ((pos_pre + 1 ) + 1 ) cap )
  **  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_15 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_16 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (five_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_17 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 1 ) + 1 ) cap )
|--
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 2 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 2 ) ((pos_pre + 1 ) + 1 ) cap )
  **  (CharArray.full out_pre ((pos_pre + 1 ) + 1 ) (app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_18 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre ((pos_pre + 2 ) + 1 ) cap )
|--
  [| (0 <= (((pos_pre + 1 ) + 1 ) + 1 )) |] 
  &&  [| (0 <= ((pos_pre + 1 ) + 1 )) |] 
  &&  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre = 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 3 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 3 ) ((pos_pre + 2 ) + 1 ) cap )
  **  (CharArray.full out_pre (((pos_pre + 1 ) + 1 ) + 1 ) (app ((app ((app (prefix) ((cons (five_pre) (nil))))) ((cons (one_pre) (nil))))) ((cons (one_pre) (nil)))) )
.

Definition append_roman_digit_partial_solve_wit_19 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre pos_pre prefix )
  **  (CharArray.undef_seg out_pre pos_pre cap )
|--
  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + (pos_pre * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre pos_pre pos_pre cap )
  **  (CharArray.full out_pre pos_pre prefix )
.

Definition append_roman_digit_partial_solve_wit_20 := 
forall (digit_pre: Z) (five_pre: Z) (ten_pre: Z) (one_pre: Z) (pos_pre: Z) (out_pre: Z) (cap: Z) (prefix: (@list Z)) ,
  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
  **  (CharArray.undef_seg out_pre (pos_pre + 1 ) cap )
|--
  [| (0 <= (pos_pre + 1 )) |] 
  &&  [| (digit_pre <> 8) |] 
  &&  [| (digit_pre <> 7) |] 
  &&  [| (digit_pre <> 6) |] 
  &&  [| (digit_pre <> 5) |] 
  &&  [| (digit_pre <> 4) |] 
  &&  [| (digit_pre <> 3) |] 
  &&  [| (digit_pre <> 2) |] 
  &&  [| (digit_pre <> 1) |] 
  &&  [| (digit_pre <> 0) |] 
  &&  [| (0 <= pos_pre) |] 
  &&  [| ((pos_pre + 4 ) < cap) |] 
  &&  [| (cap <= INT_MAX) |] 
  &&  [| (0 <= digit_pre) |] 
  &&  [| (digit_pre <= 9) |] 
  &&  [| (0 <= one_pre) |] 
  &&  [| (one_pre <= 127) |] 
  &&  [| (0 <= ten_pre) |] 
  &&  [| (ten_pre <= 127) |] 
  &&  [| (0 <= five_pre) |] 
  &&  [| (five_pre <= 127) |] 
  &&  [| ((Zlength (prefix)) = pos_pre) |]
  &&  (((out_pre + ((pos_pre + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out_pre (pos_pre + 1 ) (pos_pre + 1 ) cap )
  **  (CharArray.full out_pre (pos_pre + 1 ) (app (prefix) ((cons (one_pre) (nil)))) )
.

(*----- Function int_to_mini_romank -----*)

Definition int_to_mini_romank_safety_wit_1 := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition int_to_mini_romank_safety_wit_2 := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  ((( &( "h" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition int_to_mini_romank_safety_wit_3 := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition int_to_mini_romank_safety_wit_4 := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  ((( &( "o" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition int_to_mini_romank_safety_wit_5 := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "o" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (64 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 64) |]
.

Definition int_to_mini_romank_safety_wit_6 := 
forall (number_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_full retval 64 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "o" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (1000 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1000) |]
.

Definition int_to_mini_romank_safety_wit_7 := 
forall (number_pre: Z) (retval: Z) ,
  [| (number_pre = 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_full retval 64 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "o" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition int_to_mini_romank_safety_wit_8 := 
forall (number_pre: Z) (retval: Z) ,
  [| (number_pre = 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_full retval 64 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "o" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (109 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 109) |]
.

Definition int_to_mini_romank_safety_wit_9 := 
forall (number_pre: Z) (retval: Z) ,
  [| (number_pre = 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 64 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 109)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "o" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition int_to_mini_romank_safety_wit_10 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (((number ÷ 100 ) <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition int_to_mini_romank_safety_wit_11 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| ((number <> (INT_MIN)) \/ (100 <> (-1))) |] 
  &&  [| (100 <> 0) |]
.

Definition int_to_mini_romank_safety_wit_12 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition int_to_mini_romank_safety_wit_13 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition int_to_mini_romank_safety_wit_14 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> ((number ÷ 100 ) % ( 10 ) ))
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (99 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 99) |]
.

Definition int_to_mini_romank_safety_wit_15 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> ((number ÷ 100 ) % ( 10 ) ))
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (109 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 109) |]
.

Definition int_to_mini_romank_safety_wit_16 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> ((number ÷ 100 ) % ( 10 ) ))
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (100 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 100) |]
.

Definition int_to_mini_romank_safety_wit_17 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (((number ÷ 10 ) <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition int_to_mini_romank_safety_wit_18 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| ((number <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition int_to_mini_romank_safety_wit_19 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition int_to_mini_romank_safety_wit_20 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition int_to_mini_romank_safety_wit_21 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> ((number ÷ 10 ) % ( 10 ) ))
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (120 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 120) |]
.

Definition int_to_mini_romank_safety_wit_22 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> ((number ÷ 10 ) % ( 10 ) ))
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (99 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 99) |]
.

Definition int_to_mini_romank_safety_wit_23 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> ((number ÷ 10 ) % ( 10 ) ))
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (108 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 108) |]
.

Definition int_to_mini_romank_safety_wit_24 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| ((number <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition int_to_mini_romank_safety_wit_25 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition int_to_mini_romank_safety_wit_26 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> (number % ( 10 ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (105 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 105) |]
.

Definition int_to_mini_romank_safety_wit_27 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> (number % ( 10 ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (120 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 120) |]
.

Definition int_to_mini_romank_safety_wit_28 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> (number % ( 10 ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (118 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 118) |]
.

Definition int_to_mini_romank_safety_wit_29 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = (number % ( 10 ) )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < 64) |] 
  &&  [| ((Zlength ((roman_output_list_z (number_pre)))) = k) |] 
  &&  [| (roman_output_z number_pre (roman_output_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_output_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition int_to_mini_romank_entail_wit_1_1 := 
forall (number_pre: Z) (retval: Z) ,
  [| (number_pre = 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_seg retval (0 + 1 ) 64 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 109)
|--
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number_pre = number_pre) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = 1) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  (CharArray.full retval 1 (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg retval 1 64 )
.

Definition int_to_mini_romank_entail_wit_1_2 := 
forall (number_pre: Z) (retval: Z) ,
  [| (number_pre <> 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_full retval 64 )
|--
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number_pre = number_pre) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| (0 = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = 0) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  (CharArray.full retval 0 (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg retval 0 64 )
.

Definition int_to_mini_romank_entail_wit_2 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) (chunk: (@list Z)) (retval: Z) ,
  [| (roman_digit_z 99 109 100 ((number ÷ 100 ) % ( 10 ) ) chunk ) |] 
  &&  [| (retval = (k + (Zlength (chunk)) )) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  (CharArray.full out retval (app ((roman_thousand_list_z (number_pre))) (chunk)) )
  **  (CharArray.undef_seg out retval 64 )
|--
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (((number ÷ 100 ) % ( 10 ) ) = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = retval) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  (CharArray.full out retval (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out retval 64 )
.

Definition int_to_mini_romank_entail_wit_3 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) (chunk: (@list Z)) (retval: Z) ,
  [| (roman_digit_z 120 99 108 ((number ÷ 10 ) % ( 10 ) ) chunk ) |] 
  &&  [| (retval = (k + (Zlength (chunk)) )) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  (CharArray.full out retval (app ((roman_prefix1_list_z (number_pre))) (chunk)) )
  **  (CharArray.undef_seg out retval 64 )
|--
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (((number ÷ 10 ) % ( 10 ) ) = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = retval) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  (CharArray.full out retval (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out retval 64 )
.

Definition int_to_mini_romank_entail_wit_4 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) (chunk: (@list Z)) (retval: Z) ,
  [| (roman_digit_z 105 120 118 (number % ( 10 ) ) chunk ) |] 
  &&  [| (retval = (k + (Zlength (chunk)) )) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  (CharArray.full out retval (app ((roman_prefix2_list_z (number_pre))) (chunk)) )
  **  (CharArray.undef_seg out retval 64 )
|--
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| ((number % ( 10 ) ) = (number % ( 10 ) )) |] 
  &&  [| (0 <= retval) |] 
  &&  [| (retval < 64) |] 
  &&  [| ((Zlength ((roman_output_list_z (number_pre)))) = retval) |] 
  &&  [| (roman_output_z number_pre (roman_output_list_z (number_pre)) ) |]
  &&  (CharArray.full out retval (roman_output_list_z (number_pre)) )
  **  (CharArray.undef_seg out retval 64 )
.

Definition int_to_mini_romank_return_wit_1 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = (number % ( 10 ) )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < 64) |] 
  &&  [| ((Zlength ((roman_output_list_z (number_pre)))) = k) |] 
  &&  [| (roman_output_z number_pre (roman_output_list_z (number_pre)) ) |]
  &&  (CharArray.full out (k + 1 ) (app ((roman_output_list_z (number_pre))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) 64 )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  [| (0 <= len) |] 
  &&  [| (len < 64) |] 
  &&  [| ((Zlength (out_l)) = len) |] 
  &&  [| (problem_156_spec_z number_pre out_l ) |]
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) 64 )
.

Definition int_to_mini_romank_partial_solve_wit_1_pure := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "o" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "h" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (64 > 0) |]
.

Definition int_to_mini_romank_partial_solve_wit_1_aux := 
forall (number_pre: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  emp
|--
  [| (64 > 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  emp
.

Definition int_to_mini_romank_partial_solve_wit_1 := int_to_mini_romank_partial_solve_wit_1_pure -> int_to_mini_romank_partial_solve_wit_1_aux.

Definition int_to_mini_romank_partial_solve_wit_2 := 
forall (number_pre: Z) (retval: Z) ,
  [| (number_pre = 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (CharArray.undef_full retval 64 )
|--
  [| (number_pre = 1000) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (problem_156_pre_z number_pre ) |]
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 64 )
.

Definition int_to_mini_romank_partial_solve_wit_3_pure := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> ((number ÷ 100 ) % ( 10 ) ))
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (64 <= INT_MAX) |] 
  &&  [| (0 <= 99) |] 
  &&  [| (99 <= 127) |] 
  &&  [| (0 <= 109) |] 
  &&  [| (109 <= 127) |] 
  &&  [| (0 <= 100) |] 
  &&  [| (100 <= 127) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (((number ÷ 100 ) % ( 10 ) ) <= 9) |] 
  &&  [| (0 <= ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| ((k + 4 ) < 64) |] 
  &&  [| (0 <= k) |]
.

Definition int_to_mini_romank_partial_solve_wit_3_aux := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (64 <= INT_MAX) |] 
  &&  [| (0 <= 99) |] 
  &&  [| (99 <= 127) |] 
  &&  [| (0 <= 109) |] 
  &&  [| (109 <= 127) |] 
  &&  [| (0 <= 100) |] 
  &&  [| (100 <= 127) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (((number ÷ 100 ) % ( 10 ) ) <= 9) |] 
  &&  [| (0 <= ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| ((k + 4 ) < 64) |] 
  &&  [| (0 <= k) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = 0) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_thousand_list_z (number_pre)))) = k) |] 
  &&  [| (roman_thousand_z number_pre (roman_thousand_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_thousand_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
.

Definition int_to_mini_romank_partial_solve_wit_3 := int_to_mini_romank_partial_solve_wit_3_pure -> int_to_mini_romank_partial_solve_wit_3_aux.

Definition int_to_mini_romank_partial_solve_wit_4_pure := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> ((number ÷ 10 ) % ( 10 ) ))
  **  ((( &( "o" ) )) # Int  |-> o)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (64 <= INT_MAX) |] 
  &&  [| (0 <= 120) |] 
  &&  [| (120 <= 127) |] 
  &&  [| (0 <= 99) |] 
  &&  [| (99 <= 127) |] 
  &&  [| (0 <= 108) |] 
  &&  [| (108 <= 127) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (((number ÷ 10 ) % ( 10 ) ) <= 9) |] 
  &&  [| (0 <= ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| ((k + 4 ) < 64) |] 
  &&  [| (0 <= k) |]
.

Definition int_to_mini_romank_partial_solve_wit_4_aux := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (64 <= INT_MAX) |] 
  &&  [| (0 <= 120) |] 
  &&  [| (120 <= 127) |] 
  &&  [| (0 <= 99) |] 
  &&  [| (99 <= 127) |] 
  &&  [| (0 <= 108) |] 
  &&  [| (108 <= 127) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (((number ÷ 10 ) % ( 10 ) ) <= 9) |] 
  &&  [| (0 <= ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| ((k + 4 ) < 64) |] 
  &&  [| (0 <= k) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = 0) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix1_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix1_z number_pre (roman_prefix1_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_prefix1_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
.

Definition int_to_mini_romank_partial_solve_wit_4 := int_to_mini_romank_partial_solve_wit_4_pure -> int_to_mini_romank_partial_solve_wit_4_aux.

Definition int_to_mini_romank_partial_solve_wit_5_pure := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  ((( &( "original" ) )) # Int  |-> number_pre)
  **  ((( &( "number" ) )) # Int  |-> number)
  **  ((( &( "h" ) )) # Int  |-> h)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "o" ) )) # Int  |-> (number % ( 10 ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (64 <= INT_MAX) |] 
  &&  [| (0 <= 105) |] 
  &&  [| (105 <= 127) |] 
  &&  [| (0 <= 120) |] 
  &&  [| (120 <= 127) |] 
  &&  [| (0 <= 118) |] 
  &&  [| (118 <= 127) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| ((number % ( 10 ) ) <= 9) |] 
  &&  [| (0 <= (number % ( 10 ) )) |] 
  &&  [| ((k + 4 ) < 64) |] 
  &&  [| (0 <= k) |]
.

Definition int_to_mini_romank_partial_solve_wit_5_aux := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (64 <= INT_MAX) |] 
  &&  [| (0 <= 105) |] 
  &&  [| (105 <= 127) |] 
  &&  [| (0 <= 120) |] 
  &&  [| (120 <= 127) |] 
  &&  [| (0 <= 118) |] 
  &&  [| (118 <= 127) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| ((number % ( 10 ) ) <= 9) |] 
  &&  [| (0 <= (number % ( 10 ) )) |] 
  &&  [| ((k + 4 ) < 64) |] 
  &&  [| (0 <= k) |] 
  &&  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = 0) |] 
  &&  [| ((Zlength ((roman_prefix2_list_z (number_pre)))) = k) |] 
  &&  [| (roman_prefix2_z number_pre (roman_prefix2_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_prefix2_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
.

Definition int_to_mini_romank_partial_solve_wit_5 := int_to_mini_romank_partial_solve_wit_5_pure -> int_to_mini_romank_partial_solve_wit_5_aux.

Definition int_to_mini_romank_partial_solve_wit_6 := 
forall (number_pre: Z) (number: Z) (h: Z) (t: Z) (o: Z) (k: Z) (out: Z) ,
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = (number % ( 10 ) )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < 64) |] 
  &&  [| ((Zlength ((roman_output_list_z (number_pre)))) = k) |] 
  &&  [| (roman_output_z number_pre (roman_output_list_z (number_pre)) ) |]
  &&  (CharArray.full out k (roman_output_list_z (number_pre)) )
  **  (CharArray.undef_seg out k 64 )
|--
  [| (1 <= number_pre) |] 
  &&  [| (number_pre <= 1000) |] 
  &&  [| (number = number_pre) |] 
  &&  [| (h = ((number ÷ 100 ) % ( 10 ) )) |] 
  &&  [| (t = ((number ÷ 10 ) % ( 10 ) )) |] 
  &&  [| (o = (number % ( 10 ) )) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < 64) |] 
  &&  [| ((Zlength ((roman_output_list_z (number_pre)))) = k) |] 
  &&  [| (roman_output_z number_pre (roman_output_list_z (number_pre)) ) |]
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k 64 )
  **  (CharArray.full out k (roman_output_list_z (number_pre)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_append_roman_digit_safety_wit_1 : append_roman_digit_safety_wit_1.
Axiom proof_of_append_roman_digit_safety_wit_2 : append_roman_digit_safety_wit_2.
Axiom proof_of_append_roman_digit_safety_wit_3 : append_roman_digit_safety_wit_3.
Axiom proof_of_append_roman_digit_safety_wit_4 : append_roman_digit_safety_wit_4.
Axiom proof_of_append_roman_digit_safety_wit_5 : append_roman_digit_safety_wit_5.
Axiom proof_of_append_roman_digit_safety_wit_6 : append_roman_digit_safety_wit_6.
Axiom proof_of_append_roman_digit_safety_wit_7 : append_roman_digit_safety_wit_7.
Axiom proof_of_append_roman_digit_safety_wit_8 : append_roman_digit_safety_wit_8.
Axiom proof_of_append_roman_digit_safety_wit_9 : append_roman_digit_safety_wit_9.
Axiom proof_of_append_roman_digit_safety_wit_10 : append_roman_digit_safety_wit_10.
Axiom proof_of_append_roman_digit_safety_wit_11 : append_roman_digit_safety_wit_11.
Axiom proof_of_append_roman_digit_safety_wit_12 : append_roman_digit_safety_wit_12.
Axiom proof_of_append_roman_digit_safety_wit_13 : append_roman_digit_safety_wit_13.
Axiom proof_of_append_roman_digit_safety_wit_14 : append_roman_digit_safety_wit_14.
Axiom proof_of_append_roman_digit_safety_wit_15 : append_roman_digit_safety_wit_15.
Axiom proof_of_append_roman_digit_safety_wit_16 : append_roman_digit_safety_wit_16.
Axiom proof_of_append_roman_digit_safety_wit_17 : append_roman_digit_safety_wit_17.
Axiom proof_of_append_roman_digit_safety_wit_18 : append_roman_digit_safety_wit_18.
Axiom proof_of_append_roman_digit_safety_wit_19 : append_roman_digit_safety_wit_19.
Axiom proof_of_append_roman_digit_safety_wit_20 : append_roman_digit_safety_wit_20.
Axiom proof_of_append_roman_digit_safety_wit_21 : append_roman_digit_safety_wit_21.
Axiom proof_of_append_roman_digit_safety_wit_22 : append_roman_digit_safety_wit_22.
Axiom proof_of_append_roman_digit_safety_wit_23 : append_roman_digit_safety_wit_23.
Axiom proof_of_append_roman_digit_safety_wit_24 : append_roman_digit_safety_wit_24.
Axiom proof_of_append_roman_digit_safety_wit_25 : append_roman_digit_safety_wit_25.
Axiom proof_of_append_roman_digit_safety_wit_26 : append_roman_digit_safety_wit_26.
Axiom proof_of_append_roman_digit_safety_wit_27 : append_roman_digit_safety_wit_27.
Axiom proof_of_append_roman_digit_safety_wit_28 : append_roman_digit_safety_wit_28.
Axiom proof_of_append_roman_digit_safety_wit_29 : append_roman_digit_safety_wit_29.
Axiom proof_of_append_roman_digit_safety_wit_30 : append_roman_digit_safety_wit_30.
Axiom proof_of_append_roman_digit_safety_wit_31 : append_roman_digit_safety_wit_31.
Axiom proof_of_append_roman_digit_safety_wit_32 : append_roman_digit_safety_wit_32.
Axiom proof_of_append_roman_digit_safety_wit_33 : append_roman_digit_safety_wit_33.
Axiom proof_of_append_roman_digit_safety_wit_34 : append_roman_digit_safety_wit_34.
Axiom proof_of_append_roman_digit_safety_wit_35 : append_roman_digit_safety_wit_35.
Axiom proof_of_append_roman_digit_safety_wit_36 : append_roman_digit_safety_wit_36.
Axiom proof_of_append_roman_digit_safety_wit_37 : append_roman_digit_safety_wit_37.
Axiom proof_of_append_roman_digit_safety_wit_38 : append_roman_digit_safety_wit_38.
Axiom proof_of_append_roman_digit_safety_wit_39 : append_roman_digit_safety_wit_39.
Axiom proof_of_append_roman_digit_safety_wit_40 : append_roman_digit_safety_wit_40.
Axiom proof_of_append_roman_digit_safety_wit_41 : append_roman_digit_safety_wit_41.
Axiom proof_of_append_roman_digit_safety_wit_42 : append_roman_digit_safety_wit_42.
Axiom proof_of_append_roman_digit_safety_wit_43 : append_roman_digit_safety_wit_43.
Axiom proof_of_append_roman_digit_safety_wit_44 : append_roman_digit_safety_wit_44.
Axiom proof_of_append_roman_digit_safety_wit_45 : append_roman_digit_safety_wit_45.
Axiom proof_of_append_roman_digit_safety_wit_46 : append_roman_digit_safety_wit_46.
Axiom proof_of_append_roman_digit_safety_wit_47 : append_roman_digit_safety_wit_47.
Axiom proof_of_append_roman_digit_safety_wit_48 : append_roman_digit_safety_wit_48.
Axiom proof_of_append_roman_digit_safety_wit_49 : append_roman_digit_safety_wit_49.
Axiom proof_of_append_roman_digit_return_wit_1 : append_roman_digit_return_wit_1.
Axiom proof_of_append_roman_digit_return_wit_2 : append_roman_digit_return_wit_2.
Axiom proof_of_append_roman_digit_return_wit_3 : append_roman_digit_return_wit_3.
Axiom proof_of_append_roman_digit_return_wit_4 : append_roman_digit_return_wit_4.
Axiom proof_of_append_roman_digit_return_wit_5 : append_roman_digit_return_wit_5.
Axiom proof_of_append_roman_digit_return_wit_6 : append_roman_digit_return_wit_6.
Axiom proof_of_append_roman_digit_return_wit_7 : append_roman_digit_return_wit_7.
Axiom proof_of_append_roman_digit_return_wit_8 : append_roman_digit_return_wit_8.
Axiom proof_of_append_roman_digit_return_wit_9 : append_roman_digit_return_wit_9.
Axiom proof_of_append_roman_digit_return_wit_10 : append_roman_digit_return_wit_10.
Axiom proof_of_append_roman_digit_partial_solve_wit_1 : append_roman_digit_partial_solve_wit_1.
Axiom proof_of_append_roman_digit_partial_solve_wit_2 : append_roman_digit_partial_solve_wit_2.
Axiom proof_of_append_roman_digit_partial_solve_wit_3 : append_roman_digit_partial_solve_wit_3.
Axiom proof_of_append_roman_digit_partial_solve_wit_4 : append_roman_digit_partial_solve_wit_4.
Axiom proof_of_append_roman_digit_partial_solve_wit_5 : append_roman_digit_partial_solve_wit_5.
Axiom proof_of_append_roman_digit_partial_solve_wit_6 : append_roman_digit_partial_solve_wit_6.
Axiom proof_of_append_roman_digit_partial_solve_wit_7 : append_roman_digit_partial_solve_wit_7.
Axiom proof_of_append_roman_digit_partial_solve_wit_8 : append_roman_digit_partial_solve_wit_8.
Axiom proof_of_append_roman_digit_partial_solve_wit_9 : append_roman_digit_partial_solve_wit_9.
Axiom proof_of_append_roman_digit_partial_solve_wit_10 : append_roman_digit_partial_solve_wit_10.
Axiom proof_of_append_roman_digit_partial_solve_wit_11 : append_roman_digit_partial_solve_wit_11.
Axiom proof_of_append_roman_digit_partial_solve_wit_12 : append_roman_digit_partial_solve_wit_12.
Axiom proof_of_append_roman_digit_partial_solve_wit_13 : append_roman_digit_partial_solve_wit_13.
Axiom proof_of_append_roman_digit_partial_solve_wit_14 : append_roman_digit_partial_solve_wit_14.
Axiom proof_of_append_roman_digit_partial_solve_wit_15 : append_roman_digit_partial_solve_wit_15.
Axiom proof_of_append_roman_digit_partial_solve_wit_16 : append_roman_digit_partial_solve_wit_16.
Axiom proof_of_append_roman_digit_partial_solve_wit_17 : append_roman_digit_partial_solve_wit_17.
Axiom proof_of_append_roman_digit_partial_solve_wit_18 : append_roman_digit_partial_solve_wit_18.
Axiom proof_of_append_roman_digit_partial_solve_wit_19 : append_roman_digit_partial_solve_wit_19.
Axiom proof_of_append_roman_digit_partial_solve_wit_20 : append_roman_digit_partial_solve_wit_20.
Axiom proof_of_int_to_mini_romank_safety_wit_1 : int_to_mini_romank_safety_wit_1.
Axiom proof_of_int_to_mini_romank_safety_wit_2 : int_to_mini_romank_safety_wit_2.
Axiom proof_of_int_to_mini_romank_safety_wit_3 : int_to_mini_romank_safety_wit_3.
Axiom proof_of_int_to_mini_romank_safety_wit_4 : int_to_mini_romank_safety_wit_4.
Axiom proof_of_int_to_mini_romank_safety_wit_5 : int_to_mini_romank_safety_wit_5.
Axiom proof_of_int_to_mini_romank_safety_wit_6 : int_to_mini_romank_safety_wit_6.
Axiom proof_of_int_to_mini_romank_safety_wit_7 : int_to_mini_romank_safety_wit_7.
Axiom proof_of_int_to_mini_romank_safety_wit_8 : int_to_mini_romank_safety_wit_8.
Axiom proof_of_int_to_mini_romank_safety_wit_9 : int_to_mini_romank_safety_wit_9.
Axiom proof_of_int_to_mini_romank_safety_wit_10 : int_to_mini_romank_safety_wit_10.
Axiom proof_of_int_to_mini_romank_safety_wit_11 : int_to_mini_romank_safety_wit_11.
Axiom proof_of_int_to_mini_romank_safety_wit_12 : int_to_mini_romank_safety_wit_12.
Axiom proof_of_int_to_mini_romank_safety_wit_13 : int_to_mini_romank_safety_wit_13.
Axiom proof_of_int_to_mini_romank_safety_wit_14 : int_to_mini_romank_safety_wit_14.
Axiom proof_of_int_to_mini_romank_safety_wit_15 : int_to_mini_romank_safety_wit_15.
Axiom proof_of_int_to_mini_romank_safety_wit_16 : int_to_mini_romank_safety_wit_16.
Axiom proof_of_int_to_mini_romank_safety_wit_17 : int_to_mini_romank_safety_wit_17.
Axiom proof_of_int_to_mini_romank_safety_wit_18 : int_to_mini_romank_safety_wit_18.
Axiom proof_of_int_to_mini_romank_safety_wit_19 : int_to_mini_romank_safety_wit_19.
Axiom proof_of_int_to_mini_romank_safety_wit_20 : int_to_mini_romank_safety_wit_20.
Axiom proof_of_int_to_mini_romank_safety_wit_21 : int_to_mini_romank_safety_wit_21.
Axiom proof_of_int_to_mini_romank_safety_wit_22 : int_to_mini_romank_safety_wit_22.
Axiom proof_of_int_to_mini_romank_safety_wit_23 : int_to_mini_romank_safety_wit_23.
Axiom proof_of_int_to_mini_romank_safety_wit_24 : int_to_mini_romank_safety_wit_24.
Axiom proof_of_int_to_mini_romank_safety_wit_25 : int_to_mini_romank_safety_wit_25.
Axiom proof_of_int_to_mini_romank_safety_wit_26 : int_to_mini_romank_safety_wit_26.
Axiom proof_of_int_to_mini_romank_safety_wit_27 : int_to_mini_romank_safety_wit_27.
Axiom proof_of_int_to_mini_romank_safety_wit_28 : int_to_mini_romank_safety_wit_28.
Axiom proof_of_int_to_mini_romank_safety_wit_29 : int_to_mini_romank_safety_wit_29.
Axiom proof_of_int_to_mini_romank_entail_wit_1_1 : int_to_mini_romank_entail_wit_1_1.
Axiom proof_of_int_to_mini_romank_entail_wit_1_2 : int_to_mini_romank_entail_wit_1_2.
Axiom proof_of_int_to_mini_romank_entail_wit_2 : int_to_mini_romank_entail_wit_2.
Axiom proof_of_int_to_mini_romank_entail_wit_3 : int_to_mini_romank_entail_wit_3.
Axiom proof_of_int_to_mini_romank_entail_wit_4 : int_to_mini_romank_entail_wit_4.
Axiom proof_of_int_to_mini_romank_return_wit_1 : int_to_mini_romank_return_wit_1.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_1_pure : int_to_mini_romank_partial_solve_wit_1_pure.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_1 : int_to_mini_romank_partial_solve_wit_1.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_2 : int_to_mini_romank_partial_solve_wit_2.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_3_pure : int_to_mini_romank_partial_solve_wit_3_pure.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_3 : int_to_mini_romank_partial_solve_wit_3.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_4_pure : int_to_mini_romank_partial_solve_wit_4_pure.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_4 : int_to_mini_romank_partial_solve_wit_4.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_5_pure : int_to_mini_romank_partial_solve_wit_5_pure.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_5 : int_to_mini_romank_partial_solve_wit_5.
Axiom proof_of_int_to_mini_romank_partial_solve_wit_6 : int_to_mini_romank_partial_solve_wit_6.

End VC_Correct.
