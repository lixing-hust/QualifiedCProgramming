Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_92.
Local Open Scope sac.

(*----- Function any_int -----*)

Definition any_int_safety_wit_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH2 : (fp32_isFinite retval )) (PreH3 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH4 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH5 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH6 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH7 : (fp32_isFinite a_pre )) (PreH8 : (fp32_isFinite b_pre )) (PreH9 : (fp32_isFinite c_pre )) (PreH10 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite retval ) ” 
  &&  “ (fp32_isFinite a_pre ) ”
.

Definition any_int_safety_wit_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_ne retval a_pre )) (PreH2 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH3 : (fp32_isFinite retval )) (PreH4 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH5 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH6 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH7 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH8 : (fp32_isFinite a_pre )) (PreH9 : (fp32_isFinite b_pre )) (PreH10 : (fp32_isFinite c_pre )) (PreH11 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_3 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval_2: fp32) (result_bits_2: Z) (retval: fp32) (PreH1 : (fp32_eq retval (fp32_of_bits (result_bits_2)))) (PreH2 : (fp32_isFinite retval )) (PreH3 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH4 : (fp32_eq retval_2 a_pre )) (PreH5 : (fp32_eq retval_2 (fp32_of_bits (result_bits)))) (PreH6 : (fp32_isFinite retval_2 )) (PreH7 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH8 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH9 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH10 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH11 : (fp32_isFinite a_pre )) (PreH12 : (fp32_isFinite b_pre )) (PreH13 : (fp32_isFinite c_pre )) (PreH14 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_b" ) )) # Float  |-> retval)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval_2)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite retval ) ” 
  &&  “ (fp32_isFinite b_pre ) ”
.

Definition any_int_safety_wit_4 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (PreH1 : (fp32_ne retval_2 b_pre )) (PreH2 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH3 : (fp32_isFinite retval_2 )) (PreH4 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH5 : (fp32_eq retval a_pre )) (PreH6 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH7 : (fp32_isFinite retval )) (PreH8 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH9 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH10 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH11 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH12 : (fp32_isFinite a_pre )) (PreH13 : (fp32_isFinite b_pre )) (PreH14 : (fp32_isFinite c_pre )) (PreH15 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_5 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval_2: fp32) (result_bits_2: Z) (retval_3: fp32) (result_bits_3: Z) (retval: fp32) (PreH1 : (fp32_eq retval (fp32_of_bits (result_bits_3)))) (PreH2 : (fp32_isFinite retval )) (PreH3 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH4 : (fp32_eq retval_3 b_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_2)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH8 : (fp32_eq retval_2 a_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH12 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH13 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH14 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH15 : (fp32_isFinite a_pre )) (PreH16 : (fp32_isFinite b_pre )) (PreH17 : (fp32_isFinite c_pre )) (PreH18 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_c" ) )) # Float  |-> retval)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval_2)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite retval ) ” 
  &&  “ (fp32_isFinite c_pre ) ”
.

Definition any_int_safety_wit_6 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_safety_wit_7 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |->_)
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (b_pre)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |->_)
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (b_pre)) ) ”
).

Definition any_int_safety_wit_7_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |->_)
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (b_pre)) ) ”
.

Definition any_int_safety_wit_8 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (b_pre)) ) ” 
  &&  “ (fp32_isFinite c_pre ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (b_pre)) ) ” 
  &&  “ (fp32_isFinite c_pre ) ”
).

Definition any_int_safety_wit_8_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (b_pre)) ) ”
.

Definition any_int_safety_wit_8_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite c_pre ) ”
.

Definition any_int_safety_wit_9 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition any_int_safety_wit_10 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |->_)
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (c_pre)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |->_)
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (c_pre)) ) ”
).

Definition any_int_safety_wit_10_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |->_)
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (c_pre)) ) ”
.

Definition any_int_safety_wit_11 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (c_pre)) ) ” 
  &&  “ (fp32_isFinite b_pre ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (c_pre)) ) ” 
  &&  “ (fp32_isFinite b_pre ) ”
).

Definition any_int_safety_wit_11_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (a_pre) (c_pre)) ) ”
.

Definition any_int_safety_wit_11_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite b_pre ) ”
.

Definition any_int_safety_wit_12 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition any_int_safety_wit_13 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |->_)
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (b_pre) (c_pre)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |->_)
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (b_pre) (c_pre)) ) ”
).

Definition any_int_safety_wit_13_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |->_)
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (b_pre) (c_pre)) ) ”
.

Definition any_int_safety_wit_14 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |-> (fp32_add (b_pre) (c_pre)))
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (b_pre) (c_pre)) ) ” 
  &&  “ (fp32_isFinite a_pre ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |-> (fp32_add (b_pre) (c_pre)))
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (b_pre) (c_pre)) ) ” 
  &&  “ (fp32_isFinite a_pre ) ”
).

Definition any_int_safety_wit_14_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |-> (fp32_add (b_pre) (c_pre)))
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add (b_pre) (c_pre)) ) ”
.

Definition any_int_safety_wit_14_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |-> (fp32_add (b_pre) (c_pre)))
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite a_pre ) ”
.

Definition any_int_safety_wit_15 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |-> (fp32_add (b_pre) (c_pre)))
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition any_int_safety_wit_16 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "sum_bc" ) )) # Float  |-> (fp32_add (b_pre) (c_pre)))
  **  ((( &( "sum_ac" ) )) # Float  |-> (fp32_add (a_pre) (c_pre)))
  **  ((( &( "sum_ab" ) )) # Float  |-> (fp32_add (a_pre) (b_pre)))
  **  ((( &( "rounded_c" ) )) # Float  |-> retval_3)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition any_int_return_wit_1 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_1_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 0 )
.

Definition any_int_return_wit_2 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition any_int_return_wit_2_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (b_pre) (c_pre)) a_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (c_pre)) b_pre )) (PreH3 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH4 : (fp32_eq retval_3 c_pre )) (PreH5 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH6 : (fp32_isFinite retval_3 )) (PreH7 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH8 : (fp32_eq retval_2 b_pre )) (PreH9 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH10 : (fp32_isFinite retval_2 )) (PreH11 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH12 : (fp32_eq retval a_pre )) (PreH13 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH14 : (fp32_isFinite retval )) (PreH15 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH16 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH17 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH18 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH19 : (fp32_isFinite a_pre )) (PreH20 : (fp32_isFinite b_pre )) (PreH21 : (fp32_isFinite c_pre )) (PreH22 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 1 )
.

Definition any_int_return_wit_3 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition any_int_return_wit_3_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (c_pre)) b_pre )) (PreH2 : (fp32_ne (fp32_add (a_pre) (b_pre)) c_pre )) (PreH3 : (fp32_eq retval_3 c_pre )) (PreH4 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH5 : (fp32_isFinite retval_3 )) (PreH6 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH7 : (fp32_eq retval_2 b_pre )) (PreH8 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH9 : (fp32_isFinite retval_2 )) (PreH10 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH11 : (fp32_eq retval a_pre )) (PreH12 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH13 : (fp32_isFinite retval )) (PreH14 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH15 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH16 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH17 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH18 : (fp32_isFinite a_pre )) (PreH19 : (fp32_isFinite b_pre )) (PreH20 : (fp32_isFinite c_pre )) (PreH21 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 1 )
.

Definition any_int_return_wit_4 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition any_int_return_wit_4_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_eq (fp32_add (a_pre) (b_pre)) c_pre )) (PreH2 : (fp32_eq retval_3 c_pre )) (PreH3 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH4 : (fp32_isFinite retval_3 )) (PreH5 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH6 : (fp32_eq retval_2 b_pre )) (PreH7 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH8 : (fp32_isFinite retval_2 )) (PreH9 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH10 : (fp32_eq retval a_pre )) (PreH11 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH12 : (fp32_isFinite retval )) (PreH13 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH14 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH15 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH16 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH17 : (fp32_isFinite a_pre )) (PreH18 : (fp32_isFinite b_pre )) (PreH19 : (fp32_isFinite c_pre )) (PreH20 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 1 )
.

Definition any_int_return_wit_5 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_5_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (result_bits_3: Z) (retval_3: fp32) (PreH1 : (fp32_ne retval_3 c_pre )) (PreH2 : (fp32_eq retval_3 (fp32_of_bits (result_bits_3)))) (PreH3 : (fp32_isFinite retval_3 )) (PreH4 : (roundf_fixed_bits_92 c_bits result_bits_3 )) (PreH5 : (fp32_eq retval_2 b_pre )) (PreH6 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH7 : (fp32_isFinite retval_2 )) (PreH8 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH9 : (fp32_eq retval a_pre )) (PreH10 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH11 : (fp32_isFinite retval )) (PreH12 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH13 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH14 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH15 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH16 : (fp32_isFinite a_pre )) (PreH17 : (fp32_isFinite b_pre )) (PreH18 : (fp32_isFinite c_pre )) (PreH19 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 0 )
.

Definition any_int_return_wit_6 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (PreH1 : (fp32_ne retval_2 b_pre )) (PreH2 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH3 : (fp32_isFinite retval_2 )) (PreH4 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH5 : (fp32_eq retval a_pre )) (PreH6 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH7 : (fp32_isFinite retval )) (PreH8 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH9 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH10 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH11 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH12 : (fp32_isFinite a_pre )) (PreH13 : (fp32_isFinite b_pre )) (PreH14 : (fp32_isFinite c_pre )) (PreH15 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (PreH1 : (fp32_ne retval_2 b_pre )) (PreH2 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH3 : (fp32_isFinite retval_2 )) (PreH4 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH5 : (fp32_eq retval a_pre )) (PreH6 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH7 : (fp32_isFinite retval )) (PreH8 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH9 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH10 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH11 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH12 : (fp32_isFinite a_pre )) (PreH13 : (fp32_isFinite b_pre )) (PreH14 : (fp32_isFinite c_pre )) (PreH15 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_6_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (PreH1 : (fp32_ne retval_2 b_pre )) (PreH2 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH3 : (fp32_isFinite retval_2 )) (PreH4 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH5 : (fp32_eq retval a_pre )) (PreH6 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH7 : (fp32_isFinite retval )) (PreH8 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH9 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH10 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH11 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH12 : (fp32_isFinite a_pre )) (PreH13 : (fp32_isFinite b_pre )) (PreH14 : (fp32_isFinite c_pre )) (PreH15 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 0 )
.

Definition any_int_return_wit_7 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_ne retval a_pre )) (PreH2 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH3 : (fp32_isFinite retval )) (PreH4 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH5 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH6 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH7 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH8 : (fp32_isFinite a_pre )) (PreH9 : (fp32_isFinite b_pre )) (PreH10 : (fp32_isFinite c_pre )) (PreH11 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_ne retval a_pre )) (PreH2 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH3 : (fp32_isFinite retval )) (PreH4 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH5 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH6 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH7 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH8 : (fp32_isFinite a_pre )) (PreH9 : (fp32_isFinite b_pre )) (PreH10 : (fp32_isFinite c_pre )) (PreH11 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_92_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition any_int_return_wit_7_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_ne retval a_pre )) (PreH2 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH3 : (fp32_isFinite retval )) (PreH4 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH5 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH6 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH7 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH8 : (fp32_isFinite a_pre )) (PreH9 : (fp32_isFinite b_pre )) (PreH10 : (fp32_isFinite c_pre )) (PreH11 : (problem_92_pre a_pre b_pre c_pre )) ,
  (problem_92_spec a_pre b_pre c_pre 0 )
.

Definition any_int_partial_solve_wit_1_pure := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (PreH1 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH2 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH3 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH4 : (fp32_isFinite a_pre )) (PreH5 : (fp32_isFinite b_pre )) (PreH6 : (fp32_isFinite c_pre )) (PreH7 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_a" ) )) # Float  |->_)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_eq a_pre (fp32_of_bits (a_bits))) ” 
  &&  “ (fp32_isFinite a_pre ) ”
.

Definition any_int_partial_solve_wit_1_aux := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (PreH1 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH2 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH3 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH4 : (fp32_isFinite a_pre )) (PreH5 : (fp32_isFinite b_pre )) (PreH6 : (fp32_isFinite c_pre )) (PreH7 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (fp32_eq a_pre (fp32_of_bits (a_bits))) ” 
  &&  “ (fp32_isFinite a_pre ) ” 
  &&  “ (fp32_eq a_pre (fp32_of_bits (a_bits))) ” 
  &&  “ (fp32_eq b_pre (fp32_of_bits (b_bits))) ” 
  &&  “ (fp32_eq c_pre (fp32_of_bits (c_bits))) ” 
  &&  “ (fp32_isFinite a_pre ) ” 
  &&  “ (fp32_isFinite b_pre ) ” 
  &&  “ (fp32_isFinite c_pre ) ” 
  &&  “ (problem_92_pre a_pre b_pre c_pre ) ”
  &&  emp
.

Definition any_int_partial_solve_wit_1 := any_int_partial_solve_wit_1_pure -> any_int_partial_solve_wit_1_aux.

Definition any_int_partial_solve_wit_2_pure := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_eq retval a_pre )) (PreH2 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH3 : (fp32_isFinite retval )) (PreH4 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH5 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH6 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH7 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH8 : (fp32_isFinite a_pre )) (PreH9 : (fp32_isFinite b_pre )) (PreH10 : (fp32_isFinite c_pre )) (PreH11 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_b" ) )) # Float  |->_)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_eq b_pre (fp32_of_bits (b_bits))) ” 
  &&  “ (fp32_isFinite b_pre ) ”
.

Definition any_int_partial_solve_wit_2_aux := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (PreH1 : (fp32_eq retval a_pre )) (PreH2 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH3 : (fp32_isFinite retval )) (PreH4 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH5 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH6 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH7 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH8 : (fp32_isFinite a_pre )) (PreH9 : (fp32_isFinite b_pre )) (PreH10 : (fp32_isFinite c_pre )) (PreH11 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (fp32_eq b_pre (fp32_of_bits (b_bits))) ” 
  &&  “ (fp32_isFinite b_pre ) ” 
  &&  “ (fp32_eq retval a_pre ) ” 
  &&  “ (fp32_eq retval (fp32_of_bits (result_bits))) ” 
  &&  “ (fp32_isFinite retval ) ” 
  &&  “ (roundf_fixed_bits_92 a_bits result_bits ) ” 
  &&  “ (fp32_eq a_pre (fp32_of_bits (a_bits))) ” 
  &&  “ (fp32_eq b_pre (fp32_of_bits (b_bits))) ” 
  &&  “ (fp32_eq c_pre (fp32_of_bits (c_bits))) ” 
  &&  “ (fp32_isFinite a_pre ) ” 
  &&  “ (fp32_isFinite b_pre ) ” 
  &&  “ (fp32_isFinite c_pre ) ” 
  &&  “ (problem_92_pre a_pre b_pre c_pre ) ”
  &&  emp
.

Definition any_int_partial_solve_wit_2 := any_int_partial_solve_wit_2_pure -> any_int_partial_solve_wit_2_aux.

Definition any_int_partial_solve_wit_3_pure := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (PreH1 : (fp32_eq retval_2 b_pre )) (PreH2 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH3 : (fp32_isFinite retval_2 )) (PreH4 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH5 : (fp32_eq retval a_pre )) (PreH6 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH7 : (fp32_isFinite retval )) (PreH8 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH9 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH10 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH11 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH12 : (fp32_isFinite a_pre )) (PreH13 : (fp32_isFinite b_pre )) (PreH14 : (fp32_isFinite c_pre )) (PreH15 : (problem_92_pre a_pre b_pre c_pre )) ,
  ((( &( "rounded_c" ) )) # Float  |->_)
  **  ((( &( "rounded_b" ) )) # Float  |-> retval_2)
  **  ((( &( "rounded_a" ) )) # Float  |-> retval)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_eq c_pre (fp32_of_bits (c_bits))) ” 
  &&  “ (fp32_isFinite c_pre ) ”
.

Definition any_int_partial_solve_wit_3_aux := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (c_bits: Z) (b_bits: Z) (a_bits: Z) (result_bits: Z) (retval: fp32) (result_bits_2: Z) (retval_2: fp32) (PreH1 : (fp32_eq retval_2 b_pre )) (PreH2 : (fp32_eq retval_2 (fp32_of_bits (result_bits_2)))) (PreH3 : (fp32_isFinite retval_2 )) (PreH4 : (roundf_fixed_bits_92 b_bits result_bits_2 )) (PreH5 : (fp32_eq retval a_pre )) (PreH6 : (fp32_eq retval (fp32_of_bits (result_bits)))) (PreH7 : (fp32_isFinite retval )) (PreH8 : (roundf_fixed_bits_92 a_bits result_bits )) (PreH9 : (fp32_eq a_pre (fp32_of_bits (a_bits)))) (PreH10 : (fp32_eq b_pre (fp32_of_bits (b_bits)))) (PreH11 : (fp32_eq c_pre (fp32_of_bits (c_bits)))) (PreH12 : (fp32_isFinite a_pre )) (PreH13 : (fp32_isFinite b_pre )) (PreH14 : (fp32_isFinite c_pre )) (PreH15 : (problem_92_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (fp32_eq c_pre (fp32_of_bits (c_bits))) ” 
  &&  “ (fp32_isFinite c_pre ) ” 
  &&  “ (fp32_eq retval_2 b_pre ) ” 
  &&  “ (fp32_eq retval_2 (fp32_of_bits (result_bits_2))) ” 
  &&  “ (fp32_isFinite retval_2 ) ” 
  &&  “ (roundf_fixed_bits_92 b_bits result_bits_2 ) ” 
  &&  “ (fp32_eq retval a_pre ) ” 
  &&  “ (fp32_eq retval (fp32_of_bits (result_bits))) ” 
  &&  “ (fp32_isFinite retval ) ” 
  &&  “ (roundf_fixed_bits_92 a_bits result_bits ) ” 
  &&  “ (fp32_eq a_pre (fp32_of_bits (a_bits))) ” 
  &&  “ (fp32_eq b_pre (fp32_of_bits (b_bits))) ” 
  &&  “ (fp32_eq c_pre (fp32_of_bits (c_bits))) ” 
  &&  “ (fp32_isFinite a_pre ) ” 
  &&  “ (fp32_isFinite b_pre ) ” 
  &&  “ (fp32_isFinite c_pre ) ” 
  &&  “ (problem_92_pre a_pre b_pre c_pre ) ”
  &&  emp
.

Definition any_int_partial_solve_wit_3 := any_int_partial_solve_wit_3_pure -> any_int_partial_solve_wit_3_aux.

Module Type VC_Correct.


Axiom proof_of_any_int_safety_wit_1 : any_int_safety_wit_1.
Axiom proof_of_any_int_safety_wit_2 : any_int_safety_wit_2.
Axiom proof_of_any_int_safety_wit_3 : any_int_safety_wit_3.
Axiom proof_of_any_int_safety_wit_4 : any_int_safety_wit_4.
Axiom proof_of_any_int_safety_wit_5 : any_int_safety_wit_5.
Axiom proof_of_any_int_safety_wit_6 : any_int_safety_wit_6.
Axiom proof_of_any_int_safety_wit_7 : any_int_safety_wit_7.
Axiom proof_of_any_int_safety_wit_8 : any_int_safety_wit_8.
Axiom proof_of_any_int_safety_wit_9 : any_int_safety_wit_9.
Axiom proof_of_any_int_safety_wit_10 : any_int_safety_wit_10.
Axiom proof_of_any_int_safety_wit_11 : any_int_safety_wit_11.
Axiom proof_of_any_int_safety_wit_12 : any_int_safety_wit_12.
Axiom proof_of_any_int_safety_wit_13 : any_int_safety_wit_13.
Axiom proof_of_any_int_safety_wit_14 : any_int_safety_wit_14.
Axiom proof_of_any_int_safety_wit_15 : any_int_safety_wit_15.
Axiom proof_of_any_int_safety_wit_16 : any_int_safety_wit_16.
Axiom proof_of_any_int_return_wit_1 : any_int_return_wit_1.
Axiom proof_of_any_int_return_wit_2 : any_int_return_wit_2.
Axiom proof_of_any_int_return_wit_3 : any_int_return_wit_3.
Axiom proof_of_any_int_return_wit_4 : any_int_return_wit_4.
Axiom proof_of_any_int_return_wit_5 : any_int_return_wit_5.
Axiom proof_of_any_int_return_wit_6 : any_int_return_wit_6.
Axiom proof_of_any_int_return_wit_7 : any_int_return_wit_7.
Axiom proof_of_any_int_partial_solve_wit_1_pure : any_int_partial_solve_wit_1_pure.
Axiom proof_of_any_int_partial_solve_wit_1 : any_int_partial_solve_wit_1.
Axiom proof_of_any_int_partial_solve_wit_2_pure : any_int_partial_solve_wit_2_pure.
Axiom proof_of_any_int_partial_solve_wit_2 : any_int_partial_solve_wit_2.
Axiom proof_of_any_int_partial_solve_wit_3_pure : any_int_partial_solve_wit_3_pure.
Axiom proof_of_any_int_partial_solve_wit_3 : any_int_partial_solve_wit_3.

End VC_Correct.
