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
Require Import coins_139.
Local Open Scope sac.

(*----- Function special_factorial -----*)

Definition special_factorial_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  ((( &( "bfact" ) )) # Int64  |->_)
  **  ((( &( "fact" ) )) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition special_factorial_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  ((( &( "fact" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition special_factorial_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "bfact" ) )) # Int64  |-> 1)
  **  ((( &( "fact" ) )) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition special_factorial_safety_wit_4 := 
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((fact * i ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (fact * i )) ”
) \/
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((fact * i ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (fact * i )) ”
).

Definition special_factorial_safety_wit_4_split_goal_1 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((fact * i ) <= 9223372036854775807) ”
.

Definition special_factorial_safety_wit_4_split_goal_2 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((-9223372036854775808) <= (fact * i )) ”
.

Definition special_factorial_safety_wit_5 := 
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (bfact * (fact * i ) )) ”
) \/
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (bfact * (fact * i ) )) ”
).

Definition special_factorial_safety_wit_5_split_goal_1 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ”
.

Definition special_factorial_safety_wit_5_split_goal_2 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((-9223372036854775808) <= (bfact * (fact * i ) )) ”
.

Definition special_factorial_safety_wit_6 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> (bfact * (fact * i ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition special_factorial_entail_wit_1 := 
(
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= n0) ” 
  &&  “ (n0 <= 8) ” 
  &&  “ (problem_139_pre_z n0 ) ” 
  &&  “ (special_factorial_safe_z n0 ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n0 + 1 )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 9223372036854775807) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 9223372036854775807) ” 
  &&  “ (1 = (factorial_z ((1 - 1 )))) ” 
  &&  “ (1 = (bfact_z ((1 - 1 )))) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
) \/
(
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  TT && emp 
|--
  “ (1 = (bfact_z ((1 - 1 )))) ” 
  &&  “ (1 = (factorial_z ((1 - 1 )))) ”
  &&  emp
).

Definition special_factorial_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  TT && emp 
|--
  “ (1 = (bfact_z ((1 - 1 )))) ”
.

Definition special_factorial_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (n0: Z) (PreH1 : (n_pre = n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) ,
  TT && emp 
|--
  “ (1 = (factorial_z ((1 - 1 )))) ”
.

Definition special_factorial_entail_wit_2 := 
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ (1 <= n0) ” 
  &&  “ (n0 <= 8) ” 
  &&  “ (problem_139_pre_z n0 ) ” 
  &&  “ (special_factorial_safe_z n0 ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (1 <= (fact * i )) ” 
  &&  “ ((fact * i ) <= 9223372036854775807) ” 
  &&  “ (1 <= (bfact * (fact * i ) )) ” 
  &&  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ” 
  &&  “ ((fact * i ) = (factorial_z (((i + 1 ) - 1 )))) ” 
  &&  “ ((bfact * (fact * i ) ) = (bfact_z (((i + 1 ) - 1 )))) ”
  &&  emp
) \/
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ ((bfact * (fact * i ) ) = (bfact_z (((i + 1 ) - 1 )))) ” 
  &&  “ ((fact * i ) = (factorial_z (((i + 1 ) - 1 )))) ” 
  &&  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ” 
  &&  “ (1 <= (bfact * (fact * i ) )) ” 
  &&  “ ((fact * i ) <= 9223372036854775807) ” 
  &&  “ (1 <= (fact * i )) ”
  &&  emp
).

Definition special_factorial_entail_wit_2_split_goal_1 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ ((bfact * (fact * i ) ) = (bfact_z (((i + 1 ) - 1 )))) ”
.

Definition special_factorial_entail_wit_2_split_goal_2 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ ((fact * i ) = (factorial_z (((i + 1 ) - 1 )))) ”
.

Definition special_factorial_entail_wit_2_split_goal_3 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ”
.

Definition special_factorial_entail_wit_2_split_goal_4 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ (1 <= (bfact * (fact * i ) )) ”
.

Definition special_factorial_entail_wit_2_split_goal_5 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ ((fact * i ) <= 9223372036854775807) ”
.

Definition special_factorial_entail_wit_2_split_goal_6 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i <= n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ (1 <= (fact * i )) ”
.

Definition special_factorial_return_wit_1 := 
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ (problem_139_spec_z n0 bfact ) ”
  &&  emp
) \/
(
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ (problem_139_spec_z n0 bfact ) ”
  &&  emp
).

Definition special_factorial_return_wit_1_split_goal_1 := 
forall (n0: Z) (bfact: Z) (fact: Z) (i: Z) (PreH1 : (i > n0)) (PreH2 : (1 <= n0)) (PreH3 : (n0 <= 8)) (PreH4 : (problem_139_pre_z n0 )) (PreH5 : (special_factorial_safe_z n0 )) (PreH6 : (1 <= i)) (PreH7 : (i <= (n0 + 1 ))) (PreH8 : (1 <= fact)) (PreH9 : (fact <= 9223372036854775807)) (PreH10 : (1 <= bfact)) (PreH11 : (bfact <= 9223372036854775807)) (PreH12 : (fact = (factorial_z ((i - 1 ))))) (PreH13 : (bfact = (bfact_z ((i - 1 ))))) ,
  TT && emp 
|--
  “ (problem_139_spec_z n0 bfact ) ”
.

Module Type VC_Correct.


Axiom proof_of_special_factorial_safety_wit_1 : special_factorial_safety_wit_1.
Axiom proof_of_special_factorial_safety_wit_2 : special_factorial_safety_wit_2.
Axiom proof_of_special_factorial_safety_wit_3 : special_factorial_safety_wit_3.
Axiom proof_of_special_factorial_safety_wit_4 : special_factorial_safety_wit_4.
Axiom proof_of_special_factorial_safety_wit_5 : special_factorial_safety_wit_5.
Axiom proof_of_special_factorial_safety_wit_6 : special_factorial_safety_wit_6.
Axiom proof_of_special_factorial_entail_wit_1 : special_factorial_entail_wit_1.
Axiom proof_of_special_factorial_entail_wit_2 : special_factorial_entail_wit_2.
Axiom proof_of_special_factorial_return_wit_1 : special_factorial_return_wit_1.

End VC_Correct.
