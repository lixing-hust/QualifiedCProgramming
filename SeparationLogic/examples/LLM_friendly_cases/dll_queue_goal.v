Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_friendly_cases.dll_queue_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import common_strategy_proof.
From SimpleC.EE.LLM_friendly_cases Require Import dll_queue_strategy_goal.
From SimpleC.EE.LLM_friendly_cases Require Import dll_queue_strategy_proof.

(*----- Function enqueue -----*)

Definition enqueue_safety_wit_1 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (qhead: Z) (qtail: Z) (retval: Z) ,
  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_safety_wit_2 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (qhead: Z) (qtail: Z) (retval: Z) ,
  [| (qhead = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_safety_wit_3 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (qhead: Z) (qtail: Z) (retval: Z) ,
  [| (qhead = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_safety_wit_4 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (l0: (@list Z)) (qtailv: Z) (qtail: Z) (qhead: Z) (qtailnext: Z) (qtailprev: Z) (p: Z) ,
  [| (p <> 0) |] 
  &&  [| (qtail <> 0) |] 
  &&  [| (qhead <> 0) |] 
  &&  [| (l = (app (l0) ((cons (qtailv) (nil))))) |] 
  &&  [| (qtailnext = 0) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (dllseg qhead qtail 0 qtailprev l0 )
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> p)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((qtail)  # "list" ->ₛ "next")) # Ptr  |-> p)
  **  ((&((qtail)  # "list" ->ₛ "prev")) # Ptr  |-> qtailprev)
  **  ((&((qtail)  # "list" ->ₛ "data")) # Int  |-> qtailv)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> qtail)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition enqueue_entail_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) ,
  (store_queue q_pre l )
|--
  EX (qhead: Z)  (qtail: Z) ,
  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
.

Definition enqueue_entail_wit_2 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (qhead_2: Z) (qtail_2: Z) (retval: Z) ,
  [| (qhead_2 <> 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  (dllseg qhead_2 0 0 qtail_2 l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_2)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail_2)
|--
  EX (qtailprev: Z)  (qtailnext: Z)  (l0: (@list Z))  (qtailv: Z)  (qhead: Z)  (qtail: Z) ,
  [| (retval <> 0) |] 
  &&  [| (qtail <> 0) |] 
  &&  [| (qhead <> 0) |] 
  &&  [| (l = (app (l0) ((cons (qtailv) (nil))))) |] 
  &&  [| (qtailnext = 0) |]
  &&  (dllseg qhead qtail 0 qtailprev l0 )
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((qtail)  # "list" ->ₛ "next")) # Ptr  |-> qtailnext)
  **  ((&((qtail)  # "list" ->ₛ "prev")) # Ptr  |-> qtailprev)
  **  ((&((qtail)  # "list" ->ₛ "data")) # Int  |-> qtailv)
  **  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
.

Definition enqueue_return_wit_1 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (l0: (@list Z)) (qtailv: Z) (qtail: Z) (qhead: Z) (qtailnext: Z) (qtailprev: Z) (p: Z) ,
  [| (p <> 0) |] 
  &&  [| (qtail <> 0) |] 
  &&  [| (qhead <> 0) |] 
  &&  [| (l = (app (l0) ((cons (qtailv) (nil))))) |] 
  &&  [| (qtailnext = 0) |]
  &&  (dllseg qhead qtail 0 qtailprev l0 )
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> p)
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((qtail)  # "list" ->ₛ "next")) # Ptr  |-> p)
  **  ((&((qtail)  # "list" ->ₛ "prev")) # Ptr  |-> qtailprev)
  **  ((&((qtail)  # "list" ->ₛ "data")) # Int  |-> qtailv)
  **  ((&((p)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((p)  # "list" ->ₛ "prev")) # Ptr  |-> qtail)
  **  ((&((p)  # "list" ->ₛ "data")) # Int  |-> x_pre)
|--
  (store_queue q_pre (app (l) ((cons (x_pre) (nil)))) )
.

Definition enqueue_return_wit_2 := 
forall (x_pre: Z) (q_pre: Z) (l: (@list Z)) (qhead: Z) (qtail: Z) (retval: Z) ,
  [| (qhead = 0) |] 
  &&  [| (retval <> 0) |]
  &&  ((&((retval)  # "list" ->ₛ "next")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((retval)  # "list" ->ₛ "data")) # Int  |-> x_pre)
  **  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> retval)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> retval)
|--
  (store_queue q_pre (app (l) ((cons (x_pre) (nil)))) )
.

Definition enqueue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (qhead: Z) (qtail: Z) ,
  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  (dllseg qhead 0 0 qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
.

(*----- Function dequeue -----*)

Definition dequeue_safety_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (qhead: Z) (qtail: Z) (qhead_prev: Z) (qhead_next: Z) ,
  [| (qhead <> 0) |] 
  &&  [| (qhead_prev = 0) |]
  &&  ((( &( "x0" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> qhead)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (dllseg qhead_next 0 qhead qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_safety_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (qhead: Z) (qtail: Z) (qhead_prev: Z) (qhead_next: Z) ,
  [| (qhead_next = 0) |] 
  &&  [| (qhead <> 0) |] 
  &&  [| (qhead_prev = 0) |]
  &&  ((( &( "x0" ) )) # Int  |-> x)
  **  ((( &( "p" ) )) # Ptr  |-> qhead)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (dllseg qhead_next 0 qhead qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_safety_wit_3 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (qhead: Z) (qtail: Z) (headv: Z) (l0: (@list Z)) (qhead_prev: Z) (p: Z) (qhead_next: Z) ,
  [| (qhead <> 0) |] 
  &&  [| (l = (cons (headv) (l0))) |] 
  &&  [| (qhead_prev = p) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "x0" ) )) # Int  |-> x)
  **  ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> qhead_prev)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> headv)
  **  ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next)
  **  (dllseg qhead_next 0 qhead qtail l0 )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition dequeue_entail_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) ,
  (store_queue q_pre (cons (x) (l)) )
|--
  EX (qhead_next: Z)  (qtail: Z)  (qhead_prev: Z)  (qhead: Z) ,
  [| (qhead <> 0) |] 
  &&  [| (qhead_prev = 0) |]
  &&  ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> qhead_prev)
  **  ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next)
  **  (dllseg qhead_next 0 qhead qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
.

Definition dequeue_entail_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (qhead: Z) (qtail_2: Z) (qhead_prev_2: Z) (qhead_next_2: Z) ,
  [| (qhead_next_2 <> 0) |] 
  &&  [| (qhead <> 0) |] 
  &&  [| (qhead_prev_2 = 0) |]
  &&  (dllseg qhead_next_2 0 qhead qtail_2 l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next_2)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail_2)
|--
  EX (qhead_next: Z)  (qtail: Z)  (qhead_prev: Z)  (headv: Z)  (l0: (@list Z))  (qhead_2: Z) ,
  [| (qhead_2 <> 0) |] 
  &&  [| (l = (cons (headv) (l0))) |] 
  &&  [| (qhead_prev = qhead) |]
  &&  ((&((qhead_2)  # "list" ->ₛ "prev")) # Ptr  |-> qhead_prev)
  **  ((&((qhead_2)  # "list" ->ₛ "data")) # Int  |-> headv)
  **  ((&((qhead_2)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next)
  **  (dllseg qhead_next 0 qhead_2 qtail l0 )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_2)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
.

Definition dequeue_return_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (qhead: Z) (qtail: Z) (headv: Z) (l0: (@list Z)) (qhead_prev: Z) (p: Z) (qhead_next: Z) ,
  [| (qhead <> 0) |] 
  &&  [| (l = (cons (headv) (l0))) |] 
  &&  [| (qhead_prev = p) |]
  &&  ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> 0)
  **  ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> headv)
  **  ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next)
  **  (dllseg qhead_next 0 qhead qtail l0 )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  [| (x = x) |]
  &&  (store_queue q_pre l )
.

Definition dequeue_return_wit_2 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (qhead: Z) (qtail: Z) (qhead_prev: Z) (qhead_next: Z) ,
  [| (qhead_next = 0) |] 
  &&  [| (qhead <> 0) |] 
  &&  [| (qhead_prev = 0) |]
  &&  (dllseg qhead_next 0 qhead qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> 0)
|--
  [| (x = x) |]
  &&  (store_queue q_pre l )
.

Definition dequeue_partial_solve_wit_1 := 
forall (q_pre: Z) (l: (@list Z)) (x: Z) (qhead: Z) (qtail: Z) (qhead_prev: Z) (qhead_next: Z) ,
  [| (qhead <> 0) |] 
  &&  [| (qhead_prev = 0) |]
  &&  ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> qhead_prev)
  **  ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> x)
  **  ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next)
  **  (dllseg qhead_next 0 qhead qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
|--
  [| (qhead <> 0) |] 
  &&  [| (qhead_prev = 0) |]
  &&  ((&((qhead)  # "list" ->ₛ "next")) # Ptr  |-> qhead_next)
  **  ((&((qhead)  # "list" ->ₛ "prev")) # Ptr  |-> qhead_prev)
  **  ((&((qhead)  # "list" ->ₛ "data")) # Int  |-> x)
  **  (dllseg qhead_next 0 qhead qtail l )
  **  ((&((q_pre)  # "queue" ->ₛ "head")) # Ptr  |-> qhead_next)
  **  ((&((q_pre)  # "queue" ->ₛ "tail")) # Ptr  |-> qtail)
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include dll_queue_Strategy_Correct.

Axiom proof_of_enqueue_safety_wit_1 : enqueue_safety_wit_1.
Axiom proof_of_enqueue_safety_wit_2 : enqueue_safety_wit_2.
Axiom proof_of_enqueue_safety_wit_3 : enqueue_safety_wit_3.
Axiom proof_of_enqueue_safety_wit_4 : enqueue_safety_wit_4.
Axiom proof_of_enqueue_entail_wit_1 : enqueue_entail_wit_1.
Axiom proof_of_enqueue_entail_wit_2 : enqueue_entail_wit_2.
Axiom proof_of_enqueue_return_wit_1 : enqueue_return_wit_1.
Axiom proof_of_enqueue_return_wit_2 : enqueue_return_wit_2.
Axiom proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1.
Axiom proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1.
Axiom proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2.
Axiom proof_of_dequeue_safety_wit_3 : dequeue_safety_wit_3.
Axiom proof_of_dequeue_entail_wit_1 : dequeue_entail_wit_1.
Axiom proof_of_dequeue_entail_wit_2 : dequeue_entail_wit_2.
Axiom proof_of_dequeue_return_wit_1 : dequeue_return_wit_1.
Axiom proof_of_dequeue_return_wit_2 : dequeue_return_wit_2.
Axiom proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1.

End VC_Correct.
