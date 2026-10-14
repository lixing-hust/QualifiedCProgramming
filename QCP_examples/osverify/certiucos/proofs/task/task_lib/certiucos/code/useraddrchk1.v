
Require Import os_code_defs1.
Require Import code_notations1.
Require Import os_ucos_h1.

(* (* new definitions in os_code_defs.v *) *)

(* Definition UserAddrStart := 0%Z. *)
(* Definition UserAddrEnd := 4294867295%Z. *)
(* Definition addr : ident := 670%Z. *)
(* Definition UserAddrCheck := 671%Z. *)

(* (*err Int8s, Tint8 stands for Int8u*) *)
(* Notation "'Int8s'" := (Tint8) (at level 5) : code_scope . *)

Open Scope code_scope.

Definition UserAddrCheck_impl :=
 Int8s ·UserAddrCheck·(⌞addr @ sem_t∗ ⌟)··{
     ⌞⌟;

     (* the value for NULL is Vnull --- different from any "Vptr ..." *) 
     (* hence NULL is treated separately *)
     (* the treatment reflects "0 <= UserAddrStart" in the C code *)
     If (addr′ ==ₑ NULL){ 
         RETURN  〈Int8s〉 ′0
     };ₛ

     If ((eptrconst userAddrStart) ≥ addr′ ||ₑ addr′ >ₑ (eptrconst userAddrEnd)){ 
       RETURN 〈Int8s〉 ′0
     };ₛ
     RETURN 〈Int8s〉 ′1
 }· . 

Close Scope code_scope.

