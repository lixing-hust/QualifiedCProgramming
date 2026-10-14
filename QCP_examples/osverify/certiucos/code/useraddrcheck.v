
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition UserAddrCheck_impl :=
 Int8s ·UserAddrCheck·(⌞addr @ sem_t∗ ⌟)··{
     ⌞⌟;

     If (addr′ ==ₑ NULL){ 
         RETURN  〈Int8s〉 ′0
     };ₛ

     If ((eptrconst userAddrStart) ≥ addr′ ||ₑ addr′ >ₑ (eptrconst userAddrEnd)){ 
       RETURN 〈Int8s〉 ′0
     };ₛ
     RETURN 〈Int8s〉 ′1
 }· . 

Definition UserAddrCheckCrit_impl :=
 Int8s ·UserAddrCheckCrit·(⌞addr @ sem_t∗ ⌟)··{
     ⌞⌟;

     If (addr′ ==ₑ NULL){ 
         RETURN  〈Int8s〉 ′0
     };ₛ

     If ((eptrconst userAddrStart) ≥ addr′ ||ₑ addr′ >ₑ (eptrconst userAddrEnd)){ 
       RETURN 〈Int8s〉 ′0
     };ₛ
     RETURN 〈Int8s〉 ′1
 }· . 

Close Scope code_scope.
