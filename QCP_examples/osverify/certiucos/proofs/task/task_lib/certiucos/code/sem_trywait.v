
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import os_ucos_h.

Open Scope code_scope.

Definition sem_trywait_impl := 
Int32 ·sem_trywait·(⌞sem @ sem_t∗⌟)··{  
        ⌞
         pos @ Int32;
         x @ Int8s;
         y @ Int16u;
         p @ OS_EVENT∗
        ⌟;

        x′ =ᶠ UserAddrCheck(·sem′·);ₛ 
        IF(x′  ==ₑ ′0 ){
            pos′ =ₑ  ′-1
        }
        ELSE{
          ENTER_CRITICAL;ₛ
          pos′ =ₑ  ∗sem′;ₛ
          EXIT_CRITICAL
        };ₛ
        If (pos′ <ₑ ′0 ||ₑ pos′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3){
           RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
            RETURN ′-1
        };ₛ
        
        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        y′ =ᶠ OSSemAccept(·p′·);ₛ
        If (y′ >ₑ ′0  ){
            RETURN  ′0
        };ₛ
        RETURN  ′-1
}· .
