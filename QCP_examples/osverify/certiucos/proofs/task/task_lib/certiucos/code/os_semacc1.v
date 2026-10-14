
Require Import os_code_defs1.
Require Import code_notations1.
Require Import os_ucos_h1.

(* new definitions in os_code_defs.v *)

Open Scope code_scope.

Definition OSSemAccept_impl := 
Int16u ·OSSemAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞
         cnt @ Int16u; 
         legal @ Int8u
        ⌟;

        If (pevent′ ==ₑ NULL){
             RETURN  ′0
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·pevent′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′0
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′0
        };ₛ
(*         ENTER_CRITICAL;ₛ  *)
        cnt′ =ₑ pevent′→OSEventCnt;ₛ
        If (cnt′ >ₑ ′0){
            −−pevent′→OSEventCnt
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  cnt′
}· .

Close Scope code_scope.
