Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(*os_sem.c*)
Open Scope code_scope.

Definition OSSemAccept_impl := 
Int16u ·OSSemAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞
         cnt @ Int16u
        ⌟;

        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
             EXIT_CRITICAL;ₛ
             RETURN  ′0
        };ₛ

        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′0
        };ₛ
        
        cnt′ =ₑ pevent′→OSEventCnt;ₛ
        If (cnt′ >ₑ ′0){
            −−pevent′→OSEventCnt
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  cnt′
}· .

Definition OSSemCreate_impl := 
OS_EVENT∗ ·OSSemCreate·(⌞cnt @ Int16u⌟)··{ 
         ⌞pevent @ OS_EVENT∗⌟;

        ENTER_CRITICAL;ₛ
            If (OSIntNesting′ >ₑ ′0) {
                EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL               
            };ₛ
            EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        pevent′ =ₑ OSEventFreeList′;ₛ
        If (OSEventFreeList′ !=ₑ NULL){
            OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
        };ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ pevent′;ₛ 
        OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_ecbcre1;ₛ  
        EXIT_CRITICAL;ₛ

        If (pevent′ !=ₑ NULL) {
           pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_SEM;ₛ
           pevent′→OSEventCnt =ₑ cnt′;ₛ
           pevent′→OSEventPtr =ₑ NULL;ₛ
           OS_EventWaitListInit(­pevent′­);ₛ

           ENTER_CRITICAL;ₛ
           (* add new event to the "ghost data structure" of the active event list *)
           pevent′→OSEventListPtr =ₑ OSEventList′;ₛ
           OSEventList′ =ₑ pevent′;ₛ
           OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_ecbcre2;ₛ  
           EXIT_CRITICAL
        };ₛ 
        RETURN  pevent′
 }·.

Definition OSSemDel_impl :=
OS_EVENT∗ ·OSSemDel·(⌞pevent @ OS_EVENT∗⌟)··{ 
           ⌞
             tasks_waiting @ Int8u 
           ⌟;
             If (OSIntNesting′ >ₑ ′0) {
              RETURN pevent′             
             };ₛ
            If (pevent′ ==ₑ NULL){
                RETURN pevent′
            };ₛ
            If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
                RETURN pevent′
            };ₛ
            IF (pevent′→OSEventGrp !=ₑ ′0){
                tasks_waiting′ =ₑ ′1
            }ELSE{
                tasks_waiting′ =ₑ ′0
            };ₛ
            IF (tasks_waiting′ ==ₑ ′0){
                OS_EventRemove(­pevent′­);ₛ
                pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
                pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
                OSEventFreeList′ =ₑ pevent′;ₛ                
                RETURN  NULL 
            }ELSE{
                RETURN pevent′
            }
}·.

Definition OSSemPend_impl  :=
Int8u ·OSSemPend·(⌞pevent @ OS_EVENT∗; timeout @ Int16u⌟)··{
       ⌞⌟;

        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ

        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
             EXIT_CRITICAL;ₛ 
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ

        If (pevent′→OSEventCnt >ₑ ′0){
            −−pevent′→OSEventCnt;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        };ₛ

        OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_SEM;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­pevent′­);ₛ 
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        If (OSTCBCur′→OSTCBStat &ₑ ′OS_STAT_SEM) {
            OS_EventTO(­pevent′­);ₛ 
            (* OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ OSTCBCur′→OSTCBBitY;ₛ
            OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ  *)
            EXIT_CRITICAL;ₛ
            RETURN ′OS_TIMEOUT
        };ₛ

        OSTCBCur′→OSTCBEventPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR
}· .

Definition OSSemPost_impl := 
Int8u ·OSSemPost·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞
         x  @ Int16u
       ⌟;

        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        If (pevent′→OSEventGrp !=ₑ ′0){
            x′ =ₑ ′OS_STAT_SEM;ₛ 
            OS_EventTaskRdy(­pevent′, ecast NULL (Tptr Tvoid), x′­);ₛ 
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        If (pevent′→OSEventCnt <ₑ ′65535){
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′OS_SEM_OVF

}·.

Definition OSSemPostBin_impl := 
Int8u ·OSSemPostBin·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞
         x  @ Int16u
       ⌟;

        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        If (pevent′→OSEventGrp !=ₑ ′0){
            x′ =ₑ ′OS_STAT_SEM;ₛ 
            OS_EventTaskRdy(­pevent′, ecast NULL (Tptr Tvoid), x′­);ₛ 
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        If (pevent′→OSEventCnt <ₑ ′1){ 
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′OS_SEM_OVF

}·.

Definition OSIPCSemPost_impl := 
Int8u ·OSIPCSemPost·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞
         x  @ Int16u
       ⌟;

        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        If (pevent′→OSEventGrp !=ₑ ′0){
            x′ =ₑ ′OS_STAT_SEM;ₛ 
            OS_EventTaskRdy(­pevent′, ecast NULL (Tptr Tvoid), x′­);ₛ 
            EXIT_CRITICAL;ₛ
            OS_IPCSched(­);ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        If (pevent′→OSEventCnt <ₑ ′65535){
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt +ₑ ′1;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_NO_ERR
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′OS_SEM_OVF

}·.

Close Scope code_scope.
