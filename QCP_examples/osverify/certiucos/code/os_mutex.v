
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

Definition OSMutexAccept_impl := 
 Int8u ·OSMutexAccept·(⌞pevent @ OS_EVENT∗⌟)··{
        ⌞ 
          (* pip @ Int8u *)
        ⌟; 

           ENTER_CRITICAL;ₛ
            If (OSIntNesting′ >ₑ ′0) {
                EXIT_CRITICAL;ₛ
                RETURN ′0 
            };ₛ
            EXIT_CRITICAL;ₛ

           ENTER_CRITICAL;ₛ
          If(pevent′ ==ₑ NULL){
              EXIT_CRITICAL;ₛ
              RETURN ′0 
          };ₛ
          If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′0
          };ₛ
          If ((pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8) ==ₑ ′OS_MUTEX_AVAILABLE){
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ OSTCBCur′→OSTCBPrio;ₛ
            pevent′→OSEventPtr =ₑ OSTCBCur′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′1 
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′0  
}· .


Definition OSMutexCreate_impl := 
OS_EVENT∗ ·OSMutexCreate·(⌞prio @ Int8u; err @ Tptr Int8u⌟)··{
           ⌞pevent @ OS_EVENT∗⌟;

             ENTER_CRITICAL;ₛ
            If (OSIntNesting′ >ₑ ′0) {
                EXIT_CRITICAL;ₛ
                ENTER_CRITICAL;ₛ
                ∗err′  =ₑ ′OS_ERR_CREATE_ISR;ₛ
                EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL               
            };ₛ
            EXIT_CRITICAL;ₛ

            If (prio′ ≥ ′OS_LOWEST_PRIO) { 
                 ENTER_CRITICAL;ₛ
                 ∗err′  =ₑ ′OS_PRIO_INVALID;ₛ
                 EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL
            };ₛ

            ENTER_CRITICAL;ₛ
            If (OSTCBPrioTbl′[prio′] !=ₑ NULL) {
                EXIT_CRITICAL;ₛ
                ENTER_CRITICAL;ₛ
                ∗err′  =ₑ ′OS_PRIO_EXIST;ₛ
                EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL               
            };ₛ                   
            OSTCBPrioTbl′[prio′] =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ
            pevent′ =ₑ OSEventFreeList′;ₛ
            If (pevent′ ==ₑ NULL){
                OSTCBPrioTbl′[prio′] =ₑ NULL;ₛ
                EXIT_CRITICAL;ₛ
                ENTER_CRITICAL;ₛ
                ∗err′  =ₑ ′OS_ERR_PEVENT_NULL;ₛ
                EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL
            };ₛ 
            OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr;ₛ  
            OSTCBCur′→__OSTskMuxPtr =ₑ pevent′;ₛ
            OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_ecbcre1;ₛ
            EXIT_CRITICAL;ₛ 

            pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_MUTEX;ₛ
            pevent′→OSEventCnt  =ₑ ((〈Int16u〉prio′) ≪ ′8) |ₑ ′OS_MUTEX_AVAILABLE;ₛ  
            pevent′→OSEventPtr  =ₑ NULL;ₛ
            OS_EventWaitListInit(­pevent′­);ₛ  

            ENTER_CRITICAL;ₛ
            pevent ′ → OSEventListPtr =ₑ OSEventList ′;ₛ
            OSEventList′ =ₑ pevent′;ₛ
            OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_ecbcre2;ₛ
            EXIT_CRITICAL;ₛ
            ENTER_CRITICAL;ₛ
            ∗err′  =ₑ ′OS_NO_ERR;ₛ
            EXIT_CRITICAL;ₛ
            RETURN pevent′          
 }·.

Definition OSMutexDel_impl := 
 Int8u ·OSMutexDel·(⌞ pevent @ OS_EVENT ∗⌟)··{
        ⌞ 
         tasks_waiting @ Int8u;
         pip @ Int8u
        ⌟; 
        If (OSIntNesting′ >ₑ ′0) {
              RETURN pevent′             
        };ₛ
        If (pevent′ ==ₑ  NULL){
             RETURN NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            RETURN pevent′
        };ₛ  
        IF (pevent′→OSEventGrp !=ₑ ′0){
            tasks_waiting′ =ₑ ′1
        }ELSE{
            tasks_waiting′ =ₑ ′0
        };ₛ
        IF (tasks_waiting′ ==ₑ ′0){
            OS_EventRemove(­pevent′­);ₛ
            pip′ =ₑ 〈Int8u〉 (pevent′→OSEventCnt ≫ ′8);ₛ
            OSTCBPrioTbl′[pip′] =ₑ NULL;ₛ
            pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
            pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
            OSEventFreeList′ =ₑ pevent′;ₛ
            RETURN NULL 
        }ELSE{
            RETURN pevent′
        }    
 }· .

Definition OSMutexPend_impl :=
 Int8u ·OSMutexPend·(⌞pevent @ OS_EVENT∗; timeout @ Int16u ⌟)··{
        ⌞
           pip @ Int8u;
           mprio @ Int8u;
           isrdy @ Int8u;
           ptcb @ (Tptr OS_TCB)
        ⌟;
        ENTER_CRITICAL;ₛ 
        If (pevent′ ==ₑ  NULL){
             EXIT_CRITICAL;ₛ
             RETURN ′OS_ERR_PEVENT_NULL
        };ₛ

        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ

        If (〈Int8u〉(pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8) ==ₑ ′OS_MUTEX_AVAILABLE) {
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ OSTCBCur′→OSTCBPrio;ₛ
            pevent′→OSEventPtr =ₑ 〈Void ∗〉OSTCBCur′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        };ₛ

        pip′  =ₑ 〈Int8u〉(pevent′→OSEventCnt ≫ ′8);ₛ
        mprio′ =ₑ 〈Int8u〉(pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8);ₛ
        ptcb′  =ₑ 〈OS_TCB ∗〉 pevent′→OSEventPtr;ₛ                                                  

        If ((ptcb′→OSTCBPrio !=ₑ pip′) &&ₑ (mprio′ >ₑ (OSTCBCur′→OSTCBPrio))){  
           
            IF ((OSRdyTbl′[ptcb′→OSTCBY] &ₑ ptcb′→OSTCBBitX) !=ₑ ′0) 
            {
                OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY]&ₑ(∼ptcb′→OSTCBBitX);ₛ
                If (OSRdyTbl′[ptcb′→OSTCBY] ==ₑ ′0)
                {
                    OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼ptcb′→OSTCBBitY)
                };ₛ  
                isrdy′ =ₑ ′1 
            }ELSE{
                isrdy′ =ₑ ′0
            };ₛ
            (* NB: the assignment with PlaceHolder does not exist in the C code *) 
            OSTCBPrioTbl′[ ptcb′→OSTCBPrio ] =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ   
            ptcb′→OSTCBPrio =ₑ pip′;ₛ                             (* Change owner task prio to PIP            *)
            ptcb′→OSTCBY    =ₑ ptcb′→OSTCBPrio ≫ ′3;ₛ
            ptcb′→OSTCBBitY =ₑ OSMapTbl′[ptcb′→OSTCBY];ₛ
            ptcb′→OSTCBX    =ₑ (ptcb′→OSTCBPrio) &ₑ ′7;ₛ
            ptcb′→OSTCBBitX =ₑ OSMapTbl′[ptcb′→OSTCBX];ₛ
            If (isrdy′ ==ₑ ′1) 
            {
                OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ     (* ... make it ready at new priority.       *)
                OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX
            };ₛ
           OSTCBPrioTbl′[pip′] =ₑ 〈OS_TCB ∗〉 ptcb′
        };ₛ

        OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_MUTEX;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­pevent′­);ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        If (OSTCBCur′→OSTCBStat &ₑ ′OS_STAT_MUTEX) { 
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


Definition OSMutexPost_impl :=
 Int8u ·OSMutexPost·(⌞pevent @ OS_EVENT∗ ⌟)··{
        ⌞
(*          x @ Int8u;       *)
         pip @ Int8u;
         prio  @ Int8u
(*          y @ Int8u  *)
        ⌟;

        ENTER_CRITICAL;ₛ
        If (OSIntNesting′ >ₑ ′0) {
           EXIT_CRITICAL;ₛ
           RETURN ′OS_ERR_POST_ISR 
        };ₛ
           EXIT_CRITICAL;ₛ
           ENTER_CRITICAL;ₛ 
        If (pevent′ ==ₑ NULL){
           EXIT_CRITICAL;ₛ
           RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ
        pip′  =ₑ 〈Int8u〉(pevent′→OSEventCnt ≫ ′8);ₛ
        prio′ =ₑ 〈Int8u〉(pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8);ₛ    
        If (OSTCBCur′→OSTCBPrio !=ₑ pip′ &&ₑ OSTCBCur′→OSTCBPrio !=ₑ prio′) {
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_NOT_MUTEX_OWNER 
        };ₛ
        If (OSTCBCur′→OSTCBPrio ==ₑ pip′) {
          (* Did we have to raise current task's priority? *)
            
            OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
            If ( OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0) {
                OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ ∼OSTCBCur′→OSTCBBitY
            };ₛ
            OSTCBCur′→OSTCBPrio         =ₑ prio′;ₛ
            OSTCBCur′→OSTCBY            =ₑ prio′ ≫  ′3;ₛ
            OSTCBCur′→OSTCBBitY         =ₑ OSMapTbl′[OSTCBCur′→OSTCBY];ₛ
            OSTCBCur′→OSTCBX            =ₑ prio′ &ₑ ′7;ₛ
            OSTCBCur′→OSTCBBitX         =ₑ OSMapTbl′[OSTCBCur′→OSTCBX];ₛ
            OSRdyGrp′                    =ₑ OSRdyGrp′ |ₑ OSTCBCur′→OSTCBBitY;ₛ
            OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
            OSTCBPrioTbl′[prio′]         =ₑ 〈OS_TCB ∗〉 OSTCBCur′
        };ₛ
        OSTCBPrioTbl′[pip′]          =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ
        If (pevent′→OSEventGrp !=ₑ ′0) {
(*             x′ =ₑ ′OS_STAT_MUTEX;ₛ  *)
            prio′ =ᶠ OS_EventTaskRdy(·pevent′, 〈Void ∗〉NULL, 〈Int16u〉 ′OS_STAT_MUTEX·);ₛ
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ  (*Save priority of mutex's new owner *)
            pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ prio′;ₛ
            pevent′→OSEventPtr =ₑ OSTCBPrioTbl′[prio′];ₛ     (*Link to mutex owner's OS_TCB*)
     
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        pevent′→OSEventCnt =ₑ pevent′→OSEventCnt |ₑ ′OS_MUTEX_AVAILABLE;ₛ (* No,  Mutex is now available   *)
        pevent′→OSEventPtr =ₑ NULL;ₛ
   
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR 
 }· . 

Close Scope code_scope.
