Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(*os_q.c*)
Open Scope code_scope.

Definition OSQAccept_impl := 
 Void ∗ ·OSQAccept·(⌞pevent @ OS_EVENT∗⌟)··{
       ⌞ 
        message @ Void ∗;
        pq @ OS_Q ∗ (* ; *)
      ⌟; 
      ENTER_CRITICAL;ₛ
        If(pevent′ ==ₑ NULL){
            EXIT_CRITICAL;ₛ
            RETURN 〈Void ∗〉 NULL 
        };ₛ
        If ( pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q ){
          EXIT_CRITICAL;ₛ 
          RETURN 〈Void ∗〉 NULL 
        };ₛ
        
        pq′ =ₑ pevent′→OSEventPtr;ₛ
        IF (pq′→OSQEntries >ₑ ′0){
            message′ =ₑ ∗(pq′→ OSQOut);ₛ
            pq′ → OSQOut =ₑ pq′→OSQOut +ₑ ′1 ;ₛ
            −− pq′→OSQEntries;ₛ
           If (pq′→OSQOut ==ₑ pq′→OSQEnd){
               pq′→OSQOut =ₑ pq′→OSQStart
           }
        }ELSE{
            message′ =ₑ NULL
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN  message′ 
 }· .

Definition OSQCreate_impl :=
 OS_EVENT ∗ ·OSQCreate·(⌞size @ Int16u⌟)··{
        ⌞ 
          pevent @ OS_EVENT ∗;
          pq @ OS_Q ∗;
          pqblk @ OS_Q_FREEBLK ∗;
          start @ Void ∗∗
          ⌟; 

           If ((size′ >ₑ ′OS_MAX_Q_SIZE ) ||ₑ (size′ ==ₑ ′0)){ 
              RETURN 〈OS_EVENT ∗〉 NULL 
           };ₛ 
          ENTER_CRITICAL;ₛ
          pevent′ =ₑ OSEventFreeList′;ₛ
          If (OSEventFreeList′ !=ₑ NULL){
              OSEventFreeList′ =ₑ  〈OS_EVENT ∗〉 OSEventFreeList′→OSEventListPtr;ₛ  
              OSTCBCur′→__OSTskQPtr =ₑ pevent′;ₛ 
              OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_ecbcre1
          };ₛ
          EXIT_CRITICAL;ₛ
          If (pevent′ !=ₑ NULL) {
              ENTER_CRITICAL;ₛ
              pq′ =ₑ OSQFreeList′;ₛ
              pqblk′ =ₑ OSQFreeBlk′;ₛ
              IF (pq′ !=ₑ NULL &&ₑ  pqblk′ !=ₑ NULL){ 
                  OSQFreeList′ =ₑ OSQFreeList′→OSQPtr;ₛ 
                  OSQFreeBlk′ =ₑ OSQFreeBlk′→nextblk;ₛ
                  EXIT_CRITICAL;ₛ 
                  (* setup ghost data structure for the queue buffer *) 
                  pq′→qfreeblk =ₑ pqblk′;ₛ
                  (* setup queue control block and ECB *) 
                  start′ =ₑ pqblk′→msgqueuetbl;ₛ
                  pq′→OSQStart =ₑ start′;ₛ
                  pq′→OSQEnd =ₑ &ₐstart′[size′];ₛ
                  pq′→OSQIn =ₑ start′;ₛ 
                  pq′→OSQOut =ₑ start′;ₛ
                  pq′→OSQSize =ₑ size′;ₛ
                  pq′→OSQEntries =ₑ ′0;ₛ
                  pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_Q;ₛ
                  pevent′→OSEventCnt =ₑ ′0;ₛ
                  pevent′→OSEventPtr =ₑ pq′;ₛ
                  OS_EventWaitListInit(­pevent′­);ₛ
                  
                  ENTER_CRITICAL;ₛ
                  pevent′→OSEventListPtr =ₑ OSEventList′;ₛ
                  OSEventList′ =ₑ pevent′;ₛ
                  OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_ecbcre2;ₛ 
                  EXIT_CRITICAL
              }ELSE{
                  (* pevent′→OSEventPtr =ₑ 〈Void∗〉 OSEventFreeList′;ₛ  *)
                  pevent′→OSEventListPtr =ₑ 〈Void∗〉 OSEventFreeList′;ₛ
                  OSEventFreeList′ =ₑ  pevent′;ₛ
                  OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ
                  OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_normal;ₛ 
                  EXIT_CRITICAL;ₛ
                  pevent′ =ₑ 〈OS_EVENT∗〉NULL
              }
          };ₛ
          RETURN pevent′
 }· .

Definition OSQDel_impl :=  
 OS_EVENT∗ ·OSQDel·(⌞ pevent @ OS_EVENT∗⌟)··{ 
        ⌞ 
         tasks_waiting @ Int8u;
         tasks_post_waiting @ Int8u;
         pq @ OS_Q ∗; 
         x @ Int16u; 
         pqblk @ OS_Q_FREEBLK ∗
        ⌟; 
         
        ENTER_CRITICAL;ₛ  
        If (pevent′ ==ₑ  NULL){
             (* ∗err′ =ₑ ′OS_ERR_PEVENT_NULL;ₛ  *)
             EXIT_CRITICAL;ₛ
             RETURN pevent′
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
             (* ∗err′ =ₑ ′OS_ERR_EVENT_TYPE;ₛ  *)
             EXIT_CRITICAL;ₛ
             RETURN pevent′
        };ₛ  

        IF (pevent′→OSEventGrp !=ₑ ′0){
            tasks_waiting′ =ₑ ′1
        }ELSE{
            tasks_waiting′ =ₑ ′0
        };ₛ
        IF (pevent′→OSPostEventGrp !=ₑ ′0){
            tasks_post_waiting′ =ₑ ′1
        }ELSE{
            tasks_post_waiting′ =ₑ ′0
        };ₛ

        WHILE (pevent′→OSEventGrp !=ₑ ′0) { 
            x′ =ₑ ′OS_STAT_Q;ₛ  
            OS_EventTaskRdy(­pevent′, 〈Void ∗〉NULL, x′­)
        };ₛ 
        WHILE (pevent′→OSPostEventGrp !=ₑ ′0) { 
            x′ =ₑ ′OS_STAT_POSTQ;ₛ  
            OS_EventTaskPostRdyDel(- pevent′, x′ -) 
        };ₛ 
        (* NB: in the C code, there is an explicit type cast to (OS_Q ptr)  *) 
        OS_EventRemoveDel(­pevent′­);ₛ
        pq′ =ₑ pevent′→OSEventPtr;ₛ 
        pqblk′ =ₑ pq′→qfreeblk;ₛ
        pqblk′→nextblk =ₑ OSQFreeBlk′;ₛ
        OSQFreeBlk′ =ₑ pq′→qfreeblk;ₛ
        pq′→OSQPtr =ₑ OSQFreeList′;ₛ
        OSQFreeList′ =ₑ pq′;ₛ
        pevent′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ 
        pevent′→OSEventListPtr =ₑ OSEventFreeList′;ₛ  
        OSEventFreeList′ =ₑ pevent′;ₛ
        OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ 
        If (tasks_waiting′ ==ₑ ′1 ||ₑ tasks_post_waiting′ ==ₑ ′1) { 
            OS_Sched(­)
        };ₛ  
        (* ∗err′ =ₑ ′OS_NO_ERR;ₛ *) 
        RETURN 〈OS_EVENT ∗〉 NULL 

 }· . 

Definition OSQPend_impl :=
 Void∗ ·OSQPend·(⌞ pevent @ OS_EVENT ∗; timeout @ Int16u; err @ Int8u∗ ⌟)··{  
         ⌞ 
         message @ Void∗;
         pq @ OS_Q ∗; 
         x  @ Int16u
        ⌟;
           ENTER_CRITICAL;ₛ
            If (OSIntNesting′ >ₑ ′0) {
                EXIT_CRITICAL;ₛ
                ENTER_CRITICAL;ₛ
                ∗err′ =ₑ ′OS_ERR_PEND_ISR;ₛ
                EXIT_CRITICAL;ₛ
                RETURN  〈Void ∗〉 NULL 
            };ₛ
            EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ  NULL){
             ∗err′ =ₑ ′OS_ERR_PEVENT_NULL;ₛ
             EXIT_CRITICAL;ₛ
             RETURN 〈Void ∗〉 NULL
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            (* EXIT_CRITICAL;ₛ *)
            ∗err′ =ₑ ′OS_ERR_EVENT_TYPE;ₛ
            EXIT_CRITICAL;ₛ
            RETURN 〈Void ∗〉 NULL  
        };ₛ
        pq′ =ₑ pevent′→OSEventPtr;ₛ
        If (pq′→OSQEntries >ₑ ′0) {
            message′ =ₑ ∗(pq′→OSQOut);ₛ
            pq′→ OSQOut =ₑ pq′→OSQOut +ₑ ′1;ₛ
            −− pq′→OSQEntries;ₛ
            If (pq′→OSQOut ==ₑ pq′→OSQEnd){
                pq′→OSQOut =ₑ pq′→OSQStart
            };ₛ
            IF (pevent′→OSPostEventGrp !=ₑ ′0) { 
                x′ =ₑ ′OS_STAT_POSTQ;ₛ  
                (* NB: did not find how to express the code with notation *)  
                scall OS_EventTaskPostRdy (pevent′ :: x′ :: nil);ₛ
                EXIT_CRITICAL;ₛ 
                OS_Sched(­)
            } ELSE {
                EXIT_CRITICAL
            };ₛ 
            (* OSTCBCur′→OSTCBMsg =ₑ message′;ₛ *)
            ENTER_CRITICAL;ₛ
            ∗err′ =ₑ ′OS_NO_ERR;ₛ
            EXIT_CRITICAL;ₛ
            RETURN message′
        };ₛ
        OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_Q;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­pevent′­);ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        message′ =ₑ OSTCBCur′→OSTCBMsg;ₛ                                 
        If (message′ !=ₑ NULL){
            OSTCBCur′→OSTCBMsg =ₑ 〈Void ∗〉 NULL;ₛ  
            OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ  
            OSTCBCur′→OSTCBEventPtr =ₑ 〈OS_EVENT ∗〉 NULL;ₛ  
            EXIT_CRITICAL;ₛ
            ENTER_CRITICAL;ₛ
            ∗err′ =ₑ ′OS_NO_ERR;ₛ 
            EXIT_CRITICAL;ₛ
            RETURN message′
        };ₛ
        (* NB: the call to OS_EventTO did not exist in the uC/OS-II verification *) 
        OS_EventTO(­pevent′­);ₛ  
        (* OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ OSTCBCur′→OSTCBBitY;ₛ
        OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ  *)
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        ∗err′ =ₑ ′OS_TIMEOUT;ₛ  
        EXIT_CRITICAL;ₛ
        RETURN 〈Void ∗〉 NULL  
  }· .

Definition OSQPost_impl :=
 Int8u ·OSQPost·(⌞pevent @ OS_EVENT∗ ;  message @ Void∗⌟)··{
        ⌞
         pq @ OS_Q∗;         
         x  @ Int16u
        ⌟;
        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
           EXIT_CRITICAL;ₛ
           RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (message′ ==ₑ NULL){
          EXIT_CRITICAL;ₛ
          RETURN  ′OS_ERR_POST_NULL_PTR
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        (* ENTER_CRITICAL;ₛ *)
        If (pevent′→OSEventGrp !=ₑ ′0) {
            x′ =ₑ ′OS_STAT_Q;ₛ 
            OS_EventTaskRdy(­pevent′, message′, x′­);ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        pq′ =ₑ pevent′→OSEventPtr;ₛ
        If (pq′→OSQEntries ≥ pq′→OSQSize) {
            EXIT_CRITICAL;ₛ
            RETURN ′OS_Q_FULL
        };ₛ
        ∗(pq′→OSQIn) =ₑ message′;ₛ
        ++ (pq′→OSQIn);ₛ
        ++ (pq′→OSQEntries);ₛ
        If (pq′→OSQIn ==ₑ pq′→OSQEnd) {
            pq′→OSQIn =ₑ pq′→OSQStart
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR 
 }· .

Definition OSIPCQPost_impl :=
 Int8u ·OSIPCQPost·(⌞pevent @ OS_EVENT∗ ;  message @ Void∗⌟)··{
        ⌞
         pq @ OS_Q∗;         
         x  @ Int16u
        ⌟;
        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
           EXIT_CRITICAL;ₛ
           RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (message′ ==ₑ NULL){
          EXIT_CRITICAL;ₛ
          RETURN  ′OS_ERR_POST_NULL_PTR
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        (* ENTER_CRITICAL;ₛ *)
        If (pevent′→OSEventGrp !=ₑ ′0) {
            x′ =ₑ ′OS_STAT_Q;ₛ 
            OS_EventTaskRdy(­pevent′, message′, x′­);ₛ
            EXIT_CRITICAL;ₛ
            OS_IPCSched(­);ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        pq′ =ₑ pevent′→OSEventPtr;ₛ
        If (pq′→OSQEntries ≥ pq′→OSQSize) {
            EXIT_CRITICAL;ₛ
            RETURN ′OS_Q_FULL
        };ₛ
        ∗(pq′→OSQIn) =ₑ message′;ₛ
        ++ (pq′→OSQIn);ₛ
        ++ (pq′→OSQEntries);ₛ
        If (pq′→OSQIn ==ₑ pq′→OSQEnd) {
            pq′→OSQIn =ₑ pq′→OSQStart
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR 
 }· .
 
Definition psrc : ident := 1500%Z. 
Open Scope int_scope.

Definition OSQQuery_impl := 
Int8u ·OSQQuery·(⌞pevent @ OS_EVENT∗; pdata @OS_Q_DATA∗⌟)··{
        ⌞ 
          pq @ OS_Q ∗; 
          psrc @ Int8u ∗;
          pdest @Int8u ∗
        ⌟;
        
          ENTER_CRITICAL;ₛ
          If(pevent′ ==ₑ NULL){
              EXIT_CRITICAL;ₛ
              RETURN 〈Int8u〉′OS_ERR_PEVENT_NULL
          };ₛ

          If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
              EXIT_CRITICAL;ₛ 
              RETURN  〈Int8u〉′OS_ERR_EVENT_TYPE
          };ₛ
          
          pdata′→OSEventGrp =ₑ pevent′→OSEventGrp;ₛ
          psrc′                                =ₑ &ₐ (pevent′→OSEventTbl[′0]);ₛ
          pdest′                             =ₑ &ₐ (pdata′→OSEventTbl[′0]);ₛ
          
          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          ∗pdest′  =ₑ   ∗psrc′;ₛ
          pdest′ =ₑ  pdest′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ
          psrc′ =ₑ  psrc′ +ₑ  (econst32 ($ Z.of_nat (typelen Tint8)));ₛ

          pq′ =ₑ pevent′→OSEventPtr;ₛ
          IF (pq′→OSQEntries ){
              pdata′→OSMsg =ₑ ∗(pq′→OSQOut)
          }ELSE
          {
              pdata′→OSMsg =ₑ NULL
          };ₛ
          
          pdata′→OSNMsgs =ₑ pq′→OSQEntries;ₛ
          pdata′→OSQSize =ₑ pq′→OSQSize;ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′OS_NO_ERR
     }· .

Definition OSQTimedPost_impl :=
 Int8u ·OSQTimedPost·(⌞pevent @ OS_EVENT∗ ; timeout @ Int16u;  message @ Void∗⌟)··{
        ⌞
         pq @ OS_Q∗;
         x  @ Int16u
        ⌟;
        ENTER_CRITICAL;ₛ
        If (pevent′ ==ₑ NULL){
           EXIT_CRITICAL;ₛ
           RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (message′ ==ₑ NULL){
          EXIT_CRITICAL;ₛ
          RETURN  ′OS_ERR_POST_NULL_PTR
        };ₛ
        If (pevent′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_EVENT_TYPE
        };ₛ
        If (pevent′→OSEventGrp !=ₑ ′0) {
            x′ =ₑ ′OS_STAT_Q;ₛ 
            OS_EventTaskRdy(­pevent′, message′, x′­);ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        pq′ =ₑ pevent′→OSEventPtr;ₛ
        If (pq′→OSQEntries ≥ pq′→OSQSize) {
            OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_POSTQ;ₛ 
            OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
            scall OS_EventTaskPostWait (pevent′ :: message′ :: nil);ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            ENTER_CRITICAL;ₛ
            If (OSTCBCur′→OSTCBEventPtr !=ₑ NULL) {
                OS_EventPostTO(­pevent′­);ₛ
                OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ OSTCBCur′→OSTCBBitY;ₛ
                OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ 
                EXIT_CRITICAL;ₛ
                RETURN ′OS_TIMEOUT 
            };ₛ
            OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        };ₛ
        ∗(pq′→OSQIn) =ₑ message′;ₛ
        ++ (pq′→OSQIn);ₛ
        ++ (pq′→OSQEntries);ₛ
        If (pq′→OSQIn ==ₑ pq′→OSQEnd) {
            pq′→OSQIn =ₑ pq′→OSQStart
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR 
 }· .
 
Close Scope code_scope.
