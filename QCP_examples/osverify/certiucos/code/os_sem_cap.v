
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import useraddrcheck. 

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

Definition sem_trywait_impl := 
Int32 ·sem_trywait·(⌞sem @ sem_t∗⌟)··{  
        ⌞
         pos @ Int32;
         x @ Int8s;
         y @ Int16u;
         p @ OS_EVENT∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
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
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ

        y′ =ᶠ OSSemAccept(·p′·);ₛ

        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ 
        EXIT_CRITICAL;ₛ

        If (y′ >ₑ ′0  ){
            RETURN  ′0
        };ₛ
        RETURN  ′-1
}· .

Definition sem_init_impl :=
Int32 ·sem_init·(⌞sem @ sem_t∗ ; value @ unsigned_int⌟)··{ 
        ⌞
         pos @ Int32;
         x @ Int8s;
         y @ Int8s;
         p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ
            If (OSIntNesting′ >ₑ ′0) {
                EXIT_CRITICAL;ₛ
                RETURN  ′-1
            };ₛ
            EXIT_CRITICAL;ₛ
        x′ =ᶠ UserAddrCheck(·〈Int32u∗〉sem′·);ₛ
        If(x′  ==ₑ ′0 ||ₑ value′  >ₑ ′SEM_VALUE_MAX){
            RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        y′ =ᶠ getFreePos(·′0·);ₛ
        pos′ =ₑ 〈Int32〉 y′;ₛ
        If(pos′ ==ₑ ′255){
(*         If(pos′ <ₑ ′0){ *)
            EXIT_CRITICAL;ₛ 
            RETURN  ′-1
        };ₛ
        efield (Sem_info′[pos′]) pevent =ₑ 〈OS_EVENT ∗〉 PlaceHolder;ₛ
        EXIT_CRITICAL;ₛ

        p′ =ᶠ OSSemCreate(· 〈Int16u〉value′ ·);ₛ
        ENTER_CRITICAL;ₛ
        efield (Sem_info′[pos′]) pevent =ₑ  p′;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
        OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_normal;ₛ  
        EXIT_CRITICAL;ₛ

        If (p′ ==ₑ NULL){
            RETURN  ′-1
        };ₛ

(*OS_CAPABILITY_EN*)
        ENTER_CRITICAL;ₛ
        efield (Sem_info′[pos′]) sem_type =ₑ ′SEM_COUNTING;ₛ
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        efield (Sem_info′[pos′]) tasks_blocked =ₑ ′0;ₛ
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        ∗sem′ =ₑ  pos′;ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′0

}· .

Definition sem_init_bin_impl :=
Int32 ·sem_init_bin·(⌞sem @ sem_t∗ ; value @ unsigned_int⌟)··{ 
        ⌞
         pos @ Int32;
         x @ Int8s;
         y @ Int8s;
         p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ
            If (OSIntNesting′ >ₑ ′0) {
                EXIT_CRITICAL;ₛ
                RETURN  ′-1
            };ₛ
         EXIT_CRITICAL;ₛ

        x′ =ᶠ UserAddrCheck(·〈Int32u∗〉sem′·);ₛ
        If(x′  ==ₑ ′0 ||ₑ value′ <ₑ ′0  ||ₑ value′  >ₑ ′1){
            RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        y′ =ᶠ getFreePos(·′0·);ₛ
        pos′ =ₑ 〈Int32〉 y′;ₛ
        If(pos′ ==ₑ ′255){
(*         If(pos′ <ₑ ′0){ *)
            EXIT_CRITICAL;ₛ 
            RETURN  ′-1
        };ₛ
        efield (Sem_info′[pos′]) pevent =ₑ 〈OS_EVENT ∗〉 PlaceHolder;ₛ
        EXIT_CRITICAL;ₛ

        p′ =ᶠ OSSemCreate(· 〈Int16u〉value′ ·);ₛ
        ENTER_CRITICAL;ₛ
        efield (Sem_info′[pos′]) pevent =ₑ  p′;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
        OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_normal;ₛ  
        EXIT_CRITICAL;ₛ

        If (p′ ==ₑ NULL){
            RETURN  ′-1
        };ₛ

(*OS_CAPABILITY_EN*)
        ENTER_CRITICAL;ₛ
        efield (Sem_info′[pos′]) sem_type =ₑ ′SEM_BINARY;ₛ 
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        efield (Sem_info′[pos′]) tasks_blocked =ₑ ′0;ₛ
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        ∗sem′ =ₑ  pos′;ₛ
        EXIT_CRITICAL;ₛ
        RETURN  ′0

}· .

Definition sem_destroy_impl :=
Int32 ·sem_destroy·(⌞sem @ sem_t∗⌟)··{
        ⌞
         pos @ Int32;
         err @ Int8u;
         x @ Int8s;
         p @ OS_EVENT∗
        ⌟;

        ENTER_CRITICAL;ₛ
        x′ =ᶠ UserAddrCheckCrit(·〈Int32u∗〉sem′·);ₛ
        IF(x′  ==ₑ ′0 ){
            pos′ =ₑ  ′-1
        } ELSE {
            pos′ =ₑ  ∗sem′
        };ₛ
        If (pos′ <ₑ ′0 ||ₑ pos′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3){
            EXIT_CRITICAL;ₛ
            RETURN  ′-1
        };ₛ
        If (efield (Sem_info′[pos′]) pevent ==ₑ NULL) {
            EXIT_CRITICAL;ₛ
            RETURN  ′-1
        };ₛ

        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ Core_partition_num′ ×  (Domain2Index′[ksCurDomain′])) ||ₑ
              pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ Core_partition_num′ ×  ((Domain2Index′[ksCurDomain′])+ₑ ′1))){
         EXIT_CRITICAL;ₛ
         RETURN  ′-1
        };ₛ

        If(efield (Sem_info′[pos′]) pevent→OSEventGrp !=ₑ ′0 ||ₑ OSIntNesting′ >ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′-1
        };ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        efield (Sem_info′[pos′]) pevent =ₑ 〈OS_EVENT ∗〉 NULL;ₛ

        OSSemDel(­ p′ ­);ₛ
        EXIT_CRITICAL;ₛ

        RETURN  ′0
}· .

Definition sem_wait_impl := 
Int32 ·sem_wait·(⌞sem @ sem_t∗⌟)··{  
        ⌞
         pos @ Int32;
         x @ Int8s;
         err @ Int8u;
         p @ OS_EVENT∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟;

        ENTER_CRITICAL;ₛ
        If (OSIntNesting′ >ₑ ′0){
         EXIT_CRITICAL;ₛ
         RETURN ′-1
         };ₛ
         EXIT_CRITICAL;ₛ

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
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ


        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ p′;ₛ
        EXIT_CRITICAL;ₛ

        err′ =ᶠ OSSemPend(· p′,  〈Int16u〉′0 ·);ₛ 

        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ

        If (err′ >ₑ ′0  ){
            RETURN  ′-1
        };ₛ
        RETURN  ′0
}· .

Definition sem_timedwait_impl :=
Int32 ·sem_timedwait·(⌞sem @ sem_t∗ ;abs_timeout @ Int16u⌟)··{ 
        ⌞
         pos @ Int32;
         x @ Int8s;
         err @ Int8u;
         p @ OS_EVENT∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟;
        
        ENTER_CRITICAL;ₛ
        If (OSIntNesting′ >ₑ ′0){
         EXIT_CRITICAL;ₛ
         RETURN ′-1
         };ₛ
         EXIT_CRITICAL;ₛ

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
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ


        If(abs_timeout′ ==ₑ ′0 ||ₑ  abs_timeout′  >ₑ ′65535){
           RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ p′;ₛ
        EXIT_CRITICAL;ₛ
        
        err′ =ᶠ OSSemPend(· p′,  abs_timeout′ ·);ₛ
        
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ
      If (err′ ==ₑ ′OS_TIMEOUT){ 
          RETURN  ′-1
      };ₛ
      If (err′ >ₑ ′0){
          RETURN  ′-1
      };ₛ
        RETURN  ′0
}· .

(* Definition sem_signal_new := 302%Z.  *)

Definition sem_signal_impl :=
Int32 ·sem_signal·(⌞sem @ sem_t∗⌟)··{  (*第二个参数是const struct *)  
        ⌞
         pos @ Int32;
         x @ Int8s; 
         y @ Int8u;
         z @ Int32; 
         p @ OS_EVENT∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟;

        x′ =ᶠ UserAddrCheck(·〈Int32u∗〉sem′·);ₛ
        IF (x′  ==ₑ ′0 ) {
            pos′ =ₑ  ′-1
        } ELSE {
            ENTER_CRITICAL;ₛ
            pos′ =ₑ  ∗sem′;ₛ
            EXIT_CRITICAL
        };ₛ 
        If (pos′ <ₑ ′0 ||ₑ pos′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3 ){
           RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
            RETURN ′-1        
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ


        ENTER_CRITICAL;ₛ
        z′ =ₑ efield (Sem_info′[pos′]) sem_type ;ₛ
        EXIT_CRITICAL;ₛ
        If (z′  ==ₑ ′SEM_BINARY) {
            ENTER_CRITICAL;ₛ
            p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ p′;ₛ 
            EXIT_CRITICAL;ₛ
            y′ =ᶠ OSSemPostBin(·p′·);ₛ
            ENTER_CRITICAL;ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ 
            EXIT_CRITICAL;ₛ
            IF (y′ ==ₑ ′0){
              RETURN  ′0
            } ELSE {
              RETURN  ′-1
            }
        };ₛ

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ
        y′ =ᶠ OSSemPost(·p′·);ₛ
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ 
        EXIT_CRITICAL;ₛ
        IF (y′ ==ₑ ′0){
            RETURN  ′0
        } ELSE{
            RETURN  ′-1
        }
}· .

Definition sem_flush_impl :=
Int32 ·sem_flush·(⌞sem @ sem_t∗⌟)··{ 
        ⌞
         pos @ Int32;
         x @ Int8s;
         y @ Int16u;
         p @ OS_EVENT ∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟;

        ENTER_CRITICAL;ₛ
        If (OSIntNesting′ >ₑ ′0){
         EXIT_CRITICAL;ₛ
         RETURN ′-1
         };ₛ
         EXIT_CRITICAL;ₛ

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
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ


       ENTER_CRITICAL;ₛ
        If (efield (Sem_info′[pos′]) pevent !=ₑ NULL) {
            If (efield (Sem_info′[pos′]) pevent→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM) {
            EXIT_CRITICAL;ₛ
            RETURN ′-1
            }
        };ₛ
        EXIT_CRITICAL;ₛ

(*OS_CAPABILITY_EN*)
        ENTER_CRITICAL;ₛ
        WHILE (efield (Sem_info′[pos′]) pevent !=ₑ NULL &&ₑ efield (Sem_info′[pos′]) pevent→OSEventGrp !=ₑ ′0) 
       {
            y′ =ₑ ′OS_STAT_SEM;ₛ 
           OS_EventTaskRdy(­efield (Sem_info′[pos′]) pevent, ecast NULL (Tptr Tvoid), y′­)
        };ₛ
        EXIT_CRITICAL;ₛ

        OS_Sched(­);ₛ
        RETURN  ′0

}· .

Definition sem_getvalue_impl :=
Int32 ·sem_getvalue·(⌞sem @ sem_t∗ ; sval @Int32∗⌟)··{  (*第二个参数是const struct *)
        ⌞
         pos @ Int32;
         x @ Int8s;
         y @ Int8s;
         p @ OS_EVENT∗;
         ptcb @ OS_TCB∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟;
        
         ENTER_CRITICAL;ₛ
         ∗sval′ =ₑ ′0;ₛ
         EXIT_CRITICAL;ₛ
(*          errno′ =ₑ ′0;ₛ *)
         x′ =ᶠ UserAddrCheck(·〈Int32u∗〉sem′·);ₛ
         IF(x′  ==ₑ ′0 ){
             pos′ =ₑ  ′-1
         }
         ELSE{
             ENTER_CRITICAL;ₛ
             pos′ =ₑ  ∗sem′;ₛ
             EXIT_CRITICAL
         };ₛ

         If (pos′ <ₑ ′0 ||ₑ pos′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3){
(*            errno′ =ₑ EINVAL′;ₛ *)
           RETURN  ′-1
         };ₛ

         y′ =ᶠ UserAddrCheck(·〈Int32u∗〉sval′·);ₛ
         If (y′ ==ₑ ′0){
           RETURN  ′-1
         };ₛ
         
         ENTER_CRITICAL;ₛ
         p′ =ₑ efield (Sem_info′[pos′]) pevent;ₛ
         EXIT_CRITICAL;ₛ
         If ( p′ ==ₑ NULL){
(*            errno′ =ₑ EINVAL′;ₛ *)
           RETURN  ′-1
         };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (pos′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

         ENTER_CRITICAL;ₛ
         If ( efield (Sem_info′[pos′]) pevent ==ₑ NULL){
               EXIT_CRITICAL;ₛ
               RETURN  ′-1
        };ₛ
        
        If( efield (Sem_info′[pos′]) pevent→OSEventCnt >ₑ ′0){
              ∗sval′ =ₑ efield (Sem_info′[pos′]) pevent→OSEventCnt;ₛ
               EXIT_CRITICAL;ₛ
               RETURN  ′0
        };ₛ

         (*while*)
        ptcb′ =ₑ OSTCBList′;ₛ
        WHILE (ptcb′) {
               If(ptcb′→OSTCBEventPtr ==ₑ  efield (Sem_info′[pos′]) pevent){
                                 −−(∗sval′)
                                   };ₛ
               ptcb′ =ₑ ptcb′→OSTCBNext
         };ₛ
        EXIT_CRITICAL;ₛ
        
        RETURN  ′0
}· .

Close Scope code_scope.
