
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

Definition mq_create_impl :=
Int32  ·mq_create·(⌞mq_blockflag @ Int32; max_msgs @ Int32; msg_size @ Int32; waitq_type @ Int32 ⌟)··{
        ⌞ 
          pos @ Int32;
          x @ Int8s; 
          y @ Int8s;
          p @ OS_EVENT ∗
        ⌟; 

          If( max_msgs′ <ₑ ′0){
              RETURN ′-1 
          };ₛ

          If( msg_size′ <ₑ ′0   ){
              RETURN ′-1 
          };ₛ
          If( mq_blockflag′ !=ₑ ′0 &&ₑ mq_blockflag′ !=ₑ ′O_NONBLOCK ){
              RETURN ′-1 
          };ₛ
          If(  waitq_type′ !=ₑ ′PTHREAD_WAITQ_PRIO ){
              RETURN ′-1 
          };ₛ

          ENTER_CRITICAL;ₛ
          If (OSIntNesting′ >ₑ ′0){
          EXIT_CRITICAL;ₛ
          RETURN ′-1
          };ₛ
          EXIT_CRITICAL;ₛ
         
        ENTER_CRITICAL;ₛ
        y′ =ᶠ getFreePos(·′2·);ₛ
        pos′ =ₑ 〈Int32〉 y′;ₛ
        If(pos′ ==ₑ ′255){
(*         If(pos′ <ₑ ′0){ *)
            EXIT_CRITICAL;ₛ 
            RETURN  ′-1
        };ₛ
          efield (Mq_Attr′[pos′]) pevent =ₑ 〈OS_EVENT ∗〉PlaceHolder;ₛ
          EXIT_CRITICAL;ₛ 
          
          p′ =ᶠ OSQCreate(·〈Int16u〉max_msgs′·);ₛ
          ENTER_CRITICAL;ₛ
          efield (Mq_Attr′[pos′]) pevent =ₑ  p′;ₛ
          OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ
          OSTCBCur′→__OSTskEvLoc =ₑ ′__EvLoc_normal;ₛ
          EXIT_CRITICAL;ₛ

          If (p′ ==ₑ NULL){
              RETURN  ′-1
          };ₛ

          ENTER_CRITICAL;ₛ
          efield (Mq_Attr′[pos′]) mq_maxmsg =ₑ max_msgs′;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          efield (Mq_Attr′[pos′]) mq_msgsize =ₑ msg_size′;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          efield (Mq_Attr′[pos′]) mq_flags =ₑ mq_blockflag′;ₛ 
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          efield (Mq_Attr′[pos′]) mq_waittype =ₑ ′PTHREAD_WAITQ_PRIO;ₛ
          EXIT_CRITICAL;ₛ 
          RETURN  pos′ 
 }· .

Definition mq_delete_impl :=
 Int8s ·mq_delete·(⌞mqdes @ mqd_t ⌟)··{
        ⌞
          (* err @ Int8u;  *)
          p @ OS_EVENT ∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
       ⌟;

        (* errno′ =ₑ ′0;ₛ *)
        If (mqdes′ <ₑ ′0 ||ₑ mqdes′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3 )
        {
            (* errno′ =ₑ ′EBADF;ₛ *)
            RETURN ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

(*       If ((efield (ederef (Mq_Attr′[mqdes′])) pevent) ==ₑ ′0) *)
        ENTER_CRITICAL;ₛ
        If (efield (Mq_Attr′[mqdes′]) pevent ==ₑ NULL)
        {
            (* errno′ =ₑ ′ENOENT;ₛ *)
            EXIT_CRITICAL;ₛ
            RETURN ′-1
        };ₛ
        If (OSIntNesting′ >ₑ ′0) {
            (* errno′ =ₑ ′ECALLEDINISR;ₛ *)
            EXIT_CRITICAL;ₛ
            RETURN ′-1
        };ₛ
        p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ  
        efield (Mq_Attr′[mqdes′]) pevent =ₑ NULL;ₛ  
        OSTCBCur′→__OSTskQPtr =ₑ  p′;ₛ
        OSTCBCur′→__OSTskEvLoc =ₑ  ′__EvLoc_ecbdel;ₛ 
        EXIT_CRITICAL;ₛ

        OSQDel(­p′­);ₛ 

        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskEvLoc =ₑ  ′__EvLoc_normal;ₛ 
        (* OSTCBCur′→__OSTskQPtr =ₑ  NULL;ₛ *) 
        EXIT_CRITICAL;ₛ

        RETURN ′0 
 }· . 

Definition mq_receive_impl :=
ssize_t ·mq_receive·(⌞mqdes @ mqd_t ;  msg_ptr @ char_t∗ ; msg_len @ size_t ; pmsgprio @ unsigned_t∗ ; err @ Int8u∗⌟)··{
        ⌞ 
          ret @ char_t∗;
          x @ Int8s; 
          y @ Int32;
          z @ Int32;
          p @ OS_EVENT∗ ; 
          p1 @ Void ∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
       ⌟; 
        
          If(mqdes′ <ₑ ′0 ||ₑ mqdes′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3 ){
              RETURN ′-1 
          };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        y′ =ₑ efield (Mq_Attr′[mqdes′]) mq_msgsize;ₛ
        EXIT_CRITICAL;ₛ
        If(msg_len′ >ₑ y′ ){
         RETURN ′-1 
        };ₛ

        x′ =ᶠ UserAddrCheck(·〈Int32u∗〉msg_ptr′·);ₛ 
        If(x′ ==ₑ ′0 ){
           RETURN ′-1 
        };ₛ
          

        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
        EXIT_CRITICAL;ₛ
        If (p′ ==ₑ NULL) {
          RETURN ′-1        
        };ₛ
        
         ENTER_CRITICAL;ₛ
         z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
         EXIT_CRITICAL;ₛ
         If( z′ !=ₑ ′0 &&ₑ  z′ !=ₑ ′O_NONBLOCK){
             RETURN ′-1 
         };ₛ
    (*code about os_capability could be added here*)
        ENTER_CRITICAL;ₛ
        z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
        EXIT_CRITICAL;ₛ
        IF( z′ ==ₑ ′0 ){
          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
          OSTCBCur′→__OSTskQPtr =ₑ p′;ₛ 
          EXIT_CRITICAL;ₛ
          p1′ =ᶠ OSQPend(·p′ ,  〈Int16u〉 ′0 , err′·);ₛ
          ENTER_CRITICAL;ₛ
          OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
          EXIT_CRITICAL
        }ELSE{
              ENTER_CRITICAL;ₛ
              p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
              OSTCBCur′→__OSTskQPtr =ₑ p′;ₛ  
              EXIT_CRITICAL;ₛ
              p1′ =ᶠ OSQAccept(·p′ ·);ₛ
              ENTER_CRITICAL;ₛ
              OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
              EXIT_CRITICAL
        };ₛ
        ret′ =ₑ 〈char_t∗〉 p1′ ;ₛ
        ENTER_CRITICAL;ₛ
        z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
        EXIT_CRITICAL;ₛ
        If(ret′ ==ₑ NULL &&ₑ  z′ ==ₑ ′1 ){
             RETURN ′-1 
         };ₛ
         If(ret′ ==ₑ NULL &&ₑ  z′ ==ₑ ′0 ){
             RETURN ′-1 
         };ₛ
          
         IF(ret′ ==ₑ NULL){
             RETURN ′-1
         }ELSE{
             memcpy4(­〈Void ∗〉msg_ptr′ , 〈Void ∗〉ret′ , msg_len′ ­);ₛ 
             RETURN msg_len′
         }
 
 }· . 

Definition mq_timedreceive_impl :=
ssize_t ·mq_timedreceive·(⌞mqdes @ mqd_t ;  msg_ptr @ char_t∗ ; msg_len @ size_t ; pmsgprio @ unsigned_t∗ ; abs_timeout @ (*const*) Int16u; err @ Int8u∗⌟)··{
        ⌞ 
          ret @ char_t∗;
          x @ Int8s; 
          y @ Int32;
          z @ Int32;
          p @ OS_EVENT∗ ; 
          p1 @ Void ∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
       ⌟; 
        
      If (mqdes′ <ₑ ′0 ||ₑ mqdes′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3 ) {
         RETURN ′-1 
      };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

      If (abs_timeout′ ==ₑ ′0 ||ₑ abs_timeout′ >ₑ ′65535) {
        RETURN ′-1
      };ₛ
	    
      ENTER_CRITICAL;ₛ
      y′ =ₑ efield (Mq_Attr′[mqdes′]) mq_msgsize;ₛ
      EXIT_CRITICAL;ₛ
      If(msg_len′ >ₑ y′ ){
         RETURN ′-1 
      };ₛ

      x′ =ᶠ UserAddrCheck(·〈Int32u∗〉msg_ptr′·);ₛ 
      If(x′ ==ₑ ′0 ){
         RETURN ′-1 
      };ₛ
          
      ENTER_CRITICAL;ₛ
      p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
      EXIT_CRITICAL;ₛ
      If (p′ ==ₑ NULL) {
        RETURN ′-1        
      };ₛ
        
       ENTER_CRITICAL;ₛ
       z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
       EXIT_CRITICAL;ₛ
       If( z′ !=ₑ ′0 &&ₑ  z′ !=ₑ ′O_NONBLOCK){
           RETURN ′-1 
       };ₛ
    (*code about os_capability could be added here*)
        ENTER_CRITICAL;ₛ
        z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
        EXIT_CRITICAL;ₛ
        IF( z′ ==ₑ ′0 ){
        ENTER_CRITICAL;ₛ
        p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
        OSTCBCur′→__OSTskQPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ
        p1′ =ᶠ OSQPend(·p′ , abs_timeout′ , err′·);ₛ 
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
        EXIT_CRITICAL
          }ELSE{
              ENTER_CRITICAL;ₛ
              p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
              OSTCBCur′→__OSTskQPtr =ₑ p′;ₛ 
              EXIT_CRITICAL;ₛ
              p1′ =ᶠ OSQAccept(·p′ ·);ₛ 
              ENTER_CRITICAL;ₛ
              OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
              EXIT_CRITICAL
          };ₛ
        ret′ =ₑ 〈char_t∗〉 p1′ ;ₛ
        ENTER_CRITICAL;ₛ
        z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
        EXIT_CRITICAL;ₛ
        If(ret′ ==ₑ NULL &&ₑ  z′ ==ₑ ′1 ){
             RETURN ′-1 
         };ₛ
         If(ret′ ==ₑ NULL &&ₑ  z′ ==ₑ ′0 ){
             RETURN ′-1 
         };ₛ
          
          IF(ret′ ==ₑ NULL){
              RETURN ′-1
          }ELSE{
              memcpy4(­〈Void ∗〉msg_ptr′ , 〈Void ∗〉ret′ , msg_len′ ­);ₛ 
              RETURN msg_len′
          }
 
 }· . 

Definition rr: ident := 788%Z.

Definition mq_send_impl :=
Int32  ·mq_send·(⌞mqdes @ mqd_t; msg_ptr @ char∗; msg_len @ size_t; msgprio @ unsigned ⌟)··{
        ⌞ 
          ret @ Int32;
          x @ Int8s; 
          y @ Int32;
          z @ Int32;
          p @ OS_EVENT∗;
          rr @ Int8u;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟; 
        
          If(mqdes′ <ₑ ′0 ||ₑ mqdes′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3 ){
              RETURN ′-1 
          };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

          ENTER_CRITICAL;ₛ
          y′ =ₑ efield (Mq_Attr′[mqdes′]) mq_msgsize;ₛ
          EXIT_CRITICAL;ₛ
          If(msg_len′ >ₑ y′ ){
              RETURN ′-1 
          };ₛ
          
          x′ =ᶠ UserAddrCheck(·〈Int32u∗〉msg_ptr′·);ₛ 
          If(x′ ==ₑ ′0 ){
              RETURN ′-1 
          };ₛ
          
          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
          EXIT_CRITICAL;ₛ
          If (p′ ==ₑ NULL) {
            RETURN ′-1        
          };ₛ
        
          ENTER_CRITICAL;ₛ
          z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
          EXIT_CRITICAL;ₛ
          If( z′ !=ₑ ′0 &&ₑ  z′ !=ₑ ′O_NONBLOCK){
              RETURN ′-1 
          };ₛ
          
          ENTER_CRITICAL;ₛ
          z′ =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
          EXIT_CRITICAL;ₛ
          IF( z′ ==ₑ ′0 ){
            ENTER_CRITICAL;ₛ
            p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
            OSTCBCur′→__OSTskQPtr =ₑ p′;ₛ 
            EXIT_CRITICAL;ₛ
            rr′ =ᶠ OSQTimedPost(·p′ , 〈Int16u〉(′0) , 〈Void ∗〉msg_ptr′·);ₛ
            ENTER_CRITICAL;ₛ
            OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
            EXIT_CRITICAL
          }ELSE{
              ENTER_CRITICAL;ₛ
              p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
              OSTCBCur′→__OSTskQPtr =ₑ p′;ₛ 
              EXIT_CRITICAL;ₛ
              rr′ =ᶠ OSQPost(·p′ ,〈Void ∗〉msg_ptr′·);ₛ
              ENTER_CRITICAL;ₛ
              OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
              EXIT_CRITICAL
          };ₛ
          ret′ =ₑ 〈Int32〉 rr′ ;ₛ
          If(ret′ ==ₑ ′OS_Q_FULL){
                  RETURN ′-1 
              };ₛ
          
          IF(ret′ ==ₑ ′OS_NO_ERR){
              RETURN ′0
          }ELSE{
              RETURN ′-1 
          }
 }· .

Definition mq_getinfo_impl := 
 Void ∗ ·mq_getinfo·(⌞mqdes @ mqd_t ; mq_info @ mq_info_t∗; pdata @ OS_Q_DATA ∗⌟)··{
        ⌞ 
          i @ unsigned_int;
          Val_uacheck @ Int8s; 
          p @ OS_EVENT∗ ;
          Val_osqquery @  Int8u;
          ptcb @ OS_TCB∗;
          x @ Int8u∗;
          y @ Int8u∗;
         temp_dom @ Int8s;
         temp_num @ Int8u
        ⌟; 
        
          If(mqdes′ <ₑ ′0 ||ₑ mqdes′ ≥ ′OS_USER_MAX_EVENTS ÷ ′3 ){
              RETURN ′-1 
          };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ <ₑ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  temp_dom′)){
         RETURN  ′-1
        };ₛ

        ENTER_CRITICAL;ₛ
        temp_dom′ =ₑ Domain2Index′[ksCurDomain′];ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        temp_num′ =ₑ Core_partition_num′;ₛ
        EXIT_CRITICAL;ₛ
        If (mqdes′ ≥ ((′OS_USER_MAX_EVENTS ÷ ′3)÷ temp_num′ ×  (temp_dom′+ₑ ′1))){
         RETURN  ′-1
        };ₛ

          Val_uacheck′ =ᶠ UserAddrCheck(·〈Int32u∗〉mq_info′·);ₛ 
          If (Val_uacheck′ ==ₑ ′0){
              RETURN ′-1 
          };ₛ
          
           ENTER_CRITICAL;ₛ
           p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
           EXIT_CRITICAL;ₛ
          
          If (p′ ==ₑ NULL){
              RETURN ′-1 
          };ₛ
          
          ENTER_CRITICAL;ₛ
          p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ
          EXIT_CRITICAL;ₛ
                    
          Val_osqquery′ =ᶠ OSQQuery(·p′, pdata′·);ₛ 
          If (Val_osqquery′!=ₑ ′0){
              RETURN ′-1 
          };ₛ
          ENTER_CRITICAL;ₛ
          mq_info′→mq_curmsgs =ₑ pdata′→OSNMsgs;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          mq_info′→mq_maxmsg =ₑ pdata′→OSQSize;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          mq_info′→mq_msgsize =ₑ efield (Mq_Attr′[mqdes′]) mq_msgsize;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          mq_info′→mq_waittype =ₑ efield (Mq_Attr′[mqdes′]) mq_waittype;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          mq_info′→mq_flags =ₑ efield (Mq_Attr′[mqdes′]) mq_flags;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          mq_info′→task_blocked =ₑ ′0;ₛ
          EXIT_CRITICAL;ₛ
          
          ENTER_CRITICAL;ₛ
          If ( efield (Mq_Attr′[mqdes′]) pevent ==ₑ NULL){
               EXIT_CRITICAL;ₛ
               RETURN  ′-1
          };ₛ
        
          ptcb′ =ₑ OSTCBList′;ₛ
          WHILE (ptcb′) {
            If(ptcb′→OSTCBEventPtr ==ₑ  efield (Mq_Attr′[mqdes′]) pevent){
                  mq_info′→task_blocked =ₑ 〈Int8u〉(mq_info′→task_blocked +ₑ ′1)
            };ₛ
            ptcb′ =ₑ ptcb′→OSTCBNext
          };ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          x′ =ₑ mq_info′→OSEventTbl;ₛ
          EXIT_CRITICAL;ₛ
          ENTER_CRITICAL;ₛ
          y′ =ₑ  pdata′→OSEventTbl;ₛ
          EXIT_CRITICAL;ₛ
          memcpy4(­〈Void ∗〉x′ , 〈Void ∗〉y′ , ′OS_EVENT_TBL_SIZE × ′1 ­);ₛ  
         
          RETURN  ′0 

 }· .

Close Scope code_scope.
