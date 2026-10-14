Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.


Open Scope code_scope.

Definition OSSampleSendToDomain_impl := 
    Int8u ·OSSampleSendToDomain·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ; 
                        inTime @ Int32u⌟)··{
        ⌞ ⌟; 
        (* ENTER_CRITICAL;ₛ *)
        port_ptr′ → msgInTick =ₑ inTime′;ₛ
        port_ptr′ → msgOutTick =ₑ OSTime′;ₛ
        port_ptr′ → OSQStart → len  =ₑ msg_ptr′ → len;ₛ
        memcpy(­ &ₐ (port_ptr′ → OSQStart → data[′0]), &ₐ (msg_ptr′ → data[′0]),  〈 Tint32 〉 msg_ptr′ → len ­);ₛ 
        (* memcpy(­  port_ptr′ → OSQStart → data, msg_ptr′ → data , msg_ptr′ → len ­);ₛ  *)
        If (′DNUM !=ₑ port_ptr′ → coreNum )

        {

        GENERATEIPC(port_ptr′ → coreNum ,  ′ GET_PORT_MESSAGE)

        };ₛ
        (* EXIT_CRITICAL;ₛ *)

        RETURN ′OS_NO_ERR
    }·.


(* INT8U OSSampleSendToDomain(OS_Port * port, OSMsg * msg, INT32U inTime)
{
#if CACHE_ENABLE > 0
		CACHE_Wait wait = CACHE_WAIT;
#endif
	OS_ENTER_CRITICAL();
	port->msgInTick  = inTime;
	port->msgOutTick  = OSTime;

	port->OSQStart->len = msg->len;
	memcpy(port->OSQStart->data,msg->data,msg->len);
#if CACHE_ENABLE > 0
    CACHE_wbL1d(port,128,CACHE_NOWAIT);
    CACHE_wbL1d(port->OSQStart,128,wait);
#endif
//	*port->OSQStart = *msg;
	if (DNUM != port->coreNum) {
		generateIPC(port->coreNum,GET_PORT_MESSAGE);
	}
	OS_EXIT_CRITICAL();
	return (OS_NO_ERR);
} *)

Definition OSPortAcceptWithoutCheck_impl := 
    Int8u ·OSPortAcceptWithoutCheck·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ kport @ OS_K_Port ∗ ;
          semaphore @ Int8u ;
          resource_get_res @ Int8u⌟; 
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → direction !=ₑ ′ DESTINATION )
        {
            EXIT_CRITICAL;ₛ
            RETURN  (〈 Int8u 〉 ′OS_PORT_ERR_DIRECTION_TYPE)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (msg_ptr′ ==ₑ 〈 OSMsg_t∗ 〉NULL )
        {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_PORT_MSG_ARG_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ
        (* msg_ptr′ → len =ₑ ′0;ₛ *) (* 这一句没有办法得到len 这个地址的权限 *)
        ENTER_CRITICAL;ₛ
        (* 分区机制保证其它核无非修改该端口 *)
        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ
        If (kport′ ==ₑ 〈 OS_K_Port∗ 〉NULL )
        {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_PORT_MSG_ARG_NULL)
        };ₛ
        If (kport′ → channel ==ₑ 〈 OS_Channel ∗ 〉NULL) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_ERR_PORT_NO_CHANNEL)
        };ₛ
        semaphore′ =ₑ (〈 OS_Channel ∗ 〉 kport′ → channel) →semaphore;ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
    	    (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
            CSLSEMACC (semaphore′, resource_get_res′);ₛ
            If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0){
                EXIT_CRITICAL;ₛ
                RETURN (〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED)
            }
        };ₛ
        IF (port_ptr′→mode ==ₑ ′QUEUE) {
            If (port_ptr′→OSQEntries >ₑ ′0) {                    (* See if any messages in the queue                   *)
                msg_ptr′ →len =ₑ port_ptr′ → OSQOut → len;ₛ
                memcpy(­ &ₐ (msg_ptr′ → data[′0]), &ₐ (port_ptr′ → OSQOut → data[′0]),  〈 Tint32 〉 port_ptr′ → OSQOut → len ­);ₛ 
                port_ptr′ →OSQOut =ₑ port_ptr′ →OSQOut +ₑ ′1;ₛ
                port_ptr′ →OSQEntries =ₑ port_ptr′ →OSQEntries −  (〈 Int16u 〉 ′1);ₛ                        (* Update the number of entries in the queue   *)     
                If (port_ptr′ → OSQOut ==ₑ port_ptr ′ → OSQEnd) {          (* Wrap OUT pointer if we are at the end of the queue *)
                    port_ptr′ → OSQOut =ₑ port_ptr′ → OSQStart
                }
            }
        } ELSE { IF (port_ptr′ → mode ==ₑ ′ SAMPLE)  {
            msg_ptr ′ → len =ₑ port_ptr′ → OSQStart → len;ₛ
            memcpy(­ &ₐ (msg_ptr′ → data[′0]), &ₐ (port_ptr′ → OSQStart → data[′0]),  〈 Tint32 〉 port_ptr′ → OSQStart → len ­)
            } ELSE {
                If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                    (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                    CSLSEMREL (semaphore′ ) 
                };ₛ
                EXIT_CRITICAL;ₛ
                RETURN (〈 Int8u 〉 ′OS_PORT_ERR_TYPE)
            }
        };ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
            CSLSEMREL (semaphore′ ) 
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR
    }·.

Definition SamplePortPost_impl := 
    Int8u ·SamplePortPost·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ kport @ OS_K_Port ∗ ;
          dstKPort @ OS_K_Port ∗ ;
          channel @ OS_Channel ∗ ;
          semaphore @ Int8u ;
          error @Int8u ;
          resource_get_res @ Int8u ⌟; 
        (* #if OS_CAPABILITY_EN > 0
            OS_CSpace *pCSpace;

            pCSpace = OSCSpacePrioTbl[OSPrioCur];
            if((pCSpace->cnode.slot[CAP_PORT_CLASS].capability.content.category.category_right & PORT_POST_CAP) == 0)
            {
                return USER_CAPABILITY_NONE;
            }
        #endif *)
        kport′ =ₑ 〈 OS_K_Port∗ 〉 NULL;ₛ
        dstKPort′ =ₑ 〈 OS_K_Port∗ 〉 NULL;ₛ
        channel′ =ₑ 〈 OS_Channel ∗ 〉NULL;ₛ
        semaphore′ =ₑ ′DEFAULT_CHANNLE_SEMAPHROE;ₛ
        error′ =ₑ ′OS_NO_ERR;ₛ
        resource_get_res′ =ₑ ′0;ₛ

        ENTER_CRITICAL;ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port∗ 〉 NULL) {                    (* Validate 'pevent'                             *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′→domain) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (msg_ptr′ ==ₑ NULL) {                           (* Make sure we are not posting a NULL pointer   *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_POST_NULL_PTR)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → direction !=ₑ ′SOURCE ||ₑ port_ptr′ → mode !=ₑ ′SAMPLE ) {     (* Validate event block type                     *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_TYPE)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If ( port_ptr′ → portID ≥ ′PORT_NUMS) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ID_INVALID)
        };ₛ
        EXIT_CRITICAL;ₛ
        (* 写入消息 *)
        (* ENTER_CRITICAL;ₛ
        port_ptr′ → OSQStart → len =ₑ msg_ptr ′ → len;ₛ
        memcpy(­  port_ptr′ → OSQStart → data, msg_ptr′ → data , msg_ptr′ → len ­);ₛ 
        port_ptr′ → msgInTick =ₑ OSTime′;ₛ
        EXIT_CRITICAL;ₛ *)
        (* 获取通道结构体，查看是否有目的分区的端口，若没有则将消息加入消息队列中 *)
        ENTER_CRITICAL;ₛ
        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ
        If (kport′ ==ₑ 〈 OS_K_Port∗ 〉NULL )
        {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_ERR_PORT_UNBIND)
        };ₛ
        If (kport′ → channel ==ₑ 〈 OS_Channel ∗ 〉NULL) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_ERR_PORT_NO_CHANNEL)
        };ₛ

        channel′ =ₑ kport′ → channel;ₛ

        If (channel′ ==ₑ 〈 OS_Channel ∗ 〉NULL) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u∗ 〉′ OS_ERR_PORT_NO_CHANNEL)
        };ₛ 
        semaphore′ =ₑ channel′ → semaphore;ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
            CSLSEMACC (semaphore′, resource_get_res′);ₛ
            If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0){
                EXIT_CRITICAL;ₛ
                RETURN (〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED)
            }
        };ₛ

        dstKPort′ =ₑ channel′ →dstPortsHead;ₛ
        If (dstKPort′ !=ₑ〈 OS_K_Port∗ 〉NULL ) {
            WHILE (dstKPort′ !=ₑ〈 OS_K_Port∗ 〉NULL)
            {
                error′ =ᶠ OSSampleSendToDomain (· dstKPort′→ dmport, msg_ptr′ , port_ptr′ → msgInTick ·);ₛ	(* 向目的分区发送消息，若是目的分区已经满了则消息丢失 *)
                dstKPort′ =ₑ 〈 OS_K_Port∗ 〉 dstKPort′ → OSEventPtr;ₛ
                If (error′ !=ₑ ′OS_NO_ERR) {
                    error′ =ₑ ′OS_ERR_DSTPORT_FULL
                }
            };ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            };ₛ
            EXIT_CRITICAL;ₛ
            RETURN error′
        };ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
            CSLSEMREL (semaphore′ ) 
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN error′
    }·.

Definition PortAccept_impl := 
    Int8u ·PortAccept·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ error @ Int8u ⌟; 
        (* #if OS_CAPABILITY_EN > 0
            OS_CSpace *pCSpace;

            pCSpace = OSCSpacePrioTbl[OSPrioCur];
            if((pCSpace->cnode.slot[CAP_PORT_CLASS].capability.content.category.category_right & PORT_ACCEPT_CAP) == 0)
            {
                return USER_CAPABILITY_NONE;
            }
        #endif *)
        
        ENTER_CRITICAL;ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port∗ 〉 NULL ) {               	(* Validate 'port'                                  *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′ →domain) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED)
        };ₛ
        EXIT_CRITICAL;ₛ

        error′ =ᶠ OSPortAcceptWithoutCheck (· port_ptr′ ,msg_ptr′ ·);ₛ
        RETURN error′
    }·.

Definition PortFlush_impl := 
    Int8u ·PortFlush·(⌞port_ptr @ OS_Port ∗ ⌟)··{
        ⌞ kport @ OS_K_Port ∗ ;
          channel @ OS_Channel ∗ ;
          semaphore @ Int8u ;
          resource_get_res @ Int8u ⌟; 
        (* #if OS_CAPABILITY_EN > 0
            OS_CSpace *pCSpace;

            pCSpace = OSCSpacePrioTbl[OSPrioCur];
            if((pCSpace->cnode.slot[CAP_PORT_CLASS].capability.content.category.category_right & PORT_PEND_CAP) == 0)
            {
                return USER_CAPABILITY_NONE;
            }
        #endif *)

        resource_get_res′ =ₑ ′0;ₛ
        channel′ =ₑ 〈 OS_Channel ∗ 〉NULL;ₛ
        kport′ =ₑ 〈 OS_K_Port∗ 〉 NULL;ₛ
        semaphore′ =ₑ ′DEFAULT_CHANNLE_SEMAPHROE;ₛ
    
        (* If (port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′ →domain) {
            RETURN (〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED)
        };ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port∗ 〉 NULL ) {               	(* Validate 'port'                                  *)
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_NULL)
        };ₛ *)

        ENTER_CRITICAL;ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port∗ 〉 NULL ) {               	(* Validate 'port'                                  *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′ →domain) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED)
        };ₛ
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        (*首先进行是否是端口与通道绑定的判断，然后判断是否是核间的分区间通信通道  *)


        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ

        If (kport′ → channel !=ₑ 〈 OS_Channel ∗ 〉NULL)  {

            channel′ =ₑ kport′ → channel;ₛ
            (* #if CACHE_ENABLE > 0
                    CACHE_wbL1d(channel,128,wait);
            #endif *)
            semaphore′ =ₑ channel′ → semaphore;ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
                CSLSEMACC (semaphore′, resource_get_res′);ₛ
                If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0){
                    EXIT_CRITICAL;ₛ
                    RETURN (〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED)
                }
            }
        };ₛ
        port_ptr′ →OSQIn      =ₑ port_ptr′ →OSQStart;ₛ
        port_ptr′ →OSQOut     =ₑ port_ptr′ →OSQStart;ₛ
        port_ptr′ →OSQEntries =ₑ ′0;ₛ
        port_ptr′ →OSQStart → len =ₑ ′0;ₛ        				(* 清空消息 *)
(* #if CACHE_ENABLE > 0
    CACHE_wbL1d(dmport,128,CACHE_NOWAIT);
    CACHE_wbL1d(port_ptr′ →OSQStart,128,wait);
#endif *)
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
            CSLSEMREL (semaphore′ ) 
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR
    }·.   


Definition QPortPend_impl := 
    Int8u ·QPortPend·(⌞port_ptr @ OS_Port ∗; timeout @Tint16;  msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ kport @ OS_K_Port ∗ ;
          dstKPort @ OS_K_Port ∗ ;
          channel @ OS_Channel ∗ ;
          semaphore @ Int8u ;
          resource_get_res @ Int8u;
          err @ Int8u ⌟; 
        (* #if OS_CAPABILITY_EN > 0
            OS_CSpace *pCSpace;

            pCSpace = OSCSpacePrioTbl[OSTCBCur->OSOriginPrio];
            if((pCSpace->cnode.slot[CAP_PORT_CLASS].capability.content.category.category_right & PORT_PEND_CAP) == 0)
            {
                return USER_CAPABILITY_NONE;
            }
        #endif
        #if OS_CRITICAL_METHOD == 3                      /* Allocate storage for CPU status register           */
            OS_CPU_SR  cpu_sr;
        #endif
        #if CACHE_ENABLE > 0
                CACHE_Wait wait = CACHE_WAIT;
        #endif *)

        resource_get_res′ =ₑ ′0;ₛ
        err′ =ₑ 〈 Int8u 〉 ′OS_NO_ERR;ₛ
        channel′ =ₑ 〈 OS_Channel ∗ 〉NULL;ₛ
        kport′ =ₑ 〈 OS_K_Port∗ 〉 NULL;ₛ
        semaphore′ =ₑ ′DEFAULT_CHANNLE_SEMAPHROE;ₛ

        ENTER_CRITICAL;ₛ
        If (OSIntNesting′ >ₑ ′0) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PEND_ISR)
        };ₛ
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port∗ 〉 NULL ) { 
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ

        ENTER_CRITICAL;ₛ
        If (port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′ →domain) {
            EXIT_CRITICAL;ₛ 
            RETURN (〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED)
        };ₛ
        EXIT_CRITICAL;ₛ 

        ENTER_CRITICAL;ₛ
        If (port_ptr′ → direction !=ₑ ′DESTINATION ) {
            EXIT_CRITICAL;ₛ 
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_DIRECTION_TYPE)
        };ₛ
        EXIT_CRITICAL;ₛ 

        ENTER_CRITICAL;ₛ
        If (port_ptr′ → mode !=ₑ ′QUEUE ) {
            EXIT_CRITICAL;ₛ 
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_TYPE)
        };ₛ
        EXIT_CRITICAL;ₛ 

        ENTER_CRITICAL;ₛ
        If (msg_ptr′ ==ₑ 〈 OSMsg_t∗ 〉 NULL ) {
            EXIT_CRITICAL;ₛ 
            RETURN (〈 Int8u 〉 ′OS_PORT_MSG_ARG_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ 

        (* msg_ptr′ → len =ₑ ′0;ₛ *) (* 这一句没有办法得到len 这个地址的权限 *)
        ENTER_CRITICAL;ₛ
        (*首先进行是否是端口与通道绑定的判断，然后判断是否是核间的分区间通信通道  *)


        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ
        If (kport′ ==ₑ 〈 OS_K_Port∗ 〉 NULL ) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PORT_UNBIND)
        };ₛ

        channel′ =ₑ kport′ → channel;ₛ

        If (channel′ ==ₑ 〈 OS_Channel∗ 〉 NULL ) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PORT_NO_CHANNEL)
        };ₛ

        semaphore′ =ₑ channel′ → semaphore;ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
            CSLSEMACC (semaphore′, resource_get_res′);ₛ
            If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0 ){
                EXIT_CRITICAL;ₛ
                RETURN (〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED)
            }
        };ₛ

        If (port_ptr′ →OSQEntries >ₑ ′0) {
            msg_ptr′ → len =ₑ port_ptr′ → OSQOut → len;ₛ
            memcpy(­ &ₐ (msg_ptr′ → data[′0]), &ₐ (port_ptr′ → OSQOut → data[′0]),  〈 Tint32 〉 port_ptr′ → OSQOut → len ­);ₛ 
            port_ptr′ →OSQOut =ₑ port_ptr′ →OSQOut +ₑ ′1;ₛ
            port_ptr′ →OSQEntries =ₑ port_ptr′ →OSQEntries −  (〈 Int16u 〉 ′1);ₛ
            If (port_ptr′ →OSQOut ==ₑ port_ptr′ →OSQEnd){
                port_ptr′ →OSQOut =ₑ port_ptr′ →OSQStart
            };ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            };ₛ
            EXIT_CRITICAL;ₛ
            RETURN 〈 Int8u 〉 ′OS_NO_ERR
        };ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
            CSLSEMREL (semaphore′ ) 
        };ₛ
        OSTCBCur′→OSTCBStat =ₑ OSTCBCur′→OSTCBStat |ₑ ′OS_STAT_PORT;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­ 〈 OS_EVENT ∗ 〉port_ptr ′­);ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        If (OSTCBCur′→OSTCBMsg ==ₑ〈 Void ∗ 〉(eptrconst OS_PARTITION_MESSAGE_COME_ptr)) 
        { 
            err′ =ᶠ OSPortAcceptWithoutCheck2(· port_ptr′,  msg_ptr′ ·);ₛ
            OSTCBCur′→OSTCBMsg =ₑ 〈 Void ∗ 〉NULL;ₛ
            OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_RDY;ₛ
            OSTCBCur′→OSTCBEventPtr  =ₑ 〈 OS_EVENT ∗ 〉NULL;ₛ
            EXIT_CRITICAL;ₛ
            RETURN  err′
        };ₛ
        OS_EventTO(­  〈 OS_EVENT ∗ 〉port_ptr ′  ­);ₛ 
        EXIT_CRITICAL;ₛ
        RETURN 〈 Int8u 〉 ′OS_TIMEOUT
    }·.   

Definition QPortPost_impl := 
    Int8u ·QPortPost·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ kport @ OS_K_Port ∗ ;
          dstKPort @ OS_K_Port ∗ ;
          channel @ OS_Channel ∗ ;
          semaphore @ Int8u ;
          resource_get_res @ Int8u;
          error @ Int8u ⌟; 

        resource_get_res′ =ₑ ′0;ₛ
        semaphore′ =ₑ ′DEFAULT_CHANNLE_SEMAPHROE;ₛ
        channel′ =ₑ 〈 OS_Channel ∗ 〉NULL;ₛ
        kport′ =ₑ 〈 OS_K_Port∗ 〉 NULL;ₛ
        dstKPort′ =ₑ 〈 OS_K_Port∗ 〉 NULL;ₛ
        error′ =ₑ 〈 Int8u 〉 ′OS_NO_ERR;ₛ
        
        ENTER_CRITICAL;ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port∗ 〉 NULL) {                    (* Validate 'pevent'                             *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_NULL)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′→domain) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (msg_ptr′ ==ₑ NULL) {                           (* Make sure we are not posting a NULL pointer   *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_ERR_POST_NULL_PTR)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If (port_ptr′ → direction !=ₑ ′SOURCE ||ₑ port_ptr′ → mode !=ₑ ′QUEUE ) {     (* Validate event block type                     *)
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ERR_TYPE)
        };ₛ
        EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ
        If ( port_ptr′ → portID ≥ ′PORT_NUMS) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_PORT_ID_INVALID)
        };ₛ
        EXIT_CRITICAL;ₛ
        (* 获取通道结构体，查看是否有目的分区的端口，若没有则将消息加入消息队列中 *)
        ENTER_CRITICAL;ₛ
        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ
        If (kport′ ==ₑ 〈 OS_K_Port∗ 〉NULL )
        {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_ERR_PORT_UNBIND)
        };ₛ
        If (kport′ → channel ==ₑ 〈 OS_Channel ∗ 〉NULL) {
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉′OS_ERR_PORT_NO_CHANNEL)
        };ₛ

        channel′ =ₑ kport′ → channel;ₛ
        semaphore′ =ₑ channel′ → semaphore;ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
            CSLSEMACC (semaphore′, resource_get_res′);ₛ
            If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0){
                EXIT_CRITICAL;ₛ
                RETURN (〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED)
            }
        };ₛ
        dstKPort′ =ₑ channel′ →dstPortsHead;ₛ

        If (dstKPort′ !=ₑ〈 OS_K_Port∗ 〉NULL ) {
            WHILE (dstKPort′ !=ₑ〈 OS_K_Port∗ 〉NULL)
            {
                error′ =ᶠ OSQSendToDomain (· dstKPort′→ dmport, msg_ptr′ ·);ₛ	(* 向目的分区发送消息，若是目的分区已经满了则消息丢失 *)
                dstKPort′ =ₑ 〈 OS_K_Port∗ 〉 dstKPort′ → OSEventPtr;ₛ
                If (error′ !=ₑ ′OS_NO_ERR) {
                    error′ =ₑ ′OS_ERR_DSTPORT_FULL
                }
            };ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            };ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN error′
        };ₛ
        If (port_ptr′→ OSQEntries ≥ port_ptr′→OSQSize) {
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            };ₛ
            EXIT_CRITICAL;ₛ
            RETURN (〈 Int8u 〉 ′OS_Q_FULL)
        };ₛ
        port_ptr′ → OSQIn → len =ₑ msg_ptr′ → len;ₛ
        memcpy(­ &ₐ (port_ptr′ → OSQIn → data[′0]), &ₐ (msg_ptr′ → data[′0]),  〈 Tint32 〉 msg_ptr′ → len ­);ₛ 
        (*memcpy(­  port_ptr′ → OSQIn → data, msg_ptr′ → data , msg_ptr′ → len ­);ₛ *)
        port_ptr′ → OSQIn =ₑ port_ptr′ → OSQIn +ₑ ′1;ₛ
        port_ptr′ → OSQEntries =ₑ port_ptr′ → OSQEntries +ₑ ′1;ₛ
        If (port_ptr′ → OSQIn ==ₑ port_ptr′ → OSQEnd) {  
            port_ptr′ → OSQIn =ₑ port_ptr′ → OSQStart
        };ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
            CSLSEMREL (semaphore′ ) 
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN error′
    }·.   


Definition OS_PortTaskRdy_impl :=
    Int8u ·OS_PortTaskRdy·(⌞pevent @ OS_Port∗;  msg_ptr @ OSMsg_t ∗ ;  msk @ Int16u⌟)··{
            ⌞
            ptcb @ OS_TCB∗;
            x @ Int8u;
            y @ Int8u;
            bitx @ Int8u;
            bity @ Int8u;
            prio @ Int8u
            ⌟;
    
            y′ =ₑ OSUnMapTbl′[pevent′→OSEventGrp];ₛ
            bity′ =ₑ OSMapTbl′[y′];ₛ
            x′ =ₑ OSUnMapTbl′[pevent′→OSEventTbl[y′]];ₛ
            bitx′ =ₑ OSMapTbl′[x′];ₛ
            prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ
            pevent′→OSEventTbl[y′] =ₑ pevent′→OSEventTbl[y′] &ₑ (∼bitx′);ₛ
            If (pevent′→OSEventTbl[y′] ==ₑ ′0) {
                pevent′→OSEventGrp =ₑ pevent′→OSEventGrp &ₑ (∼bity′)
            };ₛ
            ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
            ptcb′→OSTCBDly =ₑ ′0;ₛ
            ptcb′→OSTCBEventPtr =ₑ NULL;ₛ
            If(msg_ptr′!=ₑNULL){
                ptcb′→OSTCBMsg =ₑ eptrconst OS_PARTITION_MESSAGE_COME_ptr ;ₛ
                If (pevent′→ OSQEntries <ₑ pevent′→OSQSize){
                    pevent′ → OSQIn → len =ₑ msg_ptr′ → len;ₛ
                    memcpy(­ &ₐ (pevent′ → OSQIn → data[′0]), &ₐ (msg_ptr′ → data[′0]),  〈 Tint32 〉 msg_ptr′ → len ­);ₛ 
                    (*memcpy(­  port_ptr′ → OSQIn → data, msg_ptr′ → data , msg_ptr′ → len ­);ₛ *)
                    pevent′ → OSQIn =ₑ pevent′ → OSQIn +ₑ ′1;ₛ
                    pevent′ → OSQEntries =ₑ pevent′ → OSQEntries +ₑ ′1;ₛ
                    If (pevent′ → OSQIn ==ₑ pevent′ → OSQEnd) {  
                        pevent′ → OSQIn =ₑ pevent′ → OSQStart
                    }
                }
            };ₛ
            
            ptcb′→OSTCBStat =ₑ (ptcb′→OSTCBStat) &ₑ (∼msk′);ₛ
            If (ptcb′→OSTCBStat ==ₑ ′OS_STAT_RDY){
            OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ bity′;ₛ
            OSRdyTbl′[y′] =ₑ OSRdyTbl′[y′] |ₑ bitx′
            };ₛ
            RETURN prio′
        }·.
        

Definition OSQSendToDomain_impl := 
    Int8u ·OSQSendToDomain·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ ⌟; 
        (*ENTER_CRITICAL;ₛ*) 
        If (′DNUM ==ₑ port_ptr′ → coreNum )
        {
            If (port_ptr′ → OSEventGrp !=ₑ ′0)
            {
                OS_PortTaskRdy (­ port_ptr′, msg_ptr′, 〈 Int16u 〉 ′OS_STAT_PORT ­);ₛ
                (*EXIT_CRITICAL;ₛ*)
                (*OS_Sched(­);ₛ *)
                RETURN ′OS_NO_ERR
            };ₛ
            IF (port_ptr′→ OSQEntries <ₑ port_ptr′→OSQSize)
            {
                port_ptr′ → OSQIn → len =ₑ msg_ptr′ → len;ₛ
                memcpy(­ &ₐ (port_ptr′ → OSQIn → data[′0]), &ₐ (msg_ptr′ → data[′0]),  〈 Tint32 〉 msg_ptr′ → len ­);ₛ 
                (* memcpy(­  port_ptr′ → OSQIn → data, msg_ptr′ → data , msg_ptr′ → len ­);ₛ *)
                port_ptr′ → OSQIn =ₑ port_ptr′ → OSQIn +ₑ ′1;ₛ
                port_ptr′ → OSQEntries =ₑ port_ptr′ → OSQEntries +ₑ ′1;ₛ
                If (port_ptr′ → OSQIn ==ₑ port_ptr′ → OSQEnd) {  
                    port_ptr′ → OSQIn =ₑ port_ptr′ → OSQStart
                    }
            }
            ELSE
            {
                (*EXIT_CRITICAL;ₛ*)
                RETURN (〈 Int8u 〉 ′OS_Q_FULL)
            };ₛ
            (*EXIT_CRITICAL;ₛ*)
            RETURN ′OS_NO_ERR
        };ₛ

        If (port_ptr′→ OSQEntries ≥ port_ptr′→OSQSize) {
            GENERATEIPC(port_ptr′ → coreNum ,  ′ GET_PORT_MESSAGE);ₛ
            (*EXIT_CRITICAL;ₛ*)
            RETURN (〈 Int8u 〉 ′OS_Q_FULL)
        };ₛ
        port_ptr′ → OSQIn → len =ₑ msg_ptr′ → len;ₛ
        memcpy(­ &ₐ (port_ptr′ → OSQIn → data[′0]), &ₐ (msg_ptr′ → data[′0]),  〈 Tint32 〉 msg_ptr′ → len ­);ₛ 
        (* memcpy(­  port_ptr′ → OSQIn → data, msg_ptr′ → data , msg_ptr′ → len ­);ₛ *)
        port_ptr′ → OSQIn =ₑ port_ptr′ → OSQIn +ₑ ′1;ₛ
        port_ptr′ → OSQEntries =ₑ port_ptr′ → OSQEntries +ₑ ′1;ₛ
        If (port_ptr′ → OSQIn ==ₑ port_ptr′ → OSQEnd) {  
            port_ptr′ → OSQIn =ₑ port_ptr′ → OSQStart
            };ₛ
        GENERATEIPC(port_ptr′ → coreNum ,  ′ GET_PORT_MESSAGE);ₛ
        (*EXIT_CRITICAL;ₛ*)
        RETURN ′OS_NO_ERR
    }·.

Definition OSPortAcceptWithoutCheck2_impl := 
    Int8u ·OSPortAcceptWithoutCheck2·(⌞port_ptr @ OS_Port ∗; msg_ptr @ OSMsg_t ∗ ⌟)··{
        ⌞ kport @ OS_K_Port ∗ ;
          semaphore @ Int8u ;
          resource_get_res @ Int8u⌟; 
        (* ENTER_CRITICAL;ₛ *)
        If (port_ptr′ → direction !=ₑ ′ DESTINATION )
        {
            (* EXIT_CRITICAL;ₛ *)
            RETURN  (〈 Int8u 〉 ′OS_PORT_ERR_DIRECTION_TYPE)
        };ₛ
        (* EXIT_CRITICAL;ₛ
        ENTER_CRITICAL;ₛ *)
        If (msg_ptr′ ==ₑ 〈 OSMsg_t∗ 〉NULL )
        {
            (* EXIT_CRITICAL;ₛ *)
            RETURN (〈 Int8u 〉′OS_PORT_MSG_ARG_NULL)
        };ₛ
        (* EXIT_CRITICAL;ₛ
        (* msg_ptr′ → len =ₑ ′0;ₛ *) (* 这一句没有办法得到len 这个地址的权限 *)
        ENTER_CRITICAL;ₛ *)
        (* 分区机制保证其它核无非修改该端口 *)
        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ
        If (kport′ ==ₑ 〈 OS_K_Port∗ 〉NULL )
        {
            (* EXIT_CRITICAL;ₛ *)
            RETURN (〈 Int8u 〉′OS_PORT_MSG_ARG_NULL)
        };ₛ
        If (kport′ → channel ==ₑ 〈 OS_Channel ∗ 〉NULL) {
            (* EXIT_CRITICAL;ₛ *)
            RETURN (〈 Int8u 〉′OS_ERR_PORT_NO_CHANNEL)
        };ₛ
        semaphore′ =ₑ (〈 OS_Channel ∗ 〉 kport′ → channel) →semaphore;ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
    	    (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
            CSLSEMACC (semaphore′, resource_get_res′);ₛ
            If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0){
                (* EXIT_CRITICAL;ₛ *)
                RETURN (〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED)
            }
        };ₛ
        IF (port_ptr′→mode ==ₑ ′QUEUE) {
            If (port_ptr′→OSQEntries >ₑ ′0) {                    (* See if any messages in the queue                   *)
                msg_ptr′ →len =ₑ port_ptr′ → OSQOut → len;ₛ
                memcpy(­ &ₐ (msg_ptr′ → data[′0]), &ₐ (port_ptr′ → OSQOut → data[′0]),  〈 Tint32 〉 port_ptr′ → OSQOut → len ­);ₛ 
                port_ptr′ →OSQOut =ₑ port_ptr′ →OSQOut +ₑ ′1;ₛ
                port_ptr′ →OSQEntries =ₑ port_ptr′ →OSQEntries −  (〈 Int16u 〉 ′1);ₛ                        (* Update the number of entries in the queue   *)     
                If (port_ptr′ → OSQOut ==ₑ port_ptr ′ → OSQEnd) {          (* Wrap OUT pointer if we are at the end of the queue *)
                    port_ptr′ → OSQOut =ₑ port_ptr′ → OSQStart
                }
            }
        } ELSE { IF (port_ptr′ → mode ==ₑ ′ SAMPLE)  {
            msg_ptr ′ → len =ₑ port_ptr′ → OSQStart → len;ₛ
            memcpy(­ &ₐ (msg_ptr′ → data[′0]), &ₐ (port_ptr′ → OSQStart → data[′0]),  〈 Tint32 〉 port_ptr′ → OSQStart → len ­)
            } ELSE {
                If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                    (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                    CSLSEMREL (semaphore′ ) 
                };ₛ
                (* EXIT_CRITICAL;ₛ *)
                RETURN (〈 Int8u 〉 ′OS_PORT_ERR_TYPE)
            }
        };ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
            (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
            CSLSEMREL (semaphore′ ) 
        };ₛ
        (* EXIT_CRITICAL;ₛ *)
        RETURN ′OS_NO_ERR
    }·.

Definition OSPortAddToChannel_impl := 
    OS_Port ∗ ·OSPortAddToChannel·(⌞channelID @ Tint32; port_ptr @ OS_Port ∗; err @ Int8u ∗ ⌟)··{
        ⌞ 
          semaphore @ Int8u ;
          resource_get_res @ Int8u;
          kport @ OS_K_Port ∗ ;
          channel @ OS_Channel ∗;
          re @ OS_Port ∗;
          flag @ Int32;
          srcPort @ OS_Port ∗ ⌟; 
        
        channel′ =ₑ 〈 OS_Channel ∗ 〉NULL;ₛ
        kport′ 	=ₑ 〈 OS_K_Port∗ 〉NULL;ₛ
        re′ 	=ₑ 〈 OS_Port∗ 〉NULL;ₛ
        
        If (channelID′ ≥ ′ CHANNEL_NUMS )
        {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ID_INVALID;ₛ
            RETURN  (〈 OS_Port ∗ 〉 NULL)
        };ₛ
        If (port_ptr′ ==ₑ 〈 OS_Port ∗ 〉NULL )
        {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ERR_NULL;ₛ
            RETURN  (〈 OS_Port ∗ 〉 NULL)
        };ₛ
        If (OSRunning′ &&ₑ ((port_ptr′ → coreNum !=ₑ ′DNUM ||ₑ port_ptr′ → OSEventType !=ₑ ′OS_EVENT_TYPE_PORT ||ₑ OSTCBCur′ →OSTCBY !=ₑ port_ptr′→domain)) )
        {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_ERR_PARTITION_UNMAPPED;ₛ
            RETURN  (〈 OS_Port ∗ 〉 NULL)
        };ₛ

        flag′ =ᶠ portBindCheck(· port_ptr′ → portID, channelID′ ·);ₛ
        If (flag′  ==ₑ ′ 0 )
        {
            ∗ err′ =ₑ 〈 Int8u 〉 ′CHECK_ERROR;ₛ
            RETURN  (〈 OS_Port ∗ 〉 NULL)
        };ₛ 

        (* ENTER_CRITICAL; *)
        kport′ 	=ₑ OSKernelPortIDTbl′[port_ptr′→portID];ₛ
        channel′ =ₑ OSChannelIDTbl′[channelID′];ₛ
        If (channel′ ==ₑ 〈 OS_Channel ∗ 〉NULL) {
            
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_CHANNEL_ERR_NULL;ₛ
            (* EXIT_CRITICAL;ₛ *)
            RETURN  re′
        };ₛ
        If (kport′ ==ₑ 〈 OS_K_Port∗ 〉NULL )
        {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ID_INVALID;ₛ
            (* EXIT_CRITICAL;ₛ *)
            RETURN  re′
        };ₛ
        
        semaphore′ =ₑ channel′ →semaphore;ₛ
        If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
    	    (* resource_get_res′ =ᶠ CSL_semAcquireDirect(· semaphore′ ·);ₛ *)
            CSLSEMACC (semaphore′, resource_get_res′);ₛ
            If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0){
                ∗ err′ =ₑ 〈 Int8u 〉 ′OS_CHANNEL_ERR_BEING_USED;ₛ
                (* EXIT_CRITICAL;ₛ *)
                RETURN  re′
            }
        };ₛ
        If (kport′ → channel !=ₑ 〈 OS_Channel ∗ 〉NULL) {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_ERR_PORT_HAVE_BEEN_BINDED;ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            };ₛ
            (* EXIT_CRITICAL;ₛ *)
            RETURN  re′
        };ₛ


        IF (port_ptr′→direction ==ₑ ′SOURCE) {
            If (semaphore′ ==ₑ ′DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel′ →dstPortsHead !=ₑ 〈 OS_K_Port∗ 〉NULL) {
                If (channel′ →dstPortsHead → coreNum !=ₑ kport′ → coreNum) {
                    ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ERR_MULTICORE;ₛ
                    (* EXIT_CRITICAL;ₛ *)
                    RETURN  re′ 
                } 
            };ₛ
            (* re ′  =ₑ channel′ → srcPort → dmport;ₛ  srcPort 为NULL  *)
            channel′ → srcPort =ₑ kport ′;ₛ
            channel′ → srcPortsNum =ₑ ′1;ₛ
            kport ′ → channelID =ₑ channelID′;ₛ
            kport ′ → channel =ₑ channel′;ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            }
            (* EXIT_CRITICAL;ₛ *)
        } ELSE { IF (port_ptr′ → direction ==ₑ ′ DESTINATION)  {
            IF (channel′ →dstPortsNum  !=ₑ ′0) {
                If (semaphore′ ==ₑ ′DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel′ →srcPort !=ₑ 〈 OS_K_Port∗ 〉NULL) {
                    If (channel′ →srcPort → coreNum !=ₑ kport′ → coreNum) {
                        ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ERR_MULTICORE;ₛ
                        (* EXIT_CRITICAL;ₛ *)
                        RETURN  re′ 
                    } 
                };ₛ
                If (semaphore′ ==ₑ ′DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel′ →dstPortsHead !=ₑ 〈 OS_K_Port∗ 〉NULL) {
                    If (channel′ →dstPortsHead → coreNum !=ₑ kport′ → coreNum) {
                        ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ERR_MULTICORE;ₛ
                        (* EXIT_CRITICAL;ₛ *)
                        RETURN  re′ 
                    } 
                };ₛ
                channel′ → dstPortsTail → OSEventPtr =ₑ 〈 Void∗ 〉 kport ′
            } ELSE {
                If (semaphore′ ==ₑ ′DEFAULT_CHANNLE_SEMAPHROE &&ₑ channel′ →srcPort !=ₑ 〈 OS_K_Port∗ 〉NULL) {
                    If (channel′ →srcPort → coreNum !=ₑ kport′ → coreNum) {
                        ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ERR_MULTICORE;ₛ
                        (* EXIT_CRITICAL;ₛ *)
                        RETURN  re′ 
                    } 
                };ₛ
                channel′ → dstPortsHead =ₑ kport ′;ₛ
                If (port_ptr′→mode ==ₑ ′QUEUE &&ₑ channel′ →srcPort !=ₑ 〈 OS_K_Port∗ 〉NULL ) {
                    If (channel′ →srcPort→dmport !=ₑ 〈 OS_Port∗ 〉NULL) {    
                        srcPort′ =ₑ channel′ →srcPort→dmport;ₛ
                        WHILE (srcPort′ → OSQEntries >ₑ port_ptr ′ → OSQSize )
                        {
                            srcPort′ →OSQOut =ₑ srcPort′ →OSQOut +ₑ ′1;ₛ
                            srcPort′ →OSQEntries =ₑ srcPort′ →OSQEntries −  (〈 Int16u 〉 ′1);ₛ                        (* Update the number of entries in the queue   *)     
                            If (srcPort′ → OSQOut ==ₑ srcPort ′ → OSQEnd) {          (* Wrap OUT pointer if we are at the end of the queue *)
                                srcPort′ → OSQOut =ₑ srcPort′ → OSQStart
                            }
                        };ₛ
                        WHILE (srcPort′ → OSQEntries >ₑ  ′ 0 )
                        {
                            port_ptr′ → OSQIn → len =ₑ srcPort′ → OSQOut → len;ₛ
                            memcpy(­ &ₐ (port_ptr′ → OSQIn → data[′0]), &ₐ (srcPort′ → OSQOut → data[′0]),  〈 Tint32 〉 srcPort′ → OSQOut → len ­);ₛ 
                            (* memcpy(port->OSQIn, srcPort->OSQOut->data, srcPort->OSQOut->len); *)
                            port_ptr′ → OSQIn =ₑ port_ptr′ → OSQIn +ₑ ′1;ₛ
                            port_ptr′ → OSQEntries =ₑ port_ptr′ → OSQEntries +ₑ ′1;ₛ
                            If (port_ptr′ → OSQIn ==ₑ port_ptr′ → OSQEnd) {  
                                port_ptr′ → OSQIn =ₑ port_ptr′ → OSQStart
                            };ₛ
                            srcPort′ →OSQOut =ₑ srcPort′ →OSQOut +ₑ ′1;ₛ
                            srcPort′ →OSQEntries =ₑ srcPort′ →OSQEntries −  (〈 Int16u 〉 ′1);ₛ                        (* Update the number of entries in the queue   *)     
                            If (srcPort′ → OSQOut ==ₑ srcPort ′ → OSQEnd) {          (* Wrap OUT pointer if we are at the end of the queue *)
                                srcPort′ → OSQOut =ₑ srcPort′ → OSQStart
                            }
                        }
                    }
                }
            };ₛ
            channel′ → dstPortsTail =ₑ kport ′;ₛ
            channel′ → dstPortsNum =ₑ channel′ → dstPortsNum +ₑ ′1;ₛ
            kport ′ → channelID =ₑ channelID′;ₛ
            kport ′ → channel =ₑ channel′;ₛ
            kport ′ → OSEventPtr =ₑ 〈 Void∗ 〉NULL;ₛ
            If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                CSLSEMREL (semaphore′ ) 
            }
            (* EXIT_CRITICAL;ₛ *)
            } ELSE {
                If (semaphore′ !=ₑ ′DEFAULT_CHANNLE_SEMAPHROE) {
                    (* CSL_semReleaseSemaphore (­ semaphore′  ­) *)
                    CSLSEMREL (semaphore′ ) 
                };ₛ
                (* EXIT_CRITICAL;ₛ *)
                ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ERR_TYPE;ₛ
                RETURN  re′
            }
        };ₛ

        (* EXIT_CRITICAL;ₛ *)
        ∗ err′ =ₑ 〈 Int8u 〉 ′OS_NO_ERR;ₛ
        RETURN  re′
    }·.


Definition OSKernelPortCreate_impl := 
    OS_K_Port ∗ ·OSKernelPortCreate·(⌞dmPort @ OS_Port ∗; portId @ Tint32; err @ Int8u ∗ ⌟)··{
        ⌞ 
            port @ OS_K_Port ∗ ;
            resource_get_res @ Int8u;
            corPort_ptr @ OS_Port ∗ ⌟; 
        
        port′ =ₑ 〈 OS_K_Port∗ 〉NULL;ₛ
        resource_get_res′ =ₑ 〈 Int8u 〉  ′ 0;ₛ
        
        If (portId′ ≥ ′PORT_NUMS ) {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ID_INVALID;ₛ
            RETURN  (〈 OS_K_Port ∗ 〉 NULL)
        };ₛ
        If (OSIntNesting′ >ₑ ′0) {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_ERR_CREATE_ISR;ₛ
            RETURN  (〈 OS_K_Port ∗ 〉 NULL)
        };ₛ

        corPort_ptr′ =ₑ OSDomainPortPtrList′;ₛ
        WHILE (corPort_ptr′ !=ₑ 〈 OS_Port ∗ 〉 NULL ) {
            If (corPort_ptr′ ==ₑ dmPort′ ) {
                ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ID_INVALID;ₛ
                RETURN  (〈 OS_K_Port ∗ 〉 NULL)
            };ₛ
            corPort_ptr′ =ₑ corPort_ptr′→nextPort
        };ₛ
        
        CSLSEMACC (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_PORT, resource_get_res′);ₛ
        If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′ 0) {
            ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_FAIL_TO_GET;ₛ
            RETURN  port′
        };ₛ

        If (OSKernelPortIDTbl′[portId′] ==ₑ 〈 OS_K_Port ∗ 〉 NULL ) {
            port′ =ₑ OSKernelPortFreeList′;ₛ
            If (OSKernelPortFreeList′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL ) {
                OSKernelPortFreeList′		=ₑ 〈 OS_K_Port ∗ 〉 (OSKernelPortFreeList′→OSEventPtr);ₛ
			    OSKernelPortIDTbl′[portId′] =ₑ port′
            };ₛ

            If (dmPort′→direction ==ₑ ′DESTINATION) {
                dmPort′→OSEventPtrPort =ₑ OSCorePortPtrList′;ₛ
                OSCorePortPtrList′ =ₑ dmPort′
            };ₛ

            dmPort′→nextPort =ₑ OSDomainPortPtrList′;ₛ
            OSDomainPortPtrList′ =ₑ dmPort′;ₛ
            IF (port′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL ) {
                port′→portID		=ₑ portId′;ₛ
                port′→dmport		=ₑ dmPort′;ₛ
                port′→channelID	    =ₑ ′DEFAULT_CHANELID;ₛ
                port′→OSEventPtr	=ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
                port′→coreNum       =ₑ dmPort′→coreNum;ₛ
                port′→channel       =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
                dmPort′→OSEventType =ₑ 〈 Int8u 〉 ′OS_EVENT_TYPE_PORT;ₛ
                ∗ err′              =ₑ 〈 Int8u 〉 ′OS_NO_ERR
            } ELSE {
                ∗ err′              =ₑ 〈 Int8u 〉 ′OS_PORT_DEPLETED
            };ₛ

            CSLSEMREL (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_PORT );ₛ
            RETURN  port′
        };ₛ

        CSLSEMREL (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_PORT );ₛ
        ∗ err′ =ₑ 〈 Int8u 〉 ′OS_PORT_ID_EXIST;ₛ
        RETURN  port′
    }·.

    Definition OSChannelCreate_impl :=
    OS_Channel ∗ ·OSChannelCreate·(⌞channelID @ Int8u; ch_type @ channnel_type_t; err @ Int8u ∗ ⌟)··{
        ⌞ channel @ OS_Channel ∗ ;
          resource_get_res @ Int8u ;
          semaphore @ Int8u ;
          flag @ Int32u⌟; 

        channel′ =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
        resource_get_res′ =ₑ ′0;ₛ
        semaphore′ =ₑ ′DEFAULT_CHANNLE_SEMAPHROE;ₛ
              
        If ( channelID′ ≥ ′CHANNEL_NUMS) {
            ∗ err′ =ₑ ′OS_CHANNEL_ID_INVALID;ₛ
            RETURN channel′
        };ₛ
        
        If (OSIntNesting′ >ₑ ′0) {
            ∗ err′ =ₑ ′OS_ERR_CREATE_ISR;ₛ
            RETURN 〈 OS_Channel ∗ 〉 NULL
        };ₛ

        flag′ =ᶠ channleCreateCheck (· channelID′, ch_type′ ·);ₛ
        If (flag′  ==ₑ ′ 0 )
        {
            ∗ err′ =ₑ 〈 Int8u 〉 ′CHECK_ERROR;ₛ
            RETURN  (〈 OS_Port ∗ 〉 NULL)
        };ₛ 

        (* ENTER_CRITICAL;ₛ *)
        
        CSLSEMACC (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_CHANNEL, resource_get_res′);ₛ
        If (resource_get_res′ ==ₑ 〈 Int8u 〉  ′0){
            ∗ err′ =ₑ ′OS_CHANNEL_FAIL_TO_GET;ₛ
            RETURN channel′
        };ₛ

        If (ch_type′ ==ₑ ′OUTCORE &&ₑ sys_channel_info′→ count ≥ ′OS_INTER_CORE_CHANNEL_NUMS ){
            ∗ err′ =ₑ ′OS_CHANNEL_ERR_SEMAPHORE_NULL;ₛ
            CSLSEMREL (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ
            (* EXIT_CRITICAL;ₛ *)
            RETURN channel′
        };ₛ

        If (OSChannelIDTbl′[channelID′] ==ₑ 〈 OS_Channel ∗ 〉 NULL){
            channel′ =ₑ OSChannelFreeList′;ₛ
            IF (channel′ !=ₑ 〈 OS_Channel ∗ 〉 NULL){
                OSChannelFreeList′ =ₑ 〈 OS_Channel ∗ 〉 (OSChannelFreeList′→OSEventPtr);ₛ
                OSChannelIDTbl′[channelID′] =ₑ channel′;ₛ

                If (ch_type′ ==ₑ ′OUTCORE){
                    semaphore′ =ₑ OSUnMapTbl′[sys_channel_info′ → freeTbl];ₛ
                    sys_channel_info′ → freeTbl =ₑ sys_channel_info′ → freeTbl &ₑ (∼ OSMapTbl′[semaphore′]) ;ₛ
                    sys_channel_info′ → count =ₑ sys_channel_info′ → count +ₑ ′1;ₛ
                    channel′→ semaphore =ₑ semaphore′
                };ₛ

                channel′→ channelID     =ₑ channelID′;ₛ
                channel′→ OSEventPtr    =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
                channel′→ srcPort       =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
                channel′→ dstPortsHead  =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
                channel′→ dstPortsTail	=ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
                channel′→ srcPortsNum	=ₑ ′0;ₛ
                channel′→ dstPortsNum	=ₑ ′0;ₛ

                ∗ err′ =ₑ ′OS_NO_ERR
            } ELSE { 
                ∗ err′ =ₑ ′OS_CHANNEL_DEPLETED
            };ₛ
            CSLSEMREL (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ
            (* EXIT_CRITICAL;ₛ *)
            RETURN channel′
        };ₛ

        CSLSEMREL (〈 Int8u 〉′OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ
        (* EXIT_CRITICAL;ₛ *)
        ∗ err′ =ₑ ′OS_CHANNEL_ID_EXIST;ₛ
        RETURN channel′
    }·.

Definition SamplePortCreate_impl :=
    Void ·SamplePortCreate·(⌞port @ OS_Port ∗ ; portId @ Int32u ; buff @ OSMsg_t ∗ ; err @ Int8u ∗ ⌟)··{
        ⌞ flag @ Int32u ;
          port_ptr @ OSport_attr_t ∗ ⌟; 

        port′→portID		=ₑ portId′;ₛ
        port_ptr′           =ₑ &ₐ (OSPortAttrTbl′[portId′]);ₛ
        port′→mode  		=ₑ port_ptr′→mode;ₛ
        port′→direction	    =ₑ port_ptr′→direction;ₛ
        port′→domain    	=ₑ port_ptr′→domain;ₛ
        port′→OSQStart      =ₑ buff′;ₛ
        port′→OSEventType   =ₑ 〈 Int8u 〉 ′OS_EVENT_TYPE_UNUSED;ₛ
        port′→coreNum       =ₑ ′DNUM;ₛ

        flag′ =ᶠ portCreateCheck (· 〈 Int8u 〉 portId′ ·);ₛ 
        If ( flag′ ==ₑ ′ 0) {
            ∗ err′ =ₑ 〈 Int8u 〉 ′CHECK_ERROR;ₛ
            RETURN
        };ₛ

        OSKernelPortCreate (­ port′, portId′, err′ ­);ₛ

        If (∗ err′ ==ₑ 〈 Int8u 〉 ′OS_NO_ERR ) {
            OSPortAddToChannel(­  〈 Int32u 〉 port_ptr′→channelID, port′, err′ ­)
        };ₛ
        RETURN
    }·.

Definition QPortCreate_impl :=
    Void ·QPortCreate·(⌞port @ OS_Port ∗ ; portId @ Int32u ; start @ OSMsg_t ∗ ; size @ Int16u ; err @ Int8u ∗ ⌟)··{
        ⌞ flag @ Int32u ;
          port_ptr @ OSport_attr_t ∗ ⌟; 

        port′→portID		=ₑ portId′;ₛ
        port_ptr′           =ₑ &ₐ (OSPortAttrTbl′[portId′]);ₛ
        port′→mode  		=ₑ port_ptr′→mode;ₛ
        port′→direction	    =ₑ port_ptr′→direction;ₛ
        port′→domain    	=ₑ port_ptr′→domain;ₛ
        port′→OSEventType   =ₑ 〈 Int8u 〉 ′OS_EVENT_TYPE_UNUSED;ₛ
        port′→OSQStart      =ₑ start′;ₛ
        port′→OSQEnd        =ₑ &ₐ (start′[size′]);ₛ
        port′→OSQIn         =ₑ start′;ₛ
        port′→OSQOut        =ₑ start′;ₛ
        port′→OSQSize       =ₑ size′;ₛ
        port′→OSQEntries    =ₑ ′0;ₛ
        port′→coreNum       =ₑ ′DNUM;ₛ

        flag′ =ᶠ portCreateCheck (· 〈 Int8u 〉 portId′ ·);ₛ 
        If ( flag′ ==ₑ ′ 0) {
            ∗ err′ =ₑ 〈 Int8u 〉 ′CHECK_ERROR;ₛ
            RETURN
        };ₛ

        OSKernelPortCreate (­ port′, portId′, err′ ­);ₛ

        If (∗ err′ ==ₑ 〈 Int8u 〉 ′OS_NO_ERR ) {
            OSPortAddToChannel(­  〈 Int32u 〉 port_ptr′→channelID, port′, err′ ­)
        };ₛ
        RETURN
    }·.



Definition receivePortMsg_impl := 
    Void ·receivePortMsg·(⌞⌟)··{
        ⌞ 
        port_ptr @ OS_Port ∗ ;
        ptcb @ OS_TCB ∗;
        x @ Int8u ;
        y @ Int8u ;
        prio @ Int8u ⌟; 
        port_ptr ′ =ₑ OSCorePortPtrList ′;ₛ
        WHILE (port_ptr′ !=ₑ〈 OS_Port∗ 〉NULL)
            {
                If (port_ptr′ → OSEventGrp !=ₑ ′0)
                {
                    y′ =ₑ OSUnMapTbl′[port_ptr′→OSEventGrp];ₛ
                    If (y′ ==ₑport_ptr′→ domain) {
                        x′ =ₑ OSUnMapTbl′[port_ptr′→OSEventTbl[y′]];ₛ
                        prio′ =ₑ ((y′ ≪ ′3) +ₑ x′);ₛ
                        ptcb′ =ₑ OSTCBPrioTbl′[prio′];ₛ
                        ptcb′→OSTCBMsg =ₑ eptrconst OS_PARTITION_MESSAGE_COME_ptr ;ₛ
                
                        If (((ptcb′→OSTCBStat &ₑ ′OS_STAT_ILLEGAL) ==ₑ ′OS_STAT_RDY)&&ₑ
                            ((ptcb′→OSTCBStat &ₑ ′OS_STAT_SUSPEND) ==ₑ ′OS_STAT_RDY)){
                            OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→ OSTCBBitY;ₛ
                            OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX
                        }
                    }
                };ₛ
                port_ptr′ =ₑ port_ptr′ → OSEventPtrPort
            };ₛ
        RETURN ′OS_NO_ERR
    }·.