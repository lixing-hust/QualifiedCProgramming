Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.


Open Scope code_scope.

(* 文件中所有的enter critical, exit critical 均为额外添加*)
(* 文件中所有的 OSTaskExeLoc操作均为额外添加*)

Definition IPCsend_impl := 
    Int16u ·IPCsend·(⌞dstCore @ Int8u; srcAddr @ Int8u∗ ; 
                        size @ Tint32; flag @ Int8u⌟)··{
        ⌞
            tmpsem @ OS_EVENT∗;
            (* err @ Int32u; *)
            step @ Int32;
            (* sem_ptr @ Void∗; *)
            ipcinfo @Int32u ⌟; 
        If (srcAddr ′ ==ₑ NULL ||ₑ  size′ <ₑ ′1 ||ₑ size′ >ₑ ′IPC_STEP ||ₑ 
        dstCore′ >ₑ( ′CORENUM − ′1) ||ₑ dstCore′ ==ₑ ′DNUM ||ₑ 
        flag′ >ₑ ′IPC_BROAD){
            RETURN ′EINVAL
        };ₛ
        
        GETSEM dstCore′;ₛ

        IF (′DNUM >ₑ dstCore′){
            step′ =ₑ ′DNUM − ′1
        } ELSE {
            step′ =ₑ ′DNUM
        };ₛ
        
        ENTER_CRITICAL;ₛ
        (* sem_ptr′ =ₑ IPCMem′[dstCore′] +ₑ step′ × ′IPC_STEP;ₛ  *)
        (* memcpy(­ 〈 Void∗ 〉sem_ptr′ , srcAddr′ , size′ ­);ₛ  *)
        memcpy(­ 〈 Int8u∗ 〉(IPCMem′[dstCore′] +ₑ step′ × ′IPC_STEP) , srcAddr′ , size′ ­);ₛ 
        EXIT_CRITICAL;ₛ

        ipcinfo′ =ₑ ′0;ₛ
        IF (′DNUM ==ₑ ′0){ ipcinfo′ =ₑ ′CORE0_IPC } ELSE {
        IF (′DNUM ==ₑ ′1){ ipcinfo′ =ₑ ′CORE1_IPC } ELSE {
        IF (′DNUM ==ₑ ′2){ ipcinfo′ =ₑ ′CORE2_IPC } ELSE {
        IF (′DNUM ==ₑ ′3){ ipcinfo′ =ₑ ′CORE3_IPC } ELSE {
        IF (′DNUM ==ₑ ′4){ ipcinfo′ =ₑ ′CORE4_IPC } ELSE {
        IF (′DNUM ==ₑ ′5){ ipcinfo′ =ₑ ′CORE5_IPC } ELSE {
        IF (′DNUM ==ₑ ′6){ ipcinfo′ =ₑ ′CORE6_IPC } ELSE {
        IF (′DNUM ==ₑ ′7){ ipcinfo′ =ₑ ′CORE7_IPC }
                    ELSE { ipcinfo′ =ₑ ′CORE0_IPC }
        } } } } } } };ₛ

        IF (flag′ ==ₑ ′IPC_BROAD) {
            GENERATEIPC(dstCore′ , (ipcinfo′ |ₑ ′ IPC_MESSAGE_BROAD));ₛ
            (* OSSemPend(­ IPCSendSem′[dstCore′], ′0 , &ₐ err′ ­);ₛ *)
            ENTER_CRITICAL;ₛ
            tmpsem′ =ₑ IPCSendSem′[dstCore′];ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ tmpsem′;ₛ
            EXIT_CRITICAL;ₛ
            OSSemPend(- tmpsem′, 〈 Tint16 〉 ′0 -);ₛ
            ENTER_CRITICAL;ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
            EXIT_CRITICAL;ₛ
            POSTSEM( dstCore′ )
        } ELSE {
            IF (flag′ ==ₑ ′IPC_BLOCK) {
                GENERATEIPC(dstCore′ , (ipcinfo′ |ₑ ′ IPC_MESSAGE_RDY));ₛ
                (* OSSemPend(­ IPCSendSem′[dstCore′], ′0 , &ₐ err′ ­);ₛ *)
                ENTER_CRITICAL;ₛ
                tmpsem′ =ₑ IPCSendSem′[dstCore′];ₛ
                OSTCBCur′→__OSTskSemPtr =ₑ tmpsem′;ₛ
                EXIT_CRITICAL;ₛ
                OSSemPend(- tmpsem′, 〈 Tint16 〉 ′0 -);ₛ
                ENTER_CRITICAL;ₛ
                OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
                EXIT_CRITICAL;ₛ
                POSTSEM( dstCore′ )
            }
            ELSE {
                GENERATEIPC(dstCore′ , (ipcinfo′ |ₑ ′ IPC_MESSAGE_RDY));ₛ
                POSTSEM( dstCore′ )
            }
        } ;ₛ
        RETURN ′OS_NO_ERR
    }·.


Definition IPCrecv_impl:= 
    Int16u ·IPCrecv·(⌞srcCore @ Int8u; dstAddr @ Int8u∗ ; 
                                size @ Tint32; flag @ Int8u⌟)··{
        ⌞
            (*err @ Int32u; *)
            (* IPCBroad_cur @Tint8; *)
            IPCBroad_cur @Tint32;
            tmpsem @ OS_EVENT∗;
            step @ Int32;
            ipcinfo @Int32u ⌟; 
        If (dstAddr ′ ==ₑ NULL ||ₑ  size′ <ₑ ′1 ||ₑ size′ >ₑ ′IPC_STEP ||ₑ 
        srcCore′ >ₑ( ′CORENUM − ′1) ||ₑ srcCore′ ==ₑ ′DNUM ||ₑ 
        flag′ >ₑ ′IPC_BROAD){
            RETURN ′EINVAL
        };ₛ

        IF (flag ′ !=ₑ ′IPC_BROAD) {
            ENTER_CRITICAL;ₛ
            tmpsem′ =ₑ IPCSem′[srcCore′];ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ tmpsem′;ₛ
            EXIT_CRITICAL;ₛ
            OSSemPend(- tmpsem′, 〈 Tint16 〉 ′0 -);ₛ
            ENTER_CRITICAL;ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
            EXIT_CRITICAL }
        ELSE {
            ENTER_CRITICAL;ₛ
            tmpsem′ =ₑ IPCSemShared′;ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ tmpsem′;ₛ
            EXIT_CRITICAL;ₛ
            OSSemPend(- tmpsem′, 〈 Tint16 〉 ′0 -);ₛ
            ENTER_CRITICAL;ₛ
            OSTCBCur′→__OSTskSemPtr =ₑ NULL;ₛ
            EXIT_CRITICAL;ₛ
        (* 一旦信号量可用，意味着有新的广播消息可以处理。
		  在处理共享数据（例如IPCBroad_pointer和IPCBroad_Core_Current[]数组）时，
          代码会进入临界区，确保对共享数据的访问是受保护的
		*)
            ENTER_CRITICAL;ₛ
            If (IPCBroad_pointer′ ==ₑ ′0 ||ₑ IPCBroad_pointer′ >ₑ ′CORENUM )
            { 
                EXIT_CRITICAL;ₛ
                RETURN ′EBUSY
            };ₛ
            −− IPCBroad_pointer′;ₛ
            IPCBroad_cur′ =ₑ IPCBroad_Core_Current′[IPCBroad_pointer′];ₛ
            srcCore′ =ₑ IPCBroad_cur′;ₛ 
            IPCBroad_Core_Current′[IPCBroad_pointer′] =ₑ ′(Zneg xH);ₛ
            EXIT_CRITICAL
        };ₛ
        
        (* If (err′ !=ₑ ′OS_NO_ERR){
            RETURN ′EBUSY
        };ₛ *)
        IF (srcCore′ >ₑ ′DNUM){
            step′ =ₑ srcCore′ − ′1
        } ELSE {
            step′ =ₑ srcCore′
        };ₛ
        ENTER_CRITICAL;ₛ
        memcpy(­ dstAddr′, 〈 Int8u∗ 〉(IPCMem′[′DNUM] +ₑ step′ × ′IPC_STEP) , size′ ­);ₛ 
        EXIT_CRITICAL;ₛ
        If ( flag′  !=ₑ ′IPC_NONACK){ 
            ipcinfo′ =ₑ ′0;ₛ
            IF (′DNUM ==ₑ ′0){ ipcinfo′ =ₑ ′CORE0_IPC }
            ELSE {
                IF (′DNUM ==ₑ ′1){ ipcinfo′ =ₑ ′CORE1_IPC }
                ELSE {
                    IF (′DNUM ==ₑ ′2){ ipcinfo′ =ₑ ′CORE2_IPC }
                    ELSE{
                        IF (′DNUM ==ₑ ′3){ ipcinfo′ =ₑ ′CORE3_IPC }
                        ELSE{
                            IF (′DNUM ==ₑ ′4){ ipcinfo′ =ₑ ′CORE4_IPC }
                            ELSE{
                                IF (′DNUM ==ₑ ′5){ ipcinfo′ =ₑ ′CORE5_IPC }
                                ELSE{
                                    IF (′DNUM ==ₑ ′6){ ipcinfo′ =ₑ ′CORE6_IPC }
                                    ELSE{
                                    IF (′DNUM ==ₑ ′7){ ipcinfo′ =ₑ ′CORE7_IPC }
                                    ELSE { ipcinfo′ =ₑ ′CORE0_IPC }
                                    }
                                }
                            }
                        }
                    }
                }
            };ₛ
            GENERATEIPC(srcCore′ , (ipcinfo′ |ₑ ′ IPC_MESSAGE_ACK))
        };ₛ

        If ( flag′  ==ₑ ′IPC_BROAD){
            RETURN srcCore′
        };ₛ
        RETURN ′OS_NO_ERR 
        }·.

 (* 暂时未考虑refactor *)
 (* an internal function *)
Definition OSIpc_impl:= 
    Void ·OSIpc·(⌞⌟)··{
        ⌞
            tmpsem @ OS_EVENT∗;
            read_ipcgr @ Int32u;
            corenum @ Int32 ⌟; 
        read_ipcgr′ =ₑ ∗ iIPCGRInfo′;ₛ
        CLEARIPC( 〈 Int8u 〉′DNUM, read_ipcgr′ );ₛ
        corenum′ =ᶠ OS_getCoreIPC (· read_ipcgr′ ·) ;ₛ
        If (corenum′ ==ₑ ′(Zneg xH)){
            (*printf ...*)
            RETURN 
        };ₛ
        IF ((read_ipcgr′  &ₑ ′IPC_MESSAGE_RDY) ==ₑ ′IPC_MESSAGE_RDY){
            (* if (OSSemPost (IPCSem[corenum]) != OS_NO_ERR) {printf ..}*)
            OSIPCSemPost(­ IPCSem′[corenum′] ­);ₛ
            RETURN
        } ELSE 
            { IF ((read_ipcgr′  &ₑ ′REFACTOR_RDY) ==ₑ ′REFACTOR_RDY){ 
                    doRefactorISR(­ corenum′ ­);ₛ
                    RETURN }
                ELSE {
                IF ((read_ipcgr′  &ₑ ′IPC_MESSAGE_ACK) ==ₑ ′IPC_MESSAGE_ACK){ 
                     (* if (OSSemPost (IPCSendSem[corenum]) != OS_NO_ERR) {printf ..}*)
                        OSIPCSemPost(­ IPCSendSem′[corenum′] ­);ₛ
                        RETURN }
                 ELSE { IF ((read_ipcgr′  &ₑ ′IPC_MESSAGE_BROAD) ==ₑ ′IPC_MESSAGE_BROAD){ 
                 (* if (OSSemPost (IPCSemShared ) != OS_NO_ERR) {printf ..}*)
                    IPCBroad_Core_Current′[IPCBroad_pointer′] =ₑ corenum′ ;ₛ
                    ++ IPCBroad_pointer′;ₛ
                    OSIPCSemPost(­ IPCSemShared′ ­);ₛ
                    (* 在OSIpc()函数中，OSSemPost(IPCSemShared)被调用时，
                    意味着有新的广播消息可用。调用OSSemPost()将使得等待这个信号量的其他任务得以继续执行 *)
                    RETURN }
                    ELSE {
                        RETURN
                    }
                    }
                }
            }
        }·.

(* Definition OS_getCoreIPC_impl:= 
    Int32 ·OS_getCoreIPC·(⌞read_ipcgr @ Int32u⌟)··{
        ⌞ ⌟; 
        EXIT_CRITICAL;ₛ
        IF ((read_ipcgr′  &ₑ ′CORE0_IPC) ==ₑ ′CORE0_IPC  &&ₑ ′DNUM !=ₑ ′0 ){ RETURN ′0 }
        ELSE {
            IF ((read_ipcgr′  &ₑ ′CORE1_IPC) ==ₑ ′CORE1_IPC  &&ₑ ′DNUM !=ₑ ′1 ){ RETURN ′1 }
            ELSE {
                IF ((read_ipcgr′  &ₑ ′CORE2_IPC) ==ₑ ′CORE2_IPC  &&ₑ ′DNUM !=ₑ ′2 ){ RETURN ′2 }
                ELSE{
                    IF ((read_ipcgr′  &ₑ ′CORE3_IPC) ==ₑ ′CORE3_IPC  &&ₑ ′DNUM !=ₑ ′3 ){ RETURN ′3 }
                    ELSE{
                        IF ((read_ipcgr′  &ₑ ′CORE4_IPC) ==ₑ ′CORE4_IPC  &&ₑ ′DNUM !=ₑ ′4 ){ RETURN ′4 }
                        ELSE{
                            IF ((read_ipcgr′  &ₑ ′CORE5_IPC) ==ₑ ′CORE5_IPC  &&ₑ ′DNUM !=ₑ ′5 ){ RETURN ′5 }
                            ELSE{
                                IF ((read_ipcgr′  &ₑ ′CORE6_IPC) ==ₑ ′CORE6_IPC  &&ₑ ′DNUM !=ₑ ′6 ){ RETURN ′6 }
                                ELSE{
                                IF ((read_ipcgr′  &ₑ ′CORE7_IPC) ==ₑ ′CORE7_IPC  &&ₑ ′DNUM !=ₑ ′7 ){ RETURN ′7 }
                                ELSE { RETURN ′(Zneg xH) }
                                }
                            }
                        }
                    }
                }
            }
        }
        }·. *)

Definition Refactsend_impl := 
    Int16u ·Refactsend·(⌞dstCore @ Int8u; srcAddr @ Int8u∗ ; 
                        size @ Tint32⌟)··{
        ⌞
            step @ Int32;
            ipcinfo @Int32u ⌟; 
        If (srcAddr ′ ==ₑ NULL ||ₑ  size′ <ₑ ′1 ||ₑ size′ >ₑ ′IPC_STEP ||ₑ 
        dstCore′ >ₑ( ′CORENUM − ′1) ||ₑ dstCore′ ==ₑ ′DNUM ){
            RETURN ′EINVAL
        };ₛ

        IF (′DNUM >ₑ dstCore′){
            step′ =ₑ ′DNUM − ′1
        } ELSE {
            step′ =ₑ ′DNUM
        };ₛ
        
        ENTER_CRITICAL;ₛ
        memcpy(­ 〈 Int8u∗ 〉(IPCMem′[dstCore′] +ₑ step′ × ′IPC_STEP) , srcAddr′ , size′ ­);ₛ
        EXIT_CRITICAL;ₛ

        ipcinfo′ =ₑ ′0;ₛ
        IF (′DNUM ==ₑ ′0){ ipcinfo′ =ₑ ′CORE0_IPC } ELSE {
        IF (′DNUM ==ₑ ′1){ ipcinfo′ =ₑ ′CORE1_IPC } ELSE {
        IF (′DNUM ==ₑ ′2){ ipcinfo′ =ₑ ′CORE2_IPC } ELSE {
        IF (′DNUM ==ₑ ′3){ ipcinfo′ =ₑ ′CORE3_IPC } ELSE {
        IF (′DNUM ==ₑ ′4){ ipcinfo′ =ₑ ′CORE4_IPC } ELSE {
        IF (′DNUM ==ₑ ′5){ ipcinfo′ =ₑ ′CORE5_IPC } ELSE {
        IF (′DNUM ==ₑ ′6){ ipcinfo′ =ₑ ′CORE6_IPC } ELSE {
        IF (′DNUM ==ₑ ′7){ ipcinfo′ =ₑ ′CORE7_IPC }
                    ELSE { ipcinfo′ =ₑ ′CORE0_IPC }
        } } } } } } };ₛ
        
        GENERATEIPC(dstCore′ , (ipcinfo′ |ₑ ′ REFACTOR_RDY));ₛ

        RETURN ′OS_NO_ERR
    }·.
    
Definition doRefactorISR_impl:=
    Void  ·doRefactorISR·(⌞srcCore @ Int32u⌟)··{
    ⌞
        dynrefaccfg @ dyn_refac_cfg ∗;
        step @ Int32⌟; 
        If (dynrefaccfgFreeList′ !=ₑ NULL){
            dynrefaccfg′ =ₑ dynrefaccfgFreeList′;ₛ
            dynrefaccfgFreeList′ =ₑ dynrefaccfgFreeList′→Next;ₛ
                
            IF (srcCore′ >ₑ ′DNUM){
                step′ =ₑ srcCore′ − ′1
            } ELSE {
                step′ =ₑ srcCore′
            };ₛ
            memcpy4(­ 〈 Void∗ 〉(dynrefaccfg ′) , 〈 Void ∗ 〉(IPCMem′[′ DNUM] +ₑ step′ × ′IPC_STEP) , ′ size_of_dyn_refac_cfg ­);ₛ
            (*OSTCBCur′→__OSTskQPtr =ₑ eptrconst dynrefcmsgQ_addr ;ₛ*)
            OSIPCQPost(- dynrefcmsgQ ′, 〈Void∗ 〉dynrefaccfg′ -)(*;ₛ 
            OSTCBCur′→__OSTskQPtr =ₑ NULL*)
        };ₛ
        RETURN
    }·.      

Definition LoadElf2Mem_impl := 
    Void ∗ ·LoadElf2Mem·(⌞file @ Void ∗⌟)··{
        ⌞ 
        Pro_header @ Elf32_Phdr ∗;
        Elf_header @ Elf32_Ehdr ∗;
        Pro_header_ptr @ Elf32_Phdr ∗;
        i @ Int16u;
        addrPoint @ Void ∗

        ⌟;
        Pro_header ′ =ᶠ malloc_Elf32_Phdr (·);ₛ
        Elf_header ′ =ᶠ malloc_Elf32_Ehdr (·);ₛ
        i ′ =ₑ ′ 0;ₛ
        addrPoint ′ =ₑ NULL;ₛ
        memcpy2 (-〈 (Void) ∗ 〉 Elf_header ′, file ′ -);ₛ
        Pro_header_ptr ′ =ₑ 〈 Elf32_Phdr ∗ 〉 (〈 (Int8u) ∗ 〉 file ′ +ₑ Elf_header ′ → e_phoff);ₛ
        memcpy3 (-〈 (Void) ∗ 〉 Pro_header ′, 〈 (Void) ∗ 〉 Pro_header_ptr ′ -);ₛ
        WHILE (Elf_header ′ → e_phnum >ₑ i ′)
        {
            i ′=ₑ  i ′ +ₑ ′1 ;ₛ
            IF (Pro_header ′ → p_type !=ₑ ′ PT_LOAD){
                Pro_header_ptr ′ =ₑ 〈 Elf32_Phdr ∗ 〉 (〈 (Int8u) ∗ 〉 Pro_header_ptr ′ +ₑ ′ size_of_Elf32_Phdr);ₛ
                memcpy3 (-〈 (Void) ∗ 〉 Pro_header ′, 〈 (Void) ∗ 〉 Pro_header_ptr ′ -)
            }
            ELSE 
            {
                If (Pro_header ′ → p_filesz){
                    memcpy (­〈 (Int8u) ∗ 〉 Pro_header ′ → p_vaddr, (〈 (Int8u) ∗ 〉 file ′ +ₑ Pro_header ′ → p_offset), Pro_header ′ → p_filesz ­)
                };ₛ
                If (Pro_header ′ → p_memsz >ₑ Pro_header ′ → p_filesz){
                    memset (- 〈 (Int8u) ∗ 〉 (〈 (Int8u) ∗ 〉 Pro_header ′ → p_vaddr +ₑ Pro_header ′ → p_filesz), Pro_header ′ → p_memsz − Pro_header ′ → p_filesz -)
                };ₛ
                Pro_header_ptr ′ =ₑ 〈 Elf32_Phdr ∗ 〉 (〈 (Int8u) ∗ 〉 Pro_header_ptr ′ +ₑ ′ size_of_Elf32_Phdr);ₛ
                memcpy3 (-〈 (Void) ∗ 〉 Pro_header ′, 〈 (Void) ∗ 〉 Pro_header_ptr ′ -)
            }
        };ₛ
        addrPoint ′ =ₑ Elf_header ′ → e_entry;ₛ
        (scall free_Elf32_Phdr (Pro_header ′ ::nil));ₛ
        (scall free_Elf32_Ehdr (Elf_header ′ ::nil));ₛ
    RETURN addrPoint ′ }·. 


Definition dynamic_refactor_pend_impl:=
    Int32u ·dynamic_refactor_pend·(⌞timeout @ Int16u ⌟)··{
    ⌞ 
        dynrefaccfg @ dyn_refac_cfg ∗;
        err @ Int8u; 
        i @ Int8u ;
        TaskEntry @ Void ∗;
        stkaddr @ Void ∗;
        prio @ Int32u;
        flag @ Int32u
        ⌟;
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskQPtr =ₑ eptrconst dynrefcmsgQ_addr ;ₛ
        EXIT_CRITICAL;ₛ
        dynrefaccfg′  =ᶠ OSQPend(· eptrconst dynrefcmsgQ_addr, timeout′  , &ₐ err′   ·) ;ₛ 
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskQPtr =ₑ NULL;ₛ 
        EXIT_CRITICAL;ₛ
        If (dynrefaccfg′ ==ₑ NULL){ 
            RETURN ′ -1
        };ₛ 
    (*       If (err′ !=ₑ  ′ OS_NO_ERR){ 
        RETURN err′
        };ₛ   *)
        i′ =ₑ′ 1 ;ₛ 
        WHILE (i ′  <ₑ  ′ OS_LOWEST_PRIO − ′ OS_N_SYS_TASKS )
        {
            ENTER_CRITICAL;ₛ
            IF (OSTCBPrioTbl′[i′] !=ₑ NULL )
            {
                EXIT_CRITICAL;ₛ
                err ′ =ᶠ OSTaskDel (· i ′ ·);ₛ
                If (err′ !=ₑ ′ OS_NO_ERR )
                {
                    RETURN err ′
                }
            }
            ELSE
            {
                EXIT_CRITICAL
            };ₛ 
            i ′=ₑ  i ′ +ₑ ′1 
        };ₛ
        TaskEntry ′ =ᶠ LoadElf2Mem' (· 〈 (Void) ∗ 〉  (dynrefaccfg ′ → elf) ·);ₛ
        prio ′ =ₑ dynrefaccfg ′ → prio;ₛ 
        ENTER_CRITICAL;ₛ 
        dynrefaccfg ′ → Next =ₑ dynrefaccfgFreeList ′ ;ₛ
        dynrefaccfgFreeList ′ =ₑ dynrefaccfg ′;ₛ
        EXIT_CRITICAL;ₛ
        flag ′ =ᶠ OSTaskCreate (·  TaskEntry  ′ , NULL, prio ′ ·);ₛ
        If (flag′ !=ₑ  ′ OS_NO_ERR){ 
            RETURN ′ ( -1 )
        };ₛ 
        RETURN  ′ 0 
    }·.        

Definition dyn_refac_init_impl := 
    Void ·dyn_refac_init·(⌞⌟)··{
        ⌞ 
        i @ Int8u;
        prefcfg1 @ dyn_refac_cfg ∗;
        prefcfg2 @ dyn_refac_cfg ∗
        ⌟;

        prefcfg1′ =ₑ &ₐ dynrefaccfgTbl′[′0];ₛ
        prefcfg2′ =ₑ &ₐ dynrefaccfgTbl′[′1];ₛ
        i′ =ₑ ′0;ₛ
        WHILE (i′ <ₑ (′REFAC_MSG_QUEE_MAX_LEN− ′1)) {
            prefcfg1′→Next =ₑ prefcfg2 ′;ₛ
            ++ prefcfg1′;ₛ
            ++ prefcfg2′;ₛ
            ++ i′
        };ₛ
        prefcfg1′→Next =ₑ NULL;ₛ
        dynrefaccfgFreeList′ =ₑ &ₐ NULL;ₛ
        RETURN
    }·. 
