Require Import os_code_defs.
Require Import code_notations.

Definition OSTCBStkPtr : ident := 27101%Z.
Definition OSInthandler := 27102%Z.
Definition OSInthandlerParam := 27103%Z.

Open Scope code_scope.

Definition OS_EVENT : type := 
  STRUCT os_event ­{ 
                    ⌞OSEventType @ Int8u;
                    OSEventGrp @ Int8u; 
                    OSEventCnt @ Int16u; 
                    OSEventPtr @ (Void ∗);
                    OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE);
                    OSEventListPtr @ STRUCT os_event ⋆;
                    OSPostEventGrp @ Int8u; 
                    OSPostEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE)⌟ 
                   }­.


Definition OS_Q_FREEBLK : type :=
  STRUCT os_q_freeblk ­{
                        ⌞nextblk @ STRUCT os_q_freeblk ⋆ ; 
                        msgqueuetbl @ (Tarray (Void ∗) ∘OS_MAX_Q_SIZE)⌟
                       }­.


Definition OS_Q : type := 
    STRUCT os_q ­{
                  ⌞OSQPtr @ Void ∗;
                  OSQStart @ Void ∗ ∗;
                  OSQEnd @ Void ∗ ∗;
                  OSQIn @ Void ∗ ∗;
                  OSQOut @ Void ∗ ∗;
                  OSQSize @ Int16u ;
                  OSQEntries @ Int16u ;
                  qfreeblk @ OS_Q_FREEBLK ∗⌟
           }­.

Definition OS_STK : type := Int32.

Definition OS_TCB : type := 
    STRUCT os_tcb ­{
        ⌞OSTCBNext @ STRUCT os_tcb ⋆;
        OSTCBPrev @ STRUCT os_tcb ⋆ ;
        OSTCBEventPtr @ OS_EVENT ∗ ; 
        OSTCBMsg @ Void ∗ ;
        OSTCBDly @ Int16u ;
        OSTCBStat @ Int16u ;
        OSTCBPrio @ Int8u ;
        OSTCBX @ Int8u ;
        OSTCBY @ Int8u ; 
        OSTCBBitX @ Int8u;
        OSTCBBitY @ Int8u;
        OSTCBflag @ Int8u ;
        OSTCBStkPtr @ OS_STK ∗;
        __OSTskEvLoc @ Int8u ;
        __OSTskMuxPtr @ Tptr OS_EVENT; 
        __OSTskSemPtr @ Tptr OS_EVENT;
        __OSTskQPtr @ Tptr OS_EVENT;
        tcb_cap @ (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS))
        ⌟
    }­.




Definition OS_STK_BLK : type := 
  STRUCT os_stk_blk ­{
                      ⌞nextblk @ Void ∗;
                      taskstk @ (Tarray OS_STK ∘TASK_STK_SIZE)⌟
                     }­.



(*********************** structures for GJB events ***********************)

Definition sem_info_t : type := 
  STRUCT sem_info ­{ 
    ⌞sem_type @ Int32;
    sem_name @ (char_t ∗) ; 
    sem_maxvalue @ Int32; 
    sem_curvalue @ Int32;
    sem_opencnt @ Int32;
    sem_linked @ Int32;
    tasks_blocked @ Int32;
    pevent @ (OS_EVENT ∗) ;
    (* del_flag @ Int32 *)
    sem_cap @ (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS))
  ⌟
  }­.


Definition timespec_t : type := 
  STRUCT timespec ­{ 
                    ⌞
                    timeout @ Int16u
                  ⌟
                   }­.


Definition pthread_mutexattr_t : type := 
  STRUCT pthread_mutexattr ­{ 
                    ⌞is_initialized @ Int32;
                    process_shared @ Int32; 
                    prio_ceiling@ Int32; 
                    protocol @ Int32; 
                    recursive @ Int32; 
                    waitq_type @ Int32; 
                    cancel_safe @ Int32⌟
                   }­.


Definition pthread_mutex_info_t : type := 
  STRUCT pthread_mutex_info ­{ 
      ⌞mutex_type @ Int32;
      protocol @ Int32; 
      prio_ceiling @ Int32; 
      waitq_type @ Int32;
      cancel_safe @ Int32;
      mutex_owner @ pthread_t;
      recursive_cnt @ Int32;
      tasks_blocked @ Int32;
      pevent @ OS_EVENT ∗ ;
      mutex_cap @  (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS))
      ⌟
  }­.

(* Definition Mq_Attr := Tarray mq_attr' ∘(OS_USER_MAX_EVENTS ÷ 3 ). *)

Definition mq_attr_t : type := 
  STRUCT mq_attr ­{ 
      ⌞mq_waittype @ Int32;
      mq_flags @ long; 
      mq_maxmsg @ long;
      mq_msgsize @ long;
      mq_curmsgs @ long;
      pevent @ OS_EVENT ∗ ;
      mq_cap @  (Tarray Int8u ∘(OS_MAX_TASKS - OS_N_SYS_TASKS))
    ⌟
      }­.

Definition mq_info_t : type := 
    STRUCT mq_info ­{
                  ⌞
                  mq_waittype @ Int32; 
                  mq_flags @ Long; 
                  mq_maxmsg @ Long;
                  mq_msgsize @ Long;
                  mq_curmsgs @ Long;
                  task_blocked @ Int8u;
                  OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE) 
                  ⌟
                 }­.

Definition OS_Q_DATA : type := 
    STRUCT os_q_data ­{
                  ⌞
                  OSMsg @ Void ∗; 
                  OSNMsgs @ Int16u; 
                  OSQSize @ Int16u;
                  OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE) ;
                  OSEventGrp @ Int8u
                  ⌟
                 }­.

Definition pthread_attr_t : type := 
    STRUCT pthread_attr ­{ 
                          ⌞stackaddr @ (Void ∗);
                          stacksize @ Int32;
                          sched_priority @ Int8u
                        ⌟
                          }­.
(*********************** end structures for GJB events ***********************)

(*********************** structures for ucos_conf_t  ***********************)

Definition deviceio_conf_t:type:=
 STRUCT  DeviceIO_CONF ­{
                  ⌞
                  deviceId @ (Tarray char_t ∘10%Z); 
                  startAddr @ Int32u;
                  dvsize @ Int32u
                    ⌟
                 }­.

Definition cap_conf_t : type := 
  STRUCT  Cap_CONF ­{ 
                    ⌞
                   TaskEn @ Int8u;
                   PartitionEn @ Int8u;
                   InterCommEn @ Int8u;
                   IntraCommSemEn @ Int8u;
                   IntraCommMutexEn @ Int8u;
                   IntraCommQueueEn @ Int8u
                  ⌟
                   }­. 

 Definition domain_conf_t : type := 
  STRUCT  DOMAIN_CONF ­{ 
                    ⌞
                   domain @ Int8u;
                   coreId @ Int8u;
                   dom_ID @ Int8u;
                   binAddress @ Int32u;
                   RootTaskPrio @ Int8u;
                   OSPartitionPeriod @ Int32u;
                   pAddress @ Int32u;
                   vAddress @ Int32u;
                   dom_len @ Int32u;
                   domaincf_size @ Int8u;
                   status @ Int32u;
                   portRdyGrp @ Int8u;
                   portRdyTbl @ (Tarray Int8u ∘8%Z ) ; 
                   DeviceNum @ Int8u;
                   DeviceioTbl @ (Tarray deviceio_conf_t ∘3%Z );
                   CapEnTbl @ cap_conf_t
                  ⌟
                   }­.

Definition area_t : type := 
  STRUCT AREA ­{ 
                    ⌞
                    areat_pAddress @ Int32u;
                    areat_vAddress @ Int32u;
                    areat_size @ Int32u
                  ⌟
                   }­.

Definition area_conf_t : type := 
  STRUCT AREA_CONF ­{ 
                    ⌞
                    pAddress @ Int32u;
                    vAddress @ Int32u;
                    size @ Int32u;
                    len @ Int32u
                  ⌟
                   }­.

Definition channel_conf_t : type := 
  STRUCT CHANNEL_CONF ­{ 
                    ⌞
                   coreType @ Int8u;
                   ch_ID @ Int8u;
                   channelType @ Int8u;
                   srcportID @ Int8u;
                   dstGrp @ Int8u;
                   dstTbl @ (Tarray Int8u ∘8%Z )
                  ⌟
                   }­.

Definition port_conf_t : type := 
  STRUCT PORT_CONF ­{ 
                    ⌞
                   port_ID @ Int8u;
                   direction @ Int8u;
                   channeltype @ Int8u;
                   partitionID @ Int8u;
                   channelID @ Int8u
                  ⌟
                   }­.

Definition dschedule_conf_t:type:=
 STRUCT  dschedule_conf ­{
                  ⌞
                  ds_domain @ Int32u; 
                  dslength @ Int32u 
                    ⌟
                 }­.

Definition cpu_conf_t : type := 
  STRUCT CPU_CONF ­{ 
                    ⌞
                    core @ Int32u;
                    domainRdy @ (Tarray Int8u ∘2%Z);
                    cpu_ksDomScheduleLength @ Int32u;
                    ksDomainLength @ Int32u;
                    cpu_ksDomSchedule @ (Tarray dschedule_conf_t ∘DSCHEDULE_SIZE) ;
                    cpu_ksDomains @ (Tarray domain_conf_t ∘CORENUM) 
                  ⌟
                   }­.

Definition ucos_conf_t:type:=
 STRUCT UCOS_CONF­{
                  ⌞
                  magicf @ Int32; 
                  fileVersion @ Int32; 
                  coreNums @ Int8u;
                  noPartitions @ Int8u;
                  noCommChannels @ Int8u;
                  noPorts @ Int8u;
                  IntrDomainMux @ (Tarray Int8u ∘11%Z ); 
                  allArea @ area_conf_t;
                  cpus @ (Tarray cpu_conf_t ∘ CORENUM );
                  channelTbl @ (Tarray channel_conf_t ∘CHANNEL_NUMS );
                  portRdyGrp @ Int8u;
                  portRdyTbl @ (Tarray Int8u ∘8%Z );
                  portTbl @ (Tarray port_conf_t∘PORT_NUMS);
                  magicl @ Int32u  ⌟
                 }­.

Definition domain_t : type := 
  STRUCT  DOMAIN ­{ 
                    ⌞
                   DTdomain     @ dom_t;
                   dom_t_ID  @ Int8u;
                   dom_t_OSPartitionPeriod @ time_t;
                   dom_t_pAddress  @ Int32u;
                   dom_t_vAddress  @ Int32u;
                   dom_t_len @ Int32u;
                   dom_t_size @ Int8u;
                   dom_t_status @ Int8u;
                   domainIntStatusTbl @ (Tarray Int8u ∘USER_INT_MAX_N )  
                  ⌟
                   }­.

Definition dschedule_t:type:=
 STRUCT dschedule­{
                  ⌞
                  dscd_domain @ dom_t; 
                  dscd_length @ time_t
                   ⌟
                 }­.

Definition port_attr_t : type := 
  STRUCT port_attr ­{ 
                    ⌞portat_enable @ Int8u;
                    portat_partitionID @ Int8u; 
                    portat_domain @ Int8u; 
                    portat_direction @ Int8u;
                    portat_mode @ Int8u;
                    portat_channnelID @ Int8u⌟ 
                   }­.

(*********************** end structures for ucos_conf_t  ***********************)

Definition gvarlist1 : decllist := 
             ⌞ 
              OSCtxSwCtr @ Int32u ;
              OSEventList @ OS_EVENT ∗ ;
              OSEventFreeList @ OS_EVENT ∗ ;
              OSEventTbl @ (Tarray OS_EVENT ∘OS_MAX_EVENTS);
              OSIntNesting @ Int8u;                                       
              OSIntExitY @ Int8u;
              OSPrioCur @ Int8u;
              OSPrioHighRdy @ Int8u;
              OSRdyGrp @ Int8u;
              OSRdyTbl @ (Tarray Int8u ∘OS_RDY_TBL_SIZE);
              OSRunning @ Int8u                                       
             ⌟.

Definition gvarlist2 :decllist := 
             ⌞ 
              OSTaskCtr @ Int8u;
              OSIdleCtr @ Int32u;
              OSTCBCur @ OS_TCB ∗;
              OSTCBFreeList @ OS_TCB ∗;
              OSTCBHighRdy @ OS_TCB ∗; 
              OSTCBList @ OS_TCB;                                       
              OSTCBPrioTbl @ (Tarray (OS_TCB ∗ ) ∘(OS_LOWEST_PRIO + 1)%Z );
              OSTCBTbl @ (Tarray OS_TCB ∘(OS_LOWEST_PRIO + 1));
              OSQFreeBlk @ OS_Q_FREEBLK ∗;
              OSQFreeBlkTbl @ (Tarray OS_Q_FREEBLK ∘OS_MAX_QS)
            ⌟.

Definition gvarlist3 :decllist := 
             ⌞
              OSQFreeList @ OS_Q ∗;
              OSQTbl @ (Tarray OS_Q ∘OS_MAX_QS);
              OSTime @ Int32u;
              OSMapTbl @ (Tarray Int8u 8);                                                   
              OSUnMapTbl @ (Tarray Int8u 256)
             ⌟.


Fixpoint plus_decl  (d1 d2 : decllist) {struct d1} :=
    match d1 with
     | dnil => d2
     | dcons x t d1' => dcons x t (plus_decl d1' d2)
    end.


Definition GlobalVariables := 
  plus_decl (plus_decl gvarlist1 gvarlist2) gvarlist3.

(* add by SJTU *)
Definition OSTimerRegs : type := 
    STRUCT OS_Timer_Regs ­{
                  ⌞OSRSVD0 @ Int32u;
                   OSEMUMGT @Int32u;
                   OSRSVD1 @ (Tarray Int32u 2%nat);
                   OSCNTLO @ Int32u;
                   OSCNTHI @ Int32u;
                   OSPRDLO @ Int32u;
                   OSPRDHI @ Int32u;
                   OSTCRreg @ Int32u;
                   OSTGCR @ Int32u
                  ⌟
                 }­.

Definition dyn_refac_cfg: type:=
  STRUCT refac_cfg ­{
                  ⌞dstcoreid @ Int32;
                   prio @Int32;
                   pdata @ Void ∗;
                   elf @ Void ∗;
                   Next @ STRUCT refac_cfg ⋆
                  ⌟
                 }­.
                
                 
Definition Elf32_Ehdr:type:=
  STRUCT elf32ehdr­{
                  ⌞e_type @ Int16u;
                   e_machine @Int16u;
                   e_version @Int32u;
                   e_entry @ Void ∗;
                   e_phoff @ Int32u;
                   e_shoff @ Int32u;
                   e_flags @ Int32u;
                   e_ehsize @ Int16u;
                   e_phentsize @ Int16u;
                   e_phnum @ Int16u;
                   e_shentsize @ Int16u;
                   e_shnum @ Int16u;
                   e_shstrndx @ Int16u
                  ⌟
                 }­.

Definition Elf32_Phdr:type:=
  STRUCT elf32phdr ­{
                  ⌞p_type @ Int32u;
                   p_offset @ Int32u;
                   p_vaddr @ Void ∗;
                   p_paddr @ Int32u;
                   p_filesz @ Int32u;
                   p_memsz @ Int32u;
                   p_flags @ Int32u;
                   p_align @ Int32u
                  ⌟
                 }­.

(* Definition of struct OSMsg in C file, but the name has been occupied as a field of OS_Q_DATA *)
Definition OSMsg_t : type := 
    STRUCT os_message ­{
                  ⌞len @ Int8u;
                   data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE)
                  ⌟
                 }­.

Definition OS_Port:type:=
  STRUCT os_domain_port ­{
                  ⌞
                  (* first 8 is OS_EVENT *)
                   OSEventType @ Int8u;
                   OSEventGrp @ Int8u; 
                   OSEventCnt @ Int16u; 
                   OSEventPtr @ (Void ∗);
                   OSEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE);
                   OSEventListPtr @ STRUCT os_event ⋆;
                   OSPostEventGrp @ Int8u; 
                   OSPostEventTbl @ (Tarray Int8u ∘OS_EVENT_TBL_SIZE);
                  (* remain for OS_Port *) 
                   domain @ Int32u;
                   maxMsgSize @ Int8u;
                   coreNum @ Int8u;
                   portID @ Int32u;
                   direction @ port_direction_t;
                   mode @ port_mode_t;
                   refreshRate @ Int32u;
                   status @ port_ctrl_status_t;
                   msgInTick @ Int32u;
                   msgOutTick @ Int32u;
                   OSEventPtrPort @ Void ∗;
                   nextPort @ Void ∗;
                   OSQStart @ OSMsg_t ∗;
                   OSQEnd @ OSMsg_t ∗;
                   OSQIn @ OSMsg_t ∗;
                   OSQOut @ OSMsg_t ∗;
                   OSQSize @ Int16u;
                   OSQEntries @ Int16u
                  ⌟
                 }­.

Definition OS_K_Port:type:=
  STRUCT os_k_port ­{
    ⌞portID @ Int8u;
    channelID @ Int8u;
    dmport @ OS_Port ∗; 
    channel @ Void ∗;
    coreNum @ Int8u;
    status @ port_ctrl_status_t;
    OSEventPtr @ Void ∗
    ⌟
  }­.

Definition OS_Channel:type:=
  STRUCT os_channel  ­{
    ⌞ channelID @ Int8u;
    srcPortsNum @ Int8u;
    dstPortsNum @ Int8u;
    semaphore @ Int8u;
    dstPortsHead @ OS_K_Port ∗;
    dstPortsTail @ OS_K_Port ∗;
    srcPort @ OS_K_Port ∗;
    OSEventPtr @ Void ∗
    ⌟
  }­.

Definition channel_semaphore_t : type := 
  STRUCT channel_semaphore ­{
                ⌞count @ Int8u;
                  freeTbl @ Int8u
                ⌟
                }­.

Definition OSdomain_t : type :=
  STRUCT osdomain_t  ­{
    ⌞ domain @ Int32u;
    domainID @ Int8u;
    OSPartitionPeriod @ Int32u;
    pAddress @ Int32u;
    vAddress @ Int32u;
    len @ Int32u;
    size @ Int8u;
    status @ Int8u;
    domainIntStatusTbl @ (Tarray Int8u ∘USER_INT_MAX_N)
    ⌟
  }­.

Definition OSport_attr_t : type :=
  STRUCT osport_attr_t  ­{
    ⌞ enable @ Int8u;
    partitionID @ Int8u;
    domain @ Int8u;
    direction @ port_direction_t;
    mode @ port_mode_t;
    channelID @ Int8u
    ⌟
  }­.
(* end add by SJTU *)
Close Scope code_scope.