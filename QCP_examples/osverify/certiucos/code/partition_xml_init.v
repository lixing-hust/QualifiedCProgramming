Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import ios_cap_defs.

Open Scope code_scope.

Definition is_bigEndian_impl := 
    Int8u ·is_bigEndian·(⌞ ⌟)··{
        ⌞
         a @ Int32;
         b @ char_t
        ⌟;

        a′ =ₑ  ′0x1234;ₛ
        b′ =ₑ ∗(〈char∗〉(&ₐa′));ₛ
        If (b′ ==ₑ ′0x34){
             RETURN  ′0
        };ₛ
        RETURN  ′1
}· .

Definition InitDNUM_impl := 
    Void ·InitDNUM·(⌞uconf @ ucos_conf_t∗; coreNum @ Int8u; isSame @ Int8u⌟)··{
        ⌞
         i @ Int32;
         j @ Int32;
         flag @ Int32;
         len @ Int32 ;

         to1 @ Int8u ;
         to2 @ Int8u ;
         to3 @ Int8u ;
         to4 @ Int8u ;
         to5 @ Int8u ;
         to6 @ Int8u ;
         to7 @ Int8u ;
         to8 @ Int8u ;

         tox1 @ Int32u ;
         tox2 @ Int32u ;
         tox3 @ Int32u ;
         tox4 @ Int32u 
           ⌟;
       
        i′ =ₑ ′0;ₛ   
        j′ =ₑ ′0;ₛ 

        WHILE (i′ <ₑ ′DOMAIN_SIZE) {
            tox1 ′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..binAddress;ₛ 
            If (tox1 ′ !=ₑ ′0){
            to1′ =ₑ  ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..domain;ₛ 
            Domain2Index′[ to1′ ] =ₑ j′;ₛ 
            ++ j′
            };ₛ 
            ++ i′
        };ₛ

        len′ =ₑ ((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength ;ₛ 
        Core_partition_num′  =ₑ ((uconf′→ cpus)[coreNum′])..ksDomainLength ;ₛ
        Port_num_cur′  =ₑ ′0 ;ₛ 
        tox1′  =ₑ (uconf′→ allArea)..pAddress ;ₛ 
        tox2′  =ₑ (uconf′→ allArea)..vAddress ;ₛ 
        tox3′  =ₑ (uconf′→ allArea)..size ;ₛ

        OSAll_Partition_Area′→areat_pAddress  =ₑ tox1′ ;ₛ 
        OSAll_Partition_Area′→areat_vAddress  =ₑ tox2′ ;ₛ 
        OSAll_Partition_Area′→areat_size  =ₑ tox3′ ;ₛ

        i′ =ₑ ′0;ₛ
        WHILE (i′ <ₑ len′) {
            j′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..ds_domain ;ₛ 

            to1′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..dom_ID ;ₛ   
            to2′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..domain ;ₛ   
            tox1′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..OSPartitionPeriod ;ₛ   
            tox2′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..pAddress ;ₛ   
            tox3 ′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..vAddress ;ₛ   
            tox4′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..dom_len ;ₛ   
            to3′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..domaincf_size ;ₛ  

            (ksDomains′[j′])..dom_t_ID  =ₑ to1′ ;ₛ   
            (ksDomains′[j′])..DTdomain  =ₑ to2′ ;ₛ   
            (ksDomains′[j′])..dom_t_OSPartitionPeriod  =ₑ tox1′ ;ₛ   
            (ksDomains′[j′])..dom_t_pAddress  =ₑ tox2′ ;ₛ   
            (ksDomains′[j′])..dom_t_vAddress  =ₑ tox3′ ;ₛ   
            (ksDomains′[j′])..dom_t_len  =ₑ tox4′ ;ₛ   
            (ksDomains′[j′])..dom_t_size  =ₑ to3′ ;ₛ   

            partitionID2Domain′[ to1′ ] =ₑ to2′ ;ₛ
            ++ i′
        };ₛ

        len′ =ₑ ((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength ;ₛ 
        ksDomScheduleLength′ =ₑ 〈Int8u〉len′;ₛ

        i′ =ₑ ′0;ₛ 
        WHILE (i′ <ₑ len′) {
            tox1′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..ds_domain ;ₛ   
            tox2′  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..dslength ;ₛ   

            (ksDomSchedule′[i′])..dscd_domain  =ₑ tox1′ ;ₛ   
            (ksDomSchedule′[i′])..dscd_length  =ₑ tox2′ ;ₛ   
            ++ i′
        };ₛ

        i′ =ₑ ′0;ₛ 
        to1′ =ₑ uconf′→noPorts;ₛ 
        WHILE (i′ <ₑ to1′) {
           j′ =ₑ  ′0;ₛ 
           flag′ =ₑ ′1;ₛ
           WHILE ((j′ <ₑ len′) &&ₑ flag′) {
            to2′ =ₑ ((uconf′→ portTbl)[i′])..partitionID ;ₛ 
            tox2′ =ₑ (efield (ksDomSchedule′[j′]) dscd_domain);ₛ
            to3′  =ₑ (ksDomains′ [ tox2′ ])..dom_t_ID  ;ₛ 
             IF (to2′ ==ₑ  to3′){

              to4′ =ₑ ((uconf′→ portTbl)[i′])..port_ID ;ₛ 
              to5′ =ₑ ((uconf′→ portTbl)[i′])..direction ;ₛ 
              to6′ =ₑ ((uconf′→ portTbl)[i′])..channeltype;ₛ 
              to7′ =ₑ ((uconf′→ portTbl)[i′])..channelID;ₛ 
              to8′ =ₑ partitionID2Domain′[to2′]  ;ₛ

              efield (OSPortAttrTbl′[to4′]) portat_partitionID =ₑ to2′ ;ₛ
              efield (OSPortAttrTbl′[to4′]) portat_domain =ₑ to8′ ;ₛ
              efield (OSPortAttrTbl′[to4′]) portat_direction =ₑ to5′ ;ₛ
              efield (OSPortAttrTbl′[to4′]) portat_mode =ₑ to6′ ;ₛ
              efield (OSPortAttrTbl′[to4′]) portat_channnelID =ₑ to7′ ;ₛ
              efield (OSPortAttrTbl′[to4′]) portat_enable =ₑ ′1;ₛ
              ++ Port_num_cur′ ;ₛ
              flag′ =ₑ ′0
              }
              ELSE{
                ++ j′
              } 
            };ₛ
            ++ i′
        };ₛ
    RETURN
}· .
(* Definition InitDNUM_impl := 
    Void ·InitDNUM·(⌞uconf @ ucos_conf_t∗; coreNum @ Int8u; isSame @ Int8u⌟)··{
        ⌞
         i @ Int32;
         j @ Int32;
         flag @ Int32;
         len @ Int32
        ⌟;
       
        i′ =ₑ ′0;ₛ   
        j′ =ₑ ′0;ₛ 

        ENTER_CRITICAL;ₛ

        WHILE (i′ <ₑ ′DOMAIN_SIZE) {
            If (((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..binAddress !=ₑ ′0){
            Domain2Index′[((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..binAddress] =ₑ j′;ₛ 
            ++ j′
            };ₛ 
            ++ i′
        };ₛ

        len′ =ₑ ((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength ;ₛ 
        Core_partition_num′  =ₑ ((uconf′→ cpus)[coreNum′])..ksDomainLength ;ₛ
        Port_num_cur′  =ₑ ′0 ;ₛ 
        OSAll_Partition_Area′..areat_pAddress  =ₑ (uconf′→ allArea)..pAddress ;ₛ 
        OSAll_Partition_Area′..areat_vAddress  =ₑ (uconf′→ allArea)..vAddress ;ₛ 
        OSAll_Partition_Area′..areat_size  =ₑ (uconf′→ allArea)..size ;ₛ

        i′ =ₑ ′0;ₛ
        WHILE (i′ <ₑ len′) {
            j′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..ds_domain ;ₛ 
            (ksDomains′[j′])..dom_t_ID  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..dom_ID ;ₛ   
            (ksDomains′[j′])..DTdomain  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..domain ;ₛ   
            (ksDomains′[j′])..dom_t_OSPartitionPeriod  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..OSPartitionPeriod ;ₛ   
            (ksDomains′[j′])..dom_t_pAddress  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..pAddress ;ₛ   
            (ksDomains′[j′])..dom_t_vAddress  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..vAddress ;ₛ   
            (ksDomains′[j′])..dom_t_len  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..dom_len ;ₛ   
            (ksDomains′[j′])..dom_t_size  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[j′])..domaincf_size ;ₛ   
            partitionID2Domain′[(ksDomains′[j′])..dom_t_ID] =ₑ (ksDomains′[j′])..DTdomain ;ₛ
            ++ i′
        };ₛ

        len′ =ₑ ((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength ;ₛ 
        ksDomScheduleLength′ =ₑ 〈Int8u〉len′;ₛ

        i′ =ₑ ′0;ₛ 
        WHILE (i′ <ₑ len′) {
                (ksDomSchedule′[i′])..dscd_domain  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..ds_domain ;ₛ   
                (ksDomSchedule′[i′])..dscd_length  =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[i′])..dslength ;ₛ   
            ++ i′
        };ₛ
        (* i′ =ₑ ′0;ₛ 
        WHILE (i′ <ₑ conf′→ noPorts) {
            j′ =ₑ ′0;ₛ 
            flag′ =ₑ ′1;ₛ
            WHILE ((j′ <ₑ len′) &&ₑ flag′) {
                If (((conf′→ portTbl)[i′])..partitionID ==ₑ (ksDomains′[(ksDomSchedule′[j′])..domain])..ID){
                        (OSPortAttrTbl′[(((conf′→ portTbl)[i′])..ID)])..partitionID =ₑ ((conf′→ portTbl)[i′])..partitionID;ₛ 
                        (OSPortAttrTbl′[(((conf′→ portTbl)[i′])..ID)])..domain =ₑ partitionID2Domain′[((conf′→ portTbl)[i′])..partitionID];ₛ 
                        (OSPortAttrTbl′[(((conf′→ portTbl)[i′])..ID)])..direction =ₑ ((conf′→ portTbl)[i′])..direction;ₛ 
                        (OSPortAttrTbl′[(((conf′→ portTbl)[i′])..ID)])..mode =ₑ ((conf′→ portTbl)[i′])..channeltype;ₛ 
                        (OSPortAttrTbl′[(((conf′→ portTbl)[i′])..ID)])..channnelID =ₑ ((conf′→ portTbl)[i′])..channelID;ₛ 
                        (OSPortAttrTbl′[(((conf′→ portTbl)[i′])..ID)])..enable =ₑ ′1 ;ₛ 
                        ++  Port_num_cur′ ;ₛ  
                        flag′ =ₑ ′0
                };ₛ   
            ++ j′
        };ₛ  
        ++ i′
    };ₛ *)
    EXIT_CRITICAL;ₛ
    RETURN
}· . *)

Definition initConf_impl := 
    Void ·initConf·(⌞⌟)··{
        ⌞
        sysEndian @ Int8u;
        confEndian @ Int8u;
        y @ Int8u;
        base @ Int8u∗;
        flag @ Int32;
        uconf @ ucos_conf_t∗
        ⌟;

        sysEndian′ =ₑ  ′0;ₛ
        confEndian′ =ₑ ′0;ₛ
        uconf′ =ₑ 〈ucos_conf_t∗〉 eptrconst BOOT_DATA_ADDRESS;ₛ
        flag′ =ₑ ′1;ₛ
        WHILE (flag′) {
            If ((( uconf′→ magicf ==ₑ ′0x12345678)&&ₑ(uconf′→ magicl ==ₑ ′0x12345678)) ||ₑ (( uconf′→ magicf   ==ₑ ′0x78562312)&&ₑ(uconf′→ magicl   ==ₑ ′0x78562312))){
                flag′ =ₑ ′0
               }
        };ₛ 

        y′ =ᶠ is_bigEndian(·);ₛ
        If (y′ ==ₑ ′1){
            sysEndian′ =ₑ ′1
           };ₛ
        base′ =ₑ 〈Int8u∗〉(&ₐ uconf′→ magicf);ₛ
        If (∗base′ ==ₑ ′0x12){
            confEndian′ =ₑ ′1 
           };ₛ
        If ( confEndian′ ==ₑ sysEndian′ ){
            InitDNUM(­uconf′, ′DNUM, ′1­)
        };ₛ 
    RETURN
}· .


Definition IntPartitionMuxInit_impl :=
 Void ·IntPartitionMuxInit·(⌞ ⌟)··{

        ⌞
          ucoscfg @ ucos_conf_t ∗;
          i @ Int32
       ⌟;

        ucoscfg′ =ₑ 〈ucos_conf_t ∗〉 (eptrconst BOOT_DATA_ADDRESS);ₛ
        i′ =ₑ ′0;ₛ
        WHILE (i′ <ₑ (′USER_INT_MAX_N)) {
            IntPartitionMux′[i′] =ₑ ucoscfg′→IntrDomainMux[i′];ₛ
            ++ i′
        };ₛ
        RETURN
 }·.

Definition InitCorePartition_impl := 
    Void ·InitCorePartition·(⌞coreNum @ Int8u; attr @ pthread_attr_t∗⌟)··{
        ⌞
         i @ Int8u;
         j @ Int8u;
         uconf @ ucos_conf_t∗;
         pt @ pthread_t;
         (* attr @ pthread_attr_t; *)
         entry @ Void∗;
         prio @ Int8u;
         x @ Int32;
         y @ Int32
        ⌟;

         uconf′ =ₑ 〈ucos_conf_t∗〉 eptrconst BOOT_DATA_ADDRESS;ₛ
         entry′ =ₑ 〈Void∗〉 NULL;ₛ

         j′ =ₑ ′0;ₛ
          WHILE (j′ <ₑ  (((uconf′→ cpus)[coreNum′])..cpu_ksDomScheduleLength)) {
            i′ =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomSchedule)[j′])..ds_domain;ₛ
            x′ =ᶠ is_ELFProgramValid
                    (· 〈Void∗〉 (((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..binAddress),
                        ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..vAddress,
					              ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..vAddress
                        +ₑ  ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..dom_len ·);ₛ
             IF (x′ ==ₑ ′0){
               ++ j′
              }ELSE{
                            entry′  =ᶠ LoadElf2Mem'' (· 〈 (Void) ∗ 〉  (((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..binAddress) ·);ₛ
                            attr′→stackaddr =ₑ 〈Void∗〉 (&ₐ(RootTaskStk′[ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..dom_ID]));ₛ
                            pthread_attr_init(­(* &ₐ  *)attr′ ­);ₛ
                            attr′→stacksize =ₑ ′2 × ′PTHREAD_STACK_MIN;ₛ
                            attr′→sched_priority =ₑ ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..RootTaskPrio;ₛ
                            prio′ =ₑ  attr′→sched_priority;ₛ
                            y′ =ᶠ pthread_create(· &ₐ pt′ , (* &ₐ *) attr′ , entry′ , 〈 (Void) ∗ 〉  NULL ·);ₛ
                             IF (y′ !=ₑ ′OS_NO_ERR){
                              ++ j′
                            }ELSE{
                                          If ( ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..CapEnTbl..TaskEn ==ₑ ′0 ){
                                              ucos_CNode_Delete(- prio′ , ′CAP_TASK_CLASS -)
                                          };ₛ
                                         If ( ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..CapEnTbl..PartitionEn ==ₑ ′0 ){
                                              ucos_CNode_Delete(- prio′ , ′CAP_PARTITION_CLASS -)
                                          };ₛ
                                         If ( ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..CapEnTbl..InterCommEn ==ₑ ′0 ){
                                              ucos_CNode_Delete(- prio′ , ′CAP_CHANNEL_CLASS -);ₛ
                                              ucos_CNode_Delete(- prio′ , ′CAP_PORT_CLASS -)
                                          };ₛ
                                         If ( ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..CapEnTbl..IntraCommSemEn ==ₑ ′0 ){
                                              ucos_CNode_Delete(- prio′ , ′CAP_SEM_CLASS -)
                                          };ₛ
                                         If ( ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..CapEnTbl..IntraCommQueueEn ==ₑ ′0 ){
                                              ucos_CNode_Delete(- prio′ , ′CAP_QUEUE_CLASS -)
                                          };ₛ
                                         If ( ((((uconf′→ cpus)[coreNum′])..cpu_ksDomains)[i′])..CapEnTbl..IntraCommMutexEn ==ₑ ′0 ){
                                              ucos_CNode_Delete(- prio′ , ′CAP_MUTEX_CLASS -)
                                          };ₛ
                                          ++ j′
                                          }
                             }
          };ₛ

     RETURN 

}· .

Close Scope code_scope.


