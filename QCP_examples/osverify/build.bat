@ECHO OFF
ECHO Compile framework/auxlibs/Coqlib.v
coqc -R . CertiOS framework/auxlibs/Coqlib.v
ECHO Compile framework/auxlibs/Integers.v
coqc -R . CertiOS framework/auxlibs/Integers.v
ECHO Compile framework/auxlibs/extac.v
coqc -R . CertiOS framework/auxlibs/extac.v
ECHO Compile framework/auxlibs/IntBool.v
coqc -R . CertiOS framework/auxlibs/IntBool.v
ECHO Compile tactics/basetac/LibTactics.v
coqc -R . CertiOS tactics/basetac/LibTactics.v
ECHO Compile framework/auxlibs/MapLib.v
coqc -R . CertiOS framework/auxlibs/MapLib.v
ECHO Compile framework/auxlibs/Modules.v
coqc -R . CertiOS framework/auxlibs/Modules.v
ECHO Compile framework/auxlibs/Maps.v
coqc -R . CertiOS framework/auxlibs/Maps.v
ECHO Compile tactics/basetac/join_general.v
coqc -R . CertiOS tactics/basetac/join_general.v
ECHO Compile tactics/basetac/map_tactics.v
coqc -R . CertiOS tactics/basetac/map_tactics.v
ECHO Compile framework/model/memory.v
coqc -R . CertiOS framework/model/memory.v
ECHO Compile framework/model/language.v
coqc -R . CertiOS framework/model/language.v
ECHO Compile framework/model/opsem.v
coqc -R . CertiOS framework/model/opsem.v
ECHO Compile framework/logic/assertion.v
coqc -R . CertiOS framework/logic/assertion.v
ECHO Compile framework/model/int_lock.v
coqc -R . CertiOS framework/model/int_lock.v
ECHO Compile framework/logic/inferules.v
coqc -R . CertiOS framework/logic/inferules.v
ECHO Compile framework/model/code_notations.v
coqc -R . CertiOS framework/model/code_notations.v
ECHO Compile framework/include_frm.v
coqc -R . CertiOS framework/include_frm.v
ECHO Compile certiucos/code/os_code_defs.v
coqc -R . CertiOS certiucos/code/os_code_defs.v
ECHO Compile certiucos/code/os_ucos_h.v
coqc -R . CertiOS certiucos/code/os_ucos_h.v
ECHO Compile certiucos/code/os_core.v
coqc -R . CertiOS certiucos/code/os_core.v
ECHO Compile certiucos/code/os_q.v
coqc -R . CertiOS certiucos/code/os_q.v
ECHO Compile certiucos/code/os_time.v
coqc -R . CertiOS certiucos/code/os_time.v
ECHO Compile certiucos/code/os_mutex.v
coqc -R . CertiOS certiucos/code/os_mutex.v
ECHO Compile certiucos/code/os_sem.v
coqc -R . CertiOS certiucos/code/os_sem.v
ECHO Compile certiucos/code/ev_aux_code.v
coqc -R . CertiOS certiucos/code/ev_aux_code.v
ECHO Compile certiucos/code/os_cpu_a.v
coqc -R . CertiOS certiucos/code/os_cpu_a.v
ECHO Compile certiucos/code/useraddrcheck.v
coqc -R . CertiOS certiucos/code/useraddrcheck.v
ECHO Compile certiucos/code/os_mutex_cap.v
coqc -R . CertiOS certiucos/code/os_mutex_cap.v
ECHO Compile certiucos/code/os_sem_cap.v
coqc -R . CertiOS certiucos/code/os_sem_cap.v
ECHO Compile certiucos/code/os_q_cap.v
coqc -R . CertiOS certiucos/code/os_q_cap.v
ECHO Compile certiucos/inline/inline_definitions.v
coqc -R . CertiOS certiucos/inline/inline_definitions.v
ECHO Compile tactics/basetac/join_tactics.v
coqc -R . CertiOS tactics/basetac/join_tactics.v
ECHO Compile tactics/basetac/join_lib.v
coqc -R . CertiOS tactics/basetac/join_lib.v
ECHO Compile tactics/base_tac.v
coqc -R . CertiOS tactics/base_tac.v
ECHO Compile tactics/sepauto/seplog_lemmas.v
coqc -R . CertiOS tactics/sepauto/seplog_lemmas.v
ECHO Compile tactics/pure/frmaop_sol.v
coqc -R . CertiOS tactics/pure/frmaop_sol.v
ECHO Compile tactics/sepauto/seplog_tactics.v
coqc -R . CertiOS tactics/sepauto/seplog_tactics.v
ECHO Compile tactics/sepauto/sep_join_lemmas.v
coqc -R . CertiOS tactics/sepauto/sep_join_lemmas.v
ECHO Compile tactics/sepauto/sep_combine_lemmas.v
coqc -R . CertiOS tactics/sepauto/sep_combine_lemmas.v
ECHO Compile tactics/sepauto/meta_find.v
coqc -R . CertiOS tactics/sepauto/meta_find.v
ECHO Compile tactics/sepauto/sep_combine.v
coqc -R . CertiOS tactics/sepauto/sep_combine.v
ECHO Compile tactics/sepauto/sep_cancel_ext.v
coqc -R . CertiOS tactics/sepauto/sep_cancel_ext.v
ECHO Compile tactics/sep_auto.v
coqc -R . CertiOS tactics/sep_auto.v
ECHO Compile tactics/sepauto/seplog_trm_tacs.v
coqc -R . CertiOS tactics/sepauto/seplog_trm_tacs.v
ECHO Compile tactics/basetac/perm_map_lemmas_part1.v
coqc -R . CertiOS tactics/basetac/perm_map_lemmas_part1.v
ECHO Compile tactics/basetac/perm_map_lemmas_part2.v
coqc -R . CertiOS tactics/basetac/perm_map_lemmas_part2.v
ECHO Compile tactics/basetac/perm_map_lemmas_part3.v
coqc -R . CertiOS tactics/basetac/perm_map_lemmas_part3.v
ECHO Compile tactics/basetac/perm_map_lemmas_part4.v
coqc -R . CertiOS tactics/basetac/perm_map_lemmas_part4.v
ECHO Compile tactics/basetac/perm_map_lemmas.v
coqc -R . CertiOS tactics/basetac/perm_map_lemmas.v
ECHO Compile framework/proof/mem_join_lemmas.v
coqc -R . CertiOS framework/proof/mem_join_lemmas.v
ECHO Compile framework/proof/aux_map_lib.v
coqc -R . CertiOS framework/proof/aux_map_lib.v
ECHO Compile framework/proof/memory_prop.v
coqc -R . CertiOS framework/proof/memory_prop.v
ECHO Compile framework/proof/lmachLib.v
coqc -R . CertiOS framework/proof/lmachLib.v
ECHO Compile tactics/mathauto/int_auto.v
coqc -R . CertiOS tactics/mathauto/int_auto.v
ECHO Compile tactics/mathauto/math_sol.v
coqc -R . CertiOS tactics/mathauto/math_sol.v
ECHO Compile tactics/mathauto/math_rewrite.v
coqc -R . CertiOS tactics/mathauto/math_rewrite.v
ECHO Compile tactics/math_auto.v
coqc -R . CertiOS tactics/math_auto.v
ECHO Compile tactics/hoareforward/symbolic_lemmas.v
coqc -R . CertiOS tactics/hoareforward/symbolic_lemmas.v
ECHO Compile tactics/hoareforward/symbolic_execution.v
coqc -R . CertiOS tactics/hoareforward/symbolic_execution.v
ECHO Compile certiucos/inline/inline_tactics.v
coqc -R . CertiOS certiucos/inline/inline_tactics.v
ECHO Compile certiucos/code/ios_int.v
coqc -R . CertiOS certiucos/code/ios_int.v
ECHO Compile certiucos/spec/os_inv.v
coqc -R . CertiOS certiucos/spec/os_inv.v
ECHO Compile tactics/hoareforward/derived_rules.v
coqc -R . CertiOS tactics/hoareforward/derived_rules.v
ECHO Compile tactics/hoareforward/hoare_conseq.v
coqc -R . CertiOS tactics/hoareforward/hoare_conseq.v
ECHO Compile tactics/hoareforward/hoare_assign.v
coqc -R . CertiOS tactics/hoareforward/hoare_assign.v
ECHO Compile tactics/hoareforward/hoare_if.v
coqc -R . CertiOS tactics/hoareforward/hoare_if.v
ECHO Compile tactics/hoareforward/hoare_ret.v
coqc -R . CertiOS tactics/hoareforward/hoare_ret.v
ECHO Compile tactics/hoareforward/hoare_call.v
coqc -R . CertiOS tactics/hoareforward/hoare_call.v
ECHO Compile tactics/absstep/cancel_abs.v
coqc -R . CertiOS tactics/absstep/cancel_abs.v
ECHO Compile tactics/hoareforward/hoare_tactics.v
coqc -R . CertiOS tactics/hoareforward/hoare_tactics.v
ECHO Compile tactics/pure/tv_match.v
coqc -R . CertiOS tactics/pure/tv_match.v
ECHO Compile tactics/hoareforward/init_spec.v
coqc -R . CertiOS tactics/hoareforward/init_spec.v
ECHO Compile tactics/hoare_forward.v
coqc -R . CertiOS tactics/hoare_forward.v
ECHO Compile tactics/pure/pure_lib.v
coqc -R . CertiOS tactics/pure/pure_lib.v
ECHO Compile tactics/absstep/abs_infer_step.v
coqc -R . CertiOS tactics/absstep/abs_infer_step.v
ECHO Compile tactics/absstep/abs_infer_abt.v
coqc -R . CertiOS tactics/absstep/abs_infer_abt.v
ECHO Compile tactics/abs_step.v
coqc -R . CertiOS tactics/abs_step.v
ECHO Compile tactics/pure/pure_auto.v
coqc -R . CertiOS tactics/pure/pure_auto.v
ECHO Compile tactics/pure/struct_type_match_solver.v
coqc -R . CertiOS tactics/pure/struct_type_match_solver.v
ECHO Compile tactics/pure/go.v
coqc -R . CertiOS tactics/pure/go.v
ECHO Compile tactics/pure.v
coqc -R . CertiOS tactics/pure.v
ECHO Compile tactics/ucostac/ucos_bitsmap.v
coqc -R . CertiOS tactics/ucostac/ucos_bitsmap.v
ECHO Compile certiucos/inline/inline_bittblfunctions.v
coqc -R . CertiOS certiucos/inline/inline_bittblfunctions.v
ECHO Compile certiucos/spec/abs_op.v
coqc -R . CertiOS certiucos/spec/abs_op.v
ECHO Compile certiucos/code/os_task.v
coqc -R . CertiOS certiucos/code/os_task.v
ECHO Compile certiucos/code/ios_int_ipc.v
coqc -R . CertiOS certiucos/code/ios_int_ipc.v
ECHO Compile certiucos/code/ios_int_tick.v
coqc -R . CertiOS certiucos/code/ios_int_tick.v
ECHO Compile certiucos/code/ios_int_nmi.v
coqc -R . CertiOS certiucos/code/ios_int_nmi.v
ECHO Compile certiucos/code/os_program.v
coqc -R . CertiOS certiucos/code/os_program.v
ECHO Compile certiucos/spec/os_spec.v
coqc -R . CertiOS certiucos/spec/os_spec.v
ECHO Compile certiucos/spec/lemmas_for_inv_prop.v
coqc -R . CertiOS certiucos/spec/lemmas_for_inv_prop.v
ECHO Compile framework/proof/Map.v
coqc -R . CertiOS framework/proof/Map.v
ECHO Compile framework/proof/simulation.v
coqc -R . CertiOS framework/proof/simulation.v
ECHO Compile framework/proof/auxdef.v
coqc -R . CertiOS framework/proof/auxdef.v
ECHO Compile framework/proof/oscorrectness.v
coqc -R . CertiOS framework/proof/oscorrectness.v
ECHO Compile framework/proof/absinfer_sound.v
coqc -R . CertiOS framework/proof/absinfer_sound.v
ECHO Compile tactics/sepauto/sep_lemmas_ext.v
coqc -R . CertiOS tactics/sepauto/sep_lemmas_ext.v
ECHO Compile framework/proof/joinmemLib.v
coqc -R . CertiOS framework/proof/joinmemLib.v
ECHO Compile framework/proof/rulesoundlib.v
coqc -R . CertiOS framework/proof/rulesoundlib.v
ECHO Compile framework/proof/sound_include.v
coqc -R . CertiOS framework/proof/sound_include.v
ECHO Compile framework/proof/simplrulesound.v
coqc -R . CertiOS framework/proof/simplrulesound.v
ECHO Compile framework/proof/whilesound.v
coqc -R . CertiOS framework/proof/whilesound.v
ECHO Compile framework/proof/retsound.v
coqc -R . CertiOS framework/proof/retsound.v
ECHO Compile framework/proof/conseqsound.v
coqc -R . CertiOS framework/proof/conseqsound.v
ECHO Compile framework/proof/framesound.v
coqc -R . CertiOS framework/proof/framesound.v
ECHO Compile framework/proof/ifsound.v
coqc -R . CertiOS framework/proof/ifsound.v
ECHO Compile framework/proof/assignsound.v
coqc -R . CertiOS framework/proof/assignsound.v
ECHO Compile framework/proof/fcallsound.v
coqc -R . CertiOS framework/proof/fcallsound.v
ECHO Compile framework/proof/switchsound.v
coqc -R . CertiOS framework/proof/switchsound.v
ECHO Compile framework/proof/seqcomsound.v
coqc -R . CertiOS framework/proof/seqcomsound.v
ECHO Compile framework/proof/eoisound.v
coqc -R . CertiOS framework/proof/eoisound.v
ECHO Compile framework/proof/eointsound.v
coqc -R . CertiOS framework/proof/eointsound.v
ECHO Compile framework/proof/funsim.v
coqc -R . CertiOS framework/proof/funsim.v
ECHO Compile framework/proof/methsimlift.v
coqc -R . CertiOS framework/proof/methsimlift.v
ECHO Compile framework/proof/crtsound.v
coqc -R . CertiOS framework/proof/crtsound.v
ECHO Compile framework/proof/clistisound.v
coqc -R . CertiOS framework/proof/clistisound.v
ECHO Compile framework/proof/chkissound.v
coqc -R . CertiOS framework/proof/chkissound.v
ECHO Compile framework/proof/taskcrtsound.v
coqc -R . CertiOS framework/proof/taskcrtsound.v
ECHO Compile framework/proof/taskdelsound.v
coqc -R . CertiOS framework/proof/taskdelsound.v
ECHO Compile framework/proof/intsound.v
coqc -R . CertiOS framework/proof/intsound.v
ECHO Compile framework/proof/absabtsound.v
coqc -R . CertiOS framework/proof/absabtsound.v
ECHO Compile framework/proof/rulesound.v
coqc -R . CertiOS framework/proof/rulesound.v
ECHO Compile framework/proof/soundness.v
coqc -R . CertiOS framework/proof/soundness.v
ECHO Compile framework/proof/invariant_prop_lemmas.v
coqc -R . CertiOS framework/proof/invariant_prop_lemmas.v
ECHO Compile framework/proof/contLib.v
coqc -R . CertiOS framework/proof/contLib.v
ECHO Compile framework/proof/cstepLib.v
coqc -R . CertiOS framework/proof/cstepLib.v
ECHO Compile framework/proof/step_prop.v
coqc -R . CertiOS framework/proof/step_prop.v
ECHO Compile framework/proof/invariant_prop.v
coqc -R . CertiOS framework/proof/invariant_prop.v
ECHO Compile framework/proof/absabt_lemmas.v
coqc -R . CertiOS framework/proof/absabt_lemmas.v
ECHO Compile tactics/basetac/join_lib_aux.v
coqc -R . CertiOS tactics/basetac/join_lib_aux.v
ECHO Compile framework/proof/join_prop.v
coqc -R . CertiOS framework/proof/join_prop.v
ECHO Compile framework/proof/tskabsabt_lemmas.v
coqc -R . CertiOS framework/proof/tskabsabt_lemmas.v
ECHO Compile certiucos/ucos_lib/events/Aarray_new_common.v
coqc -R . CertiOS certiucos/ucos_lib/events/Aarray_new_common.v
ECHO Compile certiucos/spec/inv_prop.v
coqc -R . CertiOS certiucos/spec/inv_prop.v
ECHO Compile certiucos/spec/evt_spec_defs.v
coqc -R . CertiOS certiucos/spec/evt_spec_defs.v
ECHO Compile certiucos/spec/ifun_spec.v 
coqc -R . CertiOS certiucos/spec/ifun_spec.v 
ECHO Compile tactics/ucostac/ucos_frmaop.v
coqc -R . CertiOS tactics/ucostac/ucos_frmaop.v
ECHO Compile tactics/ucostac/ucos_forward.v
coqc -R . CertiOS tactics/ucostac/ucos_forward.v
ECHO Compile tactics/ucostac/ucos_pauto.v
coqc -R . CertiOS tactics/ucostac/ucos_pauto.v
ECHO Compile tactics/ucostac/ucos_common.v
coqc -R . CertiOS tactics/ucostac/ucos_common.v
ECHO Compile certiucos/proofs/ucos_include.v
coqc -R . CertiOS certiucos/proofs/ucos_include.v

@REM ECHO Compile certiucos/ucos_lib/oscore_common.v
@REM coqc -R . CertiOS certiucos/ucos_lib/oscore_common.v
@REM ECHO Compile certiucos/proofs/int/ios_int_tac.v
@REM coqc -R . CertiOS certiucos/proofs/int/ios_int_tac.v    
@REM ECHO Compile certiucos/proofs/int/dintpProof.v
@REM coqc -R . CertiOS certiucos/proofs/int/dintpProof.v
@REM ECHO Compile certiucos/proofs/int/rintpProof.v
@REM coqc -R . CertiOS certiucos/proofs/int/rintpProof.v
@REM ECHO Compile certiucos/proofs/int/Unstall_handler6678Proof.v
@REM coqc -R . CertiOS certiucos/proofs/int/Unstall_handler6678Proof.v
@REM ECHO Compile certiucos/proofs/int/Unstall_handler6713Proof.v
@REM coqc -R . CertiOS certiucos/proofs/int/Unstall_handler6713Proof.v
@REM ECHO Compile certiucos/proofs/int/ExchandlersetProof.v
@REM coqc -R . CertiOS certiucos/proofs/int/ExchandlersetProof.v
@REM ECHO Compile certiucos/proofs/int/Install_handler6678Proof.v
@REM coqc -R . CertiOS certiucos/proofs/int/Install_handler6678Proof.v
@REM ECHO Compile certiucos/proofs/int/Install_handler6713Proof.v
@REM coqc -R . CertiOS certiucos/proofs/int/Install_handler6713Proof.v
@REM ECHO Compile certiucos/proofs/int/Interrupt_Init.v
@REM coqc -R . CertiOS certiucos/proofs/int/Interrupt_Init.v
@REM ECHO Compile certiucos/ucos_lib/OSIntExitIntPure.v
@REM coqc -R . CertiOS certiucos/ucos_lib/OSIntExitIntPure.v
@REM ECHO Compile certiucos/proofs/int/IntEnterProof.v
@REM coqc -R . CertiOS certiucos/proofs/int/IntEnterProof.v
@REM ECHO Compile certiucos/proofs/int/IntExitProof.v
@REM coqc -R . CertiOS certiucos/proofs/int/IntExitProof.v
@REM ECHO Compile certiucos/ucos_lib/OSTimeDlyPure.v
@REM coqc -R . CertiOS certiucos/ucos_lib/OSTimeDlyPure.v
@REM ECHO Compile certiucos/ucos_lib/OSQAcceptPure.v
@REM coqc -R . CertiOS certiucos/ucos_lib/OSQAcceptPure.v
@REM ECHO Compile certiucos/ucos_lib/OSQPostPure.v
@REM coqc -R . CertiOS certiucos/ucos_lib/OSQPostPure.v
@REM ECHO Compile certiucos/ucos_lib/OSTimeTickPure.v
@REM coqc -R . CertiOS certiucos/ucos_lib/OSTimeTickPure.v
@REM ECHO Compile certiucos/proofs/int/OSTickISR.v
@REM coqc -R . CertiOS certiucos/proofs/int/OSTickISR.v
pause
