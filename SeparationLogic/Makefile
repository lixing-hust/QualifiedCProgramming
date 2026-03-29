CURRENT_DIR=.
COQBIN=

-include CONFIGURE

# Platform-specific settings
ifeq ($(shell uname),Darwin)
	DATE = gdate
else
	DATE = date
endif

# Timing utility
timeit = @printf "%-70s" $(1); t0=$$($(DATE) +%s%3N); $(2); t1=$$($(DATE) +%s%3N); echo "$$((t1 - t0)) ms"

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	Common auxlibs compcert_lib SeparationLogic sets unifysl StrategyLib fixedpoints MonadLib examples
 
COQ_FLAG = -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib

DEP_FLAG = -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib

Common_FILES = \
  CTypes.v COps.v Notations.v

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v

ListLib_FILES = \
	Base/Positional.v Base/Inductive.v \
	General/Length.v General/Presuffix.v General/Forall.v General/IndexedElements.v General/NoDup.v 

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v relations.v ListLib.v \
  OrdersDecFact.v BinaryTree.v EqDec.v ListDec.v Bool.v Tactics.v Vec.v

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v

Unify_FILES = \
   Interface.v 

FIXPOINT_FILES = \
  Coqlib.v LiftConstructors.v  PartialOrder_Setoid.v  KnasterTarski.v  BourbakiWitt.v AllFramework.v SetsFixedpoints.v

ListMonad_Files = \
	 ListMonad.v ListBasic.v

OptionMonad_Files = \
	 OptionMonad.v OptionBasic.v

SetMonad_Files = \
	SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v MonadErrHoarePartial.v monadesafe_lib.v StateRelMonadErr.v

MonadExample_FILES = \
	kmp.v mergesort.v 
  
MONAD_FILES = \
	MonadLib/MonadLib.v \
	MonadLib/Monad.v \
	$(ListMonad_Files:%.v=MonadLib/ListMonad/%.v) \
	$(OptionMonad_Files:%.v=MonadLib/OptionMonad/%.v) \
	$(SetMonad_Files:%.v=MonadLib/SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=MonadLib/StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=MonadLib/MonadErr/%.v) \
	$(MonadExample_FILES:%.v=MonadLib/Examples/%.v) \

SL_FILES = \
  CommonAssertion.v Assertion.v Mem.v ConAssertion.v \
  NestedCriticalSTS.v CriticalSTS.v \
  IntLib.v ArrayLib.v StoreAux.v pocv02.v SeparationLogic.v CNotation.v MapLib.v 

StrategyLib_FILES = \
  DepList.v Mapping.v

Examples_Lib_FILES = \
	poly_sll_lib.v sll_lib.v sll_insert_sort_lib.v functional_queue_lib.v dll_queue_lib.v sll_queue_lib.v simple_arith/Apos_lib.v simple_arith/PDiv_lib.v bst_lib.v bst_fp_lib.v swap_lib.v eval_lib.v fme/algorithm.v fme/implement.v fme/implement_lemma.v fme/fme_lib.v typeinfer/repr_subst_prop.v typeinfer/sol_prop.v typeinfer/sound_pv.v typeinfer/type_infer_lib.v typeinfer/typeinfer_lib.v avl_shape.v sll_shape_lib.v dll_shape_lib.v \
	sll_merge_rel_lib.v kmp_lib.v kmp_rel_lib.v int_array_merge_rel_lib.v \
	malloc.v super_poly_sll2.v minigmp/GmpAux.v minigmp/GmpNumber.v cnf_trans/cnf_trans_lib.v cnf_trans/smt_lang_lib.v alpha_equiv/ast_lib.v

Examples_FILE_NAME = \
	poly_sll sll sll_insert_sort functional_queue dll_queue sll_queue simple_arith/abs simple_arith/add simple_arith/max3 simple_arith/gcd simple_arith/Always_pos simple_arith/div_test simple_arith/exgcd sum bst_insert bst_insert_rec bst_fp_insert bst_fp_delete swap eval bst_delete_rec bst_delete_rec2 typeinfer/typeinfer avl_insert sll_auto dll_auto array_auto chars \
	alpha_equiv/alpha_equiv alpha_equiv/thm_apply  minigmp/gmp \
	kmp_rel int_array_merge_rel sll_merge_rel sll_split_while cnf_trans/cnf_trans alpha_equiv/subst fme/fme

Examples_FILES = \
	$(addsuffix _goal.v, $(Examples_FILE_NAME)) \
	$(addsuffix _goal_check.v, $(Examples_FILE_NAME)) \
	$(addsuffix _proof_auto.v, $(Examples_FILE_NAME)) \
	$(addsuffix _proof_manual.v, $(Examples_FILE_NAME)) \
	$(Examples_Lib_FILES)

Strategy_FILE_NAME = \
	common poly_sll sll_shape sll dll_queue functional_queue sll_queue int_array undef_uint_array uint_array array_shape bst bst_fp eval char_array fme/fme typeinfer/typeinfer avl dll_shape safeexec safeexecE ptr_array 
  
StrategyProof_FILES = \
	$(addsuffix _strategy_goal.v, $(Strategy_FILE_NAME)) \
	$(addsuffix _strategy_goal_check.v, $(Strategy_FILE_NAME)) \
	$(addsuffix _strategy_proof.v, $(Strategy_FILE_NAME)) \

LiteOS_Lib_FILES = \
	dll sortlink tick_backup glob_vars_and_defs tick Los_Verify_State_def

LiteOS_FILE_NAME = \
	Get_Set_Value GetSortLinkNextExpireTime List_Add LOS_ListDelete LOS_ListDelInit LOS_ListEmpty LOS_ListInit OsAdd2SortLink OsDeleteNodeSortLink \
	OsDeleteSortLink OsGetNextExpireTime OsGetSortLinkAttribute OsSortLinkGetNextExpireTime OsSortLinkGetRemainTime OsSortLinkGetTargetExpireTime \
	OsSortLinkInit OsSortLinkResponseTimeConvertFreq

LiteOS_Strategy_FILE_NAME = \
	los_sortlink

LiteOS_FILE = \
	$(LiteOS_FILE_NAME:%=LiteOS/%_goal.v) \
	$(LiteOS_FILE_NAME:%=LiteOS/%_goal_check.v) \
	$(LiteOS_FILE_NAME:%=LiteOS/%_proof_auto.v) \
	$(LiteOS_FILE_NAME:%=LiteOS/%_proof_manual.v) \
	$(LiteOS_Lib_FILES:%=LiteOS/lib/%.v) \
	$(LiteOS_Strategy_FILE_NAME:%=%_strategy_goal.v) \
	$(LiteOS_Strategy_FILE_NAME:%=%_strategy_goal_check.v) \
	$(LiteOS_Strategy_FILE_NAME:%=%_strategy_proof.v) \

Project_Lib_FILES = \
	hashtbl_lib \
	mergeablelist/sll_project_lib \
	minigmp1/mini_gmp_proof_manual1 minigmp1/mini_gmp_proof_manual2 \

Project_FILE_NAME = \
	hashtable1/hashtbl mergeablelist/sll_project minigmp1/mini_gmp  minigmp2/mini_gmp minigmp3/mini_gmp \
	# hashtable/hashtbl 

Project_Strategy_FILE_NAME = \
	Project/minigmp1/mini_gmp Project/minigmp2/gmp_array Project/mergeablelist/sll_project Project/hashtable/hashtbl \

Project_FILE = \
	$(Project_FILE_NAME:%=Project/%_goal.v) \
	$(Project_FILE_NAME:%=Project/%_goal_check.v) \
	$(Project_FILE_NAME:%=Project/%_proof_auto.v) \
	$(Project_FILE_NAME:%=Project/%_proof_manual.v) \
	$(Project_Lib_FILES:%=Project/%.v) \
	$(addsuffix _strategy_goal.v, $(Project_Strategy_FILE_NAME)) \
	$(addsuffix _strategy_goal_check.v, $(Project_Strategy_FILE_NAME)) \
	$(addsuffix _strategy_proof.v, $(Project_Strategy_FILE_NAME)) \


EXAMPLE = \
	$(SL_FILES:%.v=SeparationLogic/%.v) \
	$(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
	$(Common_FILES:%.v=Common/%.v) \
	$(MONAD_FILES:%.v=%.v) \
	$(ListLib_FILES:%.v=listlib/%.v) \
	$(Sets_FILES:%.v=sets/%.v) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.v) \
	$(Examples_FILES:%.v=examples/%.v) \
	$(StrategyProof_FILES:%.v=examples/%.v) \
	$(Compcertlib_FILES:%.v=compcert_lib/%.v) \
	$(Auxlibs_FILES:%.v=auxlibs/%.v) \
	$(LiteOS_FILE:%.v=examples/%.v) \
# 	$(Project_FILE:%.v=examples/%.v) \

$(EXAMPLE:%.v=%.vo): %.vo: %.v
ifeq ($(TIMING),)
	@echo "COQC $*.v"
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v
else
	$(call timeit, "COQC $*.v", $(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v)
endif

	

all: \
	$(EXAMPLE:%.v=%.vo) \

examples : \
	$(EXAMPLE:%.v=%.vo) 

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(EXAMPLE)  > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(EXAMPLE) > .depend

clean:
	@rm -f $(EXAMPLE:%.v=%.glob)
	@rm -f $(EXAMPLE:%.v=%.vo)
	@rm -f $(EXAMPLE:%.v=%.vok)
	@rm -f $(EXAMPLE:%.v=%.vos)
	@rm -f **/.*.aux
	@rm -f examples/**/.*.aux examples/LiteOS/lib/.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

include .depend