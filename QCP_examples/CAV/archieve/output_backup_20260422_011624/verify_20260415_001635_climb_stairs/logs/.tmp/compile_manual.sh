#!/usr/bin/env bash
set -euo pipefail
WS=/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/output/verify_20260415_001635_climb_stairs
DEPS=$WS/coq/deps
GEN=$WS/coq/generated
ORIG=$WS/original
cd /home/yangfp/QualifiedCProgramming/SeparationLogic
coqc -Q "$ORIG" "" \
  -R "$DEPS" SimpleC.EE \
  -R SeparationLogic SimpleC.SL \
  -R unifysl Logic \
  -R sets SetsClass \
  -R compcert_lib compcert.lib \
  -R auxlibs AUXLib \
  -R examples SimpleC.EE \
  -R StrategyLib SimpleC.StrategyLib \
  -R Common SimpleC.Common \
  -R fixedpoints FP \
  -R MonadLib MonadLib \
  -R listlib ListLib \
  -R "$GEN" SimpleC.EE.leetcode.verify_20260415_001635_climb_stairs \
  "$GEN/climb_stairs_proof_manual.v"
coqc -Q "$ORIG" "" \
  -R "$DEPS" SimpleC.EE \
  -R SeparationLogic SimpleC.SL \
  -R unifysl Logic \
  -R sets SetsClass \
  -R compcert_lib compcert.lib \
  -R auxlibs AUXLib \
  -R examples SimpleC.EE \
  -R StrategyLib SimpleC.StrategyLib \
  -R Common SimpleC.Common \
  -R fixedpoints FP \
  -R MonadLib MonadLib \
  -R listlib ListLib \
  -R "$GEN" SimpleC.EE.leetcode.verify_20260415_001635_climb_stairs \
  "$GEN/climb_stairs_goal_check.v"
