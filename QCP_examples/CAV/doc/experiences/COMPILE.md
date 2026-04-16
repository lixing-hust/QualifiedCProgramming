# Compile Experience

本文件只记录 verify 阶段的编译经验。

## 1. 编译范围

- 只记录最终 Coq 编译与 `goal_check` 校验
- 不记录 invariant/assert/symbolic（见 `INV.md`、`ASSERTION.md`、`SYMEXEC.md`）
- 不记录 manual proof 策略（见 `PROOF.md`）

## 2. Workspace 编译

- 编译时必须区分两个目录：
- Coq 工作目录：`/home/yangfp/QualifiedCProgramming/SeparationLogic`
- 当前 verify workspace：`/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_<timestamp>_<name>/`
- 最终执行 `coqc` 时，当前 shell 必须在 `SeparationLogic/`
- 不要在 `CAV/` 目录直接执行最终 `coqc`
- 当前 workspace 编译前至少检查：`coq/generated/<name>_goal.v`、`_proof_auto.v`、`_proof_manual.v`、`_goal_check.v`
- 如果 `goal.v` 顶部 import 了 strategy 模块，还要检查 `coq/deps/` 是否已有对应 `.v`
- 公共目录缺少 `.vo` 或只读时，不要改 `SeparationLogic/examples/`；把依赖复制到当前 workspace 的 `coq/deps/`
- 通常至少需要这些 strategy 依赖：`common_strategy_*`、`int_array_strategy_*`、`uint_array_strategy_*`、`undef_uint_array_strategy_*`、`array_shape_strategy_*`
- 实际需要哪些依赖，以 `goal.v` 顶部 `From SimpleC.EE Require Import ...` 为准
- 在当前 workspace 中编译时，推荐先进入：
- `cd /home/yangfp/QualifiedCProgramming/SeparationLogic`
- 再设置：
- `WS=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_<timestamp>_<name>`
- `NAME=<name>`
- `DEPS=$WS/coq/deps`
- `GEN=$WS/coq/generated`
- `LP=SimpleC.EE.CAV.verify_<timestamp>_<name>`
- 公共参数固定包含：`-R $DEPS SimpleC.EE` 和 `-R $GEN $LP`
- 编译顺序固定为：先 `coq/deps/`，再 `goal.v`，再 `proof_auto.v`，再 `proof_manual.v`，最后 `goal_check.v`
- 不要跳过前面的文件直接编译后面的文件
- `Cannot find a physical path bound to logical path ...` 时，先检查当前目录、`-R $DEPS`、`-R $GEN`、以及 `coq/deps/` 是否已生成 `.vo`
- `... contains library X and not library Y` 时，先删除当前 workspace 下旧的 `.vo/.vos/.vok/.glob/.aux`，再用同一套 `-R` 前缀重编
- `goal_check` 失败但前面三个文件通过时，先检查 `goal_check.v` 顶部逻辑前缀、`proof_manual.v` 的 import、以及是否仍含 `Admitted.` 或新增 `Axiom`
- task-local `.v` 文件自身不合法时，不要误判成 manual proof 问题；先区分是 workspace 副本可局部修，还是应回退 contract 修正式输入
- 完成标准必须同时满足：`goal.v`、`proof_auto.v`、`proof_manual.v`、`goal_check.v` 全部通过，且 `proof_manual.v` 无 `Admitted.`、无新增 `Axiom`
- 编译完成后，`coq/generated/` 和 `coq/deps/` 下只保留 `.v`；删除 `.vo/.vos/.vok/.glob/.aux`
- 如果环境限制导致不能当场清理，必须在 `logs/issues.md` 里明确记录
- 编译阶段的问题写入 `logs/issues.md`，时间写入 `logs/metrics.md`
