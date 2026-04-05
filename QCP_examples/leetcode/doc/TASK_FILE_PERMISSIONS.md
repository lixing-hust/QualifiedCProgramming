# Per-Task File Permissions

本文件定义 `QCP_examples/leetcode/` 单题验证任务的文件权限。

每次处理某个 `input/<name>.c` 时，都必须先确定本次任务对应的唯一 workspace：

- `output/workspace_<timestamp>_<name>/`

除非用户明确授权，否则所有写操作都必须限制在这个 workspace 内。

## Core Rule

对当前题目，文件权限按下面四类理解：

- 可读：允许读取以获取信息
- 只读：允许读取、编译检查、被工具覆盖；不允许人工修改
- 可写：允许人工创建或修改
- 禁止访问：不允许读取或写入

最重要的规则：

- `coq/generated/` 中，只有 `coq/generated/<name>_proof_manual.v` 允许人工写证明和辅助引理
- `coq/generated/` 中，其余 `goal`、`proof_auto`、`goal_check`、`proof_check` 一律视为只读

## Allowed Reads

默认允许读取以下内容：

- 当前题目的输入文件：
  - `input/<name>.c`
  - `input/<name>.v`，如果存在
- 当前技能和文档：
  - `SKILL.md`
  - `doc/TASK_FILE_PERMISSIONS.md`
  - `doc/COQ_PROOF_GUIDE.md`
- `/home/yangfp/QualifiedCProgramming/QCP_examples/` 下其他例子的输入、注释版 C、证明产物和日志，可作为参考样例
- `/home/yangfp/QualifiedCProgramming/tutorial/` 下的全部教程文件
- 本仓库和上层仓库中已经存在的公共依赖，例如：
  - `../verification_stdlib.h`
  - `../common.strategies`
  - `../../SeparationLogic/` 下已有公共库

说明：

- 可以参考其他题目的例子来学习规格、invariant、proof_manual 写法
- 不应一开始就大量阅读其他例子；只有当前不会写、缺少思路时才去查阅相关例子
- 对 README、脚本、实验文件的读取应以解决当前阻塞为目的，不能替代对题目本身的分析

## Forbidden Reads

禁止读取以下内容：

- 当前目标函数同名的历史 workspace，例如当前在做 `<name>` 时，禁止读取：
  - `output/workspace_*_<name>/`

目的：

- 避免直接复用同题既有产物
- 避免抄旧证明、旧注释、旧日志

## Writable Files In Current Workspace

下面规则只针对当前题目的 workspace。

允许人工创建或修改：

- `original/<name>.c`
- `annotated/<name>.c`
- `coq/generated/<name>_proof_manual.v`
- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/proof_metrics.md`

补充说明：

- `original/<name>.c` 仅用于复制保存原始输入，不应改动其程序语义
- `annotated/<name>.c` 用于写规格、断言和 invariant
- `coq/generated/<name>_proof_manual.v` 是唯一允许人工写证明和辅助引理的 Coq 产物文件
- `logs/annotation_reasoning.md` 用于在写 annotation 前记录自然语言规格与 invariant 推理
- `logs/proof_reasoning.md` 用于在写证明前记录自然语言 proof plan 与 witness 推理
- `logs/issues.md` 和 `logs/proof_metrics.md` 必须维护

## Read-Only Files In Current Workspace

允许读取、编译检查、由工具覆盖，但不允许人工修改：

- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_goal_check.v`
- `coq/generated/<name>_proof_check.v`，如果流程已有该文件
- `logs/qcp_run.log`

硬规则：

- 不允许手改 `coq/generated/<name>_goal.v`
- 不允许手改 `coq/generated/<name>_proof_auto.v`
- 不允许手改 `coq/generated/<name>_goal_check.v`
- 不允许手改 `coq/generated/<name>_proof_check.v`
- 如果流程没有生成 `proof_check.v`，默认不要手工补建，除非用户另行要求

## Other Files Under Current Workspace

如果需要补充少量中间文件、编译日志或检查输出，必须满足：

- 只能写在当前 workspace 内
- 不能替代正式产物
- 不能散落到仓库其他位置

## Forbidden Writes

除非用户明确要求，否则禁止修改以下位置：

- `input/`
- 其他题目的 `output/workspace_*`
- 仓库级脚本、README、配置文件
- 公共头文件、公共 Coq 库、教程文件

特别说明：

- 不得为了让当前题通过而顺手修改其他题目的证明产物
- 不得把流程层脚本、README、manifest 写进单题 workspace

## Blocker Handling

出现以下情况时，不要请求人工交互；应停止越界修改，保留当前已生成产物，并在最终结果和日志中明确记录 blocker：

- 需要改变原始 C 程序的语义或算法本体
- 需要修改 `input/<name>.c` 或新增/修改 `input/<name>.v`
- 需要写当前 workspace 之外的任何文件
- 当前公共库或工具链本身有缺陷，必须改仓库级依赖才能继续

## Logging Rules

每次任务都必须在当前 workspace 中维护：

- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/proof_metrics.md`

其中至少要记录：

- 写 annotation 之前的自然语言规格/断言/invariant 推理
- 写证明之前的自然语言 witness/proof plan 推理
- 本次执行遇到的问题和阶段
- 修复方式
- 修复后是否重新 symbolic、重新证明、重新检查
- 整个任务的开始时间、结束时间、总耗时
- 各阶段时间和 token 统计口径；不能只记录编译时间

如果本次没有遇到问题，也要在 `logs/issues.md` 明确写明无异常。
