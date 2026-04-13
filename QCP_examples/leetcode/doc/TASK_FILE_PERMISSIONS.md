# Verify File Permissions

本文件只定义 Verify 的文件权限。

Verify 的前提是：
- Annotate 已经产出 `input/<name>.c`
- 如有需要，Annotate 也已产出 `input/<name>.v`

Verify 只能消费这些输入，不负责重写它们。

## Core Rule

每次处理某个 `input/<name>.c` 时，都必须先确定本次任务对应的唯一 workspace：

- `output/workspace_<timestamp>_<name>/`

除非用户明确授权，否则所有写操作都必须限制在这个 workspace 内。

## Allowed Reads

默认允许读取：
- `input/<name>.c`
- `input/<name>.v`，如果存在
- `skills/verify/SKILL.md`
- `doc/VERIFY.md`
- `doc/COQ_PROOF_GUIDE.md`
- 其他样例与教程，用于需要时参考

## Writable Files In Current Workspace

允许人工创建或修改：
- `annotated/<name>.c`
- `coq/generated/<name>_proof_manual.v`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/proof_metrics.md`

## Read-Only Files In Current Workspace

允许读取、编译检查、由工具覆盖，但不允许人工修改：
- `original/<name>.c`
- `original/<name>.v`，如果存在
- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_goal_check.v`
- `coq/generated/<name>_proof_check.v`，如果存在
- `logs/qcp_run.log`

## Forbidden Writes

除非用户明确要求，否则禁止修改：
- `input/`
- 其他题目的 workspace
- 仓库级脚本、README、配置文件
- 公共头文件、公共 Coq 库、教程文件

## Blocker Handling

如果继续推进必须改写 `input/<name>.c` 或新增/修改 `input/<name>.v`，应将其视为 Annotate 问题，而不是在 Verify 中越权修改。
