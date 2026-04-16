# Verify File Permissions

本文件只定义 Verify 阶段的读写边界。

## 1. 前提

Verify 的前提是：

- Contract 已经产出 `input/<name>.c`
- 如有需要，Contract 也已产出 `input/<name>.v`

Verify 默认只消费这些正式输入，不负责重写它们。

## 2. 当前任务的唯一 workspace

每次处理某个 `input/<name>.c` 时，都必须先确定本次任务对应的唯一 workspace：

- `output/verify_<timestamp>_<name>/`

除非用户明确授权，否则所有写操作都必须限制在这个 workspace 内。

## 3. 默认允许读取

- `input/<name>.c`
- `input/<name>.v`，如果存在
- `skills/verify/SKILL.md`
- `doc/experiences/README.md`
- `doc/experiences/SYMEXEC.md`
- `doc/experiences/ASSERTION.md`
- `doc/experiences/INV.md`
- `doc/experiences/PROOF.md`
- `doc/experiences/COMPILE.md`
- `doc/COQ_PROOF_GUIDE.md`
- `doc/SCOPE.md`

## 4. 按需允许读取

- `doc/predict/INDEX.md` 及其子文档：只在处理对应数据结构或程序形态时读取
- `doc/retrieval/INDEX.md`：只在当前步骤卡住、需要检索相似例子时读取
- `CAV/examples/`：允许作为优先检索的完整样例库
- `/home/yangfp/QualifiedCProgramming/QCP_examples/` 下其他例子：只有当 `CAV/examples/` 没有足够接近的例子时，才允许扩大范围读取
- `/home/yangfp/QualifiedCProgramming/tutorial/`：只在当前步骤确实缺少教程级说明时读取

## 5. 当前 workspace 内允许人工修改

- `annotated/<name>.c`
- `coq/generated/<name>_proof_manual.v`
- `coq/deps/` 下为当前 workspace 准备的依赖 `.v`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`

## 6. 当前 workspace 内只读文件

允许读取、编译检查、由工具覆盖，但不允许人工修改：

- `original/<name>.c`
- `original/<name>.v`，如果存在
- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_goal_check.v`
- `coq/generated/<name>_proof_check.v`，如果存在
- `logs/qcp_run.log`

## 7. 默认禁止修改

除非用户明确要求，否则禁止修改：

- `input/`
- `raw/`
- 其他题目的 workspace
- 仓库级脚本、README、配置文件
- 公共头文件、公共 Coq 库、公共 strategy 文件
- `QCP_examples/` 下与当前任务无关的其他例子
- `tutorial/` 文件

## 8. 阻塞时如何分流

如果继续推进必须：

- 改写 `input/<name>.c`
- 新增或修改 `input/<name>.v`
- 调整原始题意对应的正式 contract

就应将其视为 Contract 问题，而不是在 Verify 中越权修改。
