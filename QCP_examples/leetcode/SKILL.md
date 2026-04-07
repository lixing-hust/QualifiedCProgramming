---
name: C-code-verification
description: C代码验证技能。当用户需要检查C代码是否正确的时候使用。 
---

# C 代码验证流程

本技能用于 `QCP_examples/leetcode/` 下的单题验证。

开始任何任务前，必须先阅读并遵守：

- `doc/TASK_FILE_PERMISSIONS.md`
- `doc/retrieval/INDEX.md`
- `doc/predict/INDEX.md`

其中定义了本题允许读取和写入的范围。可以读取 `QCP_examples` 下其他例子和 `/home/yangfp/QualifiedCProgramming/tutorial/` 下全部教程做参考，但禁止读取当前目标函数同名的历史 workspace；默认只允许写当前题目的 workspace。对于其他例子，不应该一开始就阅读；只有当前步骤不会写、缺少证明或规格思路时，才去搜索并阅读相关例子。

检索规则、允许展开的样例范围、`examples/` 的特殊角色，统一以 `doc/retrieval/INDEX.md` 为准。

谓词选型、数据类型对应的断言模板、常见 unfold/fold 方向，统一以 `doc/predict/INDEX.md` 及其子文档为准。

## 核心要求

- 端到端完成单题验证，不在中途停下等待用户确认。
- 完全自动化执行，不请求人工交互；如果存在 blocker，则在最终结果和日志中明确记录。
- 优先保持原始 C 程序语义不变。
- 每次修改验证输入后，都重新 symbolic 并重新检查相关证明。
- 最终产物中不得保留 `Admitted.` 或额外 `Axiom`。
- `logs/proof_metrics.md` 必须记录整个任务的完成时间口径：至少包含任务开始时间、任务结束时间、总耗时；不能只记录编译时间。
- `logs/workspace_fingerprint.json` 必须维护，至少包含程序语义的自然语言描述和结构化关键词，供后续检索使用。
- 在写 `annotated/<name>.c` 之前，必须先输出自然语言推理到 `logs/annotation_reasoning.md`。
- 在写 `coq/generated/<name>_proof_manual.v` 之前，必须先输出自然语言推理到 `logs/proof_reasoning.md`。
- 上述自然语言推理必须先落盘，再开始对应阶段的代码或证明编辑；不能跳过，不能只在脑中完成。

## 核心流程

### 1. 审查输入

- 阅读 `input/<name>.c`
- 如果存在，阅读 `input/<name>.v`
- 判断是否需要题目专用 Coq 定义
- 明确待验证函数的输入输出语义
- 在 `logs/workspace_fingerprint.json` 中写出该程序的自然语言语义摘要和结构化关键词
- 先基于当前题目本身形成规格和证明计划；需要查阅其它材料时，按 `doc/retrieval/INDEX.md` 与 `doc/predict/INDEX.md` 执行

### 2. 写注释版 C

在当前 workspace 中维护：

- `annotated/<name>.c`
- `logs/annotation_reasoning.md`

开始写 `annotated/<name>.c` 之前，必须先在 `logs/annotation_reasoning.md` 中写出自然语言推理，至少覆盖：

- 待验证函数的语义理解
- 规格设计理由：前置条件、后置条件、必要的 `With`
- 关键断言与循环不变式的候选形式，以及为什么这样写
- 可能的溢出、边界、别名或空指针风险

在设计规格、循环不变式和中间断言前，必须先查阅 `doc/predict/INDEX.md` 及对应数据类型文档。

需要补齐：

- 函数规格：`Require`、`Ensure`、必要时 `With`
- 中间断言：`Assert`、`which implies`
- 循环不变式：`Inv`

如果题目包含循环，在写 invariant 之前必须阅读：

- `/home/yangfp/QualifiedCProgramming/tutorial/T3-assertion-and-invariant.md`

### 3. 做符号执行

运行 qcp / symexec，直到：

- 语法检查通过
- symbolic 到文件尾
- 生成或刷新当前 workspace 下的 `goal` / `proof_auto` / `goal_check` 等文件

如果失败，优先修：

- `annotated/<name>.c`
- 必要时 `input/<name>.v`

并把问题与修复过程记入 `logs/issues.md`。

### 4. 完成 witness 证明

开始这一阶段前，必须先阅读：

- `doc/COQ_PROOF_GUIDE.md`

在当前 workspace 中，只允许在这里写证明与辅助引理：

- `coq/generated/<name>_proof_manual.v`
- `logs/proof_reasoning.md`

开始写 `coq/generated/<name>_proof_manual.v` 之前，必须先在 `logs/proof_reasoning.md` 中写出自然语言推理，至少覆盖：

- 当前需要手动补的 witness 的分类与难点
- 每个 witness 准备用什么事实、引理、拆解顺序或 proof pattern
- 哪些目标依赖重新 symbolic 后的 `goal` / `proof_auto`
- 是否需要辅助引理；如果需要，辅助引理解决什么子问题

要求：

- 只证明 `coq/generated/<name>_proof_manual.v` 中需要手动补的 witness；不要求补 `coq/generated/<name>_proof_auto.v` 里的 `Admitted.`
- `goal`、`proof_auto` 只用于读取和定位目标，不作为手写证明编辑目标
- 所有需要手动补的 witness 最终都被证明
- 修改注释、题目专用 Coq 输入或证明文件后，要重新 symbolic 并重新对齐 witness
- `coq/generated/` 中的 `goal`、`proof_auto`、`goal_check`、`proof_check` 都视为只读
- 必要时补充辅助引理，但应保持职责边界清晰
- 先尝试直接证明当前目标；需要检索类似证明时，按 `doc/retrieval/INDEX.md` 执行
- 如果目标较复杂，应先拆成较小的辅助引理，再回到主 witness

### 5. 最终检查

至少完成以下检查：

- `goal_check.v` 编译通过
-  `proof_manual.v` 中没有Admitted的证明也没有Axioms的引入。
- 检查 `logs/workspace_fingerprint.json` 已存在，并包含语义自然语言描述和结构化关键词
- 检查 `logs/annotation_reasoning.md` 与 `logs/proof_reasoning.md` 已先于对应阶段产出且内容为自然语言推理
- 记录 `logs/issues.md`
- 记录 `logs/proof_metrics.md`，其中必须明确写出整个任务的开始时间、结束时间、总耗时，以及各阶段耗时（如果有）
- 清理 workspace 内临时编译产物，然后删除所有临时文件，注意在删除的时候要把之前的Rocq文件编译产生的.aux文件也删除掉，注意最后用symexec生成的几个文件不需要删除。
