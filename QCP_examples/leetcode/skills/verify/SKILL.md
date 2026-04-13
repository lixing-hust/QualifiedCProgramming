---
name: verify
description: Verify skill，消费 Annotate 输出完成注解+证明。
---

这是 Verify 阶段。它只消费 Annotate 已经准备好的验证输入，不再负责设计前后条件。

## 输入

正式输入固定为：
- `input/<name>.c`
- `input/<name>.v`，如果存在

其中：
- `input/<name>.c` 已经包含正确、完整的 `Require` / `Ensure` / `With`
- 默认这些前后条件在语法和语义上都正确

## 你的职责

Verify 只做这些事：
- 读取 `input/<name>.c` 和可选 `input/<name>.v`
- 在 `annotated/<name>.c` 中补中间 `Assert`、`which implies`、`Inv`
- 运行 symbolic / qcp
- 写 `logs/annotation_reasoning.md` 和 `logs/proof_reasoning.md`
- 完成 `coq/generated/<name>_proof_manual.v`
- 检查最终证明

## 不属于 Verify 的事

不要在这里做：
- 重写题意
- 重新设计 `Require` / `Ensure`
- 把原始代码改成验证友好形态
- 把自然语言题意翻译成规格输入

这些属于 Annotate。

### 预备文件

- 读 `doc/VERIFY.md` 了解阶段边界。  
- 读 `doc/TASK_FILE_PERMISSIONS.md` 掌握读写范围。  
- 读 `doc/COQ_PROOF_GUIDE.md` 掌握 Coq witness 模式。  
- 若题目包含循环，再读 `/home/yangfp/QualifiedCProgramming/tutorial/T3-assertion-and-invariant.md`。  
- 借助 `doc/retrieval/INDEX.md` 和 `doc/predict/INDEX.md` 找类似例子和合适谓词。

### 核心要求

- 将 `input/<name>.c`/`.v` 视为可信规格；除非冲突，不要改动 `Require`/`Ensure`。  
- 在 `annotated/<name>.c` 中补 `Assert`/`which implies`/`Inv`，先输出 `logs/annotation_reasoning.md`。  
- 每次注释/桥接改动后必须重新跑 `symexec`（同步生成 `goal`/`proof_auto`）再写 `proof_manual`。  
- 写 `logs/proof_reasoning.md` 计划手工 witness，按计划在 `coq/generated/<name>_proof_manual.v` 中补 proof。  
- 如果存在 `input/<name>.v`，可以读取并依赖它，但不要凭空生成一个新的 `.v`。
- 手写证明文件不得留下 `Admitted.` 或新增 `Axiom`。  
- `goal_check.v` 必须编译通过。

### 推荐流程

1. 读取 `input/<name>.c`（和 `input/<name>.v`）。  
2. 写 `logs/workspace_fingerprint.json`，记录自然语言语义与结构化关键词。  
3. 写 `logs/annotation_reasoning.md`，再修改 `annotated/<name>.c`。  
4. 运行 `symexec` / `qcp`：生成 `goal`、`proof_auto`、`proof_manual`、`goal_check`。  
5. 写 `logs/proof_reasoning.md` 说明手工 witness 分组与策略。  
6. 补 `coq/generated/<name>_proof_manual.v`，按 witness 顺序推进。  
7. 分别编译 `goal`→`proof_auto`→`proof_manual`→`goal_check`，处理任何警告。  
8. 写 `logs/issues.md`/`logs/proof_metrics.md`，记录情况和时间。

### 完成标准

- `goal_check.v` 编译通过。  
- `coq/generated/<name>_proof_manual.v` 无 `Admitted.`/`Axiom`。  
- 所有 log、annotated、proof_manual 文件按流程更新完毕。
