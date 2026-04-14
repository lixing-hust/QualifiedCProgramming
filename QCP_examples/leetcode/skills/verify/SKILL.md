---
name: verify
description: Verify skill，消费 Annotate 输出完成注解+证明。
---

这是 Verify 阶段。它只消费 Annotate 已经准备好的验证输入，不再负责设计前后条件。

开始当前 verify 任务前，先阅读：

- `doc/VERIFY.md`

通用经验、细节写法和判断标准统一以 `doc/VERIFY.md` 为准，这里不重复展开。

### 文档使用策略

- 默认先基于 `input/<name>.c`、可选 `input/<name>.v` 和当前 workspace 直接开始 verify 主流程，不要一开始就通读所有 doc。  
- 先尝试写 `logs/workspace_fingerprint.json`、`logs/annotation_reasoning.md` 和 `annotated/<name>.c`；只有在这个尝试过程中遇到具体问题时，才去读对应文档。  
- 只有在当前步骤确实缺少规则、模板、谓词或证明思路时，才按需读取对应文档。  
- 优先级如下：  
  1. 当前输入与当前 workspace  
  2. `doc/TASK_FILE_PERMISSIONS.md`，仅当需要确认读写边界时  
  3. `doc/VERIFY.md`，仅当需要确认 verify 目录约定或阶段边界时  
  4. `doc/COQ_PROOF_GUIDE.md`，仅当需要手工 witness 证明模式时  
  5. `/home/yangfp/QualifiedCProgramming/tutorial/T3-assertion-and-invariant.md`，仅当题目包含循环且 invariant 没有把握时  
  6. `doc/predict/INDEX.md` 和 `doc/retrieval/INDEX.md`，仅当当前步骤不会写、缺少谓词模板或需要检索类似例子时  
- 不要为了“先全面了解”而展开大段 doc；文档只解决当前阻塞。

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

本阶段的经验记录统一放在：
- `output/verify_<timestamp>_<name>/logs/`

## 不属于 Verify 的事

不要在这里做：
- 重写题意
- 重新设计 `Require` / `Ensure`
- 把原始代码改成验证友好形态
- 把自然语言题意翻译成规格输入

这些属于 Annotate。



### 核心要求

- 将 `input/<name>.c`/`.v` 视为可信规格；除非冲突，不要改动 `Require`/`Ensure`。  
- Annotate 和 Verify 的边界必须保持硬分离：`input/<name>.c` 应只包含 contract；Verify 才负责补循环 invariant、bridge assert、`which implies` 和 loop-exit assertion。  
- 先做 `workspace_fingerprint`、`annotation_reasoning`、`annotated/<name>.c` 这条主线；不要先花大量时间阅读文档或扫描样例。  
- 如果还没有开始写 `annotation_reasoning.md` 或 `annotated/<name>.c`，就不应该先去系统性阅读 doc、脚本或样例。  
- 在 `annotated/<name>.c` 中补 `Assert`/`which implies`/`Inv`，并在需要时补 loop-exit assertion；先输出 `logs/annotation_reasoning.md`。  
- 每次注释/桥接改动后必须重新跑 `symexec`（同步生成 `goal`/`proof_auto`）再写 `proof_manual`。  
- 写 `logs/proof_reasoning.md` 计划手工 witness，按计划在 `coq/generated/<name>_proof_manual.v` 中补 proof。  
- 如果存在 `input/<name>.v`，可以读取并依赖它，但不要凭空生成一个新的 `.v`。
- 手写证明文件不得留下 `Admitted.` 或新增 `Axiom`。  
- `goal_check.v` 必须编译通过。
- 本阶段的 reasoning、issues、metrics 都必须写在当前 `output/verify_<timestamp>_<name>/logs/` 下。
- `metrics.md` 记录 verify 阶段各步骤的开始时间、结束时间和耗时，不再使用只面向 proof 的 `proof_metrics.md` 命名。

### 推荐流程

1. 读取 `input/<name>.c`（和 `input/<name>.v`）。  
2. 写 `logs/workspace_fingerprint.json`，记录自然语言语义与结构化关键词。  
3. 写 `logs/annotation_reasoning.md`，再修改 `annotated/<name>.c`，把 invariant、bridge assert、`which implies` 和必要的退出断言补全。  
4. 运行 `symexec` / `qcp`：生成 `goal`、`proof_auto`、`proof_manual`、`goal_check`。  
5. 写 `logs/proof_reasoning.md` 说明手工 witness 分组与策略。  
6. 补 `coq/generated/<name>_proof_manual.v`，按 witness 顺序推进。  
7. 分别编译 `goal`→`proof_auto`→`proof_manual`→`goal_check`，处理任何警告。  
8. 只有在第 2-7 步遇到具体阻塞时，才按需读取 `doc/`、`tutorial/` 或检索样例。  
9. 写 `logs/issues.md`/`logs/metrics.md`，记录情况和各步骤时间。

### 完成标准

- `goal_check.v` 编译通过。  
- `coq/generated/<name>_proof_manual.v` 无 `Admitted.`/`Axiom`。  
- `annotated/<name>.c` 中已经补齐 Verify 应负责的 invariant、bridge assert、`which implies` 和必要退出断言，而这些内容没有回流到 `input/<name>.c`。  
- 所有 log、annotated、proof_manual 文件按流程更新完毕。
