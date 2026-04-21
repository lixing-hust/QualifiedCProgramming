---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 只消费 Contract 已经准备好的验证输入，不再负责设计前后条件。

所有 `reasoning` 和 `issues` 日志的核心目标只有一个：保证后来的智能体能够快速看懂当前状态、准确接管，并直接复用之前的定位、修复和证明工作；不要写成只有当前这一轮自己看得懂的简写。

所有 `reasoning` 和 `issues` 条目都必须达到“独立可读”：后来的智能体只读该条目，不打开对应源码，也能知道当前上下文、失败点、关键 C/Coq/命令片段、为什么失败、为什么这样修、下一步是什么。

当前任务一旦确定 workspace=`output/verify_<timestamp>_<name>/`，对应的 annotated 工作副本就唯一固定为 `annotated/verify_<timestamp>_<name>.c`。脚本调用和手动按 skill 执行都必须使用这同一个路径规则，不能各自发明不同位置或文件名。

## 1. 分步阅读规则

不要一开始把所有 experience 全部读完。

应按当前步骤读取对应文档：

- 开始 verify 任务时，先读 `doc/SCOPE.md`、`doc/PERMISSIONS.md`、`doc/experiences/README.md`
- 开始写/改当前任务对应的 `annotated/verify_<timestamp>_<name>.c` 前，读 `doc/experiences/INV.md` 和 `doc/experiences/ASSERTION.md`
- 开始跑 `symexec` 前，读 `doc/experiences/SYMEXEC.md`
- 开始写 `coq/generated/<name>_proof_manual.v` 前，读 `doc/experiences/PROOF.md`
- 开始编译 `goal` / `proof_auto` / `proof_manual` / `goal_check` 前，读 `doc/experiences/COMPILE.md`
- 编译时默认直接复用 `SeparationLogic/examples/*.vo` 的公共 strategy 预编译产物；只有缺失时才回退到当前 workspace 的 `coq/deps/`
- `doc/predict/` 下的文件只在处理对应数据结构或程序形态时读取
- `doc/retrieval/INDEX.md` 只在当前步骤卡住、需要检索相关例子时读取

## 2. 输入

- `input/<name>.c`
- `input/<name>.v`，如果存在

## 3. 输出

- `annotated/verify_<timestamp>_<name>.c`
- `output/verify_<timestamp>_<name>/coq/generated/<name>_proof_manual.v`
- `output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json`
- `output/verify_<timestamp>_<name>/logs/annotation_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/proof_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/issues.md`
- `output/verify_<timestamp>_<name>/logs/metrics.md`

## 4. 硬规则

- 默认信任 `input/<name>.c` / `.v` 的 contract，不重写 `Require` / `Ensure`
- 不要向 `annotated/verify_<timestamp>_<name>.c` 添加已内建的验证头文件：`verification_stdlib.h`、`verification_list.h`、`int_array_def.h`、`char_array_def.h`
- 如果旧输入或旧例子带有这些 include，不要把它当作必须保留的依赖；新注解和新 examples 应使用无冗余 include 的形式
- 只在当前任务对应的 `annotated/verify_<timestamp>_<name>.c` 中补 `Inv`、`Assert`、`which implies`、bridge assert、loop-exit assertion
- 每次改注释后都必须重新跑 `symexec`
- 如果当前程序确实需要补 `Inv` / `Assert`，先写 `logs/annotation_reasoning.md`，再改 annotated 工作副本；如果完全不需要补任何 Verify 注释，就跳过 `annotation_reasoning.md`
- `logs/annotation_reasoning.md` 只能追加，不能覆盖已有内容；必须写得非常具体，至少写清楚当前卡在哪个程序点、哪条注释不成立、看到了什么报错或执行现象、准备改哪一行注释、为什么这次修改预计会修复当前问题；每轮改 annotation 前后都要贴出关键 C/annotation 片段，包括相关 `Inv`、`Assert`、`which implies` 或 loop-exit assertion，并用自然语言解释为什么这样写、它表达了哪段程序状态、如何满足初始化/保持性/退出可用性、为什么能修复当前 VC 或 symexec 问题，不能只贴代码或只写概括
- 如果 `proof_manual.v` 里确实有需要手工证明的 theorem，先写 `logs/proof_reasoning.md`，再改 `proof_manual.v`；如果 `proof_manual.v` 没有需要证明的目标，就跳过 `proof_reasoning.md` 和 manual proof
- `logs/proof_reasoning.md` 只能追加，不能覆盖已有内容；必须写得非常具体，至少写清楚当前卡住的 theorem 或 witness 名、`coqc`/`coqtop` 的具体报错或剩余子目标、当前可用假设、为什么现有脚本不够、已经尝试过哪些 tactic 或 lemma、下一步准备改哪一段 proof；每轮 proof 迭代都要贴出关键 Coq 片段，包括当前 theorem/lemma、失败前后的 tactic 片段、必要的 `Show` 子目标或关键 hypotheses、准备新增或修改的 lemma 形状，并用自然语言解释为什么这样拆 lemma、为什么这个 tactic/rewrite 对应当前子目标、它依赖哪些假设、为什么这次修改能推进 proof，不能只写“尝试证明失败”
- proof 阶段必须不断迭代，直到 `goal_check.v` 编译通过，或外部时间上限触发；其他细节统一以 `doc/experiences/PROOF.md` 为准
- `proof_manual.v` 不得留下 `Admitted.` 或新增 `Axiom`
- `goal_check.v` 必须编译通过
- 编译完成后清理 `coq/` 下非 `.v` 中间产物
- `logs/issues.md` 只能追加，不能覆盖已有内容；必须写得非常具体，详细记录整个 verify 过程中的所有踩坑，而不是只记最后一个错误；每个问题至少要写清楚现象、触发条件、定位到的文件/行号或 theorem、修复动作、修复后的结果；每个代表性问题还要贴出足够读懂问题的关键代码或日志片段，例如 C annotation 片段、Coq theorem/subgoal/tactic 片段、`coqc`/`symexec` 报错片段或相关命令片段，保证后来的智能体只读 `issues.md` 也能理解问题发生在哪里、为什么发生、如何修复
- 验证过程中每解决一个有代表性的通用问题，都必须立即判断是否需要更新 Experience；如果该问题能复用于后续任务，就更新对应的 `doc/experiences/*.md`，不要等到任务最后才回忆
- Experience 只写可复用结论，不写单题流水账；按问题所属阶段写入 `SYMEXEC.md`、`ASSERTION.md`、`INV.md`、`PROOF.md` 或 `COMPILE.md`
- 每次新增、删除、重编号或重写 Experience 条目时，必须同步维护该文件开头的“常见入口”；如果该经验适合作为跨文档检索入口，还必须同步更新 `doc/experiences/README.md` 的“按症状检索”
- `logs/workspace_fingerprint.json` 不能保留脚本初始化时的空占位；必须在任务早期回填非空的 `semantic_description` 和 `keywords`，回填 `keywords` 前先读 `doc/retrieval/INDEX.md`；`keywords` 的 key 和 value 都只能来自其中定义的受控词表
- `logs/metrics.md` 只能追加，不能覆盖已有内容；唯一允许修改的已有内容是最后的 `Final Result: ...` 行
- `logs/metrics.md` 的最后必须显式写一行 `Final Result: Success` 或 `Final Result: Fail`
- 如果本次任务更新了任何经验文档，`logs/metrics.md` 必须显式列出更新了哪些经验文件；如果没有更新，也要明确写 `Experience updates: none`
- `Final Result: Success` 只能在以下条件同时满足时写：
  - `symexec` 成功并基于当前最新 annotated 文件生成了最新 `goal/proof_auto/proof_manual/goal_check`
  - `proof_manual.v` 中所有需要手工证明的 theorem 都已完成
  - `proof_manual.v` 不含 `Admitted.`，也没有新增 `Axiom`
  - `goal.v`、`proof_auto.v`、`proof_manual.v`、`goal_check.v` 全部按当前 workspace 的完整编译模板编译通过
  - `coq/` 下非 `.v` 中间产物已经清理
  - `issues.md` 和 `metrics.md` 已完整更新
- 每次 verify 任务完成后，都要选择性更新 `doc/experiences/SYMEXEC.md`、`doc/experiences/ASSERTION.md`、`doc/experiences/INV.md`、`doc/experiences/PROOF.md`、`doc/experiences/COMPILE.md`

## 5. 最短流程

1. 读 `input/<name>.c` / `.v`。
2. 先读 `doc/retrieval/INDEX.md`，再写并回填 `logs/workspace_fingerprint.json`，确保 `semantic_description` 非空，且 `keywords` 只使用受控词表中的 key 和 value。
3. 如果需要补 `Inv` / `Assert`，读 `INV.md` 和 `ASSERTION.md`，写并持续更新 `logs/annotation_reasoning.md`，记录关键 C/annotation 片段后再修改当前任务对应的 `annotated/*.c`；否则跳过这一步。
4. 读 `SYMEXEC.md`，跑 `symexec`，生成最新 `goal/proof_auto/proof_manual/goal_check`。
5. 如果 `proof_manual.v` 里还有需要手工证明的 theorem，读 `PROOF.md`，写并持续更新 `logs/proof_reasoning.md`，记录关键 Coq theorem/subgoal/tactic 片段后再补 `proof_manual.v`，编译失败就继续 proof 迭代直到通过；否则跳过这一步。
6. 读 `COMPILE.md`，按完整模板编译 `goal`、`proof_auto`、`proof_manual`、`goal_check`。
7. 每解决一个有代表性的通用问题，就同步更新对应 Experience，并同步维护对应文档开头“常见入口”和必要的 `README.md` 按症状索引；同时在 `logs/issues.md` 记录该问题的具体踩坑和修复链路。
8. 详细写 `logs/issues.md` 和 `logs/metrics.md`，把整个过程中的踩坑、定位和修复链路补全，在 `logs/metrics.md` 中列出 `Experience updates`，并在最后一行写 `Final Result: Success` 或 `Final Result: Fail`。

## 6. 完成标准

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.` / `Axiom`
- 当前任务对应的 `annotated/*.c` 已补齐 Verify 注释
- `coq/` 中间产物已清理
- 所有日志已更新
