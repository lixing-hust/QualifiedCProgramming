---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 只消费 Contract 已经准备好的验证输入，不再负责设计前后条件。

## 1. 分步阅读规则

不要一开始把所有 experience 全部读完。

应按当前步骤读取对应文档：

- 开始 verify 任务时，先读 `doc/SCOPE.md`、`doc/PERMISSIONS.md`、`doc/experiences/README.md`
- 开始写/改 `annotated/<name>.c` 前，读 `doc/experiences/INV.md` 和 `doc/experiences/ASSERTION.md`
- 开始跑 `symexec` 前，读 `doc/experiences/SYMEXEC.md`
- 开始写 `coq/generated/<name>_proof_manual.v` 前，读 `doc/experiences/PROOF.md`
- 开始编译 `goal` / `proof_auto` / `proof_manual` / `goal_check` 前，读 `doc/experiences/COMPILE.md`
- `doc/predict/` 下的文件只在处理对应数据结构或程序形态时读取，例如数组题读数组相关文档，字符串题读字符串相关文档
- `doc/retrieval/INDEX.md` 只在当前步骤卡住、需要检索相关例子时读取

只有在当前步骤确实遇到阻塞时，才额外去读其他文档。

## 2. 输入

- `input/<name>.c`
- `input/<name>.v`，如果存在

## 3. 输出

- `annotated/<name>.c`
- `coq/generated/<name>_proof_manual.v`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`

## 4. 硬规则

- 默认信任 `input/<name>.c` / `.v` 的 contract，不重写 `Require` / `Ensure`
- 只在 `annotated/<name>.c` 中补 `Inv`、`Assert`、`which implies`、bridge assert、loop-exit assertion
- 每次改注释后都必须重新跑 `symexec`
- 先写 `logs/annotation_reasoning.md`，再改 `annotated/<name>.c`
- 先写 `logs/proof_reasoning.md`，再改 `proof_manual.v`
- `proof_manual.v` 不得留下 `Admitted.` 或新增 `Axiom`
- `goal_check.v` 必须编译通过
- 编译完成后清理 `coq/` 下非 `.v` 中间产物
- 每次 verify 任务完成后，都要选择性更新 `doc/experiences/SYMEXEC.md`、`doc/experiences/ASSERTION.md`、`doc/experiences/INV.md`、`doc/experiences/PROOF.md`、`doc/experiences/COMPILE.md`

## 5. 最短流程

1. 读 `input/<name>.c` / `.v`。
2. 写 `logs/workspace_fingerprint.json`。
3. 读 `INV.md` 和 `ASSERTION.md`，写 `logs/annotation_reasoning.md`，修改 `annotated/<name>.c`。
4. 读 `SYMEXEC.md`，跑 `symexec`，生成最新 `goal/proof_auto/proof_manual/goal_check`。
5. 读 `PROOF.md`，写 `logs/proof_reasoning.md`，补 `proof_manual.v`。
6. 读 `COMPILE.md`，按顺序编译 `goal`、`proof_auto`、`proof_manual`、`goal_check`。
7. 写 `logs/issues.md` 和 `logs/metrics.md`。

## 6. 完成标准

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.` / `Axiom`
- `annotated/<name>.c` 已补齐 Verify 注释
- `coq/` 中间产物已清理
- 所有日志已更新
