---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 只消费 Contract 已经准备好的验证输入，不再负责设计前后条件。

开始当前任务前，先阅读：

- `doc/experiences/README.md`
- `doc/experiences/SYMEXEC.md`
- `doc/experiences/ASSERTION.md`
- `doc/experiences/INV.md`
- `doc/experiences/PROOF.md`
- `doc/experiences/COMPILE.md`

其他文档只在遇到具体阻塞时按需读取。

## 1. 输入

- `input/<name>.c`
- `input/<name>.v`，如果存在

## 2. 输出

- `annotated/<name>.c`
- `coq/generated/<name>_proof_manual.v`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/metrics.md`

## 3. 硬规则

- 默认信任 `input/<name>.c` / `.v` 的 contract，不重写 `Require` / `Ensure`
- 只在 `annotated/<name>.c` 中补 `Inv`、`Assert`、`which implies`、bridge assert、loop-exit assertion
- 每次改注释后都必须重新跑 `symexec`
- 先写 `logs/annotation_reasoning.md`，再改 `annotated/<name>.c`
- 先写 `logs/proof_reasoning.md`，再改 `proof_manual.v`
- `proof_manual.v` 不得留下 `Admitted.` 或新增 `Axiom`
- `goal_check.v` 必须编译通过
- 编译完成后清理 `coq/` 下非 `.v` 中间产物

## 4. 最短流程

1. 读 `input/<name>.c` / `.v`。
2. 写 `logs/workspace_fingerprint.json`。
3. 写 `logs/annotation_reasoning.md`，修改 `annotated/<name>.c`。
4. 跑 `symexec`，生成最新 `goal/proof_auto/proof_manual/goal_check`。
5. 写 `logs/proof_reasoning.md`，补 `proof_manual.v`。
6. 按顺序编译 `goal`、`proof_auto`、`proof_manual`、`goal_check`。
7. 写 `logs/issues.md` 和 `logs/metrics.md`。

## 5. 完成标准

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.` / `Axiom`
- `annotated/<name>.c` 已补齐 Verify 注释
- `coq/` 中间产物已清理
- 所有日志已更新
