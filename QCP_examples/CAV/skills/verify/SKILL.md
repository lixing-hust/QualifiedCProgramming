---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 只消费 Contract 已经准备好的验证输入，不再负责设计前后条件。

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
- 只在当前任务对应的 `annotated/verify_<timestamp>_<name>.c` 中补 `Inv`、`Assert`、`which implies`、bridge assert、loop-exit assertion
- 每次改注释后都必须重新跑 `symexec`
- 如果当前程序确实需要补 `Inv` / `Assert`，先写 `logs/annotation_reasoning.md`，再改 annotated 工作副本；如果完全不需要补任何 Verify 注释，就跳过 `annotation_reasoning.md`
- `logs/annotation_reasoning.md` 不能只写最终答案；必须记录每一轮注释层迭代中的判断、失败原因、修改方向，以及为什么这次修改有望修复当前问题
- 如果 `proof_manual.v` 里确实有需要手工证明的 theorem，先写 `logs/proof_reasoning.md`，再改 `proof_manual.v`；如果 `proof_manual.v` 没有需要证明的目标，就跳过 `proof_reasoning.md` 和 manual proof
- `logs/proof_reasoning.md` 不能只写首轮计划；必须持续追加每一轮 proof 迭代中的失败点、当前假设、为什么证不出来、尝试过什么、下一步准备怎么改
- proof 阶段的具体迭代、编译、检索和辅助引理规则统一以 `doc/experiences/PROOF.md` 为准
- `proof_manual.v` 不得留下 `Admitted.` 或新增 `Axiom`
- `goal_check.v` 必须编译通过
- 编译完成后清理 `coq/` 下非 `.v` 中间产物
- `logs/issues.md` 必须详细记录整个 verify 过程中的所有踩坑，而不是只记最后一个错误；至少要覆盖现象、触发条件、定位过程、修复动作和结果
- 每次 verify 任务完成后，都要选择性更新 `doc/experiences/SYMEXEC.md`、`doc/experiences/ASSERTION.md`、`doc/experiences/INV.md`、`doc/experiences/PROOF.md`、`doc/experiences/COMPILE.md`

## 5. 最短流程

1. 读 `input/<name>.c` / `.v`。
2. 写 `logs/workspace_fingerprint.json`。
3. 如果需要补 `Inv` / `Assert`，读 `INV.md` 和 `ASSERTION.md`，写并持续更新 `logs/annotation_reasoning.md`，修改当前任务对应的 `annotated/*.c`；否则跳过这一步。
4. 读 `SYMEXEC.md`，跑 `symexec`，生成最新 `goal/proof_auto/proof_manual/goal_check`。
5. 如果 `proof_manual.v` 里还有需要手工证明的 theorem，读 `PROOF.md`，写并持续更新 `logs/proof_reasoning.md`，补 `proof_manual.v`，编译失败就继续 proof 迭代直到通过；否则跳过这一步。
6. 读 `COMPILE.md`，按完整模板编译 `goal`、`proof_auto`、`proof_manual`、`goal_check`。
7. 详细写 `logs/issues.md` 和 `logs/metrics.md`，把整个过程中的踩坑、定位和修复链路补全。

## 6. 完成标准

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.` / `Axiom`
- 当前任务对应的 `annotated/*.c` 已补齐 Verify 注释
- `coq/` 中间产物已清理
- 所有日志已更新
