# Proof Experience

本文件只记录 `coq/generated/<name>_proof_manual.v` 的手工证明经验。

## 1. 证明范围

- 只记录 manual proof
- 不记录 invariant/assert/symexec
- 不记录 Coq 编译与路径问题
- 如果 `proof_manual.v` 里没有需要手工证明的 theorem，就直接跳过 manual proof 和 `proof_reasoning.md`

## 2. 开始前先读当前目标

- 先读 `goal.v`
- 再读 `proof_auto.v`
- 再读 `goal_check.v`
- 先确认当前 witness 的前置条件、结论和上下文变量

## 3. 先做最短证明骨架

- 先试 `pre_process`
- 再试 `entailer!`
- 纯算术部分优先交给 `lia`

## 4. 先分清卡点类型

- 算术问题
- 改写问题
- 结构展开问题
- exist / case split 问题

不要一上来就重写整段证明。

## 5. 重复依赖就抽辅助引理

- 多个 witness 反复依赖同一事实，就抽 lemma
- 复杂目标先拆小引理，再回到主 witness

## 6. `entailer!` 收不掉时先整理上下文

- 补 `Intros`
- 补 `subst`
- 补 `rewrite`
- 分开处理 separation logic 部分和纯命题部分

## 7. 失败记录必须写首个稳定错误

- 记录文件
- 记录行号
- 记录原始错误文本

## 8. 不允许绕过证明

- 不允许 `Admitted.`
- 不允许新增 `Axiom`

## 9. 改结构后必须重新 symbolic

- 改了注释
- 改了题目专用 `.v`
- 改了证明结构

都必须重新对齐 witness。

## 10. `proof_auto.v` 已经定义的 lemma，不要在 `proof_manual.v` 里重复定义

- 开始写 manual proof 前，先看一眼 `proof_auto.v`
- 如果某个 `proof_of_<name>_*` 已经在 `proof_auto.v` 里给出，就不要在 `proof_manual.v` 里再写同名 lemma
- 否则 `goal_check.v` 里同时 `Include proof_auto` 和 `Include proof_manual` 时会报重复 label
