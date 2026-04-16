# Proof Experience

本文件只记录 `coq/generated/<name>_proof_manual.v` 的手工证明经验。

## 1. 证明范围

- 只记录 manual proof
- 不记录 invariant/assert/symbolic（见 `INV.md`、`ASSERTION.md`、`SYMEXEC.md`）
- 不记录 Coq 编译与路径问题（见 `COMPILE.md`）

## 2. 开始前检查

- 开始证明前，先读当前题生成出来的 `goal.v`、`proof_auto.v`、`goal_check.v`
- 先确认当前 witness 的前置条件、结论和上下文变量，再决定搜索什么例子
- 优先参考仓库里相同或相近的 `safety_wit`、`entail_wit`、`return_wit` 证明套路，不要从零硬写
- 搜索时只看与当前目标直接相关的 witness、谓词、表达式和证明动作，不要泛读大量文件
- 处理单个 witness 时，先尝试 `pre_process`、`entailer!`、`lia`，失败后再区分是算术、改写、结构展开还是分支问题
- 如果多个 witness 反复依赖同一事实，就把它提炼成辅助引理
- 复杂目标先拆成小引理，再回到主 witness；不要在一个 lemma 里硬推到底
- `entailer!` 无法收尾时，先补 `Intros`、`subst`、`rewrite`，把 separation logic 部分和纯逻辑部分分开处理
- proof 失败记录必须写首个稳定失败点：文件、行号、原始错误文本
- 不允许通过 `Admitted.` 或新增 `Axiom` 绕过证明
- 如果修改了注释、题目专用 Coq 输入或证明结构，必须重新 symbolic 并重新对齐 witness
- 数组前缀和类题，优先把“前缀和有界”整理成局部辅助引理，再在主 witness 里实例化
- 尽量少写依赖上下文名字的脆弱 `match goal`；优先用显式 `assert`、`entailer!`、`lia`
