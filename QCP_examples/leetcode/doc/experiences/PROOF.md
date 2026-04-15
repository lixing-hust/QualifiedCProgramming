# Coq Witness Proof Guide

本文件说明在单题验证任务中如何完成 `witness` 的 Coq 证明。

职责边界：

- 只记录 `coq/generated/<name>_proof_manual.v` 的手工证明经验
- 不记录 invariant/assert/symbolic（见 `VERIFY.md`）
- 不记录 Coq 编译与路径问题（见 `COMPILE.md`）

## 总体原则

- 优先参考复用仓库中已经存在的证明套路，不要从零硬写。
- 先读当前 witness 的 statement，再决定需要搜索什么样的例子。
- 证明过程中如果发现目标过大、上下文过乱，应先拆分，而不是直接在一个 lemma 里硬推到底。

## 开始证明前应该做什么

开始写 `coq/generated/<name>_proof_manual.v` 之前，先做这几件事：

- 阅读当前题生成出来的 `goal.v`、`proof_auto.v`、`goal_check.v`
- 确认当前 witness 对应的前置条件、结论和上下文变量
- 在仓库中搜索相似的 Coq 证明，优先看：
  - `QCP_examples/` 下其他题目的 `proof_manual.v`
  - `QCP_examples/` 下其他题目的 `proof_auto.v`
  - `SeparationLogic/examples/` 和相关公共库中的现成引理与证明模式

可以重点搜索：

- 相同或相近的 witness 名称，例如 `safety_wit`、`entail_wit`、`return_wit`
- 相同的程序结构，例如循环、分支、数组访问、算术边界
- 相同的证明动作，例如 `entailer!`、`lia`、`rewrite`、`destruct`

## 搜索策略

搜索时不要泛泛地看大量文件，应该带着当前目标去找类似证明。

优先搜索：

- 同类函数的其他题目证明
- 同类 witness 的已有证明
- 当前目标里出现的关键谓词、关键表达式、关键不变量

如果一个证明片段看起来接近目标，就继续阅读它所在文件的上下文，理解：

- 它依赖哪些 imports
- 它先做了哪些 `Intros` / `subst` / `destruct`
- 它是先做 separation logic 化简，还是先做纯算术化简

## 推荐证明顺序

处理单个 witness 时，建议按下面顺序推进：

1. 先尝试最直接的自动化，如 `pre_process`、`entailer!`、`lia`
2. 如果失败，先区分失败点是：
   - 纯算术问题
   - 等式改写问题
   - 数据结构/权限展开问题
   - 量词、existential、case split 问题
3. 针对失败点补中间步骤，而不是一次性重写整段证明
4. 如果多个 witness 反复依赖同一事实，把它提炼成辅助引理

## 复杂定理的处理方式

如果一个 witness 或辅助结论明显较复杂，不要直接在主证明里硬做完。

应优先拆成更小的步骤，例如：

- 先证明纯算术引理
- 再证明某个不变量保持
- 再证明某个分支下的局部 entailment
- 最后把这些小结论拼回主 witness

拆分后的辅助引理应满足：

- 名字清楚，能说明用途
- 尽量只处理一个局部问题
- 放在 `coq/generated/<name>_proof_manual.v` 中靠前位置，便于后续复用

## 处理卡点的具体建议

常见卡点及建议：

- `entailer!` 无法收尾：
  - 先看是否缺少 `Intros`、`subst`、`rewrite`
  - 把 separation logic 部分和纯逻辑部分分开处理
- 算术目标复杂：
  - 先用 `assert` 补局部事实
  - 再用 `lia` 或已有整数引理收尾
- 分支很多：
  - 先 `destruct` 出关键条件
  - 每个分支单独整理上下文
- witness 太长难以定位：
  - 先在 `goal.v` 里确认该 witness 的精确 statement
  - 再去仓库里找相同类型的已完成证明做参照

## proof 失败记录规范

- proof 失败时，不要写笼统描述（例如“proof 编译失败”）。
- 必须记录首个稳定失败点：`文件 + 行号 + 原始错误文本`。
- 例如：`array_sum_proof_manual.v:49 Error: Tactic failure: Cannot find witness.`  
- 每次修复后都要更新这个“首个失败点”，直到 `goal_check` 通过。

## 边界要求

- 可以参考仓库里的类似 Coq 证明，但不能直接照搬当前目标函数同名 workspace 的旧证明
- 不要通过引入 `Admitted.` 或额外 `Axiom` 绕过证明
- 如果修改了注释、题目专用 Coq 输入或证明结构，必须重新 symbolic 并重新对齐 witness

## 新增稳定套路（数组前缀和类）

- `safety_wit` 常用骨架：  
  `ret = sum(sublist ...)` + 元素有界 -> 前缀和有界 -> `ret + Znth ...` 有界。
- 这种题优先写一个局部辅助引理（例如 signed sum bound），再在主 witness 中做实例化。
- 尽量少写依赖上下文名字的 `match goal`；`symexec` 重新生成后变量名和顺序会变，脚本容易脆。  
  优先用显式 `assert`、`entailer!`、`lia` 组合。
