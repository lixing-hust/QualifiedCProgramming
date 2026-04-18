# Proof Experience

本文件只记录 `coq/generated/<name>_proof_manual.v` 的手工证明经验。

## 1. 证明范围

- 只记录 manual proof
- 不记录 invariant/assert/symexec
- 不记录 Coq 编译与路径问题
- 如果 `proof_manual.v` 里没有需要手工证明的 theorem，就直接跳过 manual proof 和 `proof_reasoning.md`
- 如果 `proof_manual.v` 或 `goal_check.v` 还没有编译通过，就不能退出 proof 阶段，必须继续证明

## 2. 开始前先读当前目标

- 先读 `goal.v`
- 再读 `proof_auto.v`
- 再读 `goal_check.v`
- 先确认当前 witness 的前置条件、结论和上下文变量
- 第一轮分析先写入 `logs/proof_reasoning.md`

## 3. 先做最短证明骨架

- 先试 `pre_process`
- 再试 `entailer!`
- 纯算术部分优先交给 `lia`
- 每一轮失败后，都要把新的失败点、原因判断和下一步计划追加写入 `logs/proof_reasoning.md`

## 4. 先分清卡点类型

- 算术问题
- 改写问题
- 结构展开问题
- exist / case split 问题
- 辅助引理缺失

不要一上来就重写整段证明。

## 5. 编译失败时先看完整 proof state

- 不能只看 `coqc` 的单行报错
- 应优先用 `coqtop` 进入当前定理，查看具体假设、子目标和 tactic 后状态
- 首先搞清楚当前真正缺的是什么，再决定改 proof、加 rewrite 还是补引理

## 6. 卡住时去例子库检索

- proof 卡住时，按 `doc/retrieval/INDEX.md` 检索相关例子
- 优先看 `CAV/examples/`
- 如果 `CAV/examples/` 没有足够接近的例子，再扩大到整个 `QCP_examples/`
- 检索后要明确写出：当前目标为什么证不出来，现有例子提供了什么可复用 proof pattern

## 7. 主 witness 不要硬顶 tactic，先抽 helper lemma

如果主 witness 同时承担下面几件事：

- 展开结构
- 改写列表/数组表达式
- 处理算术 side condition
- 证明核心语义结论

就不要继续在主 witness 里硬顶 tactic。

更稳的做法是：

- 主 witness 只负责 `Exists`、`Intros`、`subst`、`rewrite`、调用引理
- 把反复出现的 list / arithmetic / sublist / append / max-min 事实先抽成 helper lemma
- helper lemma 直接写在当前 `coq/generated/<name>_proof_manual.v`

主 witness 越短，越容易编译稳定；复杂 proof 应该沉到辅助引理里。

## 8. `Cannot find witness` 往往不是神秘错误，而是 side condition 不显式

这类报错常见于：

- `lia` 需要非空条件，但上下文里没显式写出来
- 需要长度事实，但只有隐含的 `Zlength` 关系
- `Znth` / `sublist` / `replace_Znth` 的边界条件还没固定

遇到这类错误时，先不要继续换 tactic。

优先补这些显式事实：

- 非空
- 长度
- 边界
- 索引范围
- 当前分支下的等式关系

经验上，很多 `Cannot find witness` 在补完这类中间 `assert` 后就会消失。

## 9. Coq 脚本尽量写保守，不要过度依赖自动化和自动命名

更稳的写法是：

- 少用复杂的 intro-pattern
- 少依赖自动命名的 `IH`
- 中间事实用 `assert` 明确命名
- 重写后把关键索引和等式显式化简

不稳的写法通常是：

- 一步塞太多 pattern
- 指望 `lia` 自动猜出所有边界
- 依赖当前 Coq 版本恰好给出的 `IH` 名字或简化顺序

保守脚本虽然稍长，但在不同 Coq 版本和不同 proof state 下更稳定。

## 10. `entailer!` 收不掉时先整理上下文

- 补 `Intros`
- 补 `subst`
- 补 `rewrite`
- 分开处理 separation logic 部分和纯命题部分

## 11. 失败记录必须写首个稳定错误

- 记录文件
- 记录行号
- 记录原始错误文本
- 记录为什么这个错误会出现

## 12. 不允许绕过证明

- 不允许 `Admitted.`
- 不允许新增 `Axiom`

## 13. 改结构后必须重新 symbolic

- 改了注释
- 改了题目专用 `.v`
- 改了证明结构

都必须重新对齐 witness。

## 14. `proof_auto.v` 已经定义的 lemma，不要在 `proof_manual.v` 里重复定义

- 开始写 manual proof 前，先看一眼 `proof_auto.v`
- 如果某个 `proof_of_<name>_*` 已经在 `proof_auto.v` 里给出，就不要在 `proof_manual.v` 里再写同名 lemma
- 否则 `goal_check.v` 里同时 `Include proof_auto` 和 `Include proof_manual` 时会报重复 label

## 15. max/min 扫描题的 helper lemma 值得模板化

对 max/min 扫描类题目，反复会用到这些 lemma：

- 前缀中任意元素都不超过当前 prefix max
- 如果所有元素都不超过某个上界，则 prefix max 也不超过这个上界
- 在列表尾部追加一个元素后，max/min 的单调性
- 追加元素不改变当前 max/min 的条件

这类题的主 witness 通常不难，难点在这些纯 list helper lemma。

所以更稳的策略是：

- 尽早把它们沉淀成局部模板
- 主 witness 只做“把循环状态翻译成 prefix 语义，再调用 lemma”

不要每道 max/min 扫描题都从零在主 witness 里手搓同一套推理。

## 16. 如果 return witness 同时出现 `x` 和 `x_pre`，先检查 annotation 是否保留了 `x == x@pre`

典型现象：

- `return_wit` 看起来只差把当前参数名改回 `*_pre`
- proof 里缺的不是 list / arithmetic，而是“这个标量参数从头到尾没变”

处理顺序：

1. 先看 loop invariant 和 loop-exit assertion 是否显式保留了 `x == x@pre`
2. 如果没有，回 annotation 层补这个不变关系
3. 清理 generated 文件并重新跑 `symexec`

不要在 `proof_manual.v` 里硬证一个 annotation 本该直接保留的参数恒等关系。

## 17. 字符串/数组复制题如果只知道“当前位置读到 0”，先检查 contract 是否排除了中间 0

典型现象：

- `return_wit` 最后只剩：
  - `replace_Znth i 0 (l1 ++ d1) = l ++ [0]`
  - 或等价的 `CharArray.full ...` 目标
- 已知条件只有：
  - 前缀 `l1` 与 `l` 在 `< i` 上相等
  - `Znth i (l ++ [0]) = 0`
  - 长度关系

这时不要默认继续堆 tactic。

先判断当前 contract 是否真的能推出：

- `i = n`
- 或者 `l` 在 `0 <= k < n` 上都非零

如果都没有，那么 return witness 往往不是 proof 技巧问题，而是 specification 本身没有排除中间 `0`，导致“在第一个 `0` 处停止复制”不足以推出“整个目标数组等于 `l ++ [0]`”。

处理顺序：

1. 先用 `coqtop` 看清剩余目标是否已经退化成纯 list equality / `CharArray.full` equality
2. 如果是，就检查 precondition / ghost predicate 是否提供“唯一终止符”或“前缀元素非零”信息
3. 如果没有，优先记录为 contract gap，不要在 manual proof 里盲目硬证

## 18. 字符串扫描类 return witness 常见的真正桥接点是先证 `i = n`

对 `string_copy`、`strlen` 这类题，`return_wit` 最后看起来常常像：

- `replace_Znth i 0 (...) = l ++ [0]`
- 或等价的 `CharArray.full ... |-- CharArray.full ...`

这时不要直接盯着最后一条 `replace_Znth`。

更稳的顺序是：

1. 先看当前假设能不能推出 `i = n`
2. 再用前缀相等性质证明 `l1 = l`
3. 最后再去化简 `replace_Znth` / `replace_nth`

如果一开始不先拿到 `i = n`，后面的尾部归一化通常会越写越乱。

## 19. `Cannot find witness` 经常意味着长度信息还没展开到 `lia` 能直接用的形状

常见卡点：

- `Zlength (x :: l) = ...`
- `Zlength nil = ...`
- “尾部长度等于 1，所以列表只能是 `x :: nil`”

这类地方只写 `lia` 往往不够。

更稳的做法是先显式展开：

- `Zlength_cons`
- `Zlength_nil`
- `Zlength_nonneg`

必要时先单独证明一个局部事实，例如：

- 某个尾表长度恰好为 `1`
- 因此它一定是 `x :: nil`

把这层桥接写出来后，`lia` 才会稳定。

## 20. `replace_Znth` 最后一步经常卡在 `nat` 索引没有化简

即使在 `Z` 上已经知道索引等于 `0`，展开

- `replace_Znth`

之后，Coq 里常常还残着：

- `replace_nth (Z.to_nat (...)) ...`

如果这个 `Z.to_nat (...)` 不显式改成 `0%nat`，`simpl` 很可能不会继续。

稳定写法是：

1. `unfold replace_Znth`
2. 显式把 `Z.to_nat (...)` 改成 `0%nat`
3. 再 `simpl`

很多看起来像“最后一条列表相等还差一点”的目标，真正缺的就是这一步。

## 21. Coq 脚本优先用保守写法，尤其少依赖脆弱的 `destruct ... as ...` 形状

自动生成或半自动修改的 proof 中，以下写法更容易在不同环境里出问题：

- 复杂 `intro-pattern`
- 嵌套很深的 bullet
- `destruct ... as ...` 紧跟多个分支和局部重写

更稳的替代是：

- 先 `destruct`
- 再在分支里单独 `rewrite`
- 需要结构信息时，先证明一个局部 `assert`

这样脚本会更长，但通常更稳，也更容易在下一轮编译失败时精确定位 first blocker。
