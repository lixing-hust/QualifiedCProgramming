# EXPERIENCE 0405

这份笔记记录 2026-04-05 在 `leetcode/` 单题验证流程里沉淀出来的、后续可以直接复用的经验。重点不是“这一次怎么过”，而是“以后怎么更稳、更快”。

## 1. 先做规格设计，再做证明

程序验证里最常见的浪费不是证明写不出来，而是规格一开始就写得不对。

实践上应按下面顺序走：

1. 先把函数的数学语义写清楚。
2. 再决定前置条件需要限制什么。
3. 再设计循环不变式。
4. 最后才写 Coq 证明。

如果第 1 步都没有说清楚，后面的 annotation 和 proof 基本都会反复返工。

## 2. 对循环题，最重要的是找到“状态量的闭式表达”

像 `sum2` 这种题，核心不是循环本身，而是找到一个能在每次迭代前后稳定保持的闭式表达。

本次 `sum2` 的关键观察是：

- 循环累加的是 `2 * i`
- 前 `k` 项和是 `k * (k + 1)`
- 因此把循环变量写成“当前将要处理的下标”时，最自然的不变式是
  `ans == (i - 1) * i`

这个模式很通用：

- 如果每轮加 `i`，试 `ans == (i - 1) * i / 2`
- 如果每轮加 `2 * i`，试 `ans == (i - 1) * i`
- 如果每轮维护前缀和，试 `ans == sum(prefix)`
- 如果每轮维护计数，试“已经处理了多少元素”而不是“还剩多少元素”

经验上，闭式表达一旦选对，`entail_wit` 和 `return_wit` 往往会直接退化成 `lia`。

## 3. 前置条件优先约束“最终值”，常常就够了

对单调累加型循环，一个很实用的原则是：

- 如果中间状态始终不超过最终状态
- 那就优先约束最终值不溢出

例如 `sum2` 里，用

- `0 <= n`
- `n * (n + 1) <= INT_MAX`

通常就足以推出：

- `2 * i` 在范围内
- `ans + 2 * i` 在范围内
- 返回值在范围内

这样规格更短，也更利于自动化。

## 4. 不变式要贴着 `for` 的真实语义写

`for (int i = 1; i <= n; i++)` 的 invariant 不是写在循环体执行后，而是写在每次进入条件判断前。

因此像 `sum2` 这种题，正确直觉是：

- 进入循环判断前，`i` 表示“下一次准备处理的值”
- 此时 `ans` 应该表示“已经处理完 `1..i-1` 的结果”

这就是为什么

- `1 <= i && i <= n + 1`
- `ans == (i - 1) * i`

比

- `ans == i * (i + 1)`

更自然，因为后者更像“循环体执行后”的状态，不适合作为 invariant。

## 5. Coq 证明优先分成“纯算术”和“分离逻辑”两类

在 QCP 生成的 witness 里，先分辨目标属于哪一类，会极大减少无效尝试。

常见分类：

- `safety_wit`：
  多数是整数范围约束，常常是纯算术
- `entail_wit`：
  可能是纯算术，也可能是局部状态变换
- `return_wit`：
  往往是退出条件加 invariant 推出后置条件

如果目标里只有 `[| ... |]` 里的不等式、等式，没有复杂 heap 展开，那优先假设它是纯算术题，直接：

```coq
pre_process_default; lia.
```

不要一上来就写很重的 tactic。

## 6. `pre_process_default; lia` 是第一选择，不是最后选择

本次 `sum2` 的 manual witness：

- `safety_wit_3`
- `safety_wit_4`
- `safety_wit_6`
- `entail_wit_2`
- `return_wit_1`

都可以用：

```coq
pre_process_default; lia.
```

直接收掉。

这说明一个重要经验：

- 对简单算术题，先试最短证明
- 不要先手写 `assert`、`replace`、`ring`

只有当 `lia` 失败时，再拆局部事实。

## 7. 退出条件证明里，经常先把边界夹成等式

`return_wit` 的常用套路是：

- invariant 给一个上界
- 退出条件给一个严格不等式
- 两者夹出精确等式

例如：

- `i > n`
- `i <= n + 1`

可以直接推出：

- `i = n + 1`

一旦得到这个等式，返回值证明就通常变成代数代换。

这个套路对很多 `for` / `while` 题都适用。

## 8. 生成文件和手写文件要明确分工

当前 `leetcode/` 流程里，应该始终记住：

- `goal.v`、`proof_auto.v`、`goal_check.v`、`proof_check.v` 是工具生成物
- `proof_manual.v` 才是人工证明入口

不要试图把所有东西都改到生成文件里。

真正可持续的做法是：

1. 先改 annotation，让 `symexec` 生成更好的 witness
2. 再在 `proof_manual.v` 里补最少量的证明

如果 witness 本身就难看，通常先回去改 annotation，比硬凿 Coq 更省时间。

## 9. 先写自然语言推理，能明显减少返工

在写 annotation 和 proof 前，先把自然语言 reasoning 落盘，有几个实际好处：

- 能提前暴露规格是否自相矛盾
- 能提前暴露 invariant 是否不是“进入循环前”的状态
- 能提前看出哪些 safety witness 只是范围证明
- 能提前决定哪些地方值得回退到 annotation 层修

经验上，这一步不是文书工作，而是减少 proof churn 的最低成本手段。

## 10. QCP 流程里的实际工程坑

### 10.1 `symexec` 二进制未必可直接执行

这次遇到过：

- 仓库里的 `linux-binary/symexec` 没有执行位

处理办法是复制到临时目录并赋可执行权限后再运行。

以后如果再遇到 `Permission denied`，先查文件权限，不要先怀疑 prompt 或 annotation。

### 10.2 workspace 下的 include 路径可能失效

原始示例里常写：

```c
#include "verification_stdlib.h"
```

但如果验证文件被复制到更深层的 workspace 路径，这个 include 可能解析不到。

这时应优先修正验证输入的 include 路径，使它相对当前文件可解析，而不是先怀疑 `symexec` 本身。

### 10.3 `coqc` 的 loadpath 必须从正确根目录解释

`SeparationLogic/_CoqProject` 里的 `-R` 路径是相对 `SeparationLogic/` 根目录写的。

所以如果直接在别的目录运行：

```bash
coqc $(tr '\n' ' ' < _CoqProject) ...
```

就可能找不到：

- `AUXLib`
- `SimpleC.EE`
- `SetsClass`

正确做法是从 `/home/yangfp/QualifiedCProgramming/SeparationLogic` 目录下执行。

## 11. “goal_check 可编译” 和 “无 Admitted/Axiom” 不是一回事

当前这条流水线里，即使：

- `proof_manual.v` 已经把剩余 witness 证明完
- `goal_check.v` 已经编译通过

workspace 里仍可能保留：

- `proof_auto.v` 里的 `Admitted.`
- `goal.v` 里的 witness `Axiom`

这说明要明确区分两个目标：

1. 工作流目标：
   `goal_check` 编译通过，manual witness 补完
2. 更强的洁净目标：
   workspace 中完全无 `Admitted.`、无额外 `Axiom`

如果生成文件是只读的，而工具本身又会产出这些 stub，那么第 2 个目标就不是单题 proof 层能独立解决的，而是生成流水线问题。

## 12. 速度优化经验

如果同一题已经跑通过一次，后续复跑可以明显更快：

- 直接复用已验证过的 annotation 结构
- 直接复用已验证过的 manual proof 形状
- 把 `proof_auto.v` 和 `proof_manual.v` 的编译并行

这样后续复跑的主要时间就不在“想证明怎么写”，而在：

- `coqc` 启动与编译
- loadpath 解析
- workspace 初始化

因此，简单题后续再提速，收益最大的方向通常不是 tactic 微调，而是流程级缓存和更少的重复编译。

## 13. 后续建议

对未来的 `leetcode/` 单题验证，可以默认采用下面模板：

1. 先写 `annotation_reasoning.md`
2. 先找函数的数学闭式表达
3. 用“下一次待处理位置”来设计 invariant
4. 优先用最终值约束避免溢出
5. `symexec`
6. 读 `goal.v`
7. 对纯算术 witness 先试 `pre_process_default; lia`
8. 只有自动化失败时，才补辅助引理
9. 在 `proof_metrics.md` 里记录整个任务起止时间和总耗时

如果一个题在第 7 步前还很乱，通常问题不在 Coq，而在第 2 到第 4 步做得不够好。
