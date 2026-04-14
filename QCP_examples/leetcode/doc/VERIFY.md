# Verify: 验证规格输入

## 阅读方式

本文件同时承担两件事：

- verify 阶段的文档阅读指南
- verify 阶段可直接复用的通用经验

使用方式：

- 开始 verify 任务时，先从本文件开头顺序读
- 先看 workspace、输入边界和 verify 职责
- 再看后面的 manual proof 与工程验证经验

不要把“阅读指南”和“经验”分开理解；后面的经验就是前面规则的具体化。

## Workspace 记录位置

verify 阶段的经验记录统一放在：

- `output/verify_<timestamp>_<name>/logs/annotation_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/proof_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/issues.md`
- `output/verify_<timestamp>_<name>/logs/metrics.md`
- 每次 annotate 都可以基于 fingerpoint.json 去参考相近问题的经验

目录分工：
- verify 使用自己独立的 `output/verify_<timestamp>_<name>/`
- annotate 阶段经验记录保留在独立的 `output/annotate_<timestamp>_<name>/`
- `logs/metrics.md` 记录 verify 阶段各步骤时间

Verify 只消费 Annotate 的正式输出：
- `input/<name>.c`
- `input/<name>.v`，如果存在

## 基本假设

- `input/<name>.c` 已经是验证友好的 C
- 其中已有的 `Require` / `Ensure` / `With` 已经正确
- Verify 默认信任这些前后条件，不把“修规格”当默认任务

## Verify 的工作

- 在 `annotated/<name>.c` 中补 `Assert` / `which implies` / `Inv`
- 运行 symbolic / qcp
- 写 `logs/annotation_reasoning.md`
- 写 `logs/proof_reasoning.md`
- 写 `coq/generated/<name>_proof_manual.v`
- 完成最终检查

## Verify 不负责的内容

- 重写自然语言题意
- 重构原始代码为验证友好形态
- 从题意重新生成前后条件

这些都属于 Annotate。

## Manual Proof 经验

手写 `coq/generated/<name>_proof_manual.v` 时，默认采用下面的顺序：

1. 先 `Intros` / `intros`
2. 先用 `entailer!` 把 heap entailment 和纯命题尽量拆开
3. 再做算术化简、有限分类讨论、`replace ... by lia`、重写递推引理
4. 最后再回到剩余的 `entailer!` / `lia` / `reflexivity`

不要一开始就在 heap 还没消掉的时候直接做复杂算术证明。

这条顺序在 `factorial` 的 manual proof 里非常明显：

- safety witness 应先 `entailer!`，把目标拆成纯上下界，再做 `1 <= i <= 10` 的有限 case split
- entail witness 里也应先把 `factorial_inc` 和 `replace ... by lia` 用来整理式子，再让 `entailer!` 对齐 `data_at` 两侧的值

如果一个 lemma 看起来只是纯算术，但 `lia` / `ring` / `vm_compute` 一直失败，优先检查是不是还没有先把 separation entailment 消掉。

## Coq 编译路径

手工编译 generated Coq 文件时，要注意 `SeparationLogic/_CoqProject` 里的相对 `-R` 路径是以：

- `/home/yangfp/QualifiedCProgramming/SeparationLogic`

这个目录为基准，不是以 `leetcode/` 为基准。

因此后续手工运行 `coqc` 编译：

- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_proof_manual.v`
- `coq/generated/<name>_goal_check.v`

时，应从：

- `/home/yangfp/QualifiedCProgramming/SeparationLogic`

目录进入，再读取 `_CoqProject`，并额外给当前 generated 目录补逻辑路径映射。

如果在 `leetcode/` 目录直接拿 `_CoqProject` 里的参数去编译，常见结果是：

- `Cannot find a physical path bound to logical path ...`
- `_CoqProject` 里的相对库目录全部解析失败

这类错误优先按“编译工作目录不对”处理，不要先怀疑 proof 本身。

## 通用验证经验

### 对循环题，先找状态量的闭式表达

循环题的关键通常不是循环本身，而是找出一个能在每轮前后稳定保持的闭式表达。

默认优先问：

- 当前变量表示“下一次要处理的位置”，还是“已经处理完的位置”？
- 累加器、计数器、前缀结果能否写成闭式？

如果闭式表达选对，很多 `entail_wit` 和 `return_wit` 会直接退化成纯算术。

### invariant 要贴着程序真实控制点写

`for` / `while` 的 invariant 写的是“进入判断点前”的状态，不是“循环体执行后”的状态。

因此：

- 优先用“下一次待处理位置”来写 invariant
- 让累加器表示“已经处理完的前缀结果”

这比写成“本轮执行后应该成立什么”更稳定。

### 抽象谓词只展开到当前语句需要的深度

默认保持抽象谓词。

只有在以下时机才展开：

- 读字段
- 写字段
- 做 tag / case 判别
- 调用子函数
- 需要 bridge assert 对齐局部表示

而且展开只到当前语句刚好够用的那一层，不要一次性把整棵结构或整段内存全部打开。

### 指针移动、区间推进类程序，优先找 “context + focus” invariant

对链表遍历、树下降、数组双指针、分段处理，最稳的 invariant 往往不是直接描述“整个结构现在是什么”，而是：

- 已处理的上下文
- 当前正在处理的焦点
- 两者拼起来仍对应整体语义

只要程序在移动指针或边界，就优先考虑这种写法。

### `Assert` 适合阶段切换，不适合补救坏 invariant

`Assert` 最适合做的事是：

- 循环结束后固定退出条件
- 调用子过程前整理资源
- 在不同表示层之间切换

如果你发现自己要靠很多 `Assert` 才能勉强推进，优先回去改 invariant，而不是继续堆更多 `Assert`。

### proof 卡住时，优先怀疑 annotation 和表示，而不是 tactic

一个 witness 很难写时，先判断是不是下面的问题：

- 结构展开点不对
- invariant 没保留边界关系
- 高层/低层规格没有分开
- 本该 shape-only 的地方写成了值语义全展开
- 同一类局部展开在多个分支里重复

如果是这些问题，优先回退去改 `annotated/<name>.c`，通常比硬写更重的 Coq tactic 成本更低。
