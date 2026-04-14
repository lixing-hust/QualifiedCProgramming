# Verify Experience

## 阅读方式

本文件只记录 verify 阶段中 `annotated/<name>.c` 的经验：

- 循环 invariant
- bridge assert / `which implies`
- symbolic 执行与注释对齐

不记录：

- manual Coq 证明（见 `PROOF.md`）
- Coq 编译与 load-path（见 `COMPILE.md`）

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

### `return_wit` 卡住时，优先检查 invariant 是否缺“参数不变关系”

如果 `return_wit` 的左右两侧只差一个参数版本（例如 `a` vs `a@pre`），优先检查循环 invariant 是否显式保留了该关系。

典型补法：

- 在 invariant 里补 `a == a@pre`（或其他需要保持不变的参数）
- 修改后立刻重新 `symexec`，不要继续在旧 `goal/proof_manual` 上硬改

这类问题属于注释层缺信息，不是 Coq tactic 不够强。
