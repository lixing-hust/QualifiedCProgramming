# Invariant Experience

本文件只记录循环 invariant 的设计经验。

不记录：

- `Assert` / `which implies` 细节（见 `ASSERTION.md`）
- symbolic 执行流程（见 `SYMEXEC.md`）
- manual proof（见 `PROOF.md`）

## 1. 写 invariant 前，必须先做充分的自然语言 reasoning，并检查能否证出后条件

如果当前函数根本不需要补任何 `Inv` / `Assert`，就不要机械地生成 `annotation_reasoning.md`；直接跳过这一阶段。

在真正写 `Inv` 之前，必须先用自然语言把思路写清楚，而不是直接试错式地改注释。

至少要先分析：

- 当前循环变量各自表示什么：已处理部分、待处理部分、还是下一步位置
- 哪些程序变量、数组段、指针区间是每轮都要保留的
- 后条件真正需要的语义是什么
- 当前准备写的 invariant 是否会把这些语义保留下来

如果题目较复杂，这份 reasoning 应先落到当前 workspace 的 `logs/annotation_reasoning.md`，再开始改 `annotated/verify_<timestamp>_<name>.c`。

写任何 invariant 之前，还必须逐条检查它是否同时满足下面三件事：

- 初始化成立：循环第一次进入判断点前，invariant 就已经成立
- 保持性成立：假设本轮开始时 invariant 成立，执行一轮循环体后，下轮判断点前仍成立
- 退出可用：循环条件为假时，invariant 和退出条件能直接或经一个很小的 exit assertion 推出后条件

如果这三件事里有一个答不上来，就不要继续写 Coq proof，先回到注释层重做 reasoning。

一个 invariant 只做到“看起来每轮都能保持”是不够的；还必须保证最终能证出后条件。

更稳的标准是：

- invariant 保留的内容，正好覆盖后条件需要的核心语义
- 退出时只需要很少的算术整理或一个最小的 loop-exit assertion

如果退出时还需要大量重建语义，通常说明 invariant 太弱；如果 invariant 里塞了很多和后条件无关的东西，通常说明 invariant 太脏。

## 2. invariant 要写在真实控制点上

`for` / `while` 的 invariant 写的是“进入循环判断点前”的状态。

因此优先写成：

- 已处理前缀
- 下一次待处理位置
- 当前累加器/状态量对应的闭式表达

不要把 invariant 写成“本轮循环体执行结束后应该成立什么”。

## 3. 先找状态量的闭式表达

循环题的关键通常是：

- 索引到底代表“已完成”还是“待处理”
- 累加器表示哪一段结果
- 当前数据结构被拆成了哪几段

闭式表达选对之后，很多 witness 会直接退化成纯算术。

## 4. invariant 只保留后续真正需要的信息

常见需要保留的内容：

- 边界关系
- 参数不变关系
- 已处理部分的语义
- 未处理部分的 shape

不需要的内容不要提前塞进去，否则 witness 会变脏。

## 5. 指针/区间推进问题优先用 “context + focus”

对这类程序：

- 链表遍历
- 树下降
- 双指针
- 分段处理

优先考虑 invariant 由两部分组成：

- 已处理上下文
- 当前焦点

两者拼回整体语义。

## 6. 退出时要能直接通向后条件

设计 invariant 时，先问自己：

- 循环退出条件和 invariant 拼起来，能不能直接推出后条件
- 还缺不缺一个显式 loop-exit assertion

如果退出后还需要大量额外重建语义，说明 invariant 往往还不够贴题。

## 7. nested loop 必须分别有自己的 invariant

典型错误现象：

- `Error: Lack of assertions in some paths for the loop!`

常见原因：

- 只给外层循环写了 invariant
- 内层循环依赖外层语义，但自己没有局部状态描述

处理方法：

- 外层循环描述跨轮保持的全局语义
- 内层循环描述当前扫描区间/当前位置/局部单调性或局部最大值之类的中间性质
- 不要指望外层 invariant 自动覆盖内层所有路径

## 8. invariant 缺“参数不变关系”会直接污染 witness

典型现象：

- `return_wit` 左右两侧只差 `a` 和 `a@pre`
- witness 里反复重建某个形参未改变

处理方法：

- 在 invariant 中显式加入需要保持不变的参数关系
- 修改后立刻重新 `symexec`

这类问题属于 invariant 缺信息，不要拖到 `proof_manual.v` 再补救。

## 9. 对数组/DP 题，invariant 先分“已定义前缀”和“未定义后缀”

如果循环逐步写数组，优先把内存分成两段：

- 已经写好的前缀：`*_seg` 或对应完整语义
- 尚未写入的后缀：`undef_seg`

处理方法：

- 先让 shape 上闭合
- 再在已写前缀上叠加值语义

不要一开始就试图把整段数组都写成完整值语义；这很容易在初始化早期就卡住 invariant 校验。
