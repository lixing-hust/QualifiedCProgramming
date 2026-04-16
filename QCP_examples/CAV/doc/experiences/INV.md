# Invariant Experience

本文件只记录循环 invariant 的设计经验。

不记录：

- `Assert` / `which implies` 细节（见 `ASSERTION.md`）
- symbolic 执行流程（见 `SYMEXEC.md`）
- manual proof（见 `PROOF.md`）

## 1. invariant 要写在真实控制点上

`for` / `while` 的 invariant 写的是“进入循环判断点前”的状态。

因此优先写成：

- 已处理前缀
- 下一次待处理位置
- 当前累加器/状态量对应的闭式表达

不要把 invariant 写成“本轮循环体执行结束后应该成立什么”。

## 2. 先找状态量的闭式表达

循环题的关键通常是：

- 索引到底代表“已完成”还是“待处理”
- 累加器表示哪一段结果
- 当前数据结构被拆成了哪几段

闭式表达选对之后，很多 witness 会直接退化成纯算术。

## 3. invariant 只保留后续真正需要的信息

常见需要保留的内容：

- 边界关系
- 参数不变关系
- 已处理部分的语义
- 未处理部分的 shape

不需要的内容不要提前塞进去，否则 witness 会变脏。

## 4. 指针/区间推进问题优先用 “context + focus”

对这类程序：

- 链表遍历
- 树下降
- 双指针
- 分段处理

优先考虑 invariant 由两部分组成：

- 已处理上下文
- 当前焦点

两者拼回整体语义。

## 5. 退出时要能直接通向后条件

设计 invariant 时，先问自己：

- 循环退出条件和 invariant 拼起来，能不能直接推出后条件
- 还缺不缺一个显式 loop-exit assertion

如果退出后还需要大量额外重建语义，说明 invariant 往往还不够贴题。

## 6. nested loop 必须分别有自己的 invariant

典型错误现象：

- `Error: Lack of assertions in some paths for the loop!`

常见原因：

- 只给外层循环写了 invariant
- 内层循环依赖外层语义，但自己没有局部状态描述

处理方法：

- 外层循环描述跨轮保持的全局语义
- 内层循环描述当前扫描区间/当前位置/局部单调性或局部最大值之类的中间性质
- 不要指望外层 invariant 自动覆盖内层所有路径

## 7. invariant 缺“参数不变关系”会直接污染 witness

典型现象：

- `return_wit` 左右两侧只差 `a` 和 `a@pre`
- witness 里反复重建某个形参未改变

处理方法：

- 在 invariant 中显式加入需要保持不变的参数关系
- 修改后立刻重新 `symexec`

这类问题属于 invariant 缺信息，不要拖到 `proof_manual.v` 再补救。

## 8. 对数组/DP 题，invariant 先分“已定义前缀”和“未定义后缀”

如果循环逐步写数组，优先把内存分成两段：

- 已经写好的前缀：`*_seg` 或对应完整语义
- 尚未写入的后缀：`undef_seg`

处理方法：

- 先让 shape 上闭合
- 再在已写前缀上叠加值语义

不要一开始就试图把整段数组都写成完整值语义；这很容易在初始化早期就卡住 invariant 校验。
