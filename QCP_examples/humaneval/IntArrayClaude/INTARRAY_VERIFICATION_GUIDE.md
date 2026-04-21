# IntArrayClaude 数组程序验证指南

这份文档总结的是我在阅读 `QCP_examples` 中原生数组例子后得到的知识，目标是为后续验证 `QCP_examples/humaneval/IntArrayClaude` 下的题目提供一份可直接参考的“数组验证工作手册”。

本文刻意不以 `humaneval` 目录里的已有答案为主，而是主要基于下面这些原生材料整理：

- `QCP_examples/array_auto.c`
- `QCP_examples/int_array_merge_rel.c`
- `QCP_examples/sum.c`
- `QCP_examples/kmp_rel.c`
- `QCP_examples/int_array_def.h`
- `QCP_examples/int_array.strategies`
- `QCP_examples/array_shape.strategies`
- `SeparationLogic/SeparationLogic/ArrayLib.v`
- `SeparationLogic/examples/int_array_strategy_proof.v`
- `SeparationLogic/examples/array_shape_strategy_proof.v`
- `tutorial/T1-representation-predicates.md`
- `tutorial/T4-symbolic-execution.md`
- `tutorial/T5-prove-vc.md`
- `tutorial/T8-function-call.md`

最后一节会把这些知识落到 `QCP_examples/humaneval/IntArrayClaude/C_3.c` 上，说明遇到真实题目时应该如何思考。

## 1. 数组题和纯整数题的本质区别

`IntClaude` 里的题主要难在：

- 规格语义
- 循环不变式
- 算术证明

而 `IntArrayClaude` 里的题除了这些，还多了一层“内存所有权”：

- 数组不是一个纯数学对象，而是一段连续内存
- 读数组元素时，要把整段数组“拆开”成“当前位置单元 + 剩余数组”
- 写数组元素时，要把修改后的单元再“拼回去”
- 如果程序只读数组，那么循环不变式里往往要保留整个 `IntArray::full(...)`
- 如果程序写数组，那么循环不变式里经常要改成“前缀已初始化/已更新，后缀未定义或未处理”

所以数组题通常同时有两条线：

1. 纯逻辑线：当前下标 `i` 已处理到哪里，累计值/状态对应什么数学语义
2. 内存线：当前内存仍然拥有哪一段数组，数组元素是否已初始化，哪些位置已经被改写

数组题是否好验证，很大程度上取决于这两条线能否在 invariant 中同时表达清楚。

## 2. 数组表示谓词：到底在描述什么

数组相关谓词在 `SeparationLogic/SeparationLogic/ArrayLib.v` 和 `QCP_examples/int_array_def.h` 中。

### 2.1 `IntArray::full`

```c
IntArray::full(p, n, l)
```

表示：

- 指针 `p` 指向一段长度为 `n` 的整型数组
- 这段数组的数学内容是列表 `l`

这不是“只知道有一段数组”，而是“知道数组里每个元素的值是什么”。

它是数组题里最常见的只读谓词。

典型用途：

- 输入数组在整个函数过程中不被修改
- 后置条件要求数组保持不变
- invariant 里要一直保留完整数组语义

例子：

- `QCP_examples/sum.c`
- `QCP_examples/humaneval/IntArrayClaude/C_3.c`

### 2.2 `IntArray::seg`

```c
IntArray::seg(p, lo, hi, l)
```

表示：

- 数组从逻辑下标区间 `[lo, hi)` 的那一段
- 内容是列表 `l`

它适合处理：

- 两个有界子区间
- merge / mergesort 这类“只拥有数组中间一段”的程序
- 指针偏移后的后缀数组

典型用途：

- `QCP_examples/int_array_merge_rel.c`

那里会看到类似：

```c
IntArray::seg(arr, p, q + 1, s1) *
IntArray::seg(arr, q + 1, r + 1, s2)
```

含义就是把数组切成左右两半分别拥有。

### 2.3 `IntArray::missing_i`

```c
IntArray::missing_i(p, i, lo, hi, l)
```

这是数组验证中最关键的桥接谓词之一。

它表示：

- 逻辑上仍然是 `[lo, hi)` 这一段数组，内容对应 `l`
- 但第 `i` 个位置被“挖掉”了
- 也就是说，除了 `i` 这一格外，剩余所有格子的所有权都还在这个谓词里

它的作用是把“数组整体”和“当前访问单元”分离开。

读数组时的典型分解模式是：

```text
IntArray::full(p, n, l)
==>
data_at(p + i * sizeof(int), int, l[i]) *
IntArray::missing_i(p, i, 0, n, l)
```

写数组后再合并回去：

```text
IntArray::missing_i(p, i, 0, n, l) *
data_at(p + i * sizeof(int), int, v)
==>
IntArray::full(p, n, replace_Znth(i, v, l))
```

这个思想在 `QCP_examples/int_array.strategies` 和
`SeparationLogic/examples/int_array_strategy_proof.v` 里是显式编码的。

### 2.4 `IntArray::full_shape` / `seg_shape`

```c
IntArray::full_shape(p, n)
IntArray::seg_shape(p, lo, hi)
```

它们表示：

- 只知道这段数组已经初始化、有正确类型
- 但不知道数组中具体存的值

所以它们适合：

- 自动化内存安全证明
- 复制、填充、拼接这类“只关心写得进去，不关心精确内容”的程序

例子：

- `QCP_examples/array_auto.c`

例如 `array_copy1` 的 invariant：

```c
IntArray::seg_shape(dest@pre, 0, i) *
IntArray::undef_seg(dest@pre, i, n@pre)
```

它只表达：

- 前缀 `[0, i)` 已经写过，因而“有 shape”
- 后缀 `[i, n)` 还未初始化

它没有记录前缀拷贝后的精确值，所以证明更自动，但规格也更弱。

### 2.5 `IntArray::undef_full` / `undef_seg`

```c
IntArray::undef_full(p, n)
IntArray::undef_seg(p, lo, hi)
```

表示：

- 这段内存已经分配好
- 但内容未初始化，不允许直接读取

它适合描述：

- 新分配的数组
- 输出缓冲区
- 正在逐步写入但还没填满的后缀

典型例子：

- `array_copy1`
- `memset`
- `array_concat`

## 3. `ArrayLib.v` 里真正需要记住的引理族

`ArrayLib.v` 很长，但对后续数组题，最值得记住的是这些引理名字和它们的含义。

### 3.1 长度/合法性引理

- `IntArray.full_length`
- `IntArray.full_Zlength`
- `IntArray.seg_length`
- `IntArray.seg_shape_valid`

用途：

- 从数组断言推出 `Zlength l = n`
- 从 `seg/seg_shape` 推出区间满足 `lo <= hi`
- 为 `Znth`、`sublist`、`replace_Znth` 的边界证明提供前提

### 3.2 读取时拆开数组

- `IntArray.full_split_to_missing_i`
- `IntArray.seg_split_to_missing_i`
- `IntArray.full_shape_split_to_missing_i_shape`

用途：

- 当代码读 `a[i]` 或写 `a[i]` 时，把整体数组拆成：
  - 当前单元的 `data_at`
  - 剩余数组的 `missing_i` / `missing_i_shape`

这是“数组访问能被 symbolic execution 接住”的核心。

### 3.3 写回时把单元拼回数组

- `IntArray.missing_i_merge_to_full`
- `IntArray.missing_i_merge_to_seg`
- `IntArray.missing_i_shape_merge_to_full_shape`

用途：

- 执行 `a[i] = v` 后，把更新后的单元重新合并
- 如果值改了，得到的列表通常是 `replace_Znth(...)`

### 3.4 区间拆分/拼接

- `IntArray.seg_split_to_seg`
- `IntArray.seg_merge_to_seg`
- `IntArray.seg_shape_split_to_seg_shape`
- `IntArray.seg_shape_merge_to_seg_shape`
- `IntArray.seg_to_seg_shape`
- `IntArray.seg_shape_to_full_shape`

用途：

- 把一个区间拆成左右两段，或把两段再拼起来
- mergesort、KMP、后缀数组、双数组 merge 时经常用到

## 4. strategy 自动做了什么

数组验证里，很多“拆开/拼回”的动作不是你手写证明完成的，而是 strategy 自动做的。

核心文件：

- `QCP_examples/int_array.strategies`
- `QCP_examples/array_shape.strategies`
- `SeparationLogic/examples/int_array_strategy_proof.v`
- `SeparationLogic/examples/array_shape_strategy_proof.v`

### 4.1 对 `IntArray::full` 的自动化

`int_array.strategies` 里最关键的规则是：

- 从 `IntArray::full(p, n, l)` 自动取出第 `i` 个元素
- 生成 `IntArray::missing_i(p, i, 0, n, l)` 和当前位置 `data_at`
- 访问结束后再自动合并回 `IntArray::full`

也就是说，只要循环里访问的是 `a[i]` 这种规范形式，并且你已经在 invariant 中保留了 `IntArray::full(a, n, l)`，系统通常会自动把内存读写部分处理掉。

这也是为什么很多数组题的 `manual.v` 真正难点往往不是分离逻辑内存，而是：

- `sum/sublist/Znth` 的算术关系
- 分支语义
- return 规格的存在性/全称性

### 4.2 对 `*_shape` 的自动化

`array_shape.strategies` 支持另一类自动化：

- 从 `full_shape` 中取出某个单元
- 访问后再合并回 `full_shape`
- 把 `seg_shape` 拆成更小的前缀/后缀

这非常适合：

- 复制
- 初始化
- 只证明内存安全，不证明精确数组内容

### 4.3 一个重要判断标准

如果你的程序目标是“证明输出数组内容等于某个数学列表”，通常仅靠 `full_shape` 不够，必须改用：

- `IntArray::full`
- `IntArray::seg`
- `IntArray::missing_i`

如果你的目标只是“证明已经初始化完毕/不会越界/不会读未初始化内存”，`*_shape` 谓词通常更省力。

## 5. 从原生例子提炼出的几类数组题模板

## 5.1 只读扫描类

代表：

- `QCP_examples/sum.c`
- `QCP_examples/humaneval/IntArrayClaude/C_3.c`

特征：

- 输入数组不修改
- 每次循环只读 `a[i]`
- 目标通常是累计和、布尔判断、前缀性质、最大值等

推荐 invariant 模板：

```c
/*@ Inv
    0 <= i && i <= n@pre &&
    state == prefix_semantics(sublist(0, i, l)) &&
    extra_prefix_property(i, l) &&
    IntArray::full(a, n@pre, l)
*/
```

其中：

- `state` 是当前累计值/布尔值/候选答案
- `prefix_semantics(...)` 是已经处理前缀的数学语义
- `extra_prefix_property` 是为了返回证明保留的辅助性质

核心经验：

- 这类题一定要把 `IntArray::full(...)` 留在 invariant 里，因为数组没有被改写
- `manual.v` 里真正要证明的是“前缀语义如何从 `i` 推进到 `i+1`”

### 5.2 逐步写入输出数组

代表：

- `array_copy1`
- `array_concat`
- `memset`

特征：

- 目标数组起初是 `undef_*`
- 每次循环写一个位置
- 循环不需要知道精确前缀内容，或者只需知道前缀已初始化

推荐 invariant 模板：

```c
/*@ Inv
    0 <= i && i <= n@pre &&
    IntArray::seg_shape(dest@pre, 0, i) *
    IntArray::undef_seg(dest@pre, i, n@pre)
*/
```

如果要精确刻画内容，则升级为：

```c
IntArray::full(dest, n, app(done_prefix, remaining_suffix))
```

或

```c
IntArray::seg(dest, 0, i, done_prefix) *
IntArray::undef_seg(dest, i, n)
```

### 5.3 原地修改数组

代表：

- `arr_sum_update` in `QCP_examples/sum.c`

特征：

- 程序既读又写同一个数组
- invariant 里必须刻画“前缀已经改写，后缀仍是原值”

原生例子给出的经典写法是：

```c
IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))
```

这很值得直接复用。

含义：

- `[0, i)` 已经被改成 `0`
- `[i, n)` 仍然保持原始列表 `l` 的后缀

这类 invariant 非常通用。以后如果遇到：

- 前缀归零
- 前缀已处理、后缀未处理
- 前缀变换、后缀保持原状

都可以照这个结构改。

### 5.4 子区间 / 双数组 / merge 类

代表：

- `int_array_merge_rel.c`
- `kmp_rel.c`

特征：

- 不一定拥有整个数组
- 经常只拥有 `[p, q)` 或后缀 `(a + i * sizeof(int), n-i)` 这种切片
- 需要同时跟踪多个数组或多个区间

推荐做法：

- 用 `IntArray::seg`
- 明确区间边界
- 在 invariant 中显式写出每一段的所有权分布

例如 merge 的不变式思路是：

- `arr` 左半段已消耗前缀
- `arr` 右半段已消耗前缀
- `ret` 已写前缀
- 各自剩余后缀继续保留

这类题本质上是在做“数组资源分账”。

## 6. 数组题里 invariant 应该怎么写

数组题 invariant 通常至少要回答 4 个问题：

1. 现在处理到哪个下标
2. 当前程序变量的数学含义是什么
3. 数组内存现在归谁拥有
4. 写过的部分和没写过的部分分别代表什么

可以把 invariant 拆成三层来写。

### 6.1 范围层

```c
0 <= i && i <= n@pre
```

这是数组题最基础的一层，因为：

- 访问 `a[i]` 需要 `0 <= i < n`
- `Znth` / `sublist` / `replace_Znth` 证明都离不开边界

### 6.2 语义层

描述程序状态与前缀数学语义的关系。

只读扫描常见写法：

```c
acc == sum(sublist(0, i, l))
```

布尔标志常见写法：

```c
flag == 0  <->  已处理前缀满足性质
flag != 0  ->   已找到一个见证
```

### 6.3 内存层

根据程序是否修改数组来决定：

- 只读：保留 `IntArray::full(a, n, l)`
- 写输出：前缀 `seg_shape` + 后缀 `undef_seg`
- 原地更新：`IntArray::full(a, n, transformed_list)`
- 切片：若干个 `IntArray::seg(...)` 用 `*` 连接

## 7. `manual.v` 里最常见的证明内容

数组题里 `manual.v` 一般不是每一步都要自己证明内存分离逻辑。很多内存动作 strategy 已经做了。

真正常见的是下面几类证明。

### 7.1 初始 entailment

把前置条件推出循环 invariant 在 `i = 0` 时成立。

读数组类程序通常很简单：

- `sum(sublist(0, 0, l)) = 0`
- `forall k, 0 <= k < 0 -> ...` 是 vacuous
- `IntArray::full(...)` 原样保留

### 7.2 一步推进 entailment

这是数组题最常见的手工证明点。

通常形状类似：

```text
旧前缀语义 + 当前位置元素
== 新前缀语义
```

例如：

```text
sum(sublist(0, i, l)) + Znth i l 0
= sum(sublist(0, i + 1, l))
```

这类证明通常需要：

- `0 <= i < Zlength l`
- `Zlength l = n`
- `sublist` 和 `Znth` 的基础引理

### 7.3 return 证明

常见有两种。

一种是“最终累计值等于整个数组语义”：

```text
i = n
acc = prefix_semantics(i)
==>
acc = whole_array_semantics
```

另一种是像 `C_3` 这种布尔结果：

- `return 1` 时给出一个见证下标 `k`
- `return 0` 时给出一个对所有下标都成立的全称性质

### 7.4 safety 证明

数组题除了内存安全，还有 C 整数安全：

- 下标算术不溢出
- `a + i * sizeof(int)` 的偏移合法
- `num + a[i]` 不溢出

这类 safety VC 很容易被忽略，但经常是第一阻塞点。

## 8. C 函数调用和数组 frame

如果数组题里会调用别的函数，`tutorial/T8-function-call.md` 和 `int_array_merge_rel.c` 给了两条重要经验。

### 8.1 调函数时，数组所有权会被拆成 pre_mem 和 frame

如果调用函数只需要数组的一部分，那么：

- 与被调函数 precondition 匹配的那部分数组资源会被拿走
- 其余资源会作为 frame 原样保留

这就是为什么区间算法更适合用 `seg`，而不是总是用 `full`。

### 8.2 `where` 子句很重要

如果工具无法自动实例化逻辑变量，可以手动写：

```c
f(...) /*@ where l = l0, X = X */;
```

在 `int_array_merge_rel.c`、`kmp_rel.c` 里这种写法很多。

后续如果 `IntArrayClaude` 里出现辅助函数调用，这一招大概率会用上。

## 9. 对 `C_3.c` 的具体分析

文件：

- `QCP_examples/humaneval/IntArrayClaude/C_3.c`

题意：

- 输入一个整数数组 `operations`
- 初始余额为 `0`
- 顺序处理每个操作值
- 只要某个前缀和变成负数，就返回 `1`
- 如果所有前缀和都非负，返回 `0`

这是一个非常典型的“只读数组 + 前缀扫描 + 布尔提前返回”题。

### 9.1 这题的内存部分其实不难

`C_3.c` 当前规格用的是：

```c
IntArray::full(operations, operations_size, l)
```

而程序体只读 `operations[i]`，不写数组。

所以最自然的 invariant 确实就是现在这种：

```c
num == sum(sublist(0, i, l)) &&
0 <= i && i <= operations_size@pre &&
(forall k, 0 <= k && k < i -> 0 <= sum(sublist(0, k + 1, l))) &&
IntArray::full(operations, operations_size@pre, l)
```

这个 invariant 的优点是：

- `num` 精确表示已经处理前缀的和
- 全称条件记录“到目前为止所有前缀都非负”
- 数组资源 `IntArray::full(...)` 原样保存，后续每次读 `operations[i]` 时都能自动拆开

也就是说，这题的数组内存建模方向是对的。

### 9.2 这题会生成什么类型的 VC

从 `QCP_examples/humaneval/IntArray/C_3_goal.v` 可以看出，这类题会生成：

- `safety_wit`
  - 包括访问 `operations[i]` 的边界安全
  - 包括 `num + Znth i l 0` 的整数范围安全
- `entail_wit_1`
  - 初始化时 invariant 成立
- `entail_wit_2`
  - 没有提前返回时，从 `i` 推进到 `i + 1`
- `return_wit_1`
  - 提前返回 `1` 时，需要给出某个负前缀和见证
- `return_wit_2`
  - 正常结束返回 `0` 时，需要证明所有前缀和都非负

这正是只读数组扫描题的标准 VC 结构。

### 9.3 这题真正的关键证明点

如果以后让模型验证 `C_3`，最需要准备的不是内存 lemma，而是前缀和的纯逻辑 lemma。

核心需要证明：

```text
sum(sublist(0, i, l)) + Znth i l 0
= sum(sublist(0, i + 1, l))
```

并且从

```text
forall k < i, prefix(k) >= 0
and
prefix(i) + l[i] >= 0
```

推出

```text
forall k < i + 1, prefix(k) >= 0
```

这类证明本质是对“新加入的最后一个前缀”单独处理：

- 若 `k < i`，直接用旧 invariant
- 若 `k = i`，用当前分支条件 `num + operations[i] >= 0`

### 9.4 这题潜在的真实难点：整数溢出

从 `C_3_goal.v` 还能看到一个很关键的事实：

系统会要求证明

```text
INT_MIN <= num + Znth i l 0 <= INT_MAX
```

而当前 `C_3.c` 的前置条件没有给出任何关于：

- 单个数组元素范围
- 任意前缀和范围

的限制。

这意味着：

- 从“数学语义”看，题意是合理的
- 但从“C int 语义”看，`num += operations[i]` 可能溢出

所以如果以后真的去验证 `C_3`，第一件事很可能不是补 `manual.v`，而是先判断当前规约是否足以证明 C 安全。

如果不够，常见修法有两种：

1. 加强前置条件
   - 给每个元素加界
   - 或直接约束所有前缀和都在 `INT_MIN .. INT_MAX`
2. 改程序实现
   - 改用更宽的类型
   - 或改成不会溢出的实现方式

这是数组题里非常重要的经验：内存模型对了，不代表 C 安全 automatically 就够了。

## 10. 后续验证 `IntArrayClaude` 时的推荐流程

### 第一步：先判断题目属于哪一类

- 只读扫描
- 输出数组写入
- 原地更新
- 双数组/切片/merge
- 函数调用/关系规格

### 第二步：先选对谓词

- 只读：`IntArray::full`
- 写输出但不关心精确内容：`*_shape` + `undef_*`
- 写输出且关心内容：`full/seg/missing_i`
- 切片：`seg`

### 第三步：先写 invariant 的三层

- 范围层
- 语义层
- 内存层

### 第四步：预判 VC 难点

- 会不会卡 `sublist/Znth/sum`
- 会不会卡 `replace_Znth`
- 会不会卡 `INT_MIN/INT_MAX`
- 会不会卡指针偏移和切片拼接

### 第五步：决定是否需要额外 lemma

以下情况通常需要补 Coq 引理：

- 前缀和递推
- 列表分段拼接
- 更新后数组语义
- 两个 segment 合并成一个 segment
- “前缀已处理、后缀未处理”的列表表达式化简

## 11. 最值得直接复用的几条经验

- 只读数组扫描题，invariant 里通常应保留完整的 `IntArray::full(...)`
- 写数组题，关键不在“有没有数组”，而在“前缀/后缀分别表示什么”
- `missing_i` 是读写单元和整体数组之间的桥
- `*_shape` 适合只做内存安全，不适合表达精确内容
- 数组题的手工证明常常主要是纯逻辑，而不是分离逻辑
- 真正容易漏的是 C 整数安全，而不是数组越界
- 如果程序只拥有数组的一部分，尽早改用 `seg`
- 如果有函数调用和复杂逻辑变量实例化，记得考虑 `where` 子句

## 12. 建议后续优先参考的文件

如果以后验证 `IntArrayClaude` 新题，建议优先按下面顺序查：

1. `QCP_examples/int_array_def.h`
   - 先确认有哪些谓词和 Coq 函数可用
2. `SeparationLogic/SeparationLogic/ArrayLib.v`
   - 查 split / merge / shape / length 相关 lemma
3. `QCP_examples/int_array.strategies`
4. `QCP_examples/array_shape.strategies`
   - 判断哪些内存步骤会自动完成
5. `QCP_examples/array_auto.c`
   - 看 shape 风格 invariant
6. `QCP_examples/sum.c`
   - 看只读扫描和原地更新的标准写法
7. `QCP_examples/int_array_merge_rel.c`
   - 看 segment 风格和复杂 invariant
8. `QCP_examples/kmp_rel.c`
   - 看指针偏移、后缀数组和函数调用

如果是像 `C_3` 这种简单只读扫描题，最先参考的应该是：

- `QCP_examples/sum.c`
- `QCP_examples/int_array.strategies`
- `SeparationLogic/SeparationLogic/ArrayLib.v`

这三者已经基本覆盖它最核心的验证模式。

## 13. C_5 实操排障清单（可直接复用）

这部分来自 `C_5` 的真实验证过程，优先覆盖“工具链可运行性”和“证明脚本稳定性”两类问题。

### 13.1 工具链与命令层

1. `coqc` 找不到

表现：终端报 `coqc: command not found`。

处理：先激活 opam switch，再执行编译链：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
```

2. `IntArrayClaude` 目录没有 `_CoqProject`

处理：复用 `../IntClaude/_CoqProject` 生成 `COQINCLUDES`。否则 load-path 不完整，容易出现 import 失败。

3. `symexec` 报头文件找不到（如 `verification_stdlib.h`）

处理：给 `symexec` 增加 include 参数：

```bash
-IQCP_examples/
```

否则 `QCP_examples` 下公共头文件不会被解析。

### 13.2 Coq 证明脚本层

4. `Local Open Scope Z_scope` 下 `Nat.div` 被误解析

表现：`nat/Z` 类型冲突，常见在偶数下标映射证明里。

处理：显式写 `(%nat)`，例如：

```coq
((2 * k) / 2)%nat
```

5. Coq 8.20.1 下“同名变量重复引入”

表现：如 `k is already used`。

处理：用“先 `intros`，后 `revert`，再 `induction`”的结构，避免分支里重复引入同名 binder。

6. `prop_apply ... Intros` 引入额外 `model` witness，干扰后续 `sep_apply`

表现：后续内存步骤报 `No matching clauses for match`。

处理：如果只需要纯事实，优先：

- `prop_apply ...`（不 `Intros`）
- 紧接 `entailer!` 做状态归一化
- 再执行 `sep_apply`

7. `pre_process` 生成假设名不稳定

表现：不同重生成后 `H5/H6/...` 会漂移，脚本里写死假设名容易失效。

处理：用 `match goal with` 按“公式形状”抓取需要的假设，而不是依赖固定名字。

8. return 阶段内存合并顺序不当导致证明卡住

在 `seg + undef_seg` 合并成 `full` 的场景，建议顺序：

1. 先用下标等式（如 `Hk`）对齐区间端点。
2. 再应用 `IntArray.seg_to_full`。
3. 把空后缀 `undef_seg x hi hi` 化成 `emp`（`IntArray.undef_seg_empty`）。
4. 最后 `entailer!` 收尾。

### 13.3 使用建议

- 做新题时，若出现“明明逻辑对但 tactic 卡住”，先按 4-8 条排查，不要立刻加大引理。
- 改了注解或 `coins_XX.v` 后，一定重跑 `symexec` 再编译链，不在陈旧 goal 上修证明。
