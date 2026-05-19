# IntArrayClaude 循环不变式生成经验总结

更新时间：2026-05-14

本文基于 `QCP_examples/humaneval/IntArrayClaude` 中已经完成验证的程序，总结数组类 C 程序在 QCP 中生成循环不变式的经验。目标不是给每一道题单独写模板，而是把循环按程序角色分类，让大模型在新题上能先判断题型，再选择相应结构的不变式。

核心原则：

1. 不变式应描述“程序当前执行到哪里”，不要直接把最终规格硬塞进循环。
2. 每个循环不变式都应同时包含三层信息：控制事实、纯语义状态、内存资源。
3. 复杂循环优先在 `coins_XX.v` 中定义一个贴近 C 控制流的状态谓词，再在 annotation 中引用它。
4. 对数组程序，内存资源和纯语义同等重要；只写 `prefix`/`forall` 而忘记 `IntArray::full/seg/undef_seg` 通常无法通过符号执行。
5. C 整数安全必须显式考虑，尤其是累加、乘法、下标加一、`i * sizeof(int)`、`%`/`/`、`abs` 和排序交换。

## 1. 通用不变式骨架

大多数成功的不变式都遵循以下形状：

```c
/*@ Inv Assert
    exists ghost_l,

    // 1. 控制/稳定事实
    input == input@pre &&
    size == size@pre &&
    0 <= i && i <= size@pre &&
    size@pre == Zlength(input_l) &&

    // 2. 纯语义状态
    loop_state(i, input_l, acc_or_output_l, ghost_l, ...) &&
    range_condition(input_l, ...) &&

    // 3. 内存资源
    IntArray::full(input@pre, size@pre, input_l) *
    ...
*/
```

对大模型可以要求：

- 先判断循环修改哪些变量、读写哪些数组。
- 再为每个被循环推进的变量找一个“前缀语义”或“当前状态谓词”。
- 最后补齐内存资源和整数范围。

常见必须保留的事实：

```c
input == input@pre
size == size@pre
size == Zlength(input_l)
0 <= i && i <= size
IntArray::full(input, size, input_l)
```

如果数组没有被修改，就保留 `IntArray::full`。如果输出数组逐步写入，就使用：

```c
IntArray::seg(out, 0, output_size, output_l) *
IntArray::undef_seg(out, output_size, capacity)
```

## 2. 只读前缀折叠类

### 适用程序

循环只读输入数组，并维护一个或多个累计变量。

典型任务：

- 求和、乘积、计数。
- 最大值、最小值。
- 按下标条件累加。
- 统计相邻下降数。
- 扫描时维护当前最好答案。

代表题：

- `C_8`：sum/product。
- `C_85`：奇数下标求和。
- `C_109`：统计环形下降数。
- `C_121`：偶数下标正奇数求和。
- `C_122`：前 k 个元素中二位数范围求和。
- `C_135`：扫描最大满足条件的下标。
- `C_142`：按下标平方/立方/原值累加。

### 不变式结构

```c
/*@ Inv Assert
    a == a@pre &&
    n == n@pre &&
    0 <= i && i <= n@pre &&
    n@pre == Zlength(input_l) &&
    acc == prefix_fold(i, input_l) &&
    int_range_condition(input_l, n@pre) &&
    IntArray::full(a@pre, n@pre, input_l)
*/
```

如果有多个累计变量：

```c
sum == prefix_sum(input_l, i) &&
product == prefix_product(input_l, i)
```

如果累计变量是“当前最好答案”：

```c
can_arrange_prefix(i, input_l, max)
```

如果统计相邻关系：

```c
count == count_descents_prefix(i, input_l)
```

### 生成建议

让大模型在 `coins_XX.v` 中定义：

```coq
prefix_fold : Z -> list Z -> Z
```

或：

```coq
loop_prefix_state : Z -> list Z -> Z -> Prop
```

并补两个核心引理：

```coq
prefix_fold_0
prefix_fold_step
```

其中 step 引理应精确对应 C 循环体的一次更新。

### 注意点

- 不要只写 `problem_spec(input_l, acc)`，因为循环中 `acc` 只对应前缀，不对应完整输入。
- 需要给 C 运算安全单独准备范围条件，例如 `prefix_sum_int_range`、`prefix_product_int_range`。
- 若循环体中有 `i + 1`、`sum + a[i]`、`product * a[i]`，前置条件或 invariant 必须足够证明这些表达式在 `int` 范围内。

## 3. 早返回搜索 / 全称否定类

### 适用程序

循环扫描过程中一旦发现 witness 就提前返回；如果循环正常结束，则证明不存在 witness。

典型任务：

- 是否存在两个/三个元素满足条件。
- 是否有坏相邻关系。
- 是否违反排序、回文、无三连重复等性质。
- contains/member 查询。

代表题：

- `C_3`：前缀和一旦为负提前返回。
- `C_40`：三元组求和为 0。
- `C_43`：二元组求和。
- `C_72`：回文检查和总和约束。
- `C_73`：统计镜像不等对数。
- `C_126`：非降序且无连续三重复。
- `C_26` 中的 `contains` helper。

### 单层循环结构

```c
/*@ Inv Assert
    a == a@pre &&
    n == n@pre &&
    0 <= i && i <= n@pre &&
    scanned_prefix(input_l, i) &&
    IntArray::full(a@pre, n@pre, input_l)
*/
```

`scanned_prefix(input_l, i)` 表示前 `i` 个位置都没有触发提前返回条件。

例如 contains：

```c
(forall (k: Z), 0 <= k && k < i => Znth(k, l, 0) != x)
```

例如排序/无三连重复：

```c
sorted_no_triple_prefix(i, lv)
```

### 嵌套循环结构

对二重或三重循环，不要试图用一个全局谓词一次性概括所有情况。应按循环层级定义状态谓词：

```c
scanned_i(input_l, n, i)
scanned_j(input_l, n, i, j)
scanned_k(input_l, n, i, j, k)
```

外层 invariant：

```c
0 <= i && i <= n &&
scanned_i(input_l, n, i) &&
IntArray::full(a, n, input_l)
```

中层 invariant：

```c
0 <= i && i < n &&
i + 1 <= j && j <= n &&
scanned_j(input_l, n, i, j) &&
IntArray::full(a, n, input_l)
```

内层 invariant：

```c
0 <= i && i < j &&
j < n &&
j + 1 <= k && k <= n &&
scanned_k(input_l, n, i, j, k) &&
IntArray::full(a, n, input_l)
```

### 生成建议

对大模型说：

- `scanned_i` 表示所有外层下标小于 `i` 的组合已经检查且未命中。
- `scanned_j` 表示固定 `i` 时，所有第二下标小于 `j` 的组合已经检查且未命中。
- `scanned_k` 表示固定 `i,j` 时，所有第三下标小于 `k` 的组合已经检查且未命中。
- 命中分支证明存在 witness。
- 循环正常结束时用 `scanned_i(input_l, n, n)` 桥接到 false 规格。

### 注意点

- 提前返回 true 的分支需要能构造 witness。
- 正常返回 false 的分支需要能由 scanned 状态推出 forall/不存在。
- 加法判断如 `a[i] + a[j] + a[k] == 0` 仍需 `triple_sum_int_range` 一类条件保证 C 加法安全。

## 4. 输出数组逐步构造类

### 适用程序

循环向 malloc 出来的数组或输出 buffer 逐步写入内容。

典型任务：

- 生成固定公式数组。
- copy/map。
- filter。
- 根据输入逐元素构造输出。
- 输出长度可能小于容量。

代表题：

- `C_100`：make pile。
- `C_106`：三角数/阶乘序列。
- `C_130`：Tribonacci 序列数组。
- `C_152`：逐元素绝对差。
- `C_159`：固定二元素输出。
- `C_163`：筛选生成偶数。

### 每轮必写一个元素

如果每轮都写 `data[i]`，且输出长度等于循环下标：

```c
/*@ Inv Assert
    0 <= i && i <= n &&
    Zlength(target_l) == n &&
    IntArray::seg(data, 0, i, sublist(0, i, target_l)) *
    IntArray::undef_seg(data, i, n)
*/
```

例如 `make_a_pile`：

```c
IntArray::seg(data, 0, i, sublist(0, i, make_pile(n0))) *
IntArray::undef_seg(data, i, n0)
```

### filter / 条件写入

如果只有满足条件时才写入，维护单独的 `output_size` 和 `output_l`：

```c
/*@ Inv Assert
    exists output_l,
    lower <= i && i <= upper + 1 &&
    0 <= output_size && output_size <= i - lower &&
    output_size == Zlength(output_l) &&
    filter_prefix(lower, i, upper, output_l) &&
    IntArray::seg(data, 0, output_size, output_l) *
    IntArray::undef_seg(data, output_size, capacity)
*/
```

### 生成建议

在 `coins_XX.v` 中定义：

```coq
output_prefix : Z -> list Z -> list Z -> Prop
```

或对数值区间：

```coq
generate_prefix : Z -> Z -> Z -> list Z -> Prop
```

需要证明：

- 初始空前缀成立。
- 不写入分支保持前缀关系。
- 写入分支把 `output_l` 扩展一个元素。
- 循环结束时前缀关系桥接到最终 `problem_spec`。

### 注意点

- 写入数组时，资源必须从 `undef_seg` 转移到 `seg`。
- `output_size++` 需要证明不会超过容量，也不会溢出。
- filter 类不要写 `output_size == i`，通常只能写 `output_size <= i`。

## 5. 多轮辅助数组 / 去重收集类

### 适用程序

程序先扫描输入构造辅助数组，再第二轮或第三轮扫描构造最终输出。

典型任务：

- 去重。
- 统计重复集合。
- 构造中间 score 数组。
- 先 copy 再排序。

代表题：

- `C_26`：两轮循环，先收集出现一次/多次集合，再输出非重复元素。
- `C_116`：copy、score、sort 三阶段。
- `C_145`：copy score、按 score 排序。

### 不变式结构

第一轮：

```c
/*@ Inv Assert
    exists aux1_l aux2_l,
    0 <= i && i <= n &&
    0 <= aux1_size && aux1_size <= i &&
    0 <= aux2_size && aux2_size <= i &&
    aux1_size == Zlength(aux1_l) &&
    aux2_size == Zlength(aux2_l) &&
    first_loop_state(input_l, i, aux1_l, aux2_l) &&
    IntArray::full(input, n, input_l) *
    IntArray::seg(aux1, 0, aux1_size, aux1_l) *
    IntArray::undef_seg(aux1, aux1_size, n) *
    IntArray::seg(aux2, 0, aux2_size, aux2_l) *
    IntArray::undef_seg(aux2, aux2_size, n)
*/
```

第二轮：

```c
/*@ Inv Assert
    exists aux1_l aux2_l output_l,
    0 <= i && i <= n &&
    0 <= output_size && output_size <= i &&
    output_size == Zlength(output_l) &&
    first_loop_state(input_l, n, aux1_l, aux2_l) &&
    second_loop_state(input_l, aux2_l, i, output_l) &&
    IntArray::seg(output, 0, output_size, output_l) *
    IntArray::undef_seg(output, output_size, n) *
    ...
*/
```

### 生成建议

让大模型不要把所有阶段揉成一个状态。每个阶段定义自己的状态谓词：

```coq
first_loop_state
second_loop_state
copy_prefix
score_prefix
sort_outer_state
sort_inner_state
```

阶段之间通过桥接引理连接。

### 注意点

- 辅助数组如果只初始化了前缀，就必须用 `seg + undef_seg`，不能写 `full`。
- 调用 helper 函数时，helper 的 precondition 通常需要 `IntArray::seg(a, 0, size, l)`，调用后应恢复同样的 seg。
- 每个阶段结束时可以把完整前缀转成 `IntArray::full`，便于后续阶段使用。

## 6. 滚动递推变量类

### 适用程序

循环不主要操作数组，而是用几个标量变量维护数学递推序列。

典型任务：

- Fibonacci。
- Tribonacci。
- FibFib。
- Kadane 最大子段和。
- 其它序列递推。

代表题：

- `C_46`：4 个滚动变量。
- `C_55`：Fibonacci。
- `C_63`：FibFib。
- `C_114`：Kadane 递推。

### 不变式结构

```c
/*@ Inv Assert
    n == n@pre &&
    lower <= i && i <= upper &&
    a == seq(i - 2) &&
    b == seq(i - 1) &&
    step_int_range(n@pre) &&
    undef_data_at(&c)
*/
```

三变量递推：

```c
x == seq(i - 3) &&
y == seq(i - 2) &&
z == seq(i - 1)
```

Kadane 类：

```c
best_here == local_state(i, input_l) &&
best_total == global_state(i, input_l)
```

### 生成建议

先确定循环开始时 `i` 的含义。比如：

```c
for (i = 2; i <= n; i++)
```

在循环头，`a == fib_seq(i - 2)`，`b == fib_seq(i - 1)`；执行一次循环后推进到 `i + 1`。

### 注意点

- 最容易错的是下标偏移。
- 临时变量如 `c` 如果只在循环体中赋值，循环头可写 `undef_data_at(&c)`。
- 必须给每一步加法准备 `fib_step_int_range` 或类似范围条件。

## 7. 数字拆解 / 除法循环类

### 适用程序

循环通过 `%`、`/`、`abs` 拆解整数的十进制或二进制表示。

典型任务：

- 统计奇偶 digit。
- digit sum。
- 最高位/最低位判断。
- bit count。

代表题：

- `C_94`：最大素数的各位和。
- `C_116`：二进制 1 的个数。
- `C_145`：signed digit score。
- `C_146`：最高位和末位判断。
- `C_155`：even/odd digit count。

### 不变式结构

十进制 digit count：

```c
/*@ Inv Assert
    num == num@pre &&
    0 <= w && w <= INT_MAX &&
    0 <= even && even < INT_MAX &&
    0 <= odd && odd < INT_MAX &&
    digit_count_state(num@pre, w, even, odd) &&
    data_at(&d, d)
*/
```

bit count：

```c
/*@ Inv Assert
    0 <= n && n < INT_MAX &&
    0 <= b && b <= 31 &&
    bit_count_state_at(i, input_l, n, b) &&
    ...
*/
```

最高位循环：

```c
/*@ Inv Assert
    0 <= t && t < bound &&
    first_digit_state(original_abs, t) &&
    ...
*/
```

### 生成建议

状态谓词要表达：

- `w` 是尚未处理的剩余数字。
- `even/odd/sum/b` 是已经处理部分的累计结果。
- 循环体执行 `% base` 和 `/ base` 后，状态推进一步。

### 注意点

- C 的 `%` 和 `/` 在 VC 中常出现为 `Z.rem` 和 `Z.quot`。
- 如果已经证明被除数非负，可以用引理桥接到 `Z.mod` 和 `Z.div`。
- `abs(INT_MIN)` 不安全，precondition 通常需要 `INT_MIN < x`。
- 对输入 `0` 要单独建模，很多 digit 规格需要明确 `0` 表示为 `[0]` 还是空列表。

## 8. 排序 / 冒泡交换状态类

### 适用程序

程序保留排序算法本体，尤其是冒泡排序或相邻交换，而不是把排序替换成外部可信函数。

代表题：

- `C_116`：按 bit count 和数值排序。
- `C_145`：按 digit score 排序。

### 不变式结构

外层循环：

```c
/*@ Inv Assert
    exists output_l score_l,
    0 <= i && i <= n &&
    n == Zlength(output_l) &&
    n == Zlength(score_l) &&
    sort_outer_state(i, input_l, output_l, score_l) &&
    IntArray::full(data, n, output_l) *
    IntArray::full(score, n, score_l)
*/
```

内层循环：

```c
/*@ Inv Assert
    exists output_l score_l,
    0 <= i && i < n &&
    1 <= j && j <= n &&
    n == Zlength(output_l) &&
    n == Zlength(score_l) &&
    sort_inner_state(i, j, input_l, output_l, score_l) &&
    IntArray::full(data, n, output_l) *
    IntArray::full(score, n, score_l)
*/
```

### 生成建议

不要在 C annotation 中直接写复杂的：

```coq
Permutation input_l output_l /\ Sorted output_l
```

更稳的方式是：

```coq
sort_outer_state
sort_inner_state
```

这两个谓词精确模拟 C 的冒泡 pass。最终再证明：

```coq
sort_outer_state(n, input_l, output_l, score_l) ->
problem_spec(input_l, output_l)
```

### 注意点

- 交换两个数组时，`data` 和 `score` 必须同步更新。
- proof 中通常会遇到 `replace_Znth`、`Znth`、`Zlength`、相邻 swap 的列表引理。
- annotation 层保持整数组 `IntArray::full(data, n, output_l)` 比拆成多个 seg 更自然。

## 9. 外部可信排序函数类

### 适用程序

题目核心不是排序本身，排序只是辅助步骤。此时可以把 `qsort` 或排序过程建模为外部可信函数。

代表题：

- `C_33`：排序。
- `C_34`：sorted unique。
- `C_58`：sorted unique common。
- `C_70`：strange sort。
- `C_88`：根据奇偶决定升序/降序。
- `C_90`：next smallest。
- `C_123`：Collatz 奇数项收集后排序。

### 外部函数规格结构

```c
void sort_int_array(int *array, int init_size, int size, int ascending)
/*@ With l
    Require
        array != 0 &&
        init_size == Zlength(l) &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure
        exists sorted_l full_l,
        init_size == Zlength(sorted_l) &&
        size == Zlength(full_l) &&
        sublist(0, init_size, full_l) == sorted_l &&
        sorted_int_list_by(ascending, sorted_l) &&
        Permutation(l, sorted_l) &&
        IntArray::full(array, size, full_l)
*/;
```

### 生成建议

当排序不是题目要验证的核心算法时，让大模型优先选择外部排序规格，避免把复杂排序 proof 引入主任务。

排序前循环仍按“输出数组构造类”写：

```c
IntArray::seg(data, 0, output_size, output_l) *
IntArray::undef_seg(data, output_size, capacity)
```

排序后用：

```c
sorted_int_list_by(...)
Permutation(output_l, sorted_l)
```

桥接到最终规格。

## 10. 原地改写类

### 适用程序

循环直接修改输入数组或一个完整数组，而不是只写新输出前缀。

典型任务：

- 原地 reverse。
- swap。
- 原地排序。
- 前缀已处理，后缀保持原值。

### 不变式结构

整数组状态：

```c
/*@ Inv Assert
    exists current_l,
    0 <= i && i <= n &&
    current_l == app(processed_prefix, sublist(i, n, old_l)) &&
    IntArray::full(a, n, current_l)
*/
```

双数组交换：

```c
IntArray::full(a, n, app(sublist(0, i, old_b), sublist(i, n, old_a))) *
IntArray::full(b, n, app(sublist(0, i, old_a), sublist(i, n, old_b)))
```

### 生成建议

如果每次只更新一个位置，用 `replace_Znth` 建模当前数组。  
如果更新前缀，用 `app(processed_prefix, remaining_suffix)` 建模。  
如果交换两个位置，用专门的 swap 状态谓词会比直接展开 `replace_Znth` 更稳。

### 注意点

- 原地修改通常需要更多 `Znth`、`replace_Znth`、`sublist` 引理。
- annotation 中可以保留高层状态，proof 中再展开。

## 11. 局部数组与滚动变量的取舍

部分 HumanEval 原程序会使用局部数组。当前经验是：

- 如果最终只需要标量结果，优先改写为滚动变量。
- 如果必须证明局部数组精确内容，`IntArray::seg/undef_seg` 用在栈数组上可能导致函数退出时权限回收困难。
- 对 Fibonacci/Tribonacci 类题，滚动变量通常比局部数组更容易验证。

代表题：

- `C_46` 最终改为 4 个滚动变量。
- `C_55` 使用两个滚动变量。
- `C_63` 使用三变量滚动版本。

## 12. 给大模型的决策流程

可以把下面这段直接放进提示词中：

```text
请先对每个循环分类，再生成 invariant：

1. 如果循环只读数组并更新累计变量，用 prefix_fold/prefix_state。
2. 如果循环可能提前 return，用 scanned_prefix/scanned_i/scanned_j/scanned_k 表示已检查区域。
3. 如果循环逐步写输出数组，用 output_l + IntArray::seg/undef_seg。
4. 如果是 filter，维护 output_size <= 已扫描数量，而不是 output_size == i。
5. 如果有多个阶段，每个阶段单独定义 state predicate，不要把所有语义揉在一个 invariant 里。
6. 如果是递推序列，用滚动变量等于 seq(i-k) 的形式。
7. 如果是 digit/bit while，用“剩余值 + 已累计结果”的 state predicate。
8. 如果保留排序算法，用 sort_outer_state/sort_inner_state 精确模拟循环。
9. 如果排序不是核心逻辑，优先建模为外部可信 sort_int_array。
10. 每个 invariant 都必须包含下标范围、入口参数稳定、Zlength、整数范围和数组资源。
```

## 13. 常见反模式

### 反模式 1：直接写最终规格

错误倾向：

```c
problem_spec(input_l, acc)
```

循环中 `acc` 通常只对应前缀，应该改为：

```c
acc == prefix_semantics(i, input_l)
```

### 反模式 2：忘记输出数组未初始化后缀

错误倾向：

```c
IntArray::seg(out, 0, i, output_l)
```

缺少后缀资源，后续写 `out[i]` 会失败。应写：

```c
IntArray::seg(out, 0, i, output_l) *
IntArray::undef_seg(out, i, n)
```

### 反模式 3：filter 中把 output_size 写成 i

filter 只在条件满足时写入，通常应写：

```c
0 <= output_size && output_size <= i
```

而不是：

```c
output_size == i
```

### 反模式 4：嵌套搜索只写一个全局 forall

三层循环直接写全局不存在性质很难单步推进。应拆成：

```c
scanned_i
scanned_j
scanned_k
```

### 反模式 5：忽略 C 整数范围

即使数学语义正确，VC 也会检查：

- `acc + a[i]`
- `a[i] + a[j] + a[k]`
- `i + 1`
- `n * 3 + 1`
- `p * 10`
- `abs(x)`

这些都需要 range predicate。

## 14. 快速对照表

| 循环类型 | invariant 核心 | 数组资源 | 代表题 |
| --- | --- | --- | --- |
| 只读前缀折叠 | `acc == prefix_fold(i, l)` | `IntArray::full` | `C_8`, `C_85`, `C_109`, `C_135` |
| 早返回搜索 | `scanned_prefix(i, l)` | `IntArray::full` | `C_3`, `C_72`, `C_126` |
| 嵌套搜索 | `scanned_i/j/k` | `IntArray::full` | `C_40`, `C_43` |
| 输出构造 | `output_prefix(i, output_l)` | `seg + undef_seg` | `C_100`, `C_152`, `C_163` |
| filter | `output_size <= i` + `filter_prefix` | `seg + undef_seg` | `C_123`, `C_163` |
| 多阶段辅助数组 | `first_loop_state`, `second_loop_state` | 多个 `seg + undef_seg` | `C_26` |
| 滚动递推 | `a == seq(i-k)` | 通常无数组或只读数组 | `C_46`, `C_55`, `C_63`, `C_114` |
| digit/bit while | `digit_state(original, rest, acc)` | 视情况 | `C_116`, `C_145`, `C_155` |
| 保留排序算法 | `sort_outer_state`, `sort_inner_state` | `IntArray::full` | `C_116`, `C_145` |
| 外部可信排序 | `Permutation`, `sorted_int_list_by` | `seg -> full` | `C_33`, `C_34`, `C_58`, `C_70`, `C_88`, `C_90`, `C_123` |

## 15. 推荐给大模型的输出格式

让大模型为每个循环输出以下内容：

```text
循环分类：
  例如：只读前缀折叠 / 输出数组构造 / 嵌套搜索

需要的 ghost/state：
  例如：prefix_sum, prefix_product, scanned_k, output_l

invariant 三层：
  1. 控制事实：i 范围、入口参数稳定、Zlength
  2. 语义事实：prefix/state predicate
  3. 内存资源：full 或 seg/undef_seg

需要补的 Coq 引理：
  init lemma
  step lemma
  final bridge lemma
  int range lemma
```

这能显著减少大模型直接猜 annotation 的失败率，也方便后续 manual VC 对应到具体的状态推进引理。
