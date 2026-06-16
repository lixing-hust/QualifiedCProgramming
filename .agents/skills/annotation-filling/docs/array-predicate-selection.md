# Array 谓词选型

这个文档总结 `QCP_examples/QCP_demos_LLM` 中数组相关 case 的经验，目标是帮助 agent 在补 annotation 时，先判断“当前程序状态到底需要哪一类数组谓词”，而不是机械地把所有数组都写成 `IntArray::full(...)`。

## 先做总判断

先判断当前 case 是否真的是“数组类状态”。

如果程序核心资源不是“连续下标访问的连续内存”，优先考虑结构谓词或普通 `data_at`，不要为了“看起来像容器”就选数组谓词。

## 一张决策表

### 1. 你需要整个数组的精确内容

选 `IntArray::full` / `UIntArray::full` / `CharArray::full` / `PtrArray::full`。

适用状态：

- 函数会读数组元素，并且规格或循环不变式要直接谈 `l[i]`、`sum(l)`、`Permutation(l, l1)`、`Zlength(l)` 等列表语义。
- 函数会原地修改数组，但你仍然要精确追踪“修改后列表是什么”。
- refinement / pure spec 明确以列表值为抽象状态。

典型例子：

- `sum.c`：只读数组并证明返回值等于 `sum(l)`，全程保持 `IntArray::full(a, n, l)`。
- `majorityElement.c`：算法只读 `nums[i]`，但不变式要表达 `l == app(l1, l2)` 等纯语义，必须保留完整内容。
- `eval.c`：`var_value` 是固定长度 100 的环境数组，表达式求值直接依赖元素值，因此要保留 `IntArray::full(var_value, 100, l)`。
- `kmp_rel.c`：模式串/文本/前缀函数都带有精确的列表语义，因此分别使用 `CharArray::full` 和 `IntArray::full`。

### 2. 你只需要“这段数组存在且可访问”，不需要精确内容

选 `IntArray::full_shape` / `UIntArray::full_shape` / `PtrArray::full_shape`，以及相应的 `seg_shape`。

适用状态：

- 程序会读写元素，但证明目标不依赖具体元素值。
- 你只关心内存形状、长度、可读写性，不关心列表内容。
- case 主要用于练习自动策略、内存布局或简单 shape preservation。

典型例子：

- `array_auto.c` 中的 `arr_sum`、`array_swap`、`array_max`、`array_to_list`：证明目标只需要数组资源保持存在，不需要追踪每一步的值级变化，因此用 `full_shape`。
- `array_copy1`、`array_concat`、`array_vector_sum`、`pointwise_mul`：目标只要求结果数组也形成合法数组 shape，不需要给出目标数组的精确列表，因此用 `seg_shape + undef_seg` 构造已写前缀。

判断标准很简单：

- 如果你的 `Ensure`、`Inv Assert` 里出现 `l[i]`、`sublist`、`Permutation`、`sum`、`sorted`、`safeExec(... list ...)` 这类值级语义，`shape` 通常不够。
- 如果你的目标只是“数组还在”“目标缓冲区已填满”“可以继续按下标访问”，`shape` 更省事，也更稳。

### 3. 你只拥有一个连续子区间，而不是整个数组

选 `IntArray::seg` / `UIntArray::seg` / `CharArray::seg` / `PtrArray::seg`。

适用状态：

- 算法天然把数组按索引区间拆成多个逻辑片段。
- 同一底层数组在不同区间上承载不同的抽象含义。
- 你需要在不变式里同时跟踪多个相邻片段的精确内容。

典型例子：

- `int_array_merge_rel.c`：`merge` 和 `mergeSort` 的核心状态就是多个相邻区间的拼接和搬运，因此一直用 `IntArray::seg(arr, l, r, sublist)` 来表达：
  - 左半段
  - 右半段
  - 已处理前缀
  - 未处理后缀
  - 工作缓冲区的对应区间

选 `seg` 的一个明确信号是：

- 你在循环里维护多个游标 `i/j/k`
- 每个游标把同一数组切成前缀、当前位、后缀
- 这些片段的内容都要精确保留

这时不要把整个数组硬写成一个 `full` 再在纯条件里手工表达切片关系；直接用多个 `seg` 更自然，也更贴近策略规则。

### 4. 数组一开始未初始化，之后逐步写满

初始选 `*Array::undef_full`，循环里用“已写前缀 + 未写后缀”：

- 已写部分如果不需要具体值：`seg_shape`
- 已写部分如果需要具体值：`full` 或 `seg`
- 未写部分：`undef_seg`

典型例子：

- `chars.c`：字符数组初始化，起点是 `CharArray::undef_full(a, n)`，循环不变式是
  - `CharArray::full(a@pre, i, repeat_Z(m@pre, i))`
  - `CharArray::undef_seg(a@pre, i, n@pre)`
- `array_auto.c` 的 `memset`、`array_copy1`、`array_concat`、`array_vector_sum`、`pointwise_mul` 都是这一模式，只是已写前缀用的是 `seg_shape` 而不是带内容的 `seg/full`。

经验规则：

- “未初始化缓冲区逐步写满”是 `undef_full` 最典型的使用场景。
- 如果循环每次只把前缀多写一个元素，不变式几乎总是“前缀已初始化 + 后缀未初始化”。
- 如果已写前缀的值很重要，就用 `full/seg`；如果值不重要，就用 `seg_shape`。

### 5. 数组内容固定，但你现在拿到的是某个偏移后的指针

优先考虑“以当前指针为新基址的 `full`”，而不是总强迫自己回到原数组基址写 `seg`。

典型例子：

- `kmp_rel.c` 中构造 `vnext` 时，不变式使用：
  - `IntArray::full(vnext, i, vnext0)`
  - `IntArray::full((vnext + i * sizeof(int)), n - i, l0)`

这里后半段没有写成 `IntArray::seg(vnext, i, n, l0)`，而是直接把 `vnext + i * sizeof(int)` 视为“剩余后缀的起始地址”。

适用判断：

- 如果后续代码主要通过偏移后的指针访问 suffix，那么“偏移指针上的 `full`”通常更直接。
- 如果你还要同时把它和原数组的其他区间拼起来推理，`seg(base, l, r, ...)` 往往更合适。

## `missing_i` 不是默认手写谓词

`missing_i` / `missing_i_shape` / `undef_missing_i` 很重要，但在当前例子里，它们几乎不是手写 annotation 的首选。

它们更像“策略在打开一个单元时产生的中间形态”：

- `int_array.strategies`
- `char_array.strategies`
- `ptr_array.strategies`
- `array_shape.strategies`
- `undef_uint_array.strategies`

这些规则的共同模式是：

- `full` 遇到单个 `data_at` 时，会被拆成 `missing_i + 当前单元`
- `seg` 遇到单个 `data_at` 时，会被拆成区间版 `missing_i + 当前单元`
- 写回单元后，再从 `missing_i + data_at(...)` 组回 `full` 或 `seg`

因此：

- 如果你只是因为代码里出现了 `a[i]` / `a[i] = ...`，通常不要手写 `missing_i`
- 先写更高层的 `full`、`seg`、`shape`、`undef_*`
- 让现有策略在符号执行过程中自动拆开

只有当你明确需要把“除第 `i` 个元素外的其余数组”单独暴露出来时，才考虑直接写 `missing_i`

## 各谓词的典型搭配

### 只读扫描

- 首选：`full`
- 例子：`sum.c`、`majorityElement.c`

原因：

- 扫描不会破坏内容
- 不变式通常需要前缀/后缀的纯列表关系

### 原地更新，但仍要保留精确内容

- 首选：`full`
- 例子：`sum.c` 中 `arr_sum_update`、`sortArray*.c`、`int_array_quicksort.c`

原因：

- 每次写入都要反映到抽象列表上
- 排序和置零都属于“值变了，但内容语义仍是证明核心”

### 区间算法 / 双指针 / 多游标

- 首选：`seg`
- 例子：`int_array_merge_rel.c`

原因：

- 一个 `full` 很难自然表达多个逻辑区间
- `seg` 可以直接对应每个游标划分的区间

### 只关心 shape 的逐步构造

- 首选：`seg_shape + undef_seg`
- 例子：`array_auto.c`

原因：

- 证明目标不需要值
- 用 shape 版本可以显著减轻列表等式负担

### 字符串 / C 风格字符数组

- 首选：`CharArray::full(..., n + 1, app(str, cons(0, nil)))`
- 例子：`kmp_rel.c`

原因：

- C 字符串通常需要显式保留结尾 `0`
- 证明里经常既要谈逻辑字符串 `str`，又要保证底层缓冲区可用于 `strlen`

### 新分配数组的初始状态

先看分配函数的规格，而不是主观猜。

- `chars.c` / `array_auto.c` 这类“待初始化缓冲区”显式要求 `undef_full`
- `kmp_rel.c` 里的 `malloc_int_array` 规格是 `exists l, IntArray::full(__return, n, l)`，不是 `undef_full`

这说明：

- 不同 case 对“新分配内存”的建模可能不同
- 不要把“malloc 出来的数组”自动脑补成 `undef_full`
- 先读该项目里对应分配函数的规格

## 一个简化流程

补 annotation 时，可以按下面顺序选：

1. 当前资源是不是连续数组，而不是链表/树/结构体字段？
2. 我是否必须知道元素的具体值？
3. 我拥有的是整个数组，还是一个连续区间，还是一个偏移后的后缀？
4. 这块内存是已经初始化好的，还是尚未初始化、正在逐步写入？
5. 写完之后，我的证明目标是值语义，还是只有 shape 语义？

对应选择通常是：

- 精确值 + 整体数组：`full`
- 精确值 + 连续子区间：`seg`
- 只要 shape + 整体数组：`full_shape`
- 只要 shape + 连续子区间：`seg_shape`
- 未初始化整体数组：`undef_full`
- 未初始化连续子区间：`undef_seg`
- 需要暴露一个单元做读写：通常仍从 `full/seg/...` 出发，让策略产生 `missing_i`

## `Znth` / `Zhth` 风格索引观察怎么放

数组谓词负责描述“你拥有哪些资源”，而 `Znth` / `Zhth` 风格项更适合描述“你正在观察哪个位置上的值”。

先分工：

- `IntArray::full` / `seg` / `shape` / `undef_*`
  - 负责空间资源和整体 / 区间内容
- `Znth`
  - 负责从纯列表里取出某个索引位置的值
- `Zhth` 风格谓词
  - 当前仓库没有统一基础定义；如果某个 case 自己引入了这类“Z 索引下的候选值 / 边界值”纯谓词，把它视为和 `Znth` 同类的观察接口

经验上：

- 不要拿 `Znth` / `Zhth` 去替代数组谓词本身。
- 它们最适合出现在：
  - 单步读写后的纯条件
  - “当前元素 / 边界元素 / 候选最优值”相关断言
  - prefix / suffix / subarray 性质的连接点
- 如果一个 invariant 主要由一串裸露的 `Znth i l 0` 组成，通常说明你还没有把更高层的隐藏性质抽出来。

### 什么时候该把 `Znth` 包进更高层谓词

优先包起来的场景：

- 你真正想表达的是“当前 `cur` 是处理过前缀的最佳 suffix”
- 你真正想表达的是“当前 `res` 是处理过前缀的最佳子数组”
- 你真正想表达的是“第 `i` 个位置只是某个区间切分的边界点”

这时更好的写法通常是：

- `IntuitiveMaxSuffixSum(sublist(0, i, l), cur)`
- `IntuitiveMaxSubArraySum(sublist(0, i, l), res)`
- `IntArray::seg(..., sublist(...))`

而不是把 invariant 直接堆成很多 `Znth` 等式。

## 常用 `Znth` 证明套路

下面这些 lemma 在当前仓库里是高频工具，足够覆盖大多数数组 case 的索引证明。

### 1. 先证边界，再消默认值

最先要做的不是 `rewrite`，而是拿到：

- `0 <= i`
- `i < Zlength l`

一旦边界成立，`Znth` 的默认值通常就不再重要，可以用：

- `Znth_indep`

把默认值参数换掉。

### 2. 读 `cons` / 单元素前缀

常用：

- `Znth0_cons`
- `Znth_cons`

适合把 `Znth 0 (x :: xs) d` 化成 `x`，或把正索引向后递推一层。

### 3. 读拼接后的前半段 / 后半段

常用：

- `app_Znth1`
- `app_Znth2`

适合处理：

- `Znth i (l1 ++ l2) d`

特别是你在 annotation 里把“已处理前缀 + 当前元素 + 未处理后缀”拆开以后。

### 4. 读 `sublist`

常用：

- `Znth_sublist`
- `Znth_sublist0`
- `Zlength_sublist`
- `Zlength_sublist0`
- `sublist_single`
- `sublist_split`
- `sublist_split_app_l`
- `sublist_split_app_r`

典型用途：

- 把 `Znth i (sublist lo hi l) d` 改写回原列表上的 `Znth (i + lo) l d`
- 把区间拆成“左段 + 当前单元 + 右段”
- 计算处理过前缀 / 未处理后缀的长度

### 5. 处理写回后的列表

常用：

- `replace_Znth_cons`
- `replace_Znth_Znth`
- `replace_Znth_app_l`
- `replace_Znth_app_r`

这些 lemma 适合和数组策略产生的“读出一个单元再写回”场景配合使用。

经验上：

- 如果你只是读出再原样写回，`replace_Znth_Znth` 往往能直接把目标恢复成原列表。
- 如果你在前缀 / 后缀拼接的列表上更新某个位置，优先用 `replace_Znth_app_l` / `replace_Znth_app_r` 定位写入发生在哪一段。

## `Zhth` 风格谓词的使用建议

当前仓库没有统一的 `Zhth` 基础库，因此不要在 annotation 中预设它的实现细节。

如果某个 case 自己带有 `Zhth` 或类似命名的纯谓词，建议按下面方式使用：

- 把它当作“某个边界位置上候选值的观察接口”
- 让它服务于更高层的 prefix / suffix / 最优性谓词
- 不要让 invariant 的核心语义退化成“不断操作 `Zhth` 的索引算术”

也就是说：

- `Zhth` / `Znth` 负责取点
- 更高层谓词负责讲清楚这个点为什么重要

## 常见误选

### 把所有数组都写成 `full`

问题：

- 对只需要 shape 的 case，会引入大量没必要的列表等式
- `array_auto.c` 已经展示了这种场景下 `full_shape` 更稳

### 把区间算法写成 `full`

问题：

- 需要纯条件手工表达很多 `sublist/app`
- 往往比直接写多个 `seg` 更脆弱

### 把逐步初始化缓冲区写成 `full_shape`

问题：

- 如果缓冲区起点实际上是未初始化内存，就丢失了“尚未写入”的信息
- 应先用 `undef_full`，再随着循环推进切成“已写 + 未写”

### 看到 `a[i]` 就手写 `missing_i`

问题：

- 当前策略本来就会自动从 `full/seg` 拆出单元
- 直接手写 `missing_i` 往往让 annotation 更低层、更难维护

## 当前样例覆盖到的结论

- `IntArray::full` 是最常见的“值语义数组”谓词，适合读数组、排序、精确更新、refinement 中的抽象列表。
- `IntArray::seg` 主要用于区间算法和多游标状态，尤其是 merge / mergesort 这类天然切片的程序。
- `*Array::full_shape` / `seg_shape` 适合只需要内存形状、不需要元素值的自动化 case。
- `*Array::undef_full` / `undef_seg` 适合逐步初始化的输出缓冲区。
- `CharArray::full(..., n + 1, app(str, cons(0, nil)))` 是字符串 case 的标准建模方式。
- `missing_i` 系列更像策略中间态，而不是多数 annotation 的顶层选择。
- `PtrArray::*` 在当前 C 样例中没有直接案例；如果遇到指针数组，优先按 `IntArray::*` / `CharArray::*` 的同族规则判断，再结合对应 `.strategies` 检查拆分方式。

如果一时拿不准，优先回看最接近的案例：

- 只读/值语义：`sum.c`、`majorityElement.c`
- 排序/原地重排：`sortArray*.c`、`int_array_quicksort.c`
- 分段区间：`int_array_merge_rel.c`
- 逐步初始化：`chars.c`、`array_auto.c`
- 字符串 + 数组混合：`kmp_rel.c`
- 固定长度环境数组：`eval.c`
