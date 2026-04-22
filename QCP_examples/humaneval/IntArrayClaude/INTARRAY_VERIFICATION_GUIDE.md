# IntArrayClaude 数组程序验证指南

这份文档面向 `QCP_examples/humaneval/IntArrayClaude` 下的数组题。它基于 QCP v2.0.1 后的数组支持，以及当前 `LLM_friendly_cases` 中已经更新过的数组相关例子整理。

本文只参考当前仓库里的 `LLM_friendly_cases` 版本，不参考旧目录或 `QCP_democases`。

## 0. QCP v2.0.1 后的关键变化

QCP v2.0.1 对数组验证有几处会直接影响写 annotation 和证明的变化：

- 支持直接声明固定长度数组并进行符号执行，例如 `int a[10]` 这类一维基础数组。`struct list a[]` 这类 struct/union 数组仍不支持。
- 基础谓词/策略和数组相关谓词/策略已经内置。新验证任务通常不需要再为了数组而显式包含 `verification_stdlib.h`、`verification_list.h`、`common.strategies`、`int_array_def.h`、`array_shape.strategies` 等文件。
- 当前 `QCP_examples/LLM_friendly_cases` 里仍保留了一些 `*_def.h` 和 `.strategies` 文件，它们更适合作为“谓词/策略形状参考”，不要把它们当作新题必须 include 的模板。
- `ListLib` 已适配，`Znth`、`replace_Znth`、`sublist`、`app_Znth1/2`、`Znth_sublist_lt` 等列表引理可以直接作为数组 proof 的主要工具。
- qide 增加了函数推导展示，调试 symbolic execution 时可以结合 qide 观察函数 derivation，但最终仍以 `qcp-mcp symbolic/proof` 和 `rocq-mcp` 的交互式检查为准。

## 1. 最新应优先阅读的数组例子

按用途推荐如下：

- `QCP_examples/LLM_friendly_cases/sum.c`
  只读扫描、`for/while/do while` 三种循环、原地更新、指针偏移读数组。
- `QCP_examples/LLM_friendly_cases/array_cases.c`
  最新的精确数组内容模板：copy、concat、swap、vector sum、pointwise mul、max、memset、array-to-list。
- `QCP_examples/LLM_friendly_cases/array_auto.c`
  shape-only 风格模板：只证明数组有合法 shape，不证明精确内容。
- `QCP_examples/LLM_friendly_cases/chars.c`
  `CharArray` 写入和 `repeat_Z` 风格。
- `QCP_examples/LLM_friendly_cases/majorityElement.c`
  只读数组扫描，但循环语义依赖自定义抽象谓词和 `*_lib.v`。
- `QCP_examples/LLM_friendly_cases/sortArray.c`
  原地排序，使用 `IntArray::full(nums, numsSize, l)` 追踪整个数组列表的 permutation/increasing 语义。
- `QCP_examples/LLM_friendly_cases/sortArray2.c`
  原地选择排序风格。
- `QCP_examples/LLM_friendly_cases/sortArray3.c`
  原地冒泡排序风格。
- `QCP_examples/LLM_friendly_cases/int_array_merge_rel.c`
  `IntArray::seg`、多区间资源分账、refinement/safeExec 组合。
- `QCP_examples/LLM_friendly_cases/kmp_rel.c`
  `CharArray + IntArray`、`malloc_int_array`、函数调用 `where`、指针偏移后缀数组、safeExec refinement。
- `QCP_examples/LLM_friendly_cases/eval.c`
  结构体程序中读取固定大小 `IntArray::full(var_value, 100, l)`。

对应的 proof 优先参考：

- `SeparationLogic/examples/LLM_friendly_cases/sum_proof_manual.v`
- `SeparationLogic/examples/LLM_friendly_cases/array_cases_proof_manual.v`
- `SeparationLogic/examples/LLM_friendly_cases/majorityElement_proof_manual.v`
- `SeparationLogic/examples/LLM_friendly_cases/sortArray_proof_manual.v`
- `SeparationLogic/examples/LLM_friendly_cases/int_array_merge_rel_proof_manual.v`
- `SeparationLogic/examples/LLM_friendly_cases/kmp_rel_proof_manual.v`

## 2. 数组表示谓词如何选择

### 2.1 `IntArray::full`

```c
IntArray::full(p, n, l)
```

表示 `p` 指向长度为 `n` 的 int 数组，内容精确等于列表 `l`。

适合：

- 只读扫描：`sum.c`、`majorityElement.c`
- 原地更新但仍想精确描述整个数组：`sum.c` 的 `arr_sum_update`、`sortArray*.c`
- 返回时需要证明数组内容、排列、最大值、前缀和等数学性质

只读扫描 invariant 通常保留完整资源：

```c
/*@ Inv Assert
    0 <= i && i <= n@pre &&
    a == a@pre && n == n@pre &&
    state == prefix_semantics(sublist(0, i, l)) &&
    IntArray::full(a, n@pre, l)
*/
```

### 2.2 `IntArray::seg`

```c
IntArray::seg(p, lo, hi, l)
```

表示数组逻辑区间 `[lo, hi)`，内容为 `l`。它适合精确描述“只拥有数组一段”或者“输出数组前缀已经写入”的状态。

最新版 `array_cases.c` 已经大量使用 `seg + undef_seg` 来做精确内容证明。例如 `array_copy1`：

```c
IntArray::seg(dest@pre, 0, i, sublist(0, i, l)) *
IntArray::undef_seg(dest@pre, i, n@pre) *
IntArray::full(src@pre, n@pre, l)
```

这比 shape-only 版本更强：它不仅证明前缀已初始化，还证明前缀内容正是 `src` 的前缀。

### 2.3 `IntArray::undef_full` / `undef_seg`

```c
IntArray::undef_full(p, n)
IntArray::undef_seg(p, lo, hi)
```

表示内存可写但内容未初始化。输出数组、临时数组、逐步填充的后缀通常从这里开始。

精确写入模板：

```c
/*@ Inv Assert
    exists l_done,
    0 <= i && i <= n@pre &&
    Zlength(l_done) == i &&
    prefix_property(l_done, i) &&
    IntArray::seg(out@pre, 0, i, l_done) *
    IntArray::undef_seg(out@pre, i, n@pre)
*/
```

### 2.4 `*_shape`

```c
IntArray::full_shape(p, n)
IntArray::seg_shape(p, lo, hi)
```

shape 谓词只表达数组内存形状合法，不记录具体值。`array_auto.c` 是这类规格的集中例子。

适合：

- 只证明不会越界、不会读未初始化内存
- 函数后置条件不要求精确数组内容
- 快速建立内存安全 skeleton

不适合：

- 要证明拷贝后 `dest` 等于 `src`
- 要证明输出数组每项满足公式
- 要证明排序、最大值、前缀和等语义性质

### 2.5 局部固定长度栈数组

QCP 更新后可以解析并符号执行一维基础类型局部数组声明，例如：

```c
int f[100];
```

当前实验结论：

- 最小程序可以通过：

```c
int local_array_min()
/*@ Require emp
    Ensure __return == 0 && emp
*/
{
    int f[100];
    return 0;
}
```

- 对局部数组单点读写，工具可以生成并使用形如 `data_at(f + i * sizeof(INT), v)` 的资源；如果中间 assertion 只保留单个 `data_at(f, 0)`，函数退出时局部数组资源可以被回收。
- 但把局部栈数组资源手动整理成堆数组常用的精确区间谓词后，函数退出时可能无法回收局部数组权限。例如在 `C_46.c` 的尝试中，使用：

```c
IntArray::seg(f, 0, i, fib4_z_list(i)) *
IntArray::undef_seg(f, i, 100)
```

可以支撑循环内数组读写，但在 `return` 前后触发：

```text
Fail to Remove Memory Permission of f
```

这说明目前“局部栈数组支持”和“堆数组式 `IntArray::seg/undef_seg` 不变式”之间还需要额外的资源恢复方式，不能默认照搬 malloc 数组的 `seg + undef_seg` 模式。

处理建议：

- 格式转换阶段可以保留 `int f[100]`，但不要过早承诺用 `IntArray::seg/undef_seg` 完成完整 proof。
- 如果只是验证标量返回值，优先考虑把局部数组隐藏在程序执行中，或者用工具生成的单点 `data_at` 资源推进，避免在最终 return 前留下 `IntArray::seg/undef_seg` 形式的栈数组资源。
- 如果确实需要精确描述局部数组前缀内容，需要继续确认新版 QCP 对局部数组的推荐表示谓词；`int_array_def.h` 中的 `store_array_box` / `store_array_box_array` 可能相关，但当前 `LLM_friendly_cases` 中没有可直接参考的完整案例。
- 对于必须立即完成验证的题，可以暂时改写成滚动变量版本或内部 malloc 数组版本；若目标是测试局部数组支持，则先保留当前实验记录，等确认资源恢复模式后再继续。

经验：如果题目是 HumanEval 风格，后置条件通常关心内容，优先考虑 `full/seg/undef_seg`，不要过早退化成 `*_shape`。

### 2.5 `missing_i`

```c
IntArray::missing_i(p, i, lo, hi, l)
```

它是“整段数组拆出第 `i` 个单元”时的中间谓词。日常 annotation 里不一定要显式写它，因为数组访问策略通常会自动把：

```text
IntArray::full/seg + a[i]
```

拆成当前 `data_at` 和 `missing_i`，访问结束后再合并。

manual proof 卡在单点读写时，可以在 proof 里查找并使用相关 split/merge 引理，但 annotation 层优先保持 `full` 或 `seg` 的高层表达。

## 3. 最新例子里的常用 invariant 模板

### 3.1 只读扫描

代表：`sum.c`、`array_cases.c::arr_sum`、`array_cases.c::array_max`、`majorityElement.c`。

模板：

```c
/*@ Inv Assert
    exists aux,
    0 <= i && i <= n@pre &&
    a == a@pre && n == n@pre &&
    pure_prefix_relation(aux, sublist(0, i, l)) &&
    remaining_or_global_property(l) &&
    IntArray::full(a, n@pre, l)
*/
```

要点：

- 数组没有被写，`IntArray::full(a, n, l)` 应保持不变。
- 如果有 C 整数运算，前置条件要能推出每一步不溢出。`sum.c` 和 `array_cases.c` 用 `n < 100`、`0 <= l[i] < 100` 控制范围。
- 对布尔/早返回题，invariant 需要同时记录“已处理前缀语义”和“返回分支需要的 witness 或 forall 性质”。

### 3.2 精确写入输出数组

代表：`array_cases.c::array_copy1`、`array_concat`、`array_vector_sum`、`pointwise_mul`、`memset`。

模板：

```c
/*@ Inv Assert
    exists l3,
    0 <= i && i <= n@pre &&
    Zlength(l3) == i &&
    (forall (k: Z), (0 <= k && k < i) => l3[k] == expr_at(k)) &&
    IntArray::seg(out@pre, 0, i, l3) *
    IntArray::undef_seg(out@pre, i, n@pre) *
    IntArray::full(input, n@pre, l)
*/
```

最终返回常见 proof 步骤：

- 由 `i = n` 得到 `undef_seg out n n`
- rewrite 空后缀：`IntArray.undef_seg_empty`
- 用 `IntArray.seg_to_full` 把已写完整区间变回 `IntArray::full`

### 3.3 原地改写

代表：`sum.c::arr_sum_update`、`array_cases.c::array_swap`、`sortArray*.c`。

前缀已处理、后缀未处理时可以用列表拼接描述整个数组：

```c
IntArray::full(a, n@pre, app(done_prefix, sublist(i, n@pre, old_l)))
```

`arr_sum_update` 的经典写法：

```c
IntArray::full(a, n@pre, app(zeros(i), sublist(i, n@pre, l)))
```

双数组 swap 的写法：

```c
IntArray::full(a, n@pre, app(sublist(0, i, l2), sublist(i, n@pre, l1))) *
IntArray::full(b, n@pre, app(sublist(0, i, l1), sublist(i, n@pre, l2)))
```

排序类程序则通常让 `IntArray::full(nums, numsSize, l_current)` 保存当前整数组，并在纯逻辑里证明 `Permutation`、`increasing`、上下界等性质。

### 3.4 多区间和切片

代表：`int_array_merge_rel.c`、`kmp_rel.c`。

当函数只处理数组中间一段，或者需要把数组资源分给多个函数调用时，用 `seg` 比用 `full` 更自然。

merge 风格 invariant 通常显式列出每一段：

```c
IntArray::seg(arr, p, i, l_done_left) *
IntArray::seg(arr, i, q + 1, l_left) *
IntArray::seg(arr, q + 1, j, l_done_right) *
IntArray::seg(arr, j, r + 1, l_right) *
IntArray::seg(ret, p, k, l_out) *
IntArray::seg(ret, k, r + 1, l_rest)
```

`kmp_rel.c` 还展示了后缀数组的另一种写法：

```c
IntArray::full(vnext, i, vnext0) *
IntArray::full((vnext + i * sizeof(int)), n - i, l0)
```

这适合“前缀已经初始化，后缀仍作为独立数组资源保存”的 malloc 数组。

### 3.5 数组与链表/结构体混合

代表：`array_cases.c::array_to_list`、`array_auto.c::array_to_list`、`eval.c`。

当数组只作为数据源，链表或结构体是主要内存变化对象时：

- 数组仍保留 `IntArray::full(a, n, l)` 或 `full_shape`
- 链表部分用 `sllseg/sll`、`lseg/listrep` 等对应谓词
- invariant 中用 `sublist(0, i, l)` 对齐已经转成链表的前缀

## 4. proof_manual 里最常见的证明套路

### 4.1 先拿长度事实

数组 proof 经常第一步拿长度：

```coq
prop_apply IntArray.full_Zlength.
Intros_p Hlen.
```

或：

```coq
prop_apply IntArray.full_length.
Intros_p Hlen.
```

`UIntArray` 同理。后续 `Znth`、`sublist`、`seg_to_full`、循环边界证明都依赖这些长度事实。

### 4.2 输出前缀推进

`array_cases_proof_manual.v` 的典型步骤：

```coq
sep_apply (IntArray.seg_single out i value).
sep_apply (IntArray.seg_merge_to_seg out 0 i (i + 1) l_done (value :: nil)).
```

然后用 `sublist_split`、`sublist_single`、`Znth_sublist_lt`、`app_Znth1/2` 证明新列表正是旧前缀加当前元素。

### 4.3 输出数组收尾

常见顺序：

```coq
rewrite IntArray.undef_seg_empty.
sep_apply (IntArray.seg_to_full out 0 n l_done).
```

再用 `cancel` 保留 frame。

### 4.4 原地更新和 `replace_Znth`

原地 `a[i] = v` 往往会把当前列表变成：

```coq
replace_Znth i v old_list
```

最新 `ListLib` 已经可以使用 `Znth`、`replace_Znth` 相关引理。复杂证明仍可按当前 `array_cases_proof_manual.v` 的方式补局部 lemma，但只在确实需要时添加，避免一次性生成大量没用的库引理。

常见目标是把 `replace_Znth` 化成：

```coq
sublist 0 i old ++ v :: sublist (i + 1) n old
```

或者证明 `Zlength (replace_Znth i v old) = Zlength old`。

### 4.5 C 整数安全不要漏

数组 VC 不只检查越界，还会检查 C 整数范围：

- `ret + a[i]` 是否在 int/uint 范围内
- `i + 1`、`n + m`、`i * sizeof(int)` 是否安全
- `a[i] * b[i]` 是否不会溢出

`array_cases.c` 对 `UIntArray` 的 vector sum/mul 使用 `0 <= l[k] < 100`、`n < 100` 这样的约束；HumanEval 新题如果没有足够范围条件，要先判断 VC 是否语义可证，不能硬写 proof。

## 5. 新题 annotation 的推荐流程

1. 先判断数组角色：
   只读输入、输出缓冲区、原地修改、多数组切片、malloc 返回数组、固定长度局部数组。

2. 选谓词：
   只读用 `full`；精确输出用 `seg + undef_seg`；弱内存安全用 `*_shape`；区间算法用 `seg`；局部固定长度数组按工具生成的数组资源继续用对应 `full/seg/undef` 风格表达。

3. 写 invariant 三层：
   下标范围、纯语义、内存资源。数组题最常见失败是只写了语义，忘了资源如何随循环变化。

4. 每次改 annotation 后重新跑 `qcp-mcp symbolic` 到文件尾：
   重新读取完整 witness 列表，逐条判断 manual VC 是否语义可证。不要沿用旧编号。

5. manual VC 按“导出一个、检查一个、用 rocq-mcp 跑通一个、保存一个”的节奏处理：
   auto-solved 的 VC 不需要导出或回填。

6. 所有临时 proof 跑通后，再运行 symexec 生成正式 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`，然后按 VC 主体形状回填 proof。

## 6. 针对 IntArrayClaude 的实用判断

### 6.1 只读查询题

例如“是否存在”“最大值”“前缀条件”“多数元素”：

- invariant 保留 `IntArray::full(input, n, l)`
- 用 `sublist(0, i, l)` 描述已处理前缀
- 早返回时要准备 witness；正常返回时要准备 forall
- 检查元素范围和累计变量范围是否足以证明 C 安全

### 6.2 返回/填充数组题

如果函数写入调用者提供的 `return` 数组：

- precondition 用 `IntArray::undef_full(ret, n)`
- loop invariant 用 `IntArray::seg(ret, 0, i, l_done) * IntArray::undef_seg(ret, i, n)`
- `l_done` 上加 `Zlength(l_done) == i` 和逐点语义

如果只要求内存有效，不要求内容，再考虑 `seg_shape/full_shape`。

### 6.3 原地变换题

优先用整数组列表表达当前状态：

```c
IntArray::full(a, n, app(processed_prefix, remaining_suffix))
```

如果每轮交换两个位置，proof 多半会遇到 `replace_Znth`、`app_Znth1/2`、`sublist_split`。先看 `array_cases.c::array_swap` 和 `sortArray*.c`。

### 6.4 malloc 返回数组题

参考 `kmp_rel.c::constr`：

- malloc spec 可写成 `Ensure exists l, IntArray::full(__return, n, l)`
- 初始化第一个元素后，循环可用“已初始化前缀 + 未处理后缀”
- 如果后置条件要求精确内容，逐步把前缀列表作为 witness 维护

## 7. C_3 风格题的特别提醒

`C_3.c` 这类“只读数组 + 前缀和 + 早返回”题，内存 invariant 通常很简单：

```c
num == sum(sublist(0, i, l)) &&
0 <= i && i <= operations_size@pre &&
(forall k, 0 <= k && k < i -> 0 <= sum(sublist(0, k + 1, l))) &&
IntArray::full(operations, operations_size@pre, l)
```

真正关键是纯逻辑：

```text
sum(sublist(0, i, l)) + Znth i l 0
= sum(sublist(0, i + 1, l))
```

以及把“旧前缀全非负 + 当前新前缀非负”推进成 `i + 1` 的全称性质。

更容易成为 blocker 的是 C int 溢出。若前置条件没有约束元素范围或所有前缀和范围，`num += operations[i]` 的 safety VC 可能语义上不可证。此时应回到规格/annotation 判断是否需要加强前置条件，而不是硬写 Rocq proof。

## 8. 排障清单

- symbolic 失败先看 annotation 是否仍引用了过时 include 或策略；v2.0.1 后数组基础谓词/策略已内置。
- 如果 VC 中 `Zlength l = n` 缺失，先从 `IntArray.full_Zlength/full_length` 或对应 `seg` 长度引理获得。
- 如果 `seg + undef_seg` 收尾失败，先对齐循环退出下标，再 rewrite 空 `undef_seg`，最后 `seg_to_full`。
- 如果假设名在重生成后漂移，proof 里按公式形状用 `match goal with` 抓假设，少依赖固定的 `H5/H6`。
- 如果 proof 想补 `*_lib.v`，先确认该引理确实被当前 VC 需要；补完必须用 `rocq-mcp` 跑通，不引入 `Axiom`，不留下 `Admitted`。
- 不使用 `entailer!`。当前项目 proof 优先模仿 `LLM_friendly_cases` 中的 `pre_process`、`prop_apply`、`sep_apply`、`split_pure_spatial`、`cancel`、`lia`、`rewrite` 等风格。

## 9. 快速参考表

| 题型 | 首选例子 | 首选谓词 |
| --- | --- | --- |
| 只读求和/扫描 | `sum.c`, `array_cases.c::arr_sum` | `IntArray::full` / `UIntArray::full` |
| 最大值/存在性 | `array_cases.c::array_max` | `IntArray::full` |
| 多数元素/复杂抽象语义 | `majorityElement.c` | `IntArray::full` + 自定义 lib |
| 拷贝/拼接/填充且证明内容 | `array_cases.c` | `seg + undef_seg` |
| 只证明内存 shape | `array_auto.c` | `seg_shape/full_shape` |
| 原地交换/排序 | `array_cases.c::array_swap`, `sortArray*.c` | `IntArray::full` + 列表变换 |
| 多区间 merge/refinement | `int_array_merge_rel.c` | `IntArray::seg` |
| char/int 混合和函数调用 | `kmp_rel.c`, `chars.c` | `CharArray::full`, `IntArray::full`, `where` |
