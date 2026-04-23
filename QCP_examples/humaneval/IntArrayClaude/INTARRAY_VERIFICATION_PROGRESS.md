# IntArrayClaude 验证进度记录

更新时间：2026-04-23

这份文档用于记录 `QCP_examples/humaneval/IntArrayClaude` 下各题的验证进度，以及每题验证时遇到的具体问题。

它和下面两份文档分工不同：

- `INTARRAY_SPEC_WRITING_GUIDE.md`：记录前后条件怎么写。
- `INTARRAY_VERIFICATION_GUIDE.md`：记录数组程序验证的一般方法。
- 本文档：记录每一道题当前做到哪里、踩过哪些坑、后续继续时要注意什么。

## 状态说明

- `已全链通过`：已经完成 `symexec`、`manual` 证明、`goal_check` 编译，且手写文件无 `Admitted.` / `Axiom`。
- `已有生成文件`：目录中已有 `C_XX_goal.v` / `C_XX_proof_auto.v` / `C_XX_proof_manual.v` / `C_XX_goal_check.v`，但本文档尚未确认完整验收。
- `待建模`：尚未建立完整 QCP 规格和验证文件，通常需要先重写前后条件。

## 当前总览

| 题目 | 当前状态 | 备注 |
| --- | --- | --- |
| `C_3` | 已全链通过 | 只读数组、前缀和、布尔提前返回。已使用 `problem_3_pre/spec`。 |
| `C_5` | 已全链通过 | `return_wit_2` 已补完；`coins/goal/auto/manual/goal_check` 编译通过，且无 `Admitted.` / `Axiom`。 |
| `C_8` | 已全链通过 | sum/product 输出数组；使用前缀和/前缀积及范围约束处理溢出安全。 |
| `C_9` | 已全链通过 | 已切到 `INT_MIN` 语义并保留 `list_int_range`；`coins/goal/auto/manual/goal_check` 编译通过，且无 `Admitted.` / `Axiom`。 |
| `C_25` | 已全链通过 | 结构体指针返回版本；强循环不变式记录乘积、有序、素性与无小因子性质，manual 已无 `Admitted.`。 |
| `C_26` | 已全链通过 | 去重保留只出现一次的元素；使用两轮循环分别收集重复元素和输出非重复元素，manual 已无 `Admitted.`。 |
| `C_40` | 已全链通过 | 三元组求和；三层扫描谓词、溢出安全和 true/false 规格桥接已补完，manual 已无 `Admitted.`。 |
| `C_42` | 已全链通过 | 已去掉输入 `out`，改为函数内部 malloc 并返回 `IntArray *` 结构体；manual 已无 `Admitted.`。 |
| `C_43` | 已全链通过 | 二元组求和；复用 `C_40` 的分层扫描谓词模式，manual 已无 `Admitted.`。 |
| `C_46` | 已全链通过 | 已改成 4 个滚动变量，不再使用局部数组；manual 已无 `Admitted.`。 |
| `C_52` | 已全链通过 | 单层数组扫描；改为使用 `problem_52_pre/spec`，manual 已无 `Admitted.`。 |
| `C_55` | 已全链通过 | Fibonacci 滚动变量；已接入 `problem_55_pre/spec`，并用 `fib_step_int_range` 处理加法溢出，manual 已无 `Admitted.`。 |
| `C_63` | 已全链通过 | FibFib 三变量滚动版本；已接入 `problem_63_pre/spec`，manual 已无 `Admitted.`。 |
| `C_72` | 已全链通过 | 回文数组且总和不超过阈值；已补 `coins_72.v`、前缀和/镜像 invariant 和 6 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_73` | 已全链通过 | 统计左右镜像不等对数；已补 `coins_73.v`、镜像对计数 invariant 和 5 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_85` | 已全链通过 | 奇数下标求和；已补 `coins_85.v`、循环前缀和 invariant 和 5 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_100` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_106` | 已有生成文件 | manual 当前无 `Admitted.`，但本文档尚未重新跑完整验收链。 |
| `C_109` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_121` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_122` | 已有生成文件 | manual 仍含 `Admitted.`。 |

其它只有 `.c` 的题目暂按 `待建模` 处理。

## C_8 验证记录

### 结论

`C_8` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_8.v
coqc C_8_goal.v
coqc C_8_proof_auto.v
coqc C_8_proof_manual.v
coqc C_8_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_8.v C_8_proof_manual.v
```

无输出。

### 文件变更

- `C_8.c`
  - 功能性规格复用 `problem_8_pre/spec`。
  - `malloc_int_array` 的后置条件改为返回 `IntArray::undef_full`，更符合后续写 `out[0]` / `out[1]` 的内存模型。
  - 函数规格中增加 ghost 参数 `numbers0` / `numbers_size0`，用于在循环 invariant 中稳定保存入口参数。
  - 前置条件增加 `prefix_sum_product_int_range(lv, numbers_size0)`，为 `sum += numbers[i]` 和 `product *= numbers[i]` 提供溢出安全条件。
  - 循环 invariant 维护 `sum == prefix_sum(lv, i)`、`product == prefix_product(lv, i)`，并保留 `out != 0` 与输出数组未初始化资源。
- `coins_8.v`
  - `Load "../spec/8".`
  - 新增 `list_int_range`、`prefix_sum`、`prefix_product`、`prefix_sum_product_int_range`。
  - 新增 `prefix_sum_snoc`、`prefix_product_snoc`。
  - 新增 `problem_8_spec_of_prefix_full`，用于 return 处桥接到题目规格。
- `C_8_goal.v` / `C_8_proof_auto.v` / `C_8_proof_manual.v` / `C_8_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 遇到的问题

1. `numbers_size@pre` 在 `Inv Assert` 中触发前端变量查找问题。

解决方式：在函数 `With` 中加入 ghost 参数：

```c
With lv (numbers0: Z) (numbers_size0: Z)
```

并在 `Require` 和 invariant 中维护 `numbers == numbers0`、`numbers_size == numbers_size0`。

2. 原始 `malloc_int_array` 规格返回 `IntArray::full`，但程序随后写入 `out[0]` 和 `out[1]`。

解决方式：将声明规格改为：

```c
Ensure __return != 0 && IntArray::undef_full(__return, size)
```

这样写数组时策略可直接拆分未初始化段。

3. `sum += numbers[i]` 和 `product *= numbers[i]` 需要证明结果仍在 `int` 范围。

解决方式：在前置条件和 invariant 中携带：

```c
prefix_sum_product_int_range(lv, numbers_size0)
```

并在 manual 中用 `prefix_sum_snoc` / `prefix_product_snoc` 将循环更新连接到下一个前缀。

## C_3 验证记录

### 结论

`C_3` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_3.v
coqc C_3_goal.v
coqc C_3_proof_auto.v
coqc C_3_proof_manual.v
coqc C_3_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_3.v C_3_proof_manual.v
```

无输出。

### 文件变更

- `C_3.c`
  - 功能性规格改为复用 `problem_3_pre` / `problem_3_spec`。
  - 增加 `list_int_range(l, operations_size)`。
  - 增加 `prefix_sums_int_range(l, operations_size)`。
  - 循环 invariant 携带长度、安全谓词、`problem_3_pre(l)` 和前缀非负性质。
  - 循环内存谓词使用 `IntArray::full(operations@pre, operations_size@pre, l)`，方便 return VC 归还函数入口数组所有权。
- `coins_3.v`
  - `Load "../spec/3".`
  - 新增 `list_int_range` 和 `prefix_sums_int_range`。
  - 新增前缀和推进引理。
  - 新增 `problem_3_spec true/false` 的桥接引理。
- `C_3_goal.v` / `C_3_proof_auto.v` / `C_3_proof_manual.v` / `C_3_goal_check.v`
  - 已由 `symexec --gen-and-backup` 重新生成并补完 manual。

### 遇到的问题

1. 功能性规格直接写 `<->` 无法被注解解析器接受。

解决方式：后置条件改成分支式：

```c
((__return != 0) && problem_3_spec(l, true) ||
 (__return == 0) && problem_3_spec(l, false))
```

2. 注解里直接写 Coq 风格的 `->` 会被解析成 C 的结构体成员访问。

表现：`symexec` 报 `No such member 'Znth'`。

解决方式：注解中的逻辑蕴含统一使用项目风格 `=>`。

3. `true` / `false` 不是默认可用的 Coq 常量。

解决方式：在 C 注解里显式声明：

```c
/*@ Extern Coq (true: bool) (false: bool) */
```

4. `problem_3_pre/spec` 需要通过本目录的桥接文件导入。

解决方式：新增 `coins_3.v`，并在 C 注解中写：

```c
/*@ Import Coq Require Import coins_3 */
```

5. `INT_MIN` 在数组逻辑表达式里直接展开容易被注解解析器卡住。

解决方式：不要在 C 注解里展开复杂范围公式，而是封装为 Coq 谓词：

```coq
Definition list_int_range ...
Definition prefix_sums_int_range ...
```

6. 循环 invariant 必须重复携带函数入口处的纯事实。

原因：循环体内的 safety VC 和 entail VC 主要依赖当前 invariant；`Require` 中的事实不会自动作为循环内可用事实保留。

7. 只读数组的 return VC 需要归还入口数组所有权。

问题写法：

```c
IntArray::full(operations, operations_size@pre, l)
```

更稳写法：

```c
IntArray::full(operations@pre, operations_size@pre, l)
```

这样生成的 return VC 中资源与后置条件一致。

### 关键引理

```coq
sum (sublist 0 i l) + Znth i l 0 =
sum (sublist 0 (i + 1) l)
```

用途：

- 证明 `num += operations[i]` 的结果等于下一个前缀和。
- 证明加法不溢出，结合 `prefix_sums_int_range`。
- 证明提前返回 `1` 时存在负前缀。
- 证明继续循环时前缀非负 invariant 得以推进。

## C_5 验证记录

当前文件：`C_5.c`

### 当前状态

已完成第一阶段改造：

- 去掉内部 `malloc`。
- 去掉返回结构体 `IntArray`。
- 改成调用方传入输出缓冲区 `out`。
- 额外传入 `out_size`，用它描述输出缓冲区长度。
- 函数返回 `int *`，返回值为 `out`。
- 已新增 `coins_5.v`。
- `symexec --gen-and-backup` 已成功生成：
  - `C_5_goal.v`
  - `C_5_proof_auto.v`
  - `C_5_proof_manual.v`
  - `C_5_goal_check.v`
- 已确认以下文件可编译：
  - `coins_5.v`
  - `C_5_goal.v`
  - `C_5_proof_auto.v`

manual 证明尚未完成。

最新尝试结论：

- `symexec --gen-and-backup`：通过。
- `coqc coins_5.v`：通过。
- `coqc C_5_goal.v`：通过。
- `coqc C_5_proof_auto.v`：通过。
- `C_5_proof_manual.v`：仍有 `Admitted.`，尚未达到最终验收标准。

### 采用的新接口

旧接口：

```c
IntArray intersperse(const int* numbers, int numbers_size, int delimeter)
```

新接口：

```c
int *intersperse(const int *numbers, int numbers_size, int delimeter, int *out)
```

当前接口：

```c
int *intersperse(const int *numbers, int numbers_size, int delimeter, int *out, int out_size)
```

当前版本已经允许空数组输入：

```c
0 <= numbers_size
```

输出长度使用分支式关系描述：

```c
(numbers_size == 0 && out_size == 0) ||
(0 < numbers_size && out_size == 2 * numbers_size - 1)
```

### 当前规格思路

- 输入数组：`IntArray::full(numbers, numbers_size, input_l)`
- 输出长度关系：空输入时 `out_size == 0`，非空输入时 `out_size == 2 * numbers_size - 1`
- 输出缓冲区：`IntArray::undef_full(out, out_size)`
- 返回值：`__return == out`
- 输出语义：存在 `output_l`，满足 `problem_5_spec(input_l, output_l, delimeter)`
- 输出内存：`IntArray::full(out, out_size, output_l)`

### 目前遇到的问题

1. 原始版本内部调用 `malloc`，验证需要建模分配成功/失败分支。

解决方式：按当前任务要求，把输出数组改成调用方传入，避免在程序内部建模 `malloc`。

2. 返回结构体会引入 `__return.data` / `__return.size` 的字段建模。

解决方式：改成返回 `int *`，让返回值只表达 `__return == out`。

3. 使用抽象函数 `intersperse_len(numbers_size)` 作为数组长度时，数组策略无法在第一次写 `out[0]` 时自动展开该长度函数。

解决方式：改为显式传入 `out_size`，并在前置条件中写：

```c
out_size == 2 * numbers_size - 1
```

内存谓词统一使用 `out_size`。

4. 循环 invariant 初始化时，`exists out_l` 太抽象，普通 `Inv` 会要求符号执行阶段自动猜出刚写完 `out[0]` 后的列表。

解决方式：使用 `Inv Assert`，把这类初始化义务留给 Coq witness。

5. `Inv Assert` 中直接使用 `numbers_size@pre` 会报变量查找错误。

解决方式：参考旧 `IntArray/C_5.c`，在 `Inv Assert` 中直接使用当前参数名 `numbers_size`、`numbers`、`out`、`delimeter`。

6. 加入 `out_size` 后，循环体写 `out[k]` 需要在 invariant 中显式保留输出长度关系。

解决方式：循环 invariant 中加入：

```c
out_size == 2 * numbers_size - 1 &&
0 < out_size && out_size < INT_MAX
```

### 后续 manual 证明预计难点

- 需要定义或证明“写完前 `i` 个输入元素后，输出前缀满足 `problem_5_spec(sublist 0 i input_l, out_l, delimeter)`”。
- 初始状态需要构造 `out_l = [Znth 0 input_l 0]`。
- 循环推进需要把 `out_l` 扩展为 `out_l ++ [delimeter; Znth i input_l 0]`。
- 需要连接 Coq `spec/5.v` 中基于 `nat` / `nth_error` / `Nat.Even` / `Nat.Odd` 的规格与 C 侧 `Z` 下标、`sublist`、`Znth` 表达。
- 当前规格已经通过 `out_size` 覆盖 `numbers_size == 0` 的空数组分支；manual 证明仍需要补齐。

### 本轮 manual 尝试的具体阻塞点

1. `intersperse_return_wit_1`，即 `numbers_size == 0` 的返回分支。

当前需要证明：

```coq
IntArray.undef_full out_pre 0 |-- IntArray.full out_pre 0 nil
problem_5_spec input_l nil delimeter_pre
```

可行方向：

- 从 `IntArray.full numbers_pre 0 input_l` 推出 `Zlength input_l = 0`，再推出 `input_l = nil`。
- 使用 `ArrayLib` 里的 `undef_full_empty` 和 `full_empty` 处理空数组内存。
- 补一个纯引理：`input_l = nil -> problem_5_spec input_l nil d`。

2. `intersperse_entail_wit_1`，即写入 `out[0]` 后建立循环 invariant。

当前需要选择 witness：

```coq
out_l = [Znth 0 input_l 0]
```

同时需要证明：

```coq
problem_5_spec (sublist 0 1 input_l) [Znth 0 input_l 0] delimeter
```

阻塞原因：

- `problem_5_spec` 使用 `nat`、`length`、`nth_error`、`Nat.Even`、`Nat.Odd`。
- C 侧状态使用 `Z`、`sublist`、`Znth`。
- 需要专门的单元素列表桥接引理。

3. `intersperse_entail_wit_2`，即循环推进。

需要证明从旧输出前缀：

```coq
problem_5_spec (sublist 0 i input_l) out_l delimeter
```

推进到新输出前缀：

```coq
problem_5_spec (sublist 0 (i + 1) input_l)
               (out_l ++ [delimeter; Znth i input_l 0])
               delimeter
```

阻塞原因：

- 这是一个较重的纯列表引理，涉及偶数位/奇数位的 `nth_error` 映射。
- 同时还需要数组段合并：
  - `IntArray.seg out 0 k out_l`
  - `out[k] = delimeter`
  - `out[k+1] = Znth i input_l 0`
  - 合并成 `IntArray.seg out 0 (k+2) new_out_l`

4. `intersperse_return_wit_2`，即非空正常返回。

需要证明：

```coq
i >= numbers_size
i <= numbers_size
==> i = numbers_size
```

然后把：

```coq
problem_5_spec (sublist 0 i input_l) out_l delimeter
```

转换成：

```coq
problem_5_spec input_l out_l delimeter
```

还需要证明：

```coq
k = out_size
IntArray.seg out 0 k out_l *
IntArray.undef_seg out k out_size
|-- IntArray.full out out_size out_l
```

阻塞原因：

- 需要 `sublist 0 (Zlength input_l) input_l = input_l`。
- 需要从 `IntArray.full numbers numbers_size input_l` 提取 `Zlength input_l = numbers_size`。
- 需要空 `undef_seg` 和 `seg/full` 合并相关引理。

### 建议的下一步

当前直接用 `problem_5_spec` 做循环 invariant 会导致每轮循环都要处理 `nat` 偶奇下标证明，manual 成本很高。

更推荐的下一步是：

1. 在 `coins_5.v` 中定义一个 C 侧更容易验证的函数：

```coq
Fixpoint intersperse_list (l : list Z) (d : Z) : list Z := ...
```

2. 把 C invariant 改成维护精确输出前缀：

```c
IntArray::seg(out, 0, k, intersperse_list(sublist(0, i, input_l), delimeter))
```

3. 最后只在 return 处证明一次桥接：

```coq
problem_5_spec input_l (intersperse_list input_l delimeter) delimeter
```

这样可以避免在每次循环推进时反复展开 `problem_5_spec` 的 `Nat.Even` / `Nat.Odd` 条件。

### 最新验证尝试：2026-04-14

本轮已按上面的推荐方向改造并验证到中间状态：

- `C_5.c` 的循环 invariant 已改为维护精确输出前缀：

```c
IntArray::seg(out, 0, k, intersperse_list(sublist(0, i, input_l), delimeter))
```

- 为了让 return VC 能关联入口参数，函数规格中额外引入 ghost 参数：

```c
With input_l (numbers0: Z) (numbers_size0: Z) (delimeter0: Z) (out0: Z) (out_size0: Z)
```

- `Require` 中绑定真实参数和 ghost 参数，例如 `out == out0`、`numbers_size == numbers_size0`。
- `Ensure` 中使用 ghost 参数表达入口状态，例如 `__return == out0`、`IntArray::full(out0, out_size0, output_l)`。
- 内存资源仍使用真实程序变量，以便数组读写策略能匹配 `numbers[0]`、`out[k]` 等访问。

已新增并通过编译的辅助定义/引理：

```coq
Fixpoint intersperse_list (input : list Z) (d : Z) : list Z := ...

Lemma intersperse_list_snoc_nonempty : ...
Lemma intersperse_list_sublist_one : ...
Lemma intersperse_list_sublist_snoc : ...
```

当前验证结果：

- `symexec --gen-and-backup`：通过。
- `coqc coins_5.v`：通过。
- `coqc C_5_goal.v`：通过。
- `coqc C_5_proof_auto.v`：通过。
- `coqc C_5_proof_manual.v`：在保留 1 个 `Admitted.` 的情况下可编译。

manual 当前进展：

- `proof_of_intersperse_entail_wit_1`：已完成。
- `proof_of_intersperse_entail_wit_2`：已完成。
- `proof_of_intersperse_return_wit_1`：已完成。
- `proof_of_intersperse_return_wit_2`：尚未完成。

剩余阻塞点：

`proof_of_intersperse_return_wit_2` 的内存部分可以推进到把 `seg + undef_seg(empty)` 合成完整输出数组；真正剩余的是功能性桥接：

```coq
problem_5_spec input_l (intersperse_list input_l delimeter0) delimeter0
```

这个桥接需要证明递归定义的 `intersperse_list` 满足 `spec/5.v` 中基于 `nth_error`、`Nat.Even`、`Nat.Odd`、`Nat.div` 的逐下标规格。后续建议在 `coins_5.v` 中补一组独立引理：

- `length (intersperse_list input d) = 2 * length input - 1`（非空输入）。
- 偶数下标映射到原输入的 `i / 2`。
- 奇数下标恒为 `Some d`。
- 最后封装成 `problem_5_spec_intersperse_list`。

然后 `proof_of_intersperse_return_wit_2` 应只需调用该桥接引理，并完成最后的数组段合并。

### 最新验证尝试：2026-04-15（已完成）

本轮已完成 `C_5` 全链验收。

通过结果：

- `symexec`（含 `-IQCP_examples/`）：通过。
- `coqc coins_5.v`：通过。
- `coqc C_5_goal.v`：通过。
- `coqc C_5_proof_auto.v`：通过。
- `coqc C_5_proof_manual.v`：通过。
- `coqc C_5_goal_check.v`：通过。

清理结果：

- 已删除 `C_5_proof_manual_backup*.v`（共 12 个），仅保留当前 `C_5_proof_manual.v`。

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_5.v C_5_proof_manual.v
```

无输出。

本轮修复点（与 Coq 8.20.1 兼容相关）：

- `coins_5.v`
  - 调整 `intersperse_list_nth_even` / `intersperse_list_nth_odd` 的证明脚本，避免重复引入同名 binder。
  - 显式使用 `(%nat)`，修复 `Nat.div` 与 `Z_scope` 冲突。
- `C_5_proof_manual.v`
  - 补全 `proof_of_intersperse_return_wit_2` 的长度桥接与内存合并步骤。
  - 使用 `IntArray.full_length` + `sublist_self` 完成 `sublist 0 n l = l`。
  - 使用 `IntArray.seg_to_full` 与空 `undef_seg` 归约完成输出数组资源合并。

本轮新增可复用踩坑记录（建议后续题目优先排查）：

1. `coqc` 在终端里可能直接不可用。

表现：`coqc: command not found`。

处理：先执行

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
```

再编译。

2. `IntArrayClaude` 目录没有 `_CoqProject`。

处理：复用 `../IntClaude/_CoqProject` 生成 `COQINCLUDES`，否则 load-path 不完整。

3. `symexec` 可能报 `verification_stdlib.h` 找不到。

处理：命令里补 `-IQCP_examples/`，否则 `C_XX.c` 的公共头文件无法解析。

4. `Local Open Scope Z_scope` 下，`/` 默认按 `Z` 除法解释。

表现：在 `Nat.div` 相关证明里出现 `nat/Z` 类型冲突。

处理：显式写 `(%nat)`，例如 `((2 * k) / 2)%nat`。

5. Coq 8.20.1 下某些引理会触发“同名变量重复引入”（如 `k is already used`）。

处理：先 `intros` 后 `revert`，再 `induction`，避免在分支里重复引入同名 binder。

6. `prop_apply ... Intros` 有时会引入额外 `model` witness，导致后续 `sep_apply` 匹配失败（常见报错：`No matching clauses for match`）。

处理：仅为拿纯事实时，优先 `prop_apply ...`（不 `Intros`）后接 `entailer!` 归一化，再做 `sep_apply`。

7. `pre_process` 生成的假设名不稳定（`H5`/`H6` 等会变化），直接写死变量名容易在后续改动后失效。

处理：用 `match goal with` 按“公式形状”提取长度事实，再喂给 `sublist_self`。

8. 返回态内存合并时，顺序很关键。

推荐顺序：先用 `Hk` 对齐下标，再 `seg_to_full`，最后把 `undef_seg out out_size out_size` 化成 `emp`（`undef_seg_empty`），再 `entailer!`。

### 原始风险记录

这题原始版本比 `C_3` 复杂很多，不能直接套只读扫描模板。

主要风险：

- 返回值是结构体 `IntArray`，需要描述 `__return.data` 和 `__return.size`。
- 程序调用 `malloc`，规格必须决定是否建模分配成功和失败分支。
- `numbers_size == 0` 时返回 `data = NULL, size = 0`，需要单独分支。
- 非空时输出长度是 `2 * numbers_size - 1`，前置条件必须保证该表达式和后续 `malloc` 大小计算安全。
- 输出数组内容是输入元素之间插入 `delimeter`，需要定义输出列表函数，例如 `intersperse_f numbers delimeter`。
- 输入数组只读，应保持 `IntArray::full(numbers, numbers_size, input_l)`。
- 输出数组是新分配内存，后置条件需要描述 `IntArray::full(__return.data, __return.size, output_l)`，或者保留 `malloc == NULL` 失败分支。

建议后续步骤：

1. 先看 `spec/5.v`，决定是否直接复用已有 `problem_5_pre/spec`。
2. 在 `coins_5.v` 中定义 C 侧方便使用的输出列表函数和长度引理。
3. 决定是否把 `malloc` 成功作为前置假设，还是验证 `NULL` 返回分支。
4. 若保留失败分支，后置条件要分成 `data == NULL` 和 `data != NULL` 两类。
5. 写循环 invariant 时同时维护：
   - 已写输出前缀内容。
   - 输出数组已写前缀与未写后缀的内存资源。
   - `k == 2 * i - 1` 或等价的输出下标关系。

## C_9 验证记录

### 结论

- 状态：已全链通过。
- 语义：支持负数输入，`max` 初始化为 `INT_MIN`（C 里写作 `-2147483647 - 1`）。
- 验收链：

```bash
coqc coins_9.v
coqc C_9_goal.v
coqc C_9_proof_auto.v
coqc C_9_proof_manual.v
coqc C_9_goal_check.v
```

- 扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_9.v C_9_proof_manual.v
```

无输出。

### 文件变更

- `C_9.c`
  - 函数维持“输出写入预分配数组并返回 `out`”接口风格。
  - `max` 初值改为 `-2147483647 - 1`（等价于 `INT_MIN`）。
  - 循环 invariant 语义起点改为 `INT_MIN`，并显式携带 `list_int_range(lv)`。
- `coins_9.v`
  - 重建 `running_max_val` / `rolling_max_f`。
  - 增加 `sublist snoc` 推进引理与 `problem_9_spec` 桥接引理。
  - 适配 Coq 8.20.1：`length_firstn`、更稳的 `nth_firstn` 侧条件处理。
- `C_9_proof_manual.v`
  - 补完 4 个 witness：初始化态、两条分支态、return 态。
  - return 态完成 `seg + undef_seg(empty) -> full` 合并，并调用 `problem_9_spec_rolling_max_f`。

### 关键问题与处理

1. `symexec` 对 `INT_MIN/INT_MAX` 宏识别不稳定。
  处理：在 C 代码里直接使用字面量 `-2147483647 - 1`。

2. return witness 缺少功能桥接前提。
  处理：把 `list_int_range(lv)` 保留在循环 invariant 里，确保 return VC 可直接获得该纯条件。

3. manual 脚本里假设名易漂移（`H4/H5/...`）。
  处理：关键处改为 `match goal with` 按公式形状提取长度/语义等式，降低重生成后脆弱性。

### 最新验收与清理：2026-04-15（继续）

- 重新验收（在外部改动后）：
  - `coqc coins_9.v`：通过。
  - `coqc C_9_goal.v`：通过。
  - `coqc C_9_proof_auto.v`：通过。
  - `coqc C_9_proof_manual.v`：通过。
  - `coqc C_9_goal_check.v`：通过。
- 占位扫描复核：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_9.v C_9_proof_manual.v
```

无输出。

- 清理结果：
  - 已删除 `C_9_proof_manual_backup*.v`。
  - 已删除 `C_9` 与 `coins_9` 的中间编译产物（`.vo/.vok/.vos/.glob/.aux` 及隐藏 `.aux`）。

## C_25 验证记录

### 结论

- 状态：已全链通过。
- 当前接口：`factorize` 返回 `IntArray *`，结构体和内部 `data` 数组均在函数内通过自定义 malloc 建模分配。
- 当前已完成：
  - `symexec --gen-and-backup` 已生成 `C_25_goal.v` / `C_25_proof_auto.v` / `C_25_proof_manual.v` / `C_25_goal_check.v`。
  - `coins_25.v`、`C_25_goal.v`、`C_25_proof_auto.v`、`C_25_proof_manual.v`、`C_25_goal_check.v` 均可编译。
  - `C_25_proof_manual.v` 中循环初始化、整除分支、不整除分支和 return witness 均已补完。
  - `coins_25.v` 与 `C_25_proof_manual.v` 扫描无 `Admitted.` / `Axiom`。

### 文件变更

- `C_25.c`
  - 函数规格复用 `problem_25_pre_z` / `problem_25_spec_z`。
  - 循环条件使用 `i <= n / i`，避免 `i * i <= n` 在 C 层产生乘法溢出安全义务。
  - 循环 invariant 维护输出数组的已写前缀 `IntArray::seg(data, 0, size, factors)` 和未写后缀 `IntArray::undef_seg(data, size, n0)`。
  - invariant 同时记录 `size == Zlength(factors)`、`size + n <= n0`、`factorize_loop_state n0 n i factors` 等当前用于安全和内存验证的事实。
- `coins_25.v`
  - `factorize_loop_state` 已升级为功能型强不变式，除范围和长度余量外，还记录：
    - `zprod factors * n = n0`。
    - `Sorted Z.le factors`。
    - `Forall zprime factors`。
    - `Forall (fun x => x <= i) factors` 和 `Forall (fun x => x <= n) factors`。
    - `no_small_factor n i`。
  - 新增并使用的桥接定义/引理：
    - `zprod` / `zprime` / `no_small_factor`。
    - `problem_25_spec_z_of_state_exit`：从 Z 层有序、乘积、素性和尾元素关系推出 `problem_25_spec_z`。
    - `divisor_prime_from_no_small`：若 `i` 整除当前 `n` 且不存在更小因子整除 `n`，则 `i` 为素数。
    - `no_small_factor_after_div` / `no_small_factor_after_skip`：维护“无小因子”性质的两个分支引理。
    - `final_prime_from_no_small_exit`：循环退出时证明剩余 `n` 为素数。
- `C_25_proof_manual.v`
  - 已闭合 `proof_of_factorize_entail_wit_1`。
  - 已闭合 `proof_of_factorize_entail_wit_2_1`：整除分支将单元写入转成 `seg_single`，再用 `seg_merge_to_seg` 合并成更长前缀。
  - 已闭合 `proof_of_factorize_entail_wit_2_2`：不整除分支用 `Z.quot_lt` 证明 `i + 1 <= n0`，从而维护下一轮范围。
  - 已闭合 `proof_of_factorize_return_wit_1`：合并最后一个数组单元，并用强不变式推出 `problem_25_spec_z n0 (factors ++ [n])`。

### 遇到的问题

1. return witness 需要证明真正的质因数分解规格。
   处理：把 `factorize_loop_state` 升级为强不变式，记录乘积关系、已输出因子的素性/有序性、当前 `n` 无小因子等语义信息，从而推出：

```coq
problem_25_spec_z n0 (factors ++ n :: nil)
```

2. 一开始无法解释“写入输出数组的元素一定是素数”。
   原因：程序写入数组的时机只是发现 `i | n`，但“一个因子是素数”并不是由整除本身推出的。例如如果没有额外信息，`i = 4` 整除某个数时并不能说明 `4` 是素数。
   处理：在循环不变式中增加 `no_small_factor n i`，表示当前 `n` 没有小于 `i` 的因子。这样当分支中发现 `i | n` 时，`i` 就是当前 `n` 的最小因子；最小的大于 1 的因子必为素数，因此可以用 `divisor_prime_from_no_small` 证明写入的 `i` 是素数。

3. 仅靠范围类 invariant 不足以证明 `n` 在循环结束时为素数。
   处理：新增 `no_small_factor n i`，并用 `final_prime_from_no_small_exit` 将退出条件 `i > n ÷ i` 桥接为 `zprime n`。

4. 整除分支如果要证明功能性保持，还需要同时维护乘积关系。
   处理：用 `divisor_prime_from_no_small` 证明当前写入的 `i` 为素数，并维护 `zprod (factors ++ [i]) * (n ÷ i) = n0`。

5. 整除分支执行 `i -= 1` 后，下一轮循环会再次检查同一个因子。
   原因：`for` 循环末尾还会执行 `i++`，所以分支内先 `i -= 1`，循环更新后 `i` 回到原值。这是为了处理重复质因子，例如 `8 -> [2, 2, 2]`。
   验证影响：不变式必须允许除去一个 `i` 后继续保持 `no_small_factor (n / i) i`，否则无法证明下一轮继续从同一因子检查是安全且完整的。对应处理是增加并使用 `no_small_factor_after_div`。

6. 输出数组容量选择为 `n0`，但实际输出长度事先未知。
   原因：质因数个数最多不会超过原始输入 `n0`，但在函数执行前无法精确知道最终个数。
   处理：内部用 `malloc_int_array(n)` 分配 `n0` 长度的数组，后置条件只暴露已写前缀 `IntArray::seg(data, 0, output_size, output_l)`，并保留未写后缀 `IntArray::undef_seg(data, output_size, n0)`。循环中用 `size + n <= n0` 保证每次写入不会越界。

7. 这题的证明失败主要不是 C 程序内存模型问题，而是缺少数论语义。
   表现：数组 `seg/undef_seg` 的合并可以处理，但 return 处无法自动得到 `problem_25_spec_z`，尤其无法得到“所有输出元素为素数”和“最后剩余的 `n` 为素数”。
   处理：把这些数学事实放进 `coins_25.v` 的强不变式和辅助引理，而不是只在 C 注解里写范围条件。

### 后续注意

- 后续如果重新生成 goal 文件，manual 中涉及强不变式的证明可能需要按新的 hypothesis 名称微调。
- 这题的关键不是数组内存，而是数论事实：最小因子为素数，退出时剩余数为素数。

## C_26 验证记录

### 结论

- 状态：已全链通过。
- 当前接口：`remove_duplicates` 返回 `IntArray *`，结构体和内部 `data` 数组在函数内分配；临时数组 `has1` / `has2` 在返回前释放。
- 当前已完成：
  - `symexec --gen-and-backup` 已生成 `C_26_goal.v` / `C_26_proof_auto.v` / `C_26_proof_manual.v` / `C_26_goal_check.v`。
  - `coins_26.v`、`C_26_goal.v`、`C_26_proof_auto.v`、`C_26_proof_manual.v`、`C_26_goal_check.v` 均可编译。
  - `C_26_proof_manual.v` 中 `contains`、第一轮循环、第二轮循环和 return witness 均已补完。
  - `coins_26.v` 与 `C_26_proof_manual.v` 扫描无 `Admitted.` / `Axiom` / `entailer!`。

已通过的验收链：

```bash
coqc coins_26.v
coqc C_26_goal.v
coqc C_26_proof_auto.v
coqc C_26_proof_manual.v
coqc C_26_goal_check.v
```

### 文件变更

- `C_26.c`
  - 参考 `C_25.c` 的结构体返回风格，引入 `malloc_int_array_struct`、`malloc_int_array` 和 `free_int_array` wrapper。
  - `malloc_int_array` 的规格返回 `IntArray::undef_full(__return, size)`，用于后续逐个写入输出数组和临时数组。
  - `free_int_array` 只在释放临时数组时消费 `seg + undef_seg`，不把临时数组资源写进函数后置条件。
  - `contains` 保持原程序结构，只补必要 invariant：入口参数不变、长度一致、已扫描前缀不含目标值、数组资源保持。
  - `remove_duplicates` 保持原两轮算法：
    - 第一轮用 `has1` 记录见过一次的值，用 `has2` 记录重复值。
    - 第二轮把不在 `has2` 中的输入元素写入 `data`。
  - 循环 invariant 只保留验证需要的抽象谓词：
    - `remove_duplicates_first_loop(input_l, i, has1_l, has2_l)`。
    - `remove_duplicates_second_loop(input_l, has2_l, i, output_l)`。
    - 必要的指针非空、长度、数组 `seg/undef_seg/full` 资源。
- `coins_26.v`
  - `Load "../spec/26".`
  - 新增 `list_contains` / `list_not_contains`，作为 `contains` 的规格谓词。
  - 新增 `seen_values_aux` / `seen_values` / `duplicate_values`，建模第一轮循环的 `has1` 和 `has2`。
  - 新增 `filter_not_in`，建模第二轮输出。
  - 新增循环推进引理：
    - `first_loop_add_duplicate`
    - `first_loop_add_seen`
    - `first_loop_skip_duplicate`
    - `second_loop_add_output`
    - `second_loop_skip_output`
  - 新增 return 处规格桥接引理：
    - `duplicate_values_correct`
    - `filter_not_in_In_iff`
    - `filter_not_in_order`
    - `problem_26_spec_filter_not_in_duplicate_values`
    - `problem_26_spec_from_loops`
- `C_26_proof_manual.v`
  - `contains` 的两个 return 分支分别用 `In_Znth_exists` 和 `Znth_In_range` 连接数组读取与列表成员关系。
  - 第一轮三个分支分别使用 `first_loop_add_duplicate`、`first_loop_add_seen`、`first_loop_skip_duplicate`。
  - 第二轮两个分支分别使用 `second_loop_add_output`、`second_loop_skip_output`。
  - return witness 选择当前 `data_2 output_l_2 output_size_2`，再用 `problem_26_spec_from_loops` 从两个循环谓词推出 `problem_26_spec input_l output_l_2`。

### 遇到的问题

1. 一开始试图把去重写成额外的 C helper，例如 `write_unique`。
   处理：回到“尽量保持原程序不变”的原则，只给现有 `contains` 和两轮循环补规格与 invariant，不引入新的程序逻辑。

2. `has1` / `has2` 是中间变量，不应该出现在函数后置条件中。
   处理：函数后置条件只暴露返回结构体、输入数组资源和最终 `problem_26_spec`；`has1` / `has2` 的语义只放在循环 invariant 和 `coins_26.v` 的中间谓词中。

3. 临时数组不能直接从 separation logic 资源中消失。
   原因：`malloc_int_array` 产生的 `IntArray::seg/undef_seg` 资源必须被消费或归还，不能在 return 前凭空丢掉。
   处理：新增 `free_int_array` wrapper，规格为消费一个已初始化前缀和未初始化后缀，后置条件 `emp`。程序返回前释放 `has1` 和 `has2`。

4. annotation 过于繁杂时可读性很差。
   处理：不在 C 注解中展开“重复元素”“输出顺序”等复杂性质，而是封装为：

```c
remove_duplicates_first_loop(input_l, i, has1_l, has2_l)
remove_duplicates_second_loop(input_l, has2_l, i, output_l)
```

复杂列表语义放到 `coins_26.v` 中证明。

5. 不需要单独写 `list_in_range`。
   原因：本题数组内容通过 `IntArray::full/seg` 和 `Zlength` 描述，当前 VC 不需要额外元素范围谓词。
   处理：移除无用范围谓词，避免前置条件和 invariant 膨胀。

6. `contains` 的 invariant 中可以省掉很多 `@pre` 等式，但不能省掉会被循环体安全 VC 使用的入口参数事实。
   处理：最终保留 `a == a@pre && n == n@pre && x == x@pre`、`n == Zlength(l)` 和前缀不含目标值；没有把这些事实写进 `contains` 后置条件。

7. `@pre`/ghost 变量的可读性问题。
   处理：这题没有引入 `numbers0` / `a0` 这类额外 ghost 参数；能用 `@pre` 的地方按 LLM_friendly_cases 风格直接使用 `numbers@pre`、`numbers_size@pre`。

8. return 处最难的不是数组资源，而是把两轮循环结果桥接到 `problem_26_spec`。
   处理：在 `coins_26.v` 中证明：
   - `duplicate_values [] [] input` 恰好表示出现至少两次的值。
   - `filter_not_in duplicates input` 中的元素来自输入、且不在重复集合中。
   - `filter_not_in` 保持输入相对顺序。
   - 因而 `filter_not_in (duplicate_values [] [] input) input` 满足 `problem_26_spec`。

9. 证明 `duplicate_values_correct_aux` 时，`auto` 容易提前关闭某些分支，导致后续 bullet/brace 报 `No such goal` 或 `Wrong bullet`。
   处理：相关证明分支改成显式 destruct 和显式构造，不依赖过强的 `auto`。

10. 修改 `coins_26.v` 后，旧的 `C_26_goal.vo` 会与新库不一致。
    表现：编译 `C_26_proof_manual.v` 报 `makes inconsistent assumptions over library SimpleC.EE.coins_26`。
    处理：按依赖顺序重新编译 `coins_26.v`、`C_26_goal.v`、`C_26_proof_manual.v`，再编译 `C_26_proof_auto.v` 和 `C_26_goal_check.v`。

### 后续注意

- 如果重新运行 symbolic execution，需要重新检查全部 manual witness；当前 manual proof 的假设名如 `H18` / `H19` 可能因 VC 变化而需要微调。
- 本题后续类似程序可以沿用这个模式：C 注解只写抽象循环谓词，复杂列表语义放在 `coins_XX.v` 的桥接引理里。
- 临时 malloc 出来的数组若不返回给调用者，必须用 wrapper 在 C 程序中显式消费资源。

## C_40 验证记录

### 结论

- 状态：已全链通过。
- 当前函数：`triples_sum_to_zero`，只读输入数组，三层循环寻找三个互不相同元素之和为 0。
- 当前已完成：
  - `C_40.c` 已补完函数规格和三层循环 invariant。
  - `coins_40.v` 已补完三元组扫描谓词、整数溢出安全谓词和 `problem_40_spec` 桥接引理。
  - `C_40_proof_manual.v` 已补完 manual witness，包括加法安全、三层循环推进和两个 return 分支。
  - `coins_40.v` 与 `C_40_proof_manual.v` 扫描无 `Admitted.` / 手写 `Axiom`。

已通过的验收链：

```bash
coqc coins_40.v
coqc C_40_goal.v
coqc C_40_proof_auto.v
coqc C_40_proof_manual.v
coqc C_40_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_40.v C_40_proof_manual.v
```

无输出。

本次记录更新时的环境复核：当前 shell 中 `coqc` 不在 `PATH`，直接执行 `coqc coins_40.v` 报 `coqc: command not found`。后续如果需要在终端复跑，先参考 `C_5` 记录中的 `opam env --switch=coq8201` 和 load-path 处理。

### 文件变更

- `C_40.c`
  - 函数规格复用 `problem_40_pre` / `problem_40_spec`。
  - 前置条件增加 `triple_sum_int_range(input_l, l_size)`，为表达式 `l[i] + l[j] + l[k]` 的两步加法提供安全条件。
  - 三层循环分别使用 `scanned_i`、`scanned_j`、`scanned_k` 记录已经排除的搜索空间。
  - invariant 保留入口数组资源 `IntArray::full(l@pre, l_size@pre, input_l)`，并在外层/中层维护 `j`、`k` 的未初始化局部变量资源。
- `coins_40.v`
  - `Load "../spec/40".`
  - 新增 `triple_sum_int_range` 和 `triple_sum_zero`。
  - 新增扫描谓词 `scanned_i` / `scanned_j` / `scanned_k`，按三层循环分别描述：
    - 已完成的所有 `p < i` 的三元组不存在和为 0。
    - 当前 `i` 下已完成的所有 `q < j` 的组合不存在和为 0。
    - 当前 `i, j` 下已完成的所有 `r < k` 的组合不存在和为 0。
  - 新增初始化和推进引理：
    - `scanned_i_init`
    - `scanned_j_init`
    - `scanned_k_init`
    - `scanned_k_step`
    - `scanned_j_step`
    - `scanned_i_step`
  - 新增 return 桥接引理：
    - `problem_40_spec_true_of_triple`
    - `problem_40_spec_false_of_scanned_i`
    - `scanned_i_no_ordered_triple`
    - `scanned_i_no_distinct_triple`
- `C_40_proof_manual.v`
  - `safety_wit_6` / `safety_wit_7` 使用 `triple_sum_int_range` 分别证明两步加法的 int 范围。
  - `entail_wit_1` 到 `entail_wit_3` 使用扫描谓词初始化引理。
  - `entail_wit_4` 到 `entail_wit_6` 使用三层扫描推进引理，并处理局部变量 `j` / `k` 的 `undef_data_at` 与 `store_int_undef_store_int`。
  - `return_wit_1` 从 `scanned_i input_l l_size_pre i` 和 `i >= l_size_pre` 推出不存在任意 distinct 三元组，进而得到 `problem_40_spec input_l false`。
  - `return_wit_2` 从当前命中的 `i < j < k` 与和为 0，推出 `problem_40_spec input_l true`。

### 遇到的问题

1. 三层循环的“已经搜索过哪些组合”如果只写范围条件不够。
   处理：按循环层级拆成 `scanned_i` / `scanned_j` / `scanned_k`，每一层只负责当前循环已经排除的组合；循环退出时再用 step 引理把内层扫描结果提升到外层。

2. `problem_40_spec` 使用任意三个不同下标，而 C 程序只按 `i < j < k` 搜索。
   处理：在 `coins_40.v` 中证明 `scanned_i_no_distinct_triple`，把任意三个 distinct 下标按大小关系排列成有序三元组，再复用 `scanned_i_no_ordered_triple` 排除。

3. true 分支需要把 Z 下标转换成 spec 中的 nat 下标。
   处理：`problem_40_spec_true_of_triple` 使用 `Z.to_nat` 构造三个 witness，并用 `Zlength_correct`、`Z2Nat.id`、`Nat2Z.inj_lt` 桥接范围证明。

4. `l[i] + l[j] + l[k]` 在 C 层会拆成两次加法安全 VC。
   处理：`triple_sum_int_range` 同时记录 `Znth i l 0 + Znth j l 0` 和再加 `Znth k l 0` 的范围；manual 中两个 safety witness 分别取这两个结论。

5. 中层和外层循环推进时会重新初始化内层局部变量。
   处理：外层 invariant 带 `undef_data_at(&j) * undef_data_at(&k)`，中层 invariant 带 `undef_data_at(&k)`；对应 entail witness 中使用 `store_int_undef_store_int` 恢复下一层需要的局部变量资源。

### 后续注意

- 后续类似“多重循环搜索某个组合”的题，可以沿用 `scanned_i/scanned_j/scanned_k` 这种分层扫描谓词，而不是直接在 invariant 中展开完整的 `forall`。
- 如果目标 spec 用无序 distinct 下标，而程序按有序下标枚举，建议把“任意 distinct 三元组可排序成有序三元组”的桥接放在 `coins_XX.v`，C annotation 中只保留抽象扫描谓词。
- 多项整数表达式的溢出安全要按 C 实际求值顺序建模；这里需要同时证明二元和与三元和都在 `int` 范围。

## C_42 验证记录

### 结论

- 状态：已全链通过。
- 当前接口：`IntArray *incr_list(int *l, int l_size)`，不再要求调用者传入预分配 `out`。
- 当前已完成：
  - `C_42.c` 已改为函数内部调用 `malloc_int_array_struct()` 分配返回结构体，并调用 `malloc_int_array(l_size)` 分配内部 `data` 数组。
  - `coins_42.v` 已新增并通过编译。
  - `symexec --gen-and-backup` 已刷新 `C_42_goal.v` / `C_42_proof_auto.v` / `C_42_proof_manual.v` / `C_42_goal_check.v`。
  - `C_42_proof_manual.v` 中所有 manual witness 已补完。
  - `coins_42.v` 与 `C_42_proof_manual.v` 扫描无 `Admitted.` / 手写 `Axiom`。

已通过的验收链：

```bash
coqc coins_42.v
coqc C_42_goal.v
coqc C_42_proof_auto.v
coqc C_42_proof_manual.v
coqc C_42_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_42.v C_42_proof_manual.v
```

无输出。

### 文件变更

- `C_42.c`
  - 函数签名从 `void incr_list(int *l, int l_size, int *out)` 改为 `IntArray *incr_list(int *l, int l_size)`。
  - 参考 `C_25.c` 新增 `IntArray` 结构体定义、`malloc_int_array_struct` 声明和 `malloc_int_array` 声明。
  - `malloc_int_array_struct` 规格返回结构体两个字段的 `undef_data_at`，`malloc_int_array` 规格返回 `IntArray::undef_full(__return, size)`。
  - 前置条件保留输入数组 `IntArray::full(l, l_size, input_l)`，并增加：
    - `l_size == Zlength(input_l)`
    - `problem_42_pre(input_l)`
    - `list_incr_int_range(input_l)`
  - 后置条件返回 `__return` 指向的结构体，并暴露：
    - `data_at(&(__return -> data), data)`
    - `data_at(&(__return -> size), output_size)`
    - `output_size == l_size`
    - `output_l == map_incr(input_l)`
    - `problem_42_spec(input_l, output_l)`
    - `IntArray::full(data, output_size, output_l)`
  - 循环 invariant 维护已写前缀：
    - `data_at(&(out -> data), data)`
    - `data_at(&(out -> size), l_size)`
    - `IntArray::seg(data, 0, i, map_incr(sublist(0, i, input_l)))`
    - `IntArray::undef_seg(data, i, l_size)`
- `coins_42.v`
  - `Load "../spec/42".`
  - 新增 `map_incr`，定义为对每个元素加 1。
  - 新增 `list_incr_int_range`，用于证明 `l[i] + 1` 不溢出。
  - 新增 `map_incr_Zlength`，用于 return 处证明结构体 `size` 与输出列表长度一致。
  - 新增 `map_incr_sublist_snoc`，用于循环体写入后把单元素合并进已写前缀。
  - 新增 `problem_42_spec_map_incr`，把 `map_incr input_l` 桥接到题目原始 `problem_42_spec`。
- `C_42_proof_manual.v`
  - `safety_wit_3` 使用 `list_incr_int_range` 证明 `Znth i input_l 0 + 1` 在 int 范围内。
  - `entail_wit_1` 将 `IntArray::undef_full` 转成 `undef_seg`，并用空 `seg` 初始化循环不变式。
  - `entail_wit_2` 用 `map_incr_sublist_snoc`、`IntArray.seg_single` 和 `IntArray.seg_merge_to_seg` 维护已写前缀。
  - `return_wit_1` 选择返回结构体中的 `data_2`、`l_size_pre` 和 `map_incr input_l` 作为 witness，用 `sublist_self`、`IntArray.seg_to_full` 和空 `undef_seg` 把完整已写前缀转成内部数组的 `IntArray::full`，再用 `problem_42_spec_map_incr` 与 `map_incr_Zlength` 完成功能性规格和长度字段证明。

### 遇到的问题

1. 原接口把 `out` 作为输入参数，不符合当前需求。
   处理：参考 `C_25.c` 的结构体返回模式，先分配 `IntArray` 结构体，再分配内部 `data` 数组，函数返回 `IntArray *`。

2. 只写 `map_incr(sublist 0 i input_l)` 不足以自动证明循环推进。
   处理：在 `coins_42.v` 中补 `map_incr_sublist_snoc`，明确说明写入第 `i` 个元素后，前缀从 `sublist 0 i` 推进到 `sublist 0 (i + 1)`。

3. 题目 spec 使用 Coq `length` 和 `nth` 的 nat 下标，而验证中数组长度和下标主要是 Z。
   处理：`problem_42_spec_map_incr` 放在 `coins_42.v` 中证明；C annotation 中只暴露 `problem_42_spec(input_l, map_incr(input_l))`。

4. `l[i] + 1` 会产生 int 溢出 safety VC。
   处理：前置条件增加 `list_incr_int_range(input_l)`，manual 中直接取当前下标 `i` 的范围事实。

5. 空前缀初始化时，`IntArray::undef_full` 不能直接匹配 `seg + undef_seg`。
   处理：先用 `IntArray.undef_full_to_undef_seg`，再用 `IntArray.seg_empty` 生成空 `seg`。

### 后续注意

- 这类“输入数组只读、输出数组逐项写满并以结构体返回”的题，可以沿用 `C_25` / `C_42` 模式：结构体字段用 `data_at` 保留，内部数组由 `malloc_int_array` 返回 `undef_full`，循环 invariant 使用 `seg` 记录已写前缀、`undef_seg` 记录未写后缀。
- 如果输出是对输入逐元素 map，建议在 `coins_XX.v` 里定义 map 函数和 `map_sublist_snoc` 类引理，不要把 map 语义展开在 C annotation 中。

## C_43 验证记录

### 结论

- 状态：已全链通过。
- 当前函数：`pairs_sum_to_zero`，只读输入数组，双层循环寻找两个不同元素之和为 0。
- 当前已完成：
  - `C_43.c` 已补完函数规格和双层循环 invariant。
  - `coins_43.v` 已新增并通过编译。
  - `symexec --gen-and-backup` 已刷新 `C_43_goal.v` / `C_43_proof_auto.v` / `C_43_proof_manual.v` / `C_43_goal_check.v`。
  - `C_43_proof_manual.v` 中所有 manual witness 已补完。
  - `coins_43.v` 与 `C_43_proof_manual.v` 扫描无 `Admitted.` / 手写 `Axiom`。

已通过的验收链：

```bash
coqc coins_43.v
coqc C_43_goal.v
coqc C_43_proof_auto.v
coqc C_43_proof_manual.v
coqc C_43_goal_check.v
```

### 文件变更

- `C_43.c`
  - 函数规格复用 `problem_43_pre` / `problem_43_spec`。
  - 前置条件增加 `pair_sum_int_range(input_l, l_size)`，用于证明 `l[i] + l[j]` 不溢出。
  - 外层循环 invariant 使用 `scanned_i(input_l, l_size@pre, i)` 记录所有 `p < i` 的有序 pair 都已经排除。
  - 内层循环 invariant 使用 `scanned_j(input_l, l_size@pre, i, j)` 记录当前 `i` 下所有 `q < j` 的 pair 已经排除。
  - 外层 invariant 保留 `undef_data_at(&j)`，内层退出回到外层时用 `store_int_undef_store_int` 恢复局部变量资源。
- `coins_43.v`
  - `Load "../spec/43".`
  - 新增 `pair_sum_int_range`、`pair_sum_zero`。
  - 新增 `scanned_i` / `scanned_j`，以及初始化和推进引理：
    - `scanned_i_init`
    - `scanned_j_init`
    - `scanned_j_step`
    - `scanned_i_step`
  - 新增 `problem_43_spec_true_of_pair`，从命中的 `i < j` pair 推出 `problem_43_spec input_l true`。
  - 新增 `problem_43_spec_false_of_scanned_i`，从完整扫描结果推出 `problem_43_spec input_l false`。
- `C_43_proof_manual.v`
  - `safety_wit_4` 使用 `pair_sum_int_range` 证明加法安全。
  - `entail_wit_1` / `entail_wit_2` 初始化 `scanned_i` 和 `scanned_j`。
  - `entail_wit_3` / `entail_wit_4` 分别推进外层和内层扫描谓词。
  - `return_wit_1` 用 `problem_43_spec_false_of_scanned_i` 完成 false 分支。
  - `return_wit_2` 用 `problem_43_spec_true_of_pair` 完成 true 分支。

### 遇到的问题

1. 程序按 `i < j` 搜索，但原始 spec 使用任意 `i <> j` 的两个下标。
   处理：在 `coins_43.v` 中证明 `scanned_i_no_distinct_pair`，把任意 distinct pair 按大小关系转成有序 pair；反向顺序时用加法交换由 `lia` 处理。

2. 只用裸 `forall` 写在 C invariant 中可读性和证明复用都差。
   处理：仿照 `C_40`，把搜索空间封装为 `scanned_i` / `scanned_j`，C annotation 只保留抽象谓词，具体组合推理放在 `coins_43.v`。

3. return false 需要从完整扫描推出“不存在任何 distinct pair”。
   处理：外层退出时有 `i >= l_size_pre` 和 `scanned_i input_l l_size_pre i`，用 `problem_43_spec_false_of_scanned_i` 桥接到 spec。

### 后续注意

- 后续二重循环搜索题可以直接沿用 `C_43` 的 `scanned_i/scanned_j` 模式；三重循环则参考 `C_40`。
- 如果 spec 使用 nat 下标而 C proof 使用 Z 下标，桥接证明集中放在 `coins_XX.v` 中，manual proof 里只调用最终 bridge lemma。

## C_46 格式适配尝试记录

### 当前状态

- 状态：已全链通过。
- 最终处理：放弃局部固定长度数组 `int f[100]` 路线，改成 4 个滚动变量 `a/b/c/d` 保存 `fib4(i-4)` 到 `fib4(i-1)`。
- 当前已做：
  - `C_46.c` 已改为无数组版本，只使用局部标量变量。
  - `coins_46.v` 保留 `fib4_z`、`problem_46_pre_z`、`problem_46_spec_z`，新增 `fib4_z_step` 和 `fib4_step_int_range`。
  - `C_46_goal.v`、`C_46_proof_auto.v`、`C_46_proof_manual.v`、`C_46_goal_check.v` 已重新生成。
  - `C_46_proof_manual.v` 已补完 manual VC。

已通过的验收链：

```bash
coqc coins_46.v
coqc C_46_goal.v
coqc C_46_proof_auto.v
coqc C_46_proof_manual.v
coqc C_46_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_46.v C_46_proof_manual.v
```

无输出。

### 实验结论

1. 新版 QCP 能解析和符号执行最小局部数组声明：

```c
int f[100];
return 0;
```

最小程序可以 symbolic 通过，说明 `int f[100]` 本身已被支持。

2. 局部数组单点资源可以被工具处理。

实验中，如果只在中间状态保留单个 `data_at(f, 0)`，函数退出时可以回收局部数组资源。

3. 手动把局部数组整理成 `IntArray::seg/undef_seg` 后，return 时会失败。

当前尝试的循环 invariant 形状：

```c
IntArray::seg(f, 0, i, fib4_z_list(i)) *
IntArray::undef_seg(f, i, 100)
```

可以支撑初始化和循环中的数组访问继续推进，但在小分支 `return result0;` 或最终 `return result;` 前后，`symexec` 报：

```text
Fail to Remove Memory Permission of f
```

说明局部栈数组退出回收期望的资源形状，和堆数组常用的 `IntArray::seg + IntArray::undef_seg` 还不完全一致。

4. 中间 `Assert` 不能只写数组资源。

一开始为了整理 `f[0]`、`f[1]`、`f[2]` 的前缀，写了只包含数组资源的 `Assert`。后续 `if (n < 4)` 会报找不到变量 `n`。处理方式是中间断言必须保留：

```c
n == n@pre &&
0 <= n && n < 100 &&
...
```

否则前端会把后续语句需要的局部变量事实丢掉。

### 后续处理建议

- 如果继续测试局部栈数组路线，下一步不要直接照搬 malloc 数组的 `seg/undef_seg` 模式；应先确认局部数组退出时需要恢复成什么资源形状。
- `int_array_def.h` 中的 `store_array_box` / `store_array_box_array` 可能和局部数组 boxed resource 有关，但当前 `LLM_friendly_cases` 未找到完整示例，需进一步探索。
- 快速完成 `C_46` 的功能验证时，4 个滚动变量版本是可行路线，已经通过完整验证。
- 如果目标是验证 QCP 对 `int f[100]` 的新版支持，则保留当前尝试分支，继续围绕“局部数组资源如何在 return 前恢复到可回收状态”做最小实验。

## C_52 验证记录

### 结论

`C_52` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_52.v
coqc C_52_goal.v
coqc C_52_proof_auto.v
coqc C_52_proof_manual.v
coqc C_52_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_52.v C_52_proof_manual.v
```

无输出。

### 文件变更

- `C_52.c`
  - 从直接写数组下标性质的规格，改为显式使用 `problem_52_pre/spec`。
  - 循环 invariant 维护 `0 <= i <= l_size@pre`，以及前缀 `[0, i)` 中所有元素都满足 `Znth(k, input_l, 0) < t@pre`。
  - 提前返回 `0` 对应 `problem_52_spec input_l t false`，循环结束返回 `1` 对应 `problem_52_spec input_l t true`。
- `coins_52.v`
  - 新增 `Znth_In_range_52` 和 `In_Znth_exists_52`，连接 list `In` 与数组下标表示。
  - 新增 `problem_52_spec_false_of_counter` 和 `problem_52_spec_true_of_all_below`，分别处理发现反例和扫描完成两个返回分支。
- `C_52_proof_manual.v`
  - 完成 `entail_wit_2`、`return_wit_1`、`return_wit_2` 三个 manual VC。

### 注意

- `C_52_proof_auto.v` 是 symexec 生成文件，未手动补 proof；本次只检查并保证 `coins_52.v` 与 `C_52_proof_manual.v` 无 `Admitted.` / `Axiom`。

## C_55 验证记录

### 结论

`C_55` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_55.v
coqc C_55_goal.v
coqc C_55_proof_auto.v
coqc C_55_proof_manual.v
coqc C_55_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_55.v C_55_proof_manual.v
```

无输出。

### 文件变更

- `C_55.c`
  - 保持两变量滚动 Fibonacci 实现。
  - 前后条件使用 `problem_55_pre_z` / `problem_55_spec_z`，二者在 `coins_55.v` 中桥接到 `spec/55.v` 的 `problem_55_pre` / `problem_55_spec`。
  - 前置条件补充 `n < 100` 和 `fib_step_int_range(n)`，用于证明循环中的 `a + b` 和 `i + 1` 不溢出。
  - 循环 invariant 改成 `Inv Assert`，并保留 `n == n@pre`、`problem_55_pre_z(n@pre)`、`fib_step_int_range(n@pre)`、`undef_data_at(&c)`。
- `coins_55.v`
  - 新增 `problem_55_pre_z` / `problem_55_spec_z`，将 spec/55 的 nat 规格包装成 C 侧 Z 规格。
  - 新增 `fib_seq`、`fib_seq_0`、`fib_seq_1`、`fib_seq_step`、`fib_step_int_range` 和 `problem_55_spec_z_of_fib_seq`。
- `C_55_proof_manual.v`
  - 当前 manual VC 为 `fib_safety_wit_4`、`fib_entail_wit_1`、`fib_entail_wit_2`、`fib_return_wit_1`，均已完成。

### 注意

- `C_55_proof_auto.v` 是 symexec 生成文件，未手动补 proof；本次只检查并保证 `coins_55.v` 与 `C_55_proof_manual.v` 无 `Admitted.` / `Axiom`。

## C_63 验证记录

### 结论

`C_63` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_63.v
coqc C_63_goal.v
coqc C_63_proof_auto.v
coqc C_63_proof_manual.v
coqc C_63_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_63.v C_63_proof_manual.v
```

无输出。

### 文件变更

- `C_63.c`
  - 从局部数组 `ff[100]` 改成三个滚动变量 `a/b/c`，分别保存 `fibfib(i-3)`、`fibfib(i-2)`、`fibfib(i-1)`。
  - 前后条件使用 `problem_63_pre_z` / `problem_63_spec_z`，二者在 `coins_63.v` 中桥接到 `spec/63.v` 的 `problem_63_pre` / `problem_63_spec`。
  - 前置条件补充 `n < 100` 和 `fibfib_step_int_range(n)`，用于证明循环中的 `a + b`、`a + b + c` 和 `i + 1` 不溢出。
- `coins_63.v`
  - 新增 `fibfib_z`、`problem_63_pre_z`、`problem_63_spec_z`。
  - 新增 `fibfib_z_0`、`fibfib_z_1`、`fibfib_z_2`、`fibfib_z_step`、`fibfib_step_int_range` 和 `problem_63_spec_z_of_fibfib_z`。
- `C_63_proof_manual.v`
  - 完成两条加法安全 VC、循环初始化/步进 VC，以及四个 return 分支 VC。

### 注意

- `C_63_proof_auto.v` 是 symexec 生成文件，未手动补 proof；本次只检查并保证 `coins_63.v` 与 `C_63_proof_manual.v` 无 `Admitted.` / `Axiom`。

## C_68 验证记录

### 结论

`C_68` 已完成完整验证。

已通过的验收链：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/IntArrayClaude
COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_68.v
coqc $COQINCLUDES C_68_goal.v
coqc $COQINCLUDES C_68_proof_auto.v
coqc $COQINCLUDES C_68_proof_manual.v
coqc $COQINCLUDES C_68_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_68.v C_68_proof_manual.v
```

无输出。

本题编译产物已清理，包括 `.aux`、`.glob`、`.vo`、`.vos`、`.vok` 和 `C_68_proof_manual_backup*.v`。

### 文件变更

- `C_68.c`
  - 已转换为 QCP 可验证格式，使用 `verification_stdlib.h`、`verification_list.h`、`int_array_def.h`。
  - 函数接口改为 `IntArray *pluck(int *arr, int arr_size)`，返回结构体和内部 `data` 数组均在函数内分配。
  - 前置条件补充 `arr_size == Zlength(input_l)`，用于数组访问边界和最终 `sublist` 证明。
  - 循环 invariant 使用 `pluck_loop_state(input_l, i, output_l)` 描述扫描前缀后的候选结果。
  - 返回数组资源在 invariant 中拆成两种形状：
    - `output_size == 0` 时：`data_at(size, 0) * IntArray::undef_full(data, 2)`。
    - `output_size == 2` 时：`data_at(size, 2) * IntArray::full(data, 2, output_l)`。
- `coins_68.v`
  - 加载 `spec/68.v`，并保留 `problem_68_pre_z` 对原始 `problem_68_pre` 的桥接。
  - 新增 `pluck_update`、`pluck_scan_from`、`pluck_prefix_result`，在 Z 层描述 pluck 的扫描语义。
  - `problem_68_spec_z` 定义为输出等于完整扫描结果。
  - `pluck_loop_state` 定义为输出等于扫描前缀 `[0, i)` 的结果。
  - 新增 step/return 辅助引理：
    - `pluck_prefix_result_0`
    - `pluck_prefix_result_step`
    - `replace_Znth_two`
    - `pluck_loop_state_update_empty`
    - `pluck_loop_state_update_less`
    - `pluck_loop_state_skip_odd`
    - `pluck_loop_state_skip_ge`
    - `pluck_loop_state_full_spec`
- `C_68_proof_manual.v`
  - 完成 8 个 manual VC：
    - 循环初始化 `entail_wit_1`
    - 5 个循环分支推进 `entail_wit_2_1` 到 `entail_wit_2_5`
    - 2 个 return 分支 `return_wit_1` / `return_wit_2`
  - 更新写入两个元素的分支中，用 `IntArray.seg_single` 和 `IntArray.seg_merge_to_full` 把两个单点写资源合成为 `IntArray.full(data, 2, [value; index])`。

### 遇到的问题

1. `coins_68.v` 编译路径容易跑错。

   表现：

   - 在仓库根目录直接执行 `coqc QCP_examples/humaneval/IntArrayClaude/coins_68.v` 会报找不到 `../spec/68.v`。
   - 在 `IntArrayClaude` 目录直接裸跑 `coqc coins_68.v` 会报找不到 `AUXLib` / `SimpleC.SL` 等逻辑路径。

   处理：

   ```bash
   cd QCP_examples/humaneval/IntArrayClaude
   COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
   coqc $COQINCLUDES coins_68.v
   ```

   这个经验已同步写入 `QCP_examples/humaneval/SKILL.md` 和 `QCP_FORMAT_CONVERSION_GUIDE.md`。

2. `symexec` include path 一开始不完整。

   表现：

   ```text
   No such file int_array_def.h in search path
   ```

   处理：`symexec` 命令必须加：

   ```bash
   -IQCP_examples/LLM_friendly_cases
   ```

   因为 `verification_stdlib.h` 和 `int_array_def.h` 实际位于 `QCP_examples/LLM_friendly_cases/`。

3. `symexec` 生成的 Coq import 路径一开始写错。

   表现：使用 `--coq-logic-path=SimpleC.EE.humaneval.IntArrayClaude` 生成后，编译 `C_68_proof_auto.v` 报：

   ```text
   Cannot find a physical path bound to logical path
   C_68_goal with prefix SimpleC.EE.humaneval.IntArrayClaude
   ```

   处理：`IntArrayClaude` 与现有 `_CoqProject` 兼容的生成方式是：

   ```bash
   --coq-logic-path=SimpleC.EE
   -slp QCP_examples/humaneval/IntArrayClaude SimpleC.EE
   ```

   这样生成文件使用 `From SimpleC.EE Require Import C_68_goal.`。

4. 初始格式转换后的 `for` 循环缺少 invariant。

   表现：

   ```text
   Error: Lack of assertions in some paths for the loop!
   ```

   处理：补充完整 `Inv Assert`，同时包含：

   - 输入数组资源 `IntArray::full(arr, arr_size, input_l)`。
   - 循环下标边界 `0 <= i && i <= arr_size`。
   - 输出结果形状 `output_size == 0 || output_size == 2`。
   - 语义状态 `pluck_loop_state(input_l, i, output_l)`。
   - 返回结构体字段和内部数组资源。

5. 返回数组如果只写成 `seg(data, 0, output_size, output_l) * undef_seg(data, output_size, 2)`，在更新两个固定位置时不够好用。

   表现：`symexec` 在写 `data[0] = arr[i]` / `data[1] = i` 分支处出现 `Assign Exec fail`。

   处理：在 invariant 中按 `output_size` 拆资源：

   - 空结果时保留 `IntArray::undef_full(data, 2)`。
   - 非空结果时保留 `IntArray::full(data, 2, output_l)`。

   这样工具能直接处理固定下标写入和后续读取 `data[0]`。

6. `pluck` 的原始 spec 是 `list nat -> option (nat * nat)`，直接拿来做循环 step 会让证明很笨重。

   处理：在 `coins_68.v` 中建立 Z 层扫描函数：

   ```coq
   pluck_update
   pluck_scan_from
   pluck_prefix_result
   ```

   C 层规格和循环状态只证明“输出等于扫描结果”，循环推进用 `pluck_loop_state_update_*` 和 `pluck_loop_state_skip_*` 引理处理。

7. `replace_Znth` 双写结果需要单独化简。

   表现：更新已有最优结果时，内存内容是：

   ```coq
   replace_Znth 1 i (replace_Znth 0 (Znth i input_l 0) output_l_2)
   ```

   但循环 invariant 期望 `[Znth i input_l 0; i]`。

   处理：在 `coins_68.v` 中补充：

   ```coq
   replace_Znth_two
   ```

   用 `output_size_2 == Zlength output_l_2` 和 `output_size_2 == 2` 化简两次更新后的列表。

8. manual 证明中选择析取分支不能直接依赖 `Left` / `Right`。

   表现：某些目标经过 `pre_process` 后是 separation logic 层面的 `||`，直接 `Right. Left.` 报找不到普通 Coq 析取。

   处理：使用已有证明风格：

   ```coq
   rewrite <- derivable1_orp_intros1.
   rewrite <- derivable1_orp_intros2.
   ```

   逐层选择目标分支。

9. return 分支需要把数组资源整理成后置条件形状。

   处理：

   - 空结果分支：`IntArray.undef_full_to_undef_seg` + `IntArray.seg_empty`。
   - 长度为 2 的结果分支：`IntArray.full_to_seg` + `IntArray.undef_seg_empty`。

### 后续注意

- 对“返回数组容量固定但逻辑长度可能为 0 或 2”的题，循环 invariant 可以优先按长度拆资源，而不是统一使用 `seg + undef_seg`。
- 对固定位置连续写 `data[0]`、`data[1]`，manual 中常用：

  ```coq
  sep_apply (IntArray.seg_single data 1 v1).
  sep_apply (IntArray.seg_single data 0 v0).
  sep_apply (IntArray.seg_merge_to_full data 0 1 2 (v0 :: nil) (v1 :: nil)); [ | lia].
  ```

- 对 `nat`/`option` 规格，不一定要在 C invariant 中直接暴露原始 spec；可以在 `coins_XX.v` 中建立 C 侧 Z 层函数，再用小引理连接循环 step 和最终规格。

## C_72 验证记录

### 结论

`C_72` 已完成完整验证。

已通过的验收链：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/IntArrayClaude
COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_72.v
coqc $COQINCLUDES C_72_goal.v
coqc $COQINCLUDES C_72_proof_auto.v
coqc $COQINCLUDES C_72_proof_manual.v
coqc $COQINCLUDES C_72_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_72.v C_72_proof_manual.v
```

无输出。

本题编译产物已清理，包括 `.aux`、`.glob`、`.vo`、`.vos`、`.vok` 和 `C_72_proof_manual_backup*.v`。

### 文件变更

- `C_72.c`

  已补 QCP function spec 和 loop invariant，未修改 C 执行语句。函数前置条件包含 `q_size == Zlength(lv)`、`problem_72_pre_z(lv, w)`、`will_it_fly_int_range(lv)` 和输入数组资源 `IntArray::full(q, q_size, lv)`。

  后置条件使用 `problem_72_spec_z(lv, w, __return)` 连接 C 的 `0/1` 返回值与题目布尔语义，并保持输入数组资源不变。

  循环 invariant 记录：

  - `q`、`q_size`、`w` 与函数入口一致。
  - `0 <= i && i <= q_size`。
  - `s == sum(sublist(0, i, lv))`。
  - 已检查前缀满足镜像相等：
    `forall k, 0 <= k && k < i => Znth(k, lv, 0) == Znth(q_size - 1 - k, lv, 0)`。
  - `will_it_fly_int_range(lv)` 和 `IntArray::full(q, q_size, lv)`。

- `coins_72.v`

  新增 `Load "../spec/72".` 的 Coq 侧桥接文件。定义：

  - `problem_72_pre_z`：包装原始 `problem_72_pre`。
  - `mirror_all`：用 `Znth` 和 `Zlength` 表示列表回文条件。
  - `problem_72_spec_z`：用 C 返回整数表达“非 0 当且仅当回文且总和不超过 `w`”。
  - `will_it_fly_int_range`：要求所有前缀和都在 C `int` 范围内，供 `s += q[i]` 的 safety VC 使用。

  主要引理：

  - `sum_sublist_0`。
  - `sum_sublist_snoc`。
  - `mirror_prefix_extend`。
  - `mirror_prefix_mismatch_spec_false`。
  - `mirror_prefix_full`。
  - `problem_72_spec_z_weight_false`。
  - `problem_72_spec_z_true`。

- `C_72_proof_manual.v`

  已补完 6 个 manual VC：

  - `proof_of_will_it_fly_safety_wit_7`：证明 `s + q[i]` 的安全范围。
  - `proof_of_will_it_fly_entail_wit_1`：初始化循环 invariant。
  - `proof_of_will_it_fly_entail_wit_2`：相等分支推进前缀和与镜像 invariant。
  - `proof_of_will_it_fly_return_wit_1`：循环正常结束且 `s <= w` 时返回 `1`。
  - `proof_of_will_it_fly_return_wit_2`：循环正常结束但 `s > w` 时返回 `0`。
  - `proof_of_will_it_fly_return_wit_3`：发现镜像不等时提前返回 `0`。

### 遇到的问题

1. `C_72.c` 当前没有 QCP 注解，但目录里已有旧生成文件。

   表现：`C_72_proof_manual.v` 里 6 个 lemma 全是 `Admitted.`，而旧 goal 只能反映之前的注解状态，不能作为当前证明基础。

   处理：补齐 `Require` / `Ensure` / `Inv Assert` 后，用正确的 IntArrayClaude symexec 命令重新生成：

   ```bash
   linux-binary/symexec \
     --goal-file=QCP_examples/humaneval/IntArrayClaude/C_72_goal.v \
     --proof-auto-file=QCP_examples/humaneval/IntArrayClaude/C_72_proof_auto.v \
     --proof-manual-file=QCP_examples/humaneval/IntArrayClaude/C_72_proof_manual.v \
     --coq-logic-path=SimpleC.EE \
     -slp QCP_examples/humaneval/IntArrayClaude SimpleC.EE \
     --input-file=QCP_examples/humaneval/IntArrayClaude/C_72.c \
     -IQCP_examples/LLM_friendly_cases \
     --gen-and-backup \
     --no-exec-info
   ```

2. 原题 spec 使用 Coq `bool`，C 程序返回 `int`。

   表现：直接在 C 后置条件里使用 `problem_72_spec(lv, w, true/false)` 会让 return 分支写成较重的析取；并且 C 的 `0/1` 与 Coq `bool` 需要桥接。

   处理：在 `coins_72.v` 中定义 `problem_72_spec_z(lv, w, out)`，用 `out <> 0 <-> mirror_all lv /\ sum lv <= w` 表示 C 返回值语义。

3. 循环同时承担回文检查和求和，invariant 必须同时记录两条语义线。

   表现：只记录 `s == sum(sublist(0, i, lv))` 不足以证明提前返回 `0`；只记录镜像前缀又无法证明最终 `s <= w` 分支。

   处理：invariant 同时保留前缀和以及 `forall k < i` 的镜像相等事实。正常退出时用 `mirror_prefix_full` 得到 `mirror_all lv`；发现不等时用 `mirror_prefix_mismatch_spec_false` 直接证明 false 规格。

4. `s += q[i]` 需要前缀和范围约束。

   表现：safety VC 需要证明 `INT_MIN <= s + Znth i lv 0 <= INT_MAX`。

   处理：增加 `will_it_fly_int_range(lv)`，要求 `0 <= i <= Zlength lv` 的所有 `sum(sublist 0 i lv)` 都在 C `int` 范围内。manual 中先用 `sum_sublist_snoc` 把 `s + q[i]` 改写成下一前缀和，再从 range 谓词取出结论。

5. return 分支中 `entailer!` 会把部分纯目标化简掉，过晚改写 `sublist_self` 会找不到目标子项。

   表现：`C_72_proof_manual.v` 初版在 return proof 中先 `entailer!` 再 `rewrite sublist_self`，编译报：

   ```text
   Found no subterm matching "sublist 0 ?M ?L" in the current goal.
   ```

   处理：在 `entailer!` 前先 assert 出退出事实，例如 `s = sum lv` 或 `sum lv > w_pre`，再进入 separation logic entailment。

### 后续注意

- 对“循环提前返回 false，正常结束后再按累计量判断 true/false”的题，invariant 要同时记录“提前返回条件的反面已经在前缀成立”和累计量。
- 对 C `int` 返回布尔语义，建议在 `coins_XX.v` 中建一个 `problem_XX_spec_z`，避免在 C 注解里重复展开 `true/false` 析取。
- 对需要从 `sublist 0 i` 变成整表 `lv` 的 return VC，先在 `entailer!` 前 assert `i = Zlength lv` 后的结论，再交给 `entailer!` 整理资源。

## C_73 验证记录

### 结论

`C_73` 已完成完整验证。

已通过的验收链：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/IntArrayClaude
COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_73.v
coqc $COQINCLUDES C_73_goal.v
coqc $COQINCLUDES C_73_proof_auto.v
coqc $COQINCLUDES C_73_proof_manual.v
coqc $COQINCLUDES C_73_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_73.v C_73_proof_manual.v
```

无输出。

本题编译产物已清理，包括 `.aux`、`.glob`、`.vo`、`.vos`、`.vok` 和 `C_73_proof_manual_backup*.v`。

### 文件变更

- `C_73.c`

  已补 QCP function spec 和 loop invariant，未修改 C 执行语句。函数前置条件包含：

  - `0 <= arr_size && arr_size < INT_MAX`。
  - `arr_size == Zlength(lv)`。
  - `problem_73_pre_z(lv)`。
  - `smallest_change_int_range(lv)`。
  - `IntArray::full(arr, arr_size, lv)`。

  后置条件使用 `problem_73_spec_z(lv, __return)` 连接 C 循环语义和返回值，并保持输入数组资源不变。

  循环 invariant 记录：

  - `arr == arr@pre`、`arr_size == arr_size@pre`。
  - `0 <= i`、`2 * i <= arr_size`。
  - `out == count_half_mismatches_upto(i, lv)`。
  - `smallest_change_int_range(lv)`。
  - `IntArray::full(arr, arr_size, lv)`。

- `coins_73.v`

  新增 `Load "../spec/73".` 的 Coq 侧桥接文件。定义：

  - `problem_73_pre_z`：包装原始 `problem_73_pre`。
  - `count_half_mismatches_upto_nat` / `count_half_mismatches_upto`：按“已处理的镜像对数量”统计 mismatch。
  - `problem_73_spec_z`：使用退出下标存在性描述最终结果。
  - `smallest_change_int_range`：为 `out += 1` 提供 C `int` 安全范围。

  主要引理：

  - `count_half_mismatches_upto_0`。
  - `count_half_mismatches_upto_step_eq`。
  - `count_half_mismatches_upto_step_neq`。
  - `problem_73_spec_z_of_exit`。

- `C_73_proof_manual.v`

  已补完 5 个 manual VC：

  - `proof_of_smallest_change_safety_wit_9`：证明 mismatch 分支 `out + 1` 的安全范围。
  - `proof_of_smallest_change_entail_wit_1`：初始化循环 invariant。
  - `proof_of_smallest_change_entail_wit_2_1`：不等分支推进 mismatch 计数。
  - `proof_of_smallest_change_entail_wit_2_2`：相等分支推进 invariant，计数不变。
  - `proof_of_smallest_change_return_wit_1`：循环退出后连接到 `problem_73_spec_z`。

### 遇到的问题

1. `C_73.c` 没有 QCP 注解，但目录中已有旧生成文件。

   表现：旧 `C_73_proof_manual.v` 中 5 个 lemma 全是 `Admitted.`，且没有 `coins_73.v` 承载 `count_half_mismatches_upto` 等定义。

   处理：补齐 `Require` / `Ensure` / `Inv Assert` 和 `coins_73.v` 后，用正确的 IntArrayClaude symexec 命令重新生成：

   ```bash
   linux-binary/symexec \
     --goal-file=QCP_examples/humaneval/IntArrayClaude/C_73_goal.v \
     --proof-auto-file=QCP_examples/humaneval/IntArrayClaude/C_73_proof_auto.v \
     --proof-manual-file=QCP_examples/humaneval/IntArrayClaude/C_73_proof_manual.v \
     --coq-logic-path=SimpleC.EE \
     -slp QCP_examples/humaneval/IntArrayClaude SimpleC.EE \
     --input-file=QCP_examples/humaneval/IntArrayClaude/C_73.c \
     -IQCP_examples/LLM_friendly_cases \
     --gen-and-backup \
     --no-exec-info
   ```

2. 原始 spec 使用 `firstn` / `skipn` / `rev` / `count_diff`，直接放进 loop invariant 会很重。

   表现：C 循环的自然状态是下标 `i` 和镜像位置 `arr_size - 1 - i`，与原始 `smallest_change_impl` 的列表切片结构不直接同形。

   处理：在 `coins_73.v` 中建立 C 侧前缀计数函数 `count_half_mismatches_upto`，并把后置条件写成退出下标存在性：

   ```coq
   exists i,
     0 <= i /\
     2 * i <= Zlength arr /\
     i >= Zlength arr - 1 - i /\
     out = count_half_mismatches_upto i arr.
   ```

   这样 return VC 只需使用 `problem_73_spec_z_of_exit`。

3. 循环条件 `i < arr_size - 1 - i` 的可用边界要转成 `2 * (i + 1) <= arr_size`。

   表现：推进 invariant 时需要证明下一轮满足 `2 * (i + 1) <= arr_size`。

   处理：invariant 保留 `2 * i <= arr_size`，循环体分支额外有 `i < arr_size - 1 - i`，目标中的下一轮边界可由 `lia` 解决。

4. `out += 1` 需要单独的 C 整数范围谓词。

   表现：安全 VC 需要证明 `INT_MIN <= out + 1 <= INT_MAX`。

   处理：增加 `smallest_change_int_range(lv)`，在 mismatch 分支从该谓词取出当前 `i` 的 `count_half_mismatches_upto i lv + 1` 范围。

5. step 引理使用 `Zlength lv - 1 - i`，而 VC 分支假设里是 `arr_size_pre - 1 - i`。

   表现：manual 中直接 `rewrite count_half_mismatches_upto_step_neq by lia` 会失败，因为第二个 side condition 是元素不等式，不是纯算术；并且下标表达式还差 `arr_size_pre = Zlength lv` 的替换。

   处理：rewrite 时显式处理 side condition：

   ```coq
   rewrite count_half_mismatches_upto_step_neq.
   entailer!.
   - lia.
   - rewrite <- H3. exact H.
   ```

   相等分支同理使用 `count_half_mismatches_upto_step_eq`。

### 后续注意

- 对左右镜像扫描题，优先用“已处理的镜像对数量”建模，loop 边界写成 `2*i <= len`，退出规格写成 `i >= len - 1 - i`。
- 对原始 spec 里有 `firstn/skipn/rev` 的题，先建立 C 侧 step 函数；如果需要再补桥接到原始切片规格，不要一开始把这些切片表达式塞进 invariant。
- step 引理的下标最好统一用 `Zlength lv`；manual 中遇到 VC 的 `arr_size_pre` 版本时，先用长度等式改写。

## C_85 验证记录

### 结论

`C_85` 已完成完整验证。

已通过的验收链：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/IntArrayClaude
COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_85.v
coqc $COQINCLUDES C_85_goal.v
coqc $COQINCLUDES C_85_proof_auto.v
coqc $COQINCLUDES C_85_proof_manual.v
coqc $COQINCLUDES C_85_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_85.v C_85_proof_manual.v
```

无输出。

本题编译产物已清理，包括 `.aux`、`.glob`、`.vo`、`.vos`、`.vok` 和 `C_85_proof_manual_backup*.v`。

### 文件变更

- `C_85.c`

  已改成 QCP 可验证格式。增加 `problem_85_pre_z`、`problem_85_spec_z`、`sum_even_at_odd_upto`、`add_int_range` 的 `Extern Coq` 声明，并 `Import Coq Require Import coins_85`。

  函数前置条件包含：

  - `0 <= lst_size && lst_size < INT_MAX`。
  - `lst_size == Zlength(lv)`。
  - `problem_85_pre_z(lv)`。
  - `add_int_range(lv)`。
  - `IntArray::full(lst, lst_size, lv)`。

  后置条件包含：

  - `problem_85_spec_z(lv, __return)`。
  - 输入数组资源保持 `IntArray::full(lst, lst_size, lv)`。

  循环 invariant 记录：

  - 指针和长度不变：`lst == lst@pre`、`lst_size == lst_size@pre`。
  - 下标边界：`0 <= i`、`2 * i <= lst_size`。
  - 累加语义：`s == sum_even_at_odd_upto(i, lv)`。
  - 溢出约束：`add_int_range(lv)`。
  - 输入数组资源：`IntArray::full(lst, lst_size, lv)`。

- `coins_85.v`

  新增 `Load "../spec/85".` 的 Coq 侧桥接文件。定义：

  - `sum_even_at_odd_upto_nat` / `sum_even_at_odd_upto`：按“已处理的奇数下标个数”表示前缀和。
  - `problem_85_pre_z`：把原始 `problem_85_pre` 包装到 C 侧列表。
  - `problem_85_spec_z`：使用退出下标存在性描述返回值，避免在 return VC 中直接展开除法或 floor 语义。
  - `add_int_range`：为每次 `s + lst[2*i+1]` 提供有符号整数范围证明。

  主要引理：

  - `sum_even_at_odd_upto_0`。
  - `sum_even_at_odd_upto_step_even`。
  - `sum_even_at_odd_upto_step_odd`。
  - `problem_85_spec_z_of_exit`。

- `C_85_proof_manual.v`

  已补完 5 个 manual VC：

  - `proof_of_add_safety_wit_14`：证明 `s + lst[2*i+1]` 的安全范围。
  - `proof_of_add_entail_wit_1`：初始化循环 invariant。
  - `proof_of_add_entail_wit_2_1`：偶数分支推进 invariant。
  - `proof_of_add_entail_wit_2_2`：奇数分支推进 invariant。
  - `proof_of_add_return_wit_1`：退出循环后连接到 `problem_85_spec_z`。

### 遇到的问题

1. 旧生成文件与当前 `C_85.c` 规格不匹配，并且缺少 `coins_85.v`。

   表现：manual 文件仍有 `Admitted.`，且缺少连接 `../spec/85` 与 C 侧整数列表的桥接定义。

   处理：新增 `coins_85.v`，在 `C_85.c` 中导入相关 Coq 定义，然后用正确的 `symexec` 命令重新生成 `goal` / `auto` / `manual` / `goal_check`：

   ```bash
   linux-binary/symexec \
     --goal-file=QCP_examples/humaneval/IntArrayClaude/C_85_goal.v \
     --proof-auto-file=QCP_examples/humaneval/IntArrayClaude/C_85_proof_auto.v \
     --proof-manual-file=QCP_examples/humaneval/IntArrayClaude/C_85_proof_manual.v \
     --coq-logic-path=SimpleC.EE \
     -slp QCP_examples/humaneval/IntArrayClaude SimpleC.EE \
     --input-file=QCP_examples/humaneval/IntArrayClaude/C_85.c \
     -IQCP_examples/LLM_friendly_cases \
     --gen-and-backup \
     --no-exec-info
   ```

2. 累加语句需要额外的整数范围前提。

   表现：安全 VC 需要证明 `s + lst[i * 2 + 1]` 落在 `INT_MIN` 到 `INT_MAX` 之间，仅有原始 `problem_85_pre` 不够直接。

   处理：增加 `add_int_range(lv)`，要求每个合法奇数下标累加前后的和都在 C `int` 范围内。manual 中从该前提取出当前下标的范围：

   ```coq
   destruct (H i ltac:(lia) ltac:(lia)) as [_ Hsum].
   ```

3. 循环变量 `i` 表示“奇数下标计数”，不是数组下标本身。

   表现：代码访问的是 `lst[i * 2 + 1]`，循环条件是 `i * 2 + 1 < lst_size`。如果 invariant 只写 `i <= lst_size`，无法稳定证明访问合法性和退出语义。

   处理：invariant 使用 `2 * i <= lst_size`，累加值使用 `sum_even_at_odd_upto(i, lv)`。退出时由 `2 * i <= len` 和 `2 * i + 1 >= len` 共同描述已经处理完所有奇数下标。

4. `i * 2 + 1` 与 `2 * i + 1` 的归一化不一致。

   表现：C 生成目标里常出现 `i * 2 + 1`，而 Coq 辅助定义和引理中更自然的是 `2 * i + 1`，直接 `rewrite` 找不到匹配项。

   处理：manual 证明中先标准化：

   ```coq
   replace (i * 2 + 1) with (2 * i + 1) in * by lia.
   ```

   然后再使用 `sum_even_at_odd_upto_step_even` 或 `sum_even_at_odd_upto_step_odd`。

5. `Z.to_nat (i + 1)`、`Z.of_nat (Z.to_nat i)` 与 `Z.rem` / `Z.eqb` 的化简需要单独处理。

   表现：前缀和 step 引理证明时，Coq 不会自动把退出后的 `match Z.eqb (Z.rem ...) 0 with ...` 化成期望分支，也不会自动识别所有 `Z.to_nat` / `Z.of_nat` 关系。

   处理：在 `coins_85.v` 中把这类推理集中封装进 step 引理。证明中先用 `Z2Nat.id`、`Nat2Z.id`、`Z2Nat.inj_add` 整理下标，再通过 `destruct (Z.eqb ... ) eqn:?` 和 `Z.eqb_eq` / `Z.eqb_neq` 分情况处理；必要时用 `change` 把目标改写成归一化后的 `2 * i + 1` 形状。

6. 直接把返回规格写成原题公式会让 return VC 太重。

   表现：原题语义是求所有奇数下标元素之和，若直接在后置条件中使用长度除法或复杂列表过滤，退出分支需要额外证明边界、取整和前缀长度关系。

   处理：`problem_85_spec_z` 改为存在退出计数 `i`：

   ```coq
   exists i,
     0 <= i /\
     2 * i <= Zlength lst /\
     2 * i + 1 >= Zlength lst /\
     output = sum_even_at_odd_upto i lst.
   ```

   return VC 只需使用 `problem_85_spec_z_of_exit`，剩余边界交给 `lia`。

### 后续注意

- 遇到访问形如 `arr[2*i+1]` 的循环时，优先把 invariant 里的计数变量建模成“已处理的目标位置个数”，边界写成 `2*i <= len` 和退出条件对应的 `2*i+1 >= len`。
- 累加类题目如果 C 类型是 `int`，除了原始语义 precondition，通常还要单独增加面向 C 执行安全的 range predicate。
- manual 证明里涉及 `i*2` / `2*i` 的 rewrite 前，先用 `replace ... by lia` 做算术归一化。
- 如果原始 spec 带除法、过滤、奇偶筛选等复杂结构，可以在 `coins_XX.v` 中建立 C 侧前缀函数和退出下标规格，再用小引理连接回原始语义。

## 后续记录模板

复制下面模板记录下一题。

```markdown
## C_XX 验证记录

### 结论

- 状态：
- 是否全链通过：
- 是否无 `Admitted.` / `Axiom`：

### 文件变更

- `C_XX.c`：
- `coins_XX.v`：
- `C_XX_proof_manual.v`：

### 遇到的问题

1. 问题：
   解决：

2. 问题：
   解决：

### 后续注意

- 
```
