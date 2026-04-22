# IntArrayClaude 验证进度记录

更新时间：2026-04-22

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
| `C_40` | 已有生成文件 | 三元组求和，manual 仍含 `Admitted.`，需补组合和安全条件。 |
| `C_42` | 已有生成文件 | 输出数组写入，manual 仍含 `Admitted.`。 |
| `C_43` | 已有生成文件 | manual 当前无 `Admitted.`，但本文档尚未重新跑完整验收链。 |
| `C_52` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_55` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_72` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_73` | 已有生成文件 | manual 仍含 `Admitted.`。 |
| `C_85` | 已有生成文件 | manual 仍含 `Admitted.`。 |
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
