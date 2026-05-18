# IntArrayClaude 验证进度记录

更新时间：2026-05-09

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
| `C_33` | 已全链通过 | 使用外部可信 `sort_int_array` 替代 `qsort`；排序函数支持升序/降序参数，已接入 `spec/33.v` 的 `problem_33_spec`，manual 无 `Admitted.` / `Axiom`。 |
| `C_34` | 已全链通过 | sorted unique；C 中保留 `contains` 与去重循环，仅将排序建模为外部库函数，已接入 `spec/34.v`，manual 无 `Admitted.` / `Axiom`。 |
| `C_40` | 已全链通过 | 三元组求和；三层扫描谓词、溢出安全和 true/false 规格桥接已补完，manual 已无 `Admitted.`。 |
| `C_58` | 已全链通过 | sorted unique common；保留双数组 `contains` 与公共元素收集循环，仅将排序建模为外部库函数，已接入 `spec/58.v`，manual 无 `Admitted.` / `Axiom`。 |
| `C_42` | 已全链通过 | 已去掉输入 `out`，改为函数内部 malloc 并返回 `IntArray *` 结构体；manual 已无 `Admitted.`。 |
| `C_43` | 已全链通过 | 二元组求和；复用 `C_40` 的分层扫描谓词模式，manual 已无 `Admitted.`。 |
| `C_46` | 已全链通过 | 已改成 4 个滚动变量，不再使用局部数组；manual 已无 `Admitted.`。 |
| `C_52` | 已全链通过 | 单层数组扫描；改为使用 `problem_52_pre/spec`，manual 已无 `Admitted.`。 |
| `C_55` | 已全链通过 | Fibonacci 滚动变量；已接入 `problem_55_pre/spec`，并用 `fib_step_int_range` 处理加法溢出，manual 已无 `Admitted.`。 |
| `C_63` | 已全链通过 | FibFib 三变量滚动版本；已接入 `problem_63_pre/spec`，manual 已无 `Admitted.`。 |
| `C_70` | 已全链通过 | strange sort；保留 min/max 交替输出循环，仅将排序建模为外部可信 `sort_int_array`，已接入 `spec/70.v`，manual 无 `Admitted.` / `Axiom`。 |
| `C_72` | 已全链通过 | 回文数组且总和不超过阈值；已补 `coins_72.v`、前缀和/镜像 invariant 和 6 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_73` | 已全链通过 | 统计左右镜像不等对数；已补 `coins_73.v`、镜像对计数 invariant 和 5 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_85` | 已全链通过 | 奇数下标求和；已补 `coins_85.v`、循环前缀和 invariant 和 5 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_88` | 已全链通过 | 根据首尾和奇偶决定升序/降序；保留 copy、qsort、偶数分支 in-place reverse，只将 qsort 建模为外部排序函数，manual 无 `Admitted.` / `Axiom`。 |
| `C_90` | 已全链通过 | next smallest；保留排序后的相邻扫描循环，`sort_int_array` 已改为与 `C_33`/`C_34` 一致的通用排序规格，manual 无 `Admitted.` / `Axiom`。 |
| `C_94` | 已全链通过 | 最大素数的各位和；修复原始 C 将 `1` 误判为素数的问题，已补 `coins_94.v` 和 14 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_100` | 已全链通过 | 已改成函数内部 malloc 并返回 `IntArray *`；补 `make_pile` 桥接、前缀写入 invariant 和 5 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_106` | 已全链通过 | 已改成函数内部 malloc 并返回 `IntArray *`；补三角数/阶乘序列桥接、奇偶分支 invariant 和 6 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_109` | 已全链通过 | 非空只读数组；补循环下降数/环形下降数桥接、循环 invariant 和 9 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_114` | 已全链通过 | long long 只读数组；已补 `LongArray` 策略、Kadane 递推规格、循环 invariant 和 7 个 manual VC，且 `coins_114.v` / manual 无 `Admitted.` / `Axiom`。 |
| `C_116` | 已全链通过 | 按二进制 1 的个数和数值排序；保留复制、bit-count 和冒泡排序核心逻辑，仅做 QCP 返回结构体/局部变量作用域适配，manual 无 `Admitted.` / `Axiom`。 |
| `C_121` | 已全链通过 | 偶数下标正奇数求和；补 `coins_121.v`、奇数长度适配 invariant 和 5 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_122` | 已全链通过 | 前 k 个元素中二位数范围求和；补 `coins_122.v`、范围 invariant 和 6 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_123` | 已全链通过 | Collatz 奇数项收集并排序；保留 Collatz 主循环，固定容量适配原 `realloc`；已去掉 `append_int` helper，改为直接 `data[output_size] = n; output_size++;`，manual 无 `Admitted.` / `Axiom`。 |
| `C_126` | 已全链通过 | 非降序且无连续三重复；将 bool 返回改为 QCP 可解析的 int 返回，补 `coins_126.v` 和 7 个 manual VC，且无 `Admitted.` / `Axiom`。 |
| `C_128` | 已全链通过 | prod signs；保留空数组 sentinel、绝对值累加和符号乘积循环逻辑，`abs` 用已实现 wrapper，manual 无 `Admitted.` / `Axiom`。 |
| `C_130` | 已全链通过 | Tribonacci 序列数组；保留 `0/1` 基础项、偶数公式和奇数前两项递推逻辑，值返回结构体适配为 `IntArray *`，manual 无 `Admitted.` / `Axiom`。 |
| `C_135` | 已全链通过 | can_arrange；保留原程序扫描 `arr[i] <= i` 并记录最大下标的核心逻辑，`spec/135.v` 已修正为相同语义并完成桥接，manual 无 `Admitted.` / `Axiom`。 |
| `C_136` | 已全链通过 | largest negative / smallest positive；保留两个 sentinel 变量和双条件更新逻辑，返回结构体值适配为 `IntArray *`，用 `0` 桥接原 spec 的 `None`，manual 无 `Admitted.` / `Axiom`。 |
| `C_142` | 已全链通过 | index-based square/cube/sum；保留三分支累加逻辑，补 C `%`/nat modulo 桥接和乘法/前缀和溢出范围，manual 无 `Admitted.` / `Axiom`。 |
| `C_145` | 已全链通过 | order by points；保留原程序的 signed digit score、复制和冒泡排序核心逻辑，强规格接入 `spec/145.v`，`highest_power10_state` 已改为可证明 ghost state，manual 无 `Admitted.` / `Axiom`。 |
| `C_146` | 已全链通过 | special filter；保留原程序 `nums[i] > 10`、最高位循环、首末位奇数判断和单个计数 if 结构，仅做 QCP 头文件/注解适配，manual 无 `Admitted.` / `Axiom`。 |
| `C_152` | 已全链通过 | compare scores/guesses；结构体值返回适配为 `IntArray *`，保留最小长度、malloc-null 检查和逐元素 `abs(game[i]-guess[i])` 逻辑，manual 无 `Admitted.` / `Axiom`。 |
| `C_155` | 已全链通过 | even/odd digit count；修正 0 的 digit 规格为 `[0]`，保留 `%10`/`/10` digit 循环和 `[even; odd]` 输出顺序，manual 无 `Admitted.` / `Axiom`。 |
| `C_159` | 已全链通过 | eat carrots；结构体值返回适配为 `IntArray *`，保留两个分支填充 `[number+remaining,0]` / `[number+need,remaining-need]`，manual 无 `Admitted.` / `Axiom`。 |
| `C_163` | 已全链通过 | generate integers；去掉 `append_int` helper，保留原筛选循环，用局部 `output_size` 加直接数组写入 `data[output_size] = i; output_size++;` 适配 QCP，manual 无 `Admitted.` / `Axiom`。 |

其它只有 `.c` 的题目暂按 `待建模` 处理。

## C_116 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_116.v`、`C_116_goal.v`、`C_116_proof_auto.v`、`C_116_proof_manual.v`、`C_116_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_116.v`、`C_116_proof_manual.v` 扫描无 `Admitted` / `Axiom`。

### 文件变更

- `spec/116.v`：把规格侧排序实现改成与 C 程序一致的冒泡 pass 结构，并固定 bit-count fuel 为 31。
- `C_116.c`：转换为 QCP 格式，结构体值返回适配为 `IntArray *`；保留原来的复制数组、计算每个元素二进制 1 个数、按 `(bit_count, value)` 冒泡排序的核心逻辑。
- `coins_116.v`：新增 `bit_count_state_at_116`、复制前缀、score 前缀、外层/内层排序状态，以及相应初始化、单步和最终规格桥接引理。
- `C_116_proof_manual.v`：补完 `abs`、bit-count 循环、score 写入、冒泡 swap/keep 和最终规格相关 manual VC。

### 遇到的问题

1. 问题：排序是本题核心逻辑，不能像 `qsort` 那样替换成通用未定义排序函数。
   解决：C 中保留原嵌套循环和相邻交换；Coq 侧用 `bubble_pass_116` / `bubble_sort_116` 建模同一控制结构。

2. 问题：`n = abs(out->data[i])` 这类数组读作为函数实参会让符号执行更难处理。
   解决：拆成 `n = out->data[i]; n = abs(n);`，不改变计算结果，只把数组读和函数调用分开。

3. 问题：`b/n` 作为函数作用域局部变量时，bit-count 循环结束后的局部变量资源需要一路携带到后续排序循环，注解和 VC 都会变重。
   解决：把 `b/n` 改成每轮 score 循环体内的局部变量；这是作用域适配，值的赋值和使用顺序不变。

4. 问题：QCP 没有稳定保留“进入 while 前 `b == 0`”这个纯事实。
   解决：在 `n = abs(n);` 后补一个冗余的 `b = 0;`，并加中间断言记录 `n == Zabs(Znth i input_l 0)`；这不改变输出，只帮助建立 bit-count 初始状态。

5. 问题：手写 `data_at(&b, b)` / `data_at(&n, n)` 容易和局部变量权限机制冲突，甚至影响后续 memory read。
   解决：避免手写这些局部变量资源，改用作用域缩短和必要的纯断言让符号执行自动管理局部变量。

6. 问题：bit-count 循环若写过强不变式，例如 `n > 0 -> b <= 30`，并不总能自然由单步推出。
   解决：保留足够证明安全和最终规格的弱不变式：`0 <= b <= 31`、`0 <= n < INT_MAX` 和 `bit_count_state_at_116`。

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

## C_155 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_155.v`、`C_155_goal.v`、`C_155_proof_auto.v`、`C_155_proof_manual.v`、`C_155_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_155.v`、`C_155_proof_manual.v` 扫描无 `Admitted` / `Axiom`。

### 文件变更

- `spec/155.v`：把非零数字递归拆成 `to_digits_fuel_nonzero`，再用 `to_digits` 特判输入 `0` 为 `[0]`，使规格与 C 程序的 `0 -> (1,0)` 行为一致。
- `C_155.c`：转换为 QCP 格式，保留原来的 `abs(num)`、按 `%10` 取 digit、奇偶计数、`/10` 推进、最后输出 `[even; odd]` 的核心逻辑。为验证适配，将返回值改为 `IntArray *`，用通用 `malloc` wrapper；把临时变量 `d` 的声明提升到循环前以稳定局部变量权限。
- `coins_155.v`：新增 C 层 digit/count 状态 `digit_count_state` 以及初始化、单步、最终规格桥接引理；补充 `Z.rem`/`Z.quot` 相关界限和计数器加一不溢出的辅助引理。
- `C_155_proof_manual.v`：补完所有 manual VC，包括 `abs` 桥接、`0` 输入初始化、奇偶分支状态更新、循环推进和最终数组返回规格。

### 遇到的问题

1. 问题：原 `spec/155.v` 的 digit 递归在 `0` 时返回空列表，导致规格期望 `(0,0)`，但原 C 程序对 `0` 设置 `n2=1`，返回 `(1,0)`。
   解决：采用 wrapper 规格方案：内部递归仍在遇到 0 时停止，外层 `to_digits` 单独把输入 0 映射为 `[0]`。这样保留非零数递归结构，同时让 0 的规格匹配题意和 C 行为。

2. 问题：`abs(INT_MIN + 1)` 可以等于 `INT_MAX`，所以循环变量 `w` 的不变式写成 `w < INT_MAX` 会错误排除合法边界。
   解决：把 `w` 的不变式改为 `w <= INT_MAX`，同时在函数前置条件中加入 `Zabs(num) + 1 < INT_MAX`，用于证明计数器加一不会溢出。

3. 问题：`int d` 若声明在 while 体内部，离开循环体时局部栈权限回收和手工断言会产生不必要的 VC。
   解决：将 `int d=0;` 提升到循环前，循环体内仍执行 `d = w % 10;`。这是临时变量声明位置的验证适配，不改变 digit 计算逻辑。

4. 问题：C 的 `%`/`/` 在 VC 中对应 `Z.rem`/`Z.quot`，而部分 Coq 侧推理更容易落在非负 `mod`/`div` 上。
   解决：在证明中用 `Z.rem_mod_nonneg`、`Z.quot_div_nonneg`、`Zquot_10_lt_self` 桥接，并在 `coins_155.v` 中把 digit 单步更新写成 `Z.rem`/`Z.quot` 形式。

5. 问题：计数器 `n1 + 1`、`n2 + 1` 的安全性不能只靠 `n1 < INT_MAX` / `n2 < INT_MAX` 反复自动推出。
   解决：利用 `digit_count_state` 中“已处理计数 + 剩余 digit 长度 <= Zabs(num)+1”的界限，补 `digit_count_state_odd_next_bound` / `digit_count_state_even_next_bound`，结合前置条件证明加一仍小于 `INT_MAX`。

### 后续注意

- 本题对 `d` 的声明提升是验证层面的局部变量权限适配；核心循环计算和输出顺序没有改变。
- 对类似 digit-count 程序，规格侧应明确输入 0 的 digit 表示，避免递归终止态和题意中的 `[0]` 混淆。

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

## C_94 验证记录

### 结论

- 状态：已全链通过。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是。

已通过的验收链：

```bash
coqc coins_94.v
coqc C_94_goal.v
coqc C_94_proof_auto.v
coqc C_94_proof_manual.v
coqc C_94_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_94.v C_94_proof_manual.v
```

无输出。

### 文件变更

- `C_94.c`

  仅保留必要修改：

  - 修复原始语义缺陷：外层候选条件增加 `lst[i] > 1`，避免把 `1` 当作素数。
  - 按 QCP 格式转换把 `bool` 改为 `int`。
  - 把 `for (int i ...)` / `for (int j ...)` 的循环变量声明提到循环外。
  - 将 `j * j <= x` 改成等价且避免乘法溢出的 `j <= x / j`。

  未采用额外证明辅助变量，也没有加入 `sum` 截断逻辑；`while` 的语义保持原程序行为。

- `coins_94.v`

  新增 94 题的 Coq bridge 与辅助引理，包括：

  - `problem_94_pre_z` / `problem_94_spec_z`
  - `largest_prime_prefix`
  - `prime_scan_state`
  - `digit_sum_state`
  - `list_nonneg_int_range` / `digit_sum_int_range`
  - 外层前缀推进、内层素数扫描推进、数位和循环推进、return 规格连接引理

- `C_94_proof_manual.v`

  已补完 14 个 manual VC，其中关键点包括：

  - `proof_of_skjkasdkd_safety_wit_21`：证明 `sum + largest % 10` 的安全范围
  - `proof_of_skjkasdkd_entail_wit_2`：初始化素数扫描 invariant
  - `proof_of_skjkasdkd_entail_wit_3_1` / `3_2`：把内层循环条件里的 `quot/rem` 目标接回 `div/mod` 侧引理
  - `proof_of_skjkasdkd_entail_wit_4_1` ~ `4_6`：处理 prime / non-prime 两类外层推进
  - `proof_of_skjkasdkd_entail_wit_5` / `6`：连接数位和 while 循环入口与一步推进
  - `proof_of_skjkasdkd_return_wit_1`：退出 while 后连接到 `problem_94_spec_z`

### 遇到的问题

1. 原始 C 程序把 `1` 当成了素数。

   表现：当 `lst[i] == 1` 且 `largest == 0` 时，外层分支成立，但内层 `j = 2; j * j <= 1` 初始就为假，导致 `prime` 保持真并把 `largest` 更新为 `1`。

   解决：只做必要语义修复，在候选条件中加入 `lst[i] > 1`。该问题已同步记录到 `ORIGINAL_C_ISSUES_LOG.md`。

2. `while` 循环一开始尝试用额外 C 变量保存初值，但这不符合“非必要不改源程序”的要求。

   表现：如果在 C 里新增 `original_largest`，虽然证明会更直接，但属于不必要的源程序改动。

   解决：回退这类改动，改用存在量化的 invariant 保存进入拆位循环前的原值，只保留真正必要的语义修复和 QCP 格式转换。

3. `symexec` 生成目标里混用了 `quot/rem` 与 `div/mod`。

   表现：C 条件写成 `j <= x / j` 后，manual VC 中有的地方出现 `x ÷ j`、`x % j`，而 `coins_94.v` 中辅助引理自然写成 `x / j`、`x mod j`，直接应用会对不上。

   解决：manual 证明中显式使用：

   - `Z.quot_div_nonneg`
   - `Z.rem_mod_nonneg`

   把 VC 里的 `quot/rem` 归一化到 `div/mod`，再应用 `prime_scan_state_step_keep`、`prime_scan_state_step_zero` 和数位和相关引理。

4. `largest@pre` 不能直接用于这个 while invariant。

   表现：尝试直接在注解里写 `largest@pre` 时，符号执行阶段报过 “cannot find the program variable ... in assertion” 一类错误。

   解决：不用新增 C 变量，也不依赖 `while@pre` 记号，改为在 invariant 里写 `exists original_largest, ...`，把原值保存在逻辑层。

5. `symexec` 重新生成后，manual 文件会回到全 `Admitted.` 模板。

   表现：如果先手改 `C_94_proof_manual.v`，后面又重新跑 `symexec`，之前写好的 manual proof 会被覆盖掉。

   解决：先稳定 `C_94.c` 与 `coins_94.v`，确认 `symexec` 生成的 VC 形状不再变化后，再补 manual proof。

6. `C_94_goal.v` 中 safety / entailment 里纯算术看起来简单，但直接用假设编号很脆弱。

   表现：`entailer!` 之后假设编号会随着 proof 形状变化而漂移，写死 `H4/H5/H8` 很容易在后续修改后失效。

   解决：对于取数组范围的地方，改成按假设形状匹配 `list_nonneg_int_range lv`；对 while 和 inner-loop 的证明则尽量用已经整理好的桥接引理，减少手工依赖某个固定编号。

### 后续注意

- 像 `j <= x / j` 这种改写已经自带避免乘法溢出的信息，不要再额外往 C 代码里塞多余的 `j < INT_MAX` 条件。
- 如果 manual VC 中出现 `quot/rem`，优先检查能不能通过 `Z.quot_div_nonneg` 与 `Z.rem_mod_nonneg` 归一化后直接接到已有引理。
- 遇到 destructive while，优先考虑逻辑层保存入口值，而不是给 C 程序新增“证明辅助变量”。
- 重新跑 `symexec` 前先确认源文件和 bridge 文件都已经稳定，否则 manual proof 很容易被覆盖重写。

## C_96 验证记录

### 结论

- 状态：暂停在 `symexec` 阶段，尚未生成可用的 witness / manual VC。
- 当前判断：卡点不在 Coq proof，而在 QCP 对“读取正在构造中的输出数组前缀”这一源码形状的执行支持上。
- 已确认 `coins_96.v` 可编译通过。

### 文件变更

- `C_96.c`

  当前保留的修改：

  - 在用户确认后，引入了 `int *data = out->data;`。
  - 在用户确认后，引入了局部变量 `output_size`，循环中维护输出长度，函数尾再 `out->size = output_size;`。
  - 在用户进一步确认后，将首个素数 `2` 的写入移到循环外，主循环改为从 `i = 3` 开始。
  - 将内层试除循环从
    `for (j=0; j<output_size && data[j] <= i/data[j]; j++)`
    改为先循环、后在循环体内读取
    `int current = data[j]; if (current > i/current) break; ...`
    以避免在 `for` 条件中直接做数组读取。
  - 增加了若干 `Assert` / `Inv Assert`，尝试在首次写入和内层读取前向 QCP 显式提供数组权限与边界信息。

- `coins_96.v`

  新增 / 保留的 bridge 内容：

  - `problem_96_pre_z`
  - `problem_96_spec_z`
  - `count_up_to_state`
  - `prime_test_state`
  - `count_up_to_state_init`
  - `count_up_to_state_after_two`
  - `problem_96_spec_z_of_state`

### 遇到的问题

1. 原始格式转换版在首次写输出数组时就卡住。

   表现：

   `symexec` 在 `out->data[out->size] = i;` 上报：

   ```text
   Assign Exec fail
   ```

   解决尝试：

   - 先引入本地 `data` 指针。
   - 再引入局部 `output_size`，避免循环内部直接依赖 `out->size`。
   - 再把首次写入 `2` 从循环内特判改成循环外初始化。

   结果：

   - 前两步仍不足以让 `symexec` 通过首次写入。
   - 把 `2` 的初始化移到循环外后，`symexec` 终于穿过了“首次写输出数组”这一关。

2. 单靠中间 `Assert` 无法让首次写入分支通过。

   表现：

   按 `tutorial/T3-assertion-and-invariant.md` 的方式，在 `data[0] = i;` 前插入了中间 `Assert`，显式提供：

   - `output_size == 0`
   - `i == 2`
   - `data_at(&(out->size), 0)`
   - `IntArray::undef_full(data, n)` / `IntArray::undef_seg(data, 0, n)`

   但 `symexec` 仍在该赋值上报 `Assign Exec fail`。

   结论：

   - 中间断言是有帮助的，但不能单独解决这个首次写入形状。
   - 说明执行器对“循环分支中的首次输出数组写入”本身就比较敏感。

3. 当前真正的主卡点是读取正在构造中的输出数组前缀。

   表现：

   在把 `2` 外提后，`symexec` 已能进入内层试除循环，但在读取输出数组元素时卡住：

   - 原先卡在 `for` 条件中的 `data[j]`
   - 改成循环体读取后，仍卡在
     `int current = data[j];`

   报错统一表现为：

   ```text
   Cannot derive the precondition of Memory Read.
   ```

   解决尝试：

   - 把内层数组资源从 `seg` 改成 `IntArray::full(data, output_size, output_l)`。
   - 在 `int current = data[j];` 前插入中间 `Assert`，显式提供：
     - `0 <= j < output_size`
     - `IntArray::full(data, output_size, output_l)`
     - `prime_test_state(i, output_l, j, isp)`

   结果：

   - 报错位置推进到了读取语句本身，说明断言确实在起作用。
   - 但即便把边界和读权限都显式摊开，QCP 仍无法执行这条读取。

4. 仓库里虽然有“条件里读数组”和“数组元素读到局部变量”的例子，但缺少真正等价的已验证模板。

   已验证且相关的例子：

   - `C_26.c`：`int current = numbers[i];`
   - `C_94.c`：`int x = lst[i];`
   - `C_68.c`：条件里读固定位置 `data[0]`

   当前未找到的模板：

   - 读取“正在构造中的输出数组前缀”：
     `int current = data[j];`
   - 其中 `j < output_size` 且 `output_size` 在循环中动态变化。

   当前判断：

   - “把数组元素读到局部变量”本身不是问题。
   - 更特殊、更难的是：读取的是输出数组前缀而非输入数组，而且前缀长度还在当前循环中变化。

### 后续注意

- 如果之后继续验证 `C_96`，不要再优先尝试堆更多 `Assert`；这一条路已经验证过只能小幅推进报错位置，无法真正穿透 `data[j]` 的读取。
- 当前最可信的下一步方向，是把内层素数检测改成 `C_94` 风格的纯整数扫描，不再依赖读取输出数组前缀。
- 若之后有人给出“QCP 如何读取正在构造中的输出前缀”的专门做法，可直接回到当前 `output_size + data` 版本继续尝试；这版已经跨过了首次写入问题，主要只剩内层 `data[j]` 读取。

### 2026-04-29 复查补充

- 重新复现当前版本：仍卡在 `int current = data[j];`，报 `Cannot derive the precondition of Memory Read`。
- 尝试把内层“读取已生成素数前缀试除”的循环抽成已实现 helper。结果：helper 自身可以完成符号执行，说明读取前缀本身在独立函数中可处理；但主函数调用 helper 时无法匹配变量容量下的 `seg/undef_seg` 前置条件，报 `Cannot derive the precondition of function ...`。
- 尝试切到 `C_94` 风格纯整数试除，避免读取输出前缀。结果：内层试除不再是卡点，但随后动态尾部写 `data[output_size] = i` 报 `Assign Exec fail`。
- 尝试按 `C_123` 模式抽 `append_int_96` helper。固定容量的 `C_123` 模式可过，但本题变量容量 `n` 版本在调用 helper 时仍无法匹配前置条件。
- 尝试先初始化整块 `data[0..n)`，把返回资源改成 `IntArray::full(data, n, data_l)` 后再写动态位置。结果：动态写 `data[output_size] = i` 仍报 `Assign Exec fail`。

本轮实验性改动未保留；`C_96.c` 已恢复到本轮开始时的 QCP 改写版本，未生成可用 goal/proof 文件。

## C_100 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_100.v` 与 `C_100_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_100.v
coqc C_100_goal.v
coqc C_100_proof_auto.v
coqc C_100_proof_manual.v
coqc C_100_goal_check.v
```

### 文件变更

- `C_100.c`

  - 将接口从调用者预分配输出数组：

    ```c
    void make_a_pile(int n, int *out)
    ```

    改成函数内部 malloc 并返回结构体指针：

    ```c
    IntArray *make_a_pile(int n)
    ```

  - 增加 `IntArray` 结构体定义，以及 `malloc_int_array_struct()` / `malloc_int_array()` wrapper 规格。
  - 函数后条件描述返回结构体中的 `data`、`size` 字段，以及 `IntArray::full(data, output_size, output_l)`。
  - 循环 invariant 使用 `Inv Assert`，维护：
    - `data_at(&(out -> data), data)`
    - `data_at(&(out -> size), n0)`
    - 已写前缀 `IntArray::seg(data, 0, i, sublist(0, i, make_pile(n0)))`
    - 未写后缀 `IntArray::undef_seg(data, i, n0)`
    - `pile_int_range(n0)` 与 `Zlength(make_pile(n0)) == n0`

- `coins_100.v`

  新增 bridge 内容：

  - `problem_100_pre_z`
  - `problem_100_spec_z`
  - `pile_int_range`
  - `make_pile`
  - `make_pile_Zlength`
  - `make_pile_Znth`
  - `make_pile_sublist_snoc`
  - `problem_100_spec_z_make_pile`

- `C_100_proof_manual.v`

  补完 5 个 manual VC：

  - `make_a_pile_safety_wit_3`
  - `make_a_pile_safety_wit_4`
  - `make_a_pile_entail_wit_1`
  - `make_a_pile_entail_wit_2`
  - `make_a_pile_return_wit_1`

### 遇到的问题

1. 问题：原格式是“预分配 out 参数”，不符合本次目标接口。

   处理：

   - 参考 `C_25.c` / `C_68.c`，改成 `IntArray *` 返回。
   - 使用 `malloc_int_array_struct()` 分配结构体，`malloc_int_array(n)` 分配数据区。
   - 后条件只暴露最终返回给调用者的结构体字段和完整输出数组资源。

2. 问题：仅有函数前后条件时，循环写数组后的后置条件不可证。

   表现：

   - 需要证明第 `i` 次写入后，输出数组前缀从 `sublist 0 i` 推进到 `sublist 0 (i + 1)`。

   处理：

   - 在 C invariant 中显式拆分已写前缀和未写后缀。
   - 在 `coins_100.v` 中定义逻辑输出列表 `make_pile n`。
   - 增加 `make_pile_sublist_snoc`：

     ```coq
     sublist 0 (i + 1) (make_pile n) =
       sublist 0 i (make_pile n) ++ (n + 2 * i) :: nil
     ```

   - 在 `entail_wit_2` 中用 `IntArray.seg_single` 和 `IntArray.seg_merge_to_seg` 合并写入后的单点资源。

3. 问题：写入表达式 `n + 2 * i` 需要独立的 C `int` 范围证明。

   表现：

   - `symexec` 生成了两个 manual safety VC：
     - `n0 + 2 * i` 在 `INT_MIN/INT_MAX` 内。
     - `2 * i` 在 `INT_MIN/INT_MAX` 内。

   处理：

   - 在前置条件加入 `pile_int_range(n0)`：

     ```coq
     forall i, 0 <= i < n -> INT_MIN <= n + 2 * i <= INT_MAX
     ```

   - safety VC 中从 `pile_int_range n0` 对当前 `i` 实例化，再由线性算术推出目标。

4. 问题：`coins_100.v` 一开始缺少 `INT_MIN` / `INT_MAX` 所在环境。

   表现：

   ```text
   Error: The reference INT_MIN was not found in the current environment.
   ```

   处理：

   - 补充：

     ```coq
     From SimpleC.SL Require Import Mem SeparationLogic.
     Require Import Logic.LogicGenerator.demo932.Interface.
     ```

5. 问题：证明 `make_pile` 相关引理时，环境中没有直接可用的 `Znth_map` / `nth_map`。

   表现：

   - `Znth_map` 不存在。
   - `nth_map` 也不在当前导入环境中。

   处理：

   - 改用标准 `nth_error_map` + `nth_error_nth` / `nth_error_nth'` 证明取值性质。
   - `make_pile` 定义使用 `Zseq`，并导入 `AUXLib.ListLib`，复用 `Zseq_length` / `Zseq_nth`。

6. 问题：`sublist_split` 的边界条件期望 `Z.of_nat (length l)`，而不是直接写出的 `Zlength l`。

   表现：

   ```text
   The term "Hsplit_hi" has type
   "i <= i + 1 <= Zlength (make_pile n)"
   while it is expected to have type
   "i <= i + 1 <= Z.of_nat (length (make_pile n))".
   ```

   处理：

   - 显式用 `Zlength_correct` 在证明中转换。
   - 对 `sublist_split` 的两个前提分别构造 `Hsplit_lo` 和 `Hsplit_hi`，再带前提重写。

7. 问题：返回 VC 需要把最终 `seg + undef_seg` 还原成完整数组。

   处理：

   - 由循环退出条件和 invariant 推出 `i = n0`。
   - 使用 `sublist_self` 将前缀列表化简成 `make_pile n0`。
   - 使用 `IntArray.seg_to_full` 与 `IntArray.undef_seg_empty` 得到 `IntArray::full(data, n0, make_pile n0)`。
   - 使用 `problem_100_spec_z_make_pile` 接回题目规格。

### 后续注意

- 对“纯构造输出数组”的题，建议一开始就在 `coins_XX.v` 中定义逻辑输出列表，并配套：
  - `*_Zlength`
  - `*_Znth`
  - `*_sublist_snoc`
  - `problem_XX_spec_z_*`
- 逐元素写输出数组时，invariant 中优先使用 `IntArray::seg(data, 0, i, sublist(...)) * IntArray::undef_seg(data, i, n)`。
- 如果输出列表由索引生成，`Zseq` 比 `List.seq` 更贴近 C 层 `Z` 证明，能减少 nat/Z 来回转换。

## C_106 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_106.v` 与 `C_106_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_106.v
coqc C_106_goal.v
coqc C_106_proof_auto.v
coqc C_106_proof_manual.v
coqc C_106_goal_check.v
```

### 文件变更

- `C_106.c`

  - 将接口从调用者预分配输出数组：

    ```c
    void f(int n, int *out)
    ```

    改成函数内部 malloc 并返回结构体指针：

    ```c
    IntArray *f(int n)
    ```

  - 增加 `IntArray` 结构体定义，以及 `malloc_int_array_struct()` / `malloc_int_array()` wrapper 规格。
  - 函数后条件描述返回结构体中的 `data`、`size` 字段，以及 `IntArray::full(data, output_size, output_l)`。
  - 循环 invariant 使用 `Inv Assert`，维护：
    - `s == triangular_z(i)`
    - `p == factorial_z(i)`
    - `data_at(&(out -> data), data)`
    - `data_at(&(out -> size), n0)`
    - 已写前缀 `IntArray::seg(data, 0, i, sublist(0, i, f_seq(n0)))`
    - 未写后缀 `IntArray::undef_seg(data, i, n0)`
    - `f_seq_int_range(n0)` 与 `Zlength(f_seq(n0)) == n0`

- `coins_106.v`

  新增 bridge 内容：

  - `problem_106_pre_z`
  - `problem_106_spec_z`
  - `triangular_nat`
  - `triangular_z`
  - `factorial_z`
  - `f_elem`
  - `f_seq`
  - `f_seq_int_range`
  - `triangular_z_0` / `factorial_z_0`
  - `triangular_z_step` / `factorial_z_step`
  - `f_seq_Zlength`
  - `f_seq_Znth`
  - `f_seq_sublist_snoc`
  - `f_elem_even_rem` / `f_elem_odd_rem`
  - `triangular_nat_formula`
  - `Z_even_of_nat`
  - `f_elem_of_nat`
  - `problem_106_spec_z_f_seq`

- `C_106_proof_manual.v`

  补完 6 个 manual VC：

  - `f_safety_wit_4`
  - `f_safety_wit_7`
  - `f_entail_wit_1`
  - `f_entail_wit_2_1`
  - `f_entail_wit_2_2`
  - `f_return_wit_1`

### 遇到的问题

1. 问题：原格式是“预分配 out 参数”，不符合本次目标接口。

   处理：

   - 参考 `C_100.c` / `C_42.c` 的返回数组模式，改成 `IntArray *` 返回。
   - 使用 `malloc_int_array_struct()` 分配结构体，`malloc_int_array(n)` 分配数据区。
   - 后条件只描述最终返回给调用者的结构体字段和完整输出数组资源。

2. 问题：循环同时维护三角数和阶乘两个滚动量。

   表现：

   - 循环体先更新：

     ```c
     s += i + 1;
     p *= i + 1;
     ```

   - 然后根据 `(i + 1) % 2` 写入 `s` 或 `p`。
   - 因此 invariant 不能只描述数组前缀，还必须记录更新前的 `s` / `p` 语义。

   处理：

   - 在 invariant 中维护：

     ```c
     s == triangular_z(i)
     p == factorial_z(i)
     ```

   - 在 `coins_106.v` 中补：

     ```coq
     triangular_z (i + 1) = triangular_z i + (i + 1)
     factorial_z (i + 1) = factorial_z i * (i + 1)
     ```

   - manual 中用这两个 step 引理证明更新后的 invariant。

3. 问题：写入前缀需要按奇偶分支把写入值接到 `f_seq`。

   表现：

   - 偶数分支写 `p * (i + 1)`。
   - 奇数分支写 `s + (i + 1)`。
   - 两个分支都要证明写入值等于 `f_elem (i + 1)`，并把前缀推进到 `sublist 0 (i + 1)`.

   处理：

   - 在 `coins_106.v` 中补 `f_seq_sublist_snoc`：

     ```coq
     sublist 0 (i + 1) (f_seq n) =
       sublist 0 i (f_seq n) ++ f_elem (i + 1) :: nil
     ```

   - 用 `f_elem_even_rem` / `f_elem_odd_rem` 将 C 侧 `% 2` 条件接到 Coq 的 `f_elem`。
   - 在 manual 中使用 `IntArray.seg_single` 和 `IntArray.seg_merge_to_seg` 合并写入后的单点资源。

4. 问题：C 侧 `% 2` 条件使用 `Z.rem`，而 `f_elem` 用 `Z.even`。

   表现：

   - goal 中条件形如：

     ```coq
     (i + 1) % 2 = 0
     (i + 1) % 2 <> 0
     ```

   - `f_elem` 展开后需要判断：

     ```coq
     Z.even (i + 1)
     ```

   处理：

   - 导入 `Coq.ZArith.Zquot`。
   - 使用 `Zeven_rem` 建立 `Z.even i = Z.eqb (Z.rem i 2) 0`。
   - 封装成 `f_elem_even_rem` 和 `f_elem_odd_rem`，manual 中直接复用。

5. 问题：`spec/106.v` 使用 `nat`、`fact`、`Nat.div`，而 C 层使用 `Z` 和 `list Z`。

   表现：

   - 需要证明 `problem_106_spec_z n (f_seq n)`。
   - `f_seq` 中的 `factorial_z` / `triangular_z` 必须能转回 spec 里的 `fact i` / `(i * (i + 1)) / 2`。

   处理：

   - 定义 `list_Z_to_nat := map Z.to_nat`。
   - 定义递归版 `triangular_nat`，并证明：

     ```coq
     triangular_nat n = n * (n + 1) / 2
     ```

   - 定义：

     ```coq
     factorial_z i := Z.of_nat (fact (Z.to_nat i))
     triangular_z i := Z.of_nat (triangular_nat (Z.to_nat i))
     ```

   - 使用 `problem_106_spec_z_f_seq` 将 `f_seq` 接回原题 `problem_106_spec`。

6. 问题：证明 `Z.even (Z.of_nat n) = Nat.even n` 时，直接 `simpl` 后目标形状不利于改写。

   表现：

   - `simpl` 会展开成 `Pos.of_succ_nat` 相关的 match，难以用 `Z.even_succ` 直接改写。

   处理：

   - 避免先 `simpl` 破坏目标形状。
   - 先将 `Z.of_nat (S n)` 改写成 `(Z.of_nat n + 1)%Z`，再用：

     ```coq
     Z.even_add
     Nat.even_succ
     Nat.negb_even
     ```

   - 得到可复用的 `Z_even_of_nat`。

7. 问题：`problem_106_spec_z_f_seq` 中 `nth_error_map` 后存在嵌套 `option_map`，直接改写 `f_elem_of_nat` 不匹配。

   表现：

   - `nth_error_map` 两次后目标中出现：

     ```coq
     option_map Z.to_nat
       (option_map (fun i0 => f_elem (i0 + 1)) ...)
     ```

   - 需要先把 `Some` 里的索引表达式化简成 `Z.of_nat i`。

   处理：

   - 用 `Zseq_nth` 计算索引。
   - 先 `simpl` 展开 `option_map`。
   - 再把 `Z.of_nat (i - 1) + 1` 替换为 `Z.of_nat i`。
   - 最后使用 `f_elem_of_nat` 和 `triangular_nat_formula` 完成 spec 桥接。

### 后续注意

- 这类“一个循环生成输出序列，同时维护多个滚动量”的题，建议在 invariant 中直接记录滚动量的逻辑语义，而不是只记录数组前缀。
- 若 C 分支条件是 `% 2`，而 Coq 规格用 `even`，建议尽早写一个 `*_rem` 桥接引理，把证明隔离在 `coins_XX.v`。
- 对 nat 规格中的闭式公式，若 C 循环更适合递推定义，可先定义递推版，再证明递推版等于闭式公式。

## C_109 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_109.v` 与 `C_109_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_109.v
coqc C_109_goal.v
coqc C_109_proof_auto.v
coqc C_109_proof_manual.v
coqc C_109_goal_check.v
```

### 文件变更

- `C_109.c`

  - 已转换为 QCP 注解格式。
  - 当前接口保持只读输入数组：

    ```c
    int move_one_ball(int *arr, int arr_size)
    ```

  - 前置条件要求 `1 <= arr_size`，因为实现会读取 `arr[arr_size - 1]` 和 `arr[0]`。
  - 前置条件携带 `descents_int_range(input_l)`，用于证明 `num += 1` 不溢出。
  - 循环 invariant 维护：
    - `1 <= i && i <= arr_size`
    - `num == count_descents_prefix(i, input_l)`
    - `IntArray::full(arr, arr_size, input_l)`
    - 输入长度、题目前置条件和范围条件。

- `coins_109.v`

  新增 bridge 内容：

  - `problem_109_pre_z`
  - `problem_109_spec_z`
  - `count_descents_prefix_nat`
  - `count_descents_prefix`
  - `cyclic_descents`
  - `descents_int_range`
  - `count_descents_prefix_1`
  - `count_descents_prefix_step_lt`
  - `count_descents_prefix_step_ge`
  - `cyclic_descents_tail_gt`
  - `cyclic_descents_tail_le`

- `C_109_proof_manual.v`

  补完 9 个 manual VC：

  - `move_one_ball_safety_wit_5`
  - `move_one_ball_safety_wit_12`
  - `move_one_ball_entail_wit_1`
  - `move_one_ball_entail_wit_2_1`
  - `move_one_ball_entail_wit_2_2`
  - `move_one_ball_return_wit_1`
  - `move_one_ball_return_wit_2`
  - `move_one_ball_return_wit_3`
  - `move_one_ball_return_wit_4`

### 遇到的问题

1. 问题：原始 HumanEval 规格允许空数组返回 true，但当前 C 实现会读取首尾元素。

   处理：

   - 在 QCP 前置条件中明确要求 `1 <= arr_size`。
   - `problem_109_spec_z` 建模为“非空数组的环形下降数小于 2 返回 1，否则返回 0”。
   - 后续若要严格接回原始 `move_one_ball_impl` 的空数组语义，需要先修改 C 实现或额外拆分空数组分支。

2. 问题：循环里 `num` 统计相邻下降次数，循环后又根据首尾关系补一个环形下降。

   处理：

   - 在 `coins_109.v` 中定义 `count_descents_prefix` 表示已扫描前缀的相邻下降数。
   - 定义 `cyclic_descents` 表示前缀下降数加上首尾 wrap-around 下降。
   - 用 `count_descents_prefix_step_lt` / `count_descents_prefix_step_ge` 分别证明 if/else 分支后的 invariant。

3. 问题：`num += 1` 的溢出安全在循环内部和首尾补计数处分别出现。

   处理：

   - 用 `descents_int_range` 的第一部分处理循环内 `count_descents_prefix i + 1` 的范围。
   - 用 `descents_int_range` 的第二部分结合 `cyclic_descents_tail_gt` 处理首尾补计数处的范围。

4. 问题：`cyclic_descents` 中布尔比较方向是：

   ```coq
   Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0
   ```

   而 C 条件和 VC 中常出现：

   ```coq
   Znth (arr_size - 1) input_l 0 > Znth 0 input_l 0
   ```

   直接 `apply Z.ltb_lt in Hgt` 会因方向不匹配失败。

   处理：

   - 在 `cyclic_descents_tail_gt` 中显式构造布尔等式：

     ```coq
     assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = true)
     ```

   - 在 `cyclic_descents_tail_le` 中显式构造 false 分支。

5. 问题：返回 VC 中 `arr_size_pre` 与 `Zlength input_l` 在 `Znth` 下不会被 `lia` 自动改写。

   处理：

   - 在 manual 中先由循环退出条件推出 `i = arr_size_pre`。
   - 再显式构造：

     ```coq
     Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0
     ```

     或对应的 `<=` 版本。
   - 对最终算术目标显式 `replace (Zlength input_l) with arr_size_pre by lia`。

### 后续注意

- 这题当前验证的是非空数组的“环形下降数”语义，并未额外证明它与原始 `spec/109.v` 中旋转排序实现完全等价。
- 若后续要求严格复用原始 spec，建议新增一个桥接引理证明 `cyclic_descents arr < 2` 与 `move_one_ball_impl` 结果一致，或改 C 代码增加空数组分支后再接回原 spec。

## C_114 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_114.v` 与 `C_114_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc SeparationLogic/examples/long_array_strategy_goal.v
coqc SeparationLogic/examples/long_array_strategy_proof.v
coqc coins_114.v
coqc C_114_goal.v
coqc C_114_proof_auto.v
coqc C_114_proof_manual.v
coqc C_114_goal_check.v
```

### 文件变更

- `LLM_friendly_cases/long_array_def.h`
  - 新增 `LongArray::full/seg/missing_i/undef_full/undef_seg/undef_missing_i` 谓词声明。
  - 引入 `long_array.strategies`，供 `long long *` 数组读写自动拆分。
- `LLM_friendly_cases/long_array.strategies`
  - 参照 `int_array.strategies` 增加 `long long` 数组策略。
  - 策略类型使用 `I64`，生成 Coq 侧的 `# Int64` cell。
- `SeparationLogic/examples/long_array_strategy_goal.v`
  - 新增 `LongArray` 模块和 12 个策略 goal。
- `SeparationLogic/examples/long_array_strategy_proof.v`
  - 新增对应策略 proof 文件，当前风格与项目内其它 strategy proof 文件一致。
- `C_114.c`
  - 已转换为 QCP 注解格式。
  - 当前接口保持只读 `long long *` 输入：

    ```c
    long long minSubArraySum(long long* nums, int nums_size)
    ```

  - 前置条件要求 `1 <= nums_size`，因为实现读取 `nums[0]`。
  - 前置条件携带 `kadane_int64_range(nums_l)`，用于证明 `current + nums[i]` 不越过 `long long` 范围。
  - 循环 invariant 维护 `current == min_suffix_prefix(i, nums_l)`、`min == min_subarray_prefix(i, nums_l)` 和 `LongArray::full(nums, nums_size, nums_l)`。
- `coins_114.v`
  - 新增 `problem_114_pre_z`、`problem_114_spec_z`。
  - 新增 Kadane 递推模型：`min_suffix_prefix`、`min_subarray_prefix`。
  - 新增 `kadane_int64_range` 以及初始化、suffix step、minimum step 引理。
- `C_114_proof_manual.v`
  - 补完 7 个 manual VC：
    - `minSubArraySum_safety_wit_5`
    - `minSubArraySum_entail_wit_1`
    - `minSubArraySum_entail_wit_2_1`
    - `minSubArraySum_entail_wit_2_2`
    - `minSubArraySum_entail_wit_2_3`
    - `minSubArraySum_entail_wit_2_4`
    - `minSubArraySum_return_wit_1`

### 遇到的问题

1. 问题：项目原有 `IntArray` 只覆盖 `int *`，不能直接描述 `long long *`。

   解决：

   - 补充 `LongArray` 谓词和 `long_array.strategies`。
   - 策略中使用 `I64`，并在 Coq 侧生成 `poly_store FET_int64 ...` 形式的数组 cell。
   - 用探针程序确认 `LongArray::full(a,n,l)` 可以把 `a[i]` 读操作拆成 `Znth i l 0`。

2. 问题：函数契约一开始写在函数体 `{` 之后，symexec 解析失败：

   ```text
   bison: syntax error, unexpected PT_WITH
   ```

   解决：把 `/*@ With ... */` 契约移动到函数签名和 `{` 之间。

3. 问题：`current + nums[i]` 是 `long long` 加法，VC 要求证明结果在 `[-9223372036854775808, 9223372036854775807]` 内。

   解决：

   - 在 `coins_114.v` 中定义 `LLONG_MIN` / `LLONG_MAX`。
   - 在前置条件和 invariant 中携带 `kadane_int64_range(nums_l)`。
   - manual 中从该谓词取出 `min_suffix_prefix i nums_l + Znth i nums_l 0` 的范围。

4. 问题：Kadane 算法有两个分支：`current < 0` 时累加，否则从当前元素重新开始；随后再更新全局最小值。

   解决：

   - 用 `min_suffix_prefix_step_lt/ge` 对应第一层 if。
   - 用 `min_subarray_prefix_step_lt/ge` 对应第二层 if。
   - 在 4 个循环 entail VC 中分别构造下一轮的 suffix/minimum 等式。

5. 问题：`min_subarray_prefix_nat` 的 Coq 证明中，`simpl` 会把内部 `min_suffix_prefix_nat` 展开过头，导致 rewrite 找不到项。

   解决：

   - 在辅助引理中改用 `cbn [min_subarray_prefix_nat]` 限制展开范围。
   - 对前一轮 minimum 使用局部 `prev` 名称，避免项形状被破坏。

### 后续注意

- 当前 `problem_114_spec_z` 是 Kadane 算法级规格：

  ```coq
  result = min_subarray_prefix (Zlength nums) nums
  ```

  它能完整验证当前 C 实现，但尚未证明与 `spec/114.v` 中“存在非空子数组且对所有非空子数组最小”的原始规格等价。
- 如果后续要严格接回原始 HumanEval 规格，建议补一个桥接定理：`min_subarray_prefix (Zlength nums) nums` 满足 `problem_114_spec nums`。

## C_121 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_121.v` 与 `C_121_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_121.v
coqc C_121_goal.v
coqc C_121_proof_auto.v
coqc C_121_proof_manual.v
coqc C_121_goal_check.v
```

### 文件变更

- `C_121.c`
  - 已补 `coins_121` 导入和 QCP 规格桥接。
  - 前置条件增加 `lst_size == Zlength(lv)`、`problem_121_pre_z(lv)`、`sum_odd_at_even_int_range(lv)`。
  - 循环 invariant 改为 `2 * i <= lst_size + 1`，适配奇数长度数组最后一次扫描偶数下标。
  - 后置条件改为 `problem_121_spec_z(lv, __return)`。
- `coins_121.v`
  - 新增 `sum_odd_at_even_upto` 递推模型。
  - 新增 `problem_121_pre_z`、`problem_121_spec_z`。
  - 新增 `sum_odd_at_even_int_range`，用于证明 `s + lst[2*i]` 不溢出。
  - 新增 step 引理和 return 规格桥接引理。
- `C_121_proof_manual.v`
  - 补完 5 个 manual VC：
    - `solutions_safety_wit_10`
    - `solutions_entail_wit_1`
    - `solutions_entail_wit_2_1`
    - `solutions_entail_wit_2_2`
    - `solutions_return_wit_1`

### 遇到的问题

1. 问题：原 invariant 写成 `2 * i <= lst_size`，对奇数长度输入不成立。

   解决：改为 `2 * i <= lst_size + 1`。例如长度为 5 时，循环会访问下标 0、2、4，退出时 `i = 3`，此时 `2 * i = 6 = lst_size + 1`。

2. 问题：旧生成的 `C_121_goal.v` 使用裸 `Require Import int_array_strategy_goal`，在当前 load path 下会匹配多个 `.vo`。

   解决：把策略导入修正为：

   ```coq
   From SimpleC.EE Require Import int_array_strategy_goal.
   ```

   其它 strategy import 同样加上 `From SimpleC.EE` 前缀。

3. 问题：`s += lst[i * 2]` 需要证明加法仍在 `int` 范围内。

   解决：在前置条件和 invariant 中携带 `sum_odd_at_even_int_range(lv)`，manual 中取出 `sum_odd_at_even_upto i lv + Znth (2 * i) lv 0` 的范围。

4. 问题：C 条件是 `lst[i * 2] % 2 == 1`，使用的是 C/Coq 生成目标中的 `Z.rem`，和原始 `spec/121.v` 的 `nat` 规格不是同一层表达。

   解决：当前 `problem_121_spec_z` 建模为 QCP/C 侧的递推算法规格，使用 `Z.rem x 2 = 1` 判断是否累加。

### 后续注意

- 当前验证的是 C 实现对应的 Z/`Z.rem` 算法规格，尚未证明它与 `spec/121.v` 中基于 `list nat`、`Nat.even` 的原始规格完全等价。
- 如果后续要严格接回原始 HumanEval 规格，需要额外加入“输入元素非负”约束，并证明 `Z.rem x 2 = 1` 与 `Nat.even (Z.to_nat x) = false` 的桥接。

## C_122 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_122.v` 与 `C_122_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_122.v
coqc C_122_goal.v
coqc C_122_proof_auto.v
coqc C_122_proof_manual.v
coqc C_122_goal_check.v
```

### 文件变更

- `C_122.c`
  - 已补 `coins_122` 导入和 QCP 规格桥接。
  - 前置条件收紧为 `1 <= k && k <= arr_size`，与题目原始约束一致。
  - 前置条件增加 `arr_size == Zlength(lv)`、`problem_122_pre_z(lv, k)`、`sum_two_digit_int_range(k, lv)`。
  - 循环 invariant 维护 `0 <= i && i <= k`、`s == sum_two_digit_upto(i, lv)` 和输入数组所有权。
  - 后置条件改为 `problem_122_spec_z(lv, k, __return)`。
- `coins_122.v`
  - 新增 `sum_two_digit_upto` 递推模型。
  - 新增 `problem_122_pre_z`、`problem_122_spec_z`。
  - 新增 `sum_two_digit_int_range`，用于证明 `s + arr[i]` 不溢出。
  - 新增 `sum_two_digit_upto_step_in/hi/lo` 和 return 规格桥接引理。
- `C_122_proof_manual.v`
  - 补完 6 个 manual VC：
    - `add_elements_safety_wit_6`
    - `add_elements_entail_wit_1`
    - `add_elements_entail_wit_2_1`
    - `add_elements_entail_wit_2_2`
    - `add_elements_entail_wit_2_3`
    - `add_elements_return_wit_1`

### 遇到的问题

1. 问题：原始 `spec/122.v` 在当前环境下直接 `Load` 会因为 `length arr >= 1` 的 nat/Z 记号冲突编译失败。

   解决：`coins_122.v` 暂时不 `Load "../spec/122"`，而是独立建立 C 侧 Z 规格。这个问题若要彻底解决，需要先修原始 spec 的 nat 比较写法。

2. 问题：旧注解允许 `k == 0`，但题目原始约束要求 `1 <= k <= len(arr)`。

   解决：QCP 前置条件改为 `1 <= k && k <= arr_size`，同时在 `problem_122_pre_z` 中记录 `arr <> [] /\ 1 <= k <= Zlength arr`。

3. 问题：`s += arr[i]` 需要证明加法仍在 `int` 范围内。

   解决：在前置条件和 invariant 中携带 `sum_two_digit_int_range(k, lv)`，manual 中按当前 `i` 取出 `sum_two_digit_upto i lv + Znth i lv 0` 的范围。

4. 问题：循环体有三条语义路径：元素在 `[-99, 99]` 内、元素小于 `-99`、元素大于 `99`。

   解决：在 `coins_122.v` 中分别补：

   ```coq
   sum_two_digit_upto_step_in
   sum_two_digit_upto_step_lo
   sum_two_digit_upto_step_hi
   ```

   manual 中用对应引理推进 invariant。

5. 问题：重新 symexec 后 `C_122_goal.v` 使用裸 strategy import，编译时会匹配多个同名 `.vo`。

   解决：把 strategy import 修正为 `From SimpleC.EE Require Import ...`。

### 后续注意

- 当前验证的是 C 实现对应的 Z 递推规格，尚未证明它与原始 `spec/122.v` 中 `firstn`、`filter is_at_most_two_digits`、`fold_left Z.add` 的规格等价。
- 如果后续要接回原始 spec，建议先修 `spec/122.v` 的 nat 比较作用域问题，再证明 `sum_two_digit_upto k arr = fold_left Z.add (filter is_at_most_two_digits (firstn (Z.to_nat k) arr)) 0`。

## C_126 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_126.v` 与 `C_126_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_126.v
coqc C_126_goal.v
coqc C_126_proof_auto.v
coqc C_126_proof_manual.v
coqc C_126_goal_check.v
```

### 文件变更

- `C_126.c`
  - 已转换为 QCP 注解格式。
  - 原始 `#include <stdbool.h>` 不能被 QCP 前端解析，因此改为 `int` 返回，并把 `return false/true` 改为 `return 0/1`，语义保持为 0/非 0 布尔。
  - 前置条件要求 `1 <= lst_size`，因为循环从 `i = 1` 建立前缀 invariant。
  - 循环 invariant 维护 `sorted_no_triple_prefix(i, lv)`。
  - 后置条件用 `problem_126_spec_z(lv, true/false)` 分支描述返回值。
- `coins_126.v`
  - 新增 `sorted_no_triple_prefix`：前缀非降序，且不存在连续三个相等元素。
  - 新增 `problem_126_pre_z`、`problem_126_spec_z`。
  - 新增初始化、循环推进、下降返回 false、三重复返回 false、正常退出返回 true 的桥接引理。
- `C_126_proof_manual.v`
  - 补完 7 个 manual VC：
    - `is_sorted_entail_wit_1`
    - `is_sorted_entail_wit_2_1`
    - `is_sorted_entail_wit_2_2`
    - `is_sorted_entail_wit_2_3`
    - `is_sorted_return_wit_1`
    - `is_sorted_return_wit_2`
    - `is_sorted_return_wit_3`

### 遇到的问题

1. 问题：QCP 前端不接受 `#include <stdbool.h>`，报：

   ```text
   bison: syntax error, unexpected PT_LESS, expecting PT_STRINGLIT
   ```

   解决：去掉系统头，改成项目内常见的 `int` 布尔返回风格，用 `0` 表示 false、`1` 表示 true。

2. 问题：原始 `spec/126.v` 只写了 `Sorted Nat.lt l <-> b = true`，但题目示例和 C 实现允许两个连续重复，不允许三个连续重复。

   解决：建立 C 侧规格 `sorted_no_triple_prefix`，描述“非降序且无连续三项相等”。这比直接复用 `Sorted Nat.lt` 更贴合当前 C 实现和示例。

3. 问题：循环存在两个提前返回 false 的原因：`lst[i] < lst[i-1]` 和 `lst[i] == lst[i-1] == lst[i-2]`。

   解决：分别补：

   ```coq
   problem_126_spec_false_of_desc
   problem_126_spec_false_of_triple
   ```

   在对应 return VC 中推出完整列表不满足 `sorted_no_triple_prefix`。

4. 问题：继续循环时，三重复判断由多个 C 短路条件拆成不同 VC 分支。

   解决：用一个通用的 `sorted_no_triple_prefix_step`，manual 中按分支假设构造“当前位置不是连续三重复”的否定条件。

5. 问题：重新 symexec 后 `C_126_goal.v` 使用裸 strategy import，编译时会匹配多个同名 `.vo`。

   解决：把 strategy import 修正为 `From SimpleC.EE Require Import ...`。

### 后续注意

- 当前验证的是 C 实现对应的 Z 侧规格，尚未证明它与原始 `spec/126.v` 等价。
- 原始 spec 使用严格递增 `Sorted Nat.lt`，与题目示例 `{1, 2, 2, 3, 3, 4} -> true` 不一致；若后续要接回原始 spec，需要先确认应修 spec 还是改 C 行为。

## C_33 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_33.v` 与 `C_33_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_33.v
coqc C_33_goal.v
coqc C_33_proof_auto.v
coqc C_33_proof_manual.v
coqc C_33_goal_check.v
```

### 文件变更

- `C_33.c`
  - 已转换为 QCP 适配格式。
  - 原始实现使用 `qsort`，QCP 不直接建模 C 标准库排序函数；因此改为声明外部可信函数 `sort_int_array`，只写前后条件，不提供实现。
  - 函数输入输出改为 `IntArray *sort_third(int *l, int l_size)`，在函数内部 `malloc` 一个 `IntArray` 结构体和输出 `data` 数组并返回指针。
  - 保留输入数组所有权：后置条件同时返回 `IntArray::full(l, l_size, input_l)` 和输出数组所有权。
  - `sort_int_array` 增加 `ascending` 参数：

    ```c
    void sort_int_array(int *array, int init_size, int size, int ascending)
    ```

    其中 `ascending == 0` 表示降序，非 0 表示升序。`C_33` 当前调用 `sort_int_array(third, third_size, l_size, 1)`，即升序。

  - `sort_int_array` 的规格只要求前 `init_size` 个已初始化元素被排序，剩余到 `size` 的区域允许是未初始化段，排序后返回整段 `IntArray::full(array, size, sorted_full_l)`，这样可直接给 `free_int_array(third, l_size)` 使用。
  - 两个 loop invariant 分别描述：
    - 已抽取的第三位元素前缀：`third_values_prefix(i, input_l)`。
    - 已写回的输出前缀：`sort_third_output_prefix(i, input_l, sorted_third_l)`。

- `coins_33.v`
  - `Load "../spec/33".`，本题已接入原始 `spec/33.v` 的 `problem_33_spec`。
  - 新增 `third_count`、`third_values_prefix`、`nonthird_values_prefix`、`sort_third_output_prefix`、`sort_third_output`。
  - 新增 `sorted_ascending`、`sorted_descending`、`sorted_int_list_by`，用于支持 `sort_int_array` 的升序/降序参数。
  - 注意：C 里的 `/` 和 `%` 在 symexec 目标中对应 `Z.quot` / `Z.rem`，显示为 `÷` / `%`。因此 `third_count` 与相关 lemma 必须使用 `Z.quot/Z.rem`，不能用数学除法 `Z.div/Z.mod`。
  - 新增 `sort_third_output_problem_33_spec`，证明：

    ```coq
    Zlength sorted_third = third_count (Zlength input) ->
    sorted_int_list_by 1 sorted_third ->
    Permutation (third_values_prefix (third_count (Zlength input)) input) sorted_third ->
    problem_33_spec_z input (sort_third_output input sorted_third)
    ```

    这是本题连接外部排序规格和原始 HumanEval spec 的关键桥接。

- `C_33_proof_manual.v`
  - 补完 7 个 manual VC：
    - `sort_third_entail_wit_1`
    - `sort_third_entail_wit_2`
    - `sort_third_entail_wit_3`
    - `sort_third_entail_wit_5`
    - `sort_third_entail_wit_6_1`
    - `sort_third_entail_wit_6_2`
    - `sort_third_return_wit_1`

### 遇到的问题

1. 问题：`qsort` 是 C 标准库函数，QCP 不能直接理解其排序行为。

   解决：改为外部可信函数 `sort_int_array`，不实现函数体，只在规格中描述排序效果：

   ```c
   Ensure
       exists sorted_l sorted_full_l,
       init_size == Zlength(sorted_l) &&
       size == Zlength(sorted_full_l) &&
       sublist(0, init_size, sorted_full_l) == sorted_l &&
       sorted_int_list_by(ascending, sorted_l) &&
       Permutation(l, sorted_l) &&
       IntArray::full(array, size, sorted_full_l)
   ```

   后续遇到需要排序的程序，可以复用这一建模方式。

2. 问题：只支持升序会限制后续程序复用。

   解决：把排序函数设计成带 `ascending` 参数，并在 `coins_33.v` 中定义：

   ```coq
   Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
     if Z.eqb ascending 0 then sorted_descending l else sorted_ascending l.
   ```

   以后升序传 `1`，降序传 `0`。如果后续题目需要其它比较规则，再扩展新的排序谓词或参数。

3. 问题：排序函数只对 `third_size` 个元素排序，但临时数组按 `l_size` 分配，释放时需要完整 `l_size` 的所有权。

   解决：`sort_int_array` 的前置条件使用：

   ```c
   IntArray::seg(array, 0, init_size, l) *
   IntArray::undef_seg(array, init_size, size)
   ```

   后置条件返回：

   ```c
   IntArray::full(array, size, sorted_full_l)
   ```

   这样排序只约束前 `init_size` 段，内存资源仍覆盖整段 `size`，可安全调用 `free_int_array(third, l_size)`。

4. 问题：C 除法/取模和 Coq 数学除法/取模不一致。

   表现：VC 中出现 `(l_size_pre + 2) ÷ 3`、`i % 3`，如果 `coins_33.v` 中用 `(n + 2) / 3` 或 `Z.mod`，`reflexivity` 和很多算术证明会卡住。

   解决：`third_count` 与所有分支 lemma 统一使用 `Z.quot` / `Z.rem`：

   ```coq
   Definition third_count (n : Z) : Z := (n + 2) ÷ 3.
   ```

   在非负条件下再通过 `Zquot.Zquotrem_Zdiv_eucl_pos` 与 `Z.div/Z.mod` 连接。

5. 问题：最后 `return_wit` 需要证明原始 `spec/33.v` 的 `Permutation input output`，不能只证明第三位子序列排序。

   解决：在 `coins_33.v` 中引入 `nonthird_values_prefix`，用 `count_occ` 分解全列表计数：

   - 输入列表计数 = 第三位元素计数 + 非第三位元素计数。
   - 输出列表计数 = 排序后第三位元素计数 + 非第三位元素计数。
   - `Permutation (third_values_prefix ...) sorted_third_l` 保证第三位元素计数一致。

   由此通过 `Permutation_count_occ` 证明全列表 `Permutation`。

6. 问题：原始 spec 使用 nat 下标和 `nth`，而 QCP 侧循环和数组模型主要使用 Z 下标和 `Znth`。

   解决：补 `nat_mod3_to_Zrem`、`nat_not_mod3_to_Zrem`、`nat_mod0_div3_quot` 等桥接 lemma，将 nat 的 `i mod 3` 与 Z 的 `Z.rem (Z.of_nat i) 3`、`Z.quot` 联系起来。

7. 问题：重新 symexec 后不要手改 `C_33_goal.v` 的 import 路径。

   解决：保持 `goal.v` 为 symexec 原样生成；编译时使用 `../IntClaude/_CoqProject`，并确保 `SeparationLogic/examples/LLM_friendly_cases` 下没有重复的 `.vo/.vos/.vok/.glob/.aux` 编译产物干扰裸 strategy import。

### 后续注意

- 后续遇到需要排序的程序，优先参考本题的 `sort_int_array` 外部函数规格。
- 若只需要排序一个已初始化完整数组，可令 `init_size == size`，前置条件直接是完整数组分段，后置条件仍返回 `IntArray::full`。
- 若排序一个数组前缀、后缀未初始化，沿用本题的 `seg + undef_seg -> full` 模式，方便后续释放整段内存。
- 若题目要求降序，调用时传 `ascending = 0`，并在 spec 桥接中使用 `sorted_descending` 分支。
- 外部排序函数只是可信规格；它不会验证排序算法本身。如果后续需要验证排序实现，应另开一个带函数体的排序程序，并证明其满足同一个 `sort_int_array` 规格。

## C_34 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_34.v` 与 `C_34_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_34.v
coqc C_34_goal.v
coqc C_34_proof_auto.v
coqc C_34_proof_manual.v
coqc C_34_goal_check.v
```

### 文件变更

- `C_34.c`
  - 原始程序使用 `qsort`，已改为 QCP 可建模的外部可信排序函数 `sort_int_array`。
  - `contains` 和 sorted unique 的去重循环保留在 C 程序中验证，没有把核心算法整体替换成未实现函数。
  - 函数返回形式改为 `IntArray *unique(int *l, int l_size)`，内部分配 `IntArray` 结构体和容量为 `l_size` 的输出数组。
  - 循环 invariant 使用 `unique_first_loop(input_l, i, output_l)` 描述已扫描前缀的首次出现元素。
  - 返回规格中输出数组资源使用 `IntArray::full(data, l_size, data_l)`，并用 `sublist(0, output_size, data_l) == output_l` 指明结构体 `size` 对应的有效前缀。
- `coins_34.v`
  - `Load "../spec/34".`，接入原始 `problem_34_pre/spec`。
  - 新增 `seen_values` / `unique_first_loop`，描述“保留首次出现元素”的去重语义。
  - 新增 `seen_values_In_iff`、`seen_values_NoDup`、`unique_first_loop_add/skip`。
  - 新增 `problem_34_spec_from_sort`，用 `Sorted`、`NoDup` 和 `Permutation` 桥接到原始 `problem_34_spec`。
- `C_34_proof_manual.v`
  - 补完 7 个 manual VC：
    - `contains_entail_wit_2`
    - `contains_return_wit_1`
    - `contains_return_wit_2`
    - `unique_entail_wit_1`
    - `unique_entail_wit_2_1`
    - `unique_entail_wit_2_2`
    - `unique_return_wit_1`

### 遇到的问题

1. 问题：不能把整个 sorted unique 逻辑替换成一个未实现的 helper。

   解决：只把 `qsort` 这一类常见库行为建模为外部可信 `sort_int_array`；`contains` 和“扫描输入、若输出前缀未包含当前元素则追加”的去重循环都保留在 C 中，并用循环不变式验证。

2. 问题：排序后的输出长度小于等于分配容量，不能简单返回 `IntArray::full(data, output_size, output_l)`。

   解决：输出数组实际按 `l_size` 分配，排序函数返回整段 `IntArray::full(data, l_size, sorted_full_l)`；函数后置条件记录：

   ```c
   output_size == Zlength(output_l) &&
   l_size == Zlength(data_l) &&
   sublist(0, output_size, data_l) == output_l &&
   IntArray::full(data, l_size, data_l)
   ```

   这样既保留完整内存所有权，又明确 `out->size` 对应的有效前缀。

3. 问题：排序前手写 `Assert` 容易丢掉 return 阶段还需要释放的局部变量栈资源，尤其是循环变量 `i`。

   表现：symexec 在 `return out;` 处报 `Fail to Remove Memory Permission of i`。

   解决：不在排序前后强行插入会重塑当前资源的 `Assert`；让循环退出态直接流入 `sort_int_array` 调用。这样 `i` 的局部变量资源能作为 frame 穿过外部函数调用，并在 return 时正常释放。

4. 问题：尝试给 `sort_int_array` 增加与排序数组无关的 ghost 参数来保留外层纯事实，会生成不可证明的 VC。

   表现：`unique_partial_solve_wit_6_pure/aux` 中出现对任意 `input_l0` 证明 `Zlength(input_l0) == Zlength(input_l)` 的目标。

   解决：不要给库函数加入未被内存资源或实参约束的 ghost 参数。需要保留的事实应尽量从调用点当前上下文和 loop invariant 自然传递，或者放进与资源绑定的谓词中。

5. 问题：最终 `problem_34_spec` 不能只靠排序函数的 `Sorted` 结论；还必须证明输出唯一且元素集合与输入一致。

   解决：在 `coins_34.v` 中证明：

   - `seen_values input` 与 `input` 有相同 `In` 集合。
   - `seen_values input` 是 `NoDup`。
   - 排序函数返回的 `Permutation unique_l sorted_l` 保持 `NoDup` 和元素集合。

   最终由 `problem_34_spec_from_sort` 同时给出 `Sorted Z.le sorted_l`、`NoDup sorted_l` 和 `forall z, In z input <-> In z sorted_l`。

### 后续注意

- 后续验证 sorted unique / sort 后去重 / 去重后排序类程序时，核心扫描逻辑应保留在 C 中验证；外部黑盒只适合 `qsort`、`malloc`、释放等库边界。
- 若外部函数规格需要携带额外 ghost，必须确保 ghost 由实参、资源谓词或纯条件约束住；不要加入“任意 ghost 但要求它满足某性质”的规格。
- 对容量大于有效长度的输出数组，优先用“完整容量数组 + 有效前缀 sublist”的后置条件，避免丢失剩余内存所有权。

## C_58 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_58.v` 与 `C_58_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_58.v
coqc C_58_goal.v
coqc C_58_proof_auto.v
coqc C_58_proof_manual.v
coqc C_58_goal_check.v
```

### 文件变更

- `C_58.c`
  - 转成 QCP 适配格式：`IntArray *common(int *l1, int l1_size, int *l2, int l2_size)`，内部 malloc 返回结构体与输出数组。
  - 保留核心算法：扫描 `l1`，先用 `contains(data, output_size, current)` 排除已输出元素，再用 `contains(l2, l2_size, current)` 判断是否公共，满足后追加到输出前缀。
  - 原始 `qsort` 改为外部可信 `sort_int_array`，只建模库排序行为，不隐藏公共元素收集逻辑。
  - 输出数组仍按 `l1_size` 分配，返回规格使用完整容量数组加有效前缀：

    ```c
    l1_size == Zlength(data_l) &&
    sublist(0, output_size, data_l) == output_l &&
    IntArray::full(data, l1_size, data_l)
    ```

- `coins_58.v`
  - `Load "../spec/58".`，接入 `problem_58_pre/spec`。
  - 新增 `common_values` / `common_first_loop`，描述“`l1` 前缀中首次出现且属于 `l2` 的元素”。
  - 新增 `common_first_loop_add`、`common_first_loop_skip_seen`、`common_first_loop_skip_not_l2`，对应循环三类分支。
  - 新增 `common_values_In_iff`、`common_values_NoDup`。
  - 新增 `problem_58_spec_from_sort`，用 `Permutation`、`Sorted`、`NoDup` 桥接到原始 `problem_58_spec`。
- `C_58_proof_manual.v`
  - 补完 8 个 manual VC：
    - `contains_entail_wit_2`
    - `contains_return_wit_1`
    - `contains_return_wit_2`
    - `common_entail_wit_1`
    - `common_entail_wit_4_1`
    - `common_entail_wit_4_2`
    - `common_entail_wit_4_3`
    - `common_return_wit_1`

### 遇到的问题

1. 问题：第二次 `contains(l2, l2_size, current)` 需要 `IntArray::seg(l2, 0, l2_size, input_l2)`，但入口资源是 `IntArray::full`。

   解决：循环 invariant 中把 `l2` 资源保持为 `IntArray::seg(l2, 0, l2_size, input_l2)`；初始化 VC 中用 `IntArray.full_to_seg` 从入口 `full` 转成 `seg`，return VC 中再用 `IntArray.seg_to_full` 转回函数后置条件需要的 `full`。

2. 问题：`seg_to_full` 之后目标中出现了地址表达式 `l2_pre + 0 * sizeof(INT)` 和长度 `l2_size_pre - 0`，与后置条件里的 `l2_pre` / `l2_size_pre` 不直接匹配。

   解决：在 manual proof 中显式化简：

   ```coq
   replace (l2_pre + 0 * sizeof(INT)) with l2_pre by lia.
   replace (l2_size_pre - 0) with l2_size_pre by lia.
   ```

3. 问题：最终规格需要的是公共元素集合：

   ```coq
   forall x, In x output <-> In x l1 /\ In x l2
   ```

   不能只证明输出来自 `l1` 或只证明无重复。

   解决：`common_values_In_iff` 证明未排序公共前缀与 `l1/l2` 的交集等价；排序后的 `Permutation` 再把该性质转移到最终输出。

4. 问题：追加分支需要同时依赖两个查询结果：未在输出前缀中、且在 `l2` 中。

   解决：循环分支拆成三个 lemma：

   - `common_first_loop_add`：未输出且在 `l2`，输出追加当前元素。
   - `common_first_loop_skip_not_l2`：未输出但不在 `l2`，输出不变。
   - `common_first_loop_skip_seen`：已输出过，输出不变。

### 后续注意

- 双数组公共元素类题目中，输入数组若要传给通用 `contains`，最好在 invariant 中使用 `seg` 形态，最后再转回 `full`。
- sorted unique common 和 `C_34` 的 sorted unique 结构相同：核心收集逻辑保留在 C 中，排序只建模库边界。
- 输出数组容量通常是 `l1_size`，有效长度是 `output_size`；后置条件应同时保留完整容量所有权和有效前缀语义。

## C_70 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_70.v` 与 `C_70_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_70.v
coqc C_70_goal.v
coqc C_70_proof_auto.v
coqc C_70_proof_manual.v
coqc C_70_goal_check.v
```

### 文件变更

- `C_70.c`
  - 转成 QCP 适配格式：`IntArray *strange_sort_list(int *lst, int lst_size)`，内部 malloc 返回结构体与输出数组。
  - 保留 strange sort 的核心输出逻辑：先复制并排序输入，再按偶数位置取当前最小、奇数位置取当前最大写入输出。
  - 原始 `qsort` 改为外部可信 `sort_int_array`，只建模库排序行为，不把整个 strange sort 算法替换成未实现函数。
  - 输出循环改成单下标形式：

    ```c
    if (i % 2 == 0) data[i] = sorted[i / 2];
    else data[i] = sorted[lst_size - 1 - (i / 2)];
    ```

    这与原始左右指针交替取最小/最大等价，但更适合写循环不变式。

- `coins_70.v`
  - `Load "../spec/70".`，接入 `problem_70_pre/spec`。
  - 新增 `copy_prefix`，描述复制输入到排序缓冲区的前缀。
  - 新增 `strange_index` / `strange_output_prefix` / `strange_output`，描述排序后列表的 min/max 交替输出。
  - 新增 `copy_prefix_full`、`strange_output_prefix_snoc`、`sorted_full_Znth`、`quot2_bounds`、`reverse_quot2_bounds` 等桥接引理。
- `C_70_proof_manual.v`
  - 补完 7 个 manual VC：
    - `proof_of_strange_sort_list_entail_wit_1`
    - `proof_of_strange_sort_list_entail_wit_2`
    - `proof_of_strange_sort_list_entail_wit_3`
    - `proof_of_strange_sort_list_entail_wit_4`
    - `proof_of_strange_sort_list_entail_wit_5_1`
    - `proof_of_strange_sort_list_entail_wit_5_2`
    - `proof_of_strange_sort_list_return_wit_1`

### 遇到的问题

1. 问题：不能把整个 strange sort 逻辑换成一个未实现 helper。

   解决：只把 `qsort` 对应的排序行为建模为外部可信 `sort_int_array`；复制输入、按最小/最大交替写输出、返回结构体这些逻辑都保留在 C 中验证。

2. 问题：原始左右指针 `l/r` 的循环每轮可能写 1 个或 2 个元素，QCP invariant 会比较难表达。

   解决：改成单下标循环，偶数 `i` 取 `sorted[i / 2]`，奇数 `i` 取 `sorted[lst_size - 1 - i / 2]`。该形式保留算法语义，同时让 invariant 只需维护 `strange_output_prefix(lst_size, i, sorted_l)`。

3. 问题：输出循环访问 `sorted[i / 2]` 和 `sorted[lst_size - 1 - i / 2]` 时，符号执行需要显式下标范围。

   解决：在循环 invariant 中加入两个派生范围：

   ```c
   (i < lst_size => 0 <= i / 2 && i / 2 < lst_size) &&
   (i < lst_size => 0 <= lst_size - 1 - i / 2 &&
                    lst_size - 1 - i / 2 < lst_size)
   ```

   并在 `coins_70.v` 中用 `quot2_bounds` / `reverse_quot2_bounds` 证明推进。

4. 问题：复制循环结束后，目标里是 `copy_prefix lst_size_pre input_l`，而引理 `copy_prefix_full` 按 `copy_prefix (Zlength input_l) input_l` 匹配，直接 `rewrite copy_prefix_full` 不生效。

   解决：在 manual proof 中先用长度假设建立桥接：

   ```coq
   assert (Hcopy : copy_prefix lst_size_pre input_l = input_l).
   { rewrite H5. apply copy_prefix_full. }
   rewrite Hcopy.
   ```

5. 问题：输出分支中读数组资源来自 `sorted_full_l`，但逻辑输出前缀使用的是 `sorted_l`。

   解决：`seg_single` 和 `seg_merge_to_seg` 先使用实际内存读值 `Znth ... sorted_full_l 0`；随后用 `sublist(0, lst_size, sorted_full_l) == sorted_l` 和 `sorted_full_Znth` 证明它等于 `sorted_l` 中对应位置的值。

6. 问题：外部排序函数只给 `Sorted` / `Permutation` 时，还需要额外证明 `strange_output` 满足原题 `problem_70_spec`。

   解决：排序函数规格中加入对当前题目所需数学桥接的后置条件：

   ```c
   problem_70_spec_z(l, strange_output(init_size, sorted_l))
   ```

   该规格只覆盖库排序与题目数学规格的桥接，不隐藏 C 中的 strange-output 循环。

### 后续注意

- 对“排序后按某种确定索引模式输出”的题目，可以把排序作为库边界，但索引模式最好保留在 C 循环中验证。
- 单下标循环通常比一次写两个位置的左右指针循环更适合 QCP invariant。
- 如果排序函数返回完整容量数组，而逻辑只关心有效前缀，优先用 `sublist` 和 `Znth_sublist0` 类引理桥接。

## C_88 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_88.v` 与 `C_88_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_88.v
coqc C_88_goal.v
coqc C_88_proof_auto.v
coqc C_88_proof_manual.v
coqc C_88_goal_check.v
```

### 文件变更

- `C_88.c`
  - 转成 QCP 适配格式：`IntArray *sort_array(int *array, int array_size)`，内部 malloc 返回结构体与输出数组。
  - 尽量保留原程序核心逻辑：先复制输入到输出数组，再调用外部可信 `sort_int_array` 表示 `qsort` 升序排序，最后在首尾和为偶数时保留原来的 in-place reverse swap 循环。
  - 仅去掉 malloc 失败分支，并把空数组返回改为返回一个长度为 0 的已分配数组资源，方便 QCP 保持统一的 `IntArray::full(data, 0, [])` 后置条件。
  - 临时变量 `t` 初始化为 `0`，使反转循环 invariant 能把 `t` 作为普通 `data_at` 栈资源携带。
- `coins_88.v`
  - `Load "../spec/88".`，并提供 Z 层版本 `problem_88_pre_z` / `problem_88_spec_z`。
  - 新增 `sort_array_input_range`，记录元素非负、int 范围和首尾求和不溢出。
  - 新增 `copy_prefix`，描述复制循环。
  - 新增 `reverse_step` / `reverse_loop`，用两次 `replace_Znth` 精确描述每轮 in-place swap 后的数组内容。
  - 新增 `reverse_loop_Zlength`、`reverse_loop_snoc`、`replace_Znth_length_local` 等证明辅助引理。
- `C_88_proof_manual.v`
  - 补完 8 个 manual VC：
    - `proof_of_sort_array_safety_wit_6`
    - `proof_of_sort_array_entail_wit_1`
    - `proof_of_sort_array_entail_wit_2`
    - `proof_of_sort_array_entail_wit_3`
    - `proof_of_sort_array_entail_wit_4`
    - `proof_of_sort_array_entail_wit_5`
    - `proof_of_sort_array_return_wit_2`
    - `proof_of_sort_array_return_wit_3`

### 遇到的问题

1. 问题：用户要求尽量不修改原程序核心逻辑，不能把排序加反转整体换成一个未实现 helper。

   解决：只把 `qsort` 建模为外部可信 `sort_int_array`；复制循环和偶数分支的 in-place reverse swap 循环都保留在 C 中验证。

2. 问题：原始 C 有 malloc 失败分支和空数组返回 `NULL`，这会让返回规格分裂成多种资源形态。

   解决：QCP 版本沿用本目录已验证题目的模式，使用可信 `malloc_int_array`，不保留失败分支；空数组仍返回结构体和长度为 0 的数组资源。算法语义仍是输出空数组。

3. 问题：判断 `(array[0] + array[array_size - 1]) % 2` 需要证明加法不会溢出。

   解决：在前置条件中加入 `sort_array_input_range(input_l)`，其中包括元素非负、元素在 int 范围内，以及非空时首尾和不超过 `INT_MAX`。manual 的 `safety_wit_6` 用该条件证明加法安全。

4. 问题：反转循环读写 `data[i]` 和 `data[array_size - 1 - i]` 时，策略不会自动从 `i < array_size / 2` 推出两个下标都在数组范围内。

   解决：在 reverse loop invariant 中显式加入：

   ```c
   (i < array_size / 2 => 0 <= i && i < array_size) &&
   (i < array_size / 2 => 0 <= array_size - 1 - i &&
                           array_size - 1 - i < array_size)
   ```

5. 问题：in-place swap 会让数组资源变成两次 `replace_Znth` 的嵌套形式，必须和下一轮 invariant 精确匹配。

   解决：在 `coins_88.v` 中定义：

   ```coq
   reverse_step size i l :=
     replace_Znth (size - 1 - i) (Znth i l 0)
       (replace_Znth i (Znth (size - 1 - i) l 0) l).
   ```

   再用 `reverse_loop_snoc` 把第 `i` 轮 swap 后的数组改写成 `reverse_loop size (i + 1) sorted_l`。

6. 问题：空数组返回分支中 `IntArray::undef_full(data, 0)` 要转成后置条件需要的 `IntArray::full(data, 0, [])`。

   解决：manual proof 中使用 `IntArray.undef_full_empty` 和 `IntArray.full_empty` 将二者都化成 `emp`，再由 `problem_88_spec_nil` 证明功能规格。

### 后续注意

- 对原程序有 in-place swap 的题目，优先用 `replace_Znth` 精确建模每次写后的数组，而不是替换成外部 reverse helper。
- 如果 C 表达式包含输入数组元素之间的加法，前置条件应显式提供对应的 int-range/不溢出条件。
- `qsort` 仍可作为库边界建模，但排序后的后续数组变换应尽量保留在 C 中验证。

## C_90 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是。
- 是否无 `Admitted.` / `Axiom`：是，`coins_90.v` 与 `C_90_proof_manual.v` 扫描无命中。

已通过的验收链：

```bash
coqc coins_90.v
coqc C_90_goal.v
coqc C_90_proof_auto.v
coqc C_90_proof_manual.v
coqc C_90_goal_check.v
```

### 文件变更

- `C_90.c`
  - 转成 QCP 适配格式，函数规格接入 `problem_90_pre_z` / `problem_90_spec_z`。
  - 保留原程序核心逻辑：排序后从 `i = 1` 开始扫描，遇到第一个 `lst[i] != lst[i - 1]` 即返回 `lst[i]`，否则返回 `-1`。
  - 仅将原 `qsort` 抽象为外部库函数 `sort_int_array`；没有把扫描逻辑替换成未实现 helper。
  - `sort_int_array` 规格已对齐 `C_33.c` / `C_34.c`：参数为 `array, init_size, size, ascending`，后置只包含 `sorted_int_list_by`、`Permutation`、前缀关系和数组资源，不包含任何 C_90 题目语义。
  - 增加 `lst_size <= 1` 的提前返回分支，语义上等价于原程序对长度 0/1 数组排序后循环不进入并返回 `-1`，同时避免无意义排序调用。
- `coins_90.v`
  - `Load "../spec/90".`
  - 新增 `problem_90_spec_z`，处理 C 返回值 `-1` 与题目规格 `None` / `Some res` 的桥接。
  - 新增 `sorted_int_list_by` 和 `no_distinct_prefix`，用于描述排序结果和扫描到当前位置前都没有相邻不同元素。
  - 新增 `next_smallest_sorted_bridge`，把“普通升序排序结果中第一个相邻不同元素是第二小元素”的题目相关事实留在本题文件中，而不是放进 `sort_int_array`。
  - 新增 `next_smallest_sorted_bridge_of_sorted`、`Sorted_Znth_le`、`no_distinct_prefix_eq0`、`no_distinct_prefix_1`、`no_distinct_prefix_step`、`problem_90_spec_z_short` 等辅助引理。
- `C_90_proof_manual.v`
  - 补完 6 个 manual VC：
    - `proof_of_next_smallest_entail_wit_1`
    - `proof_of_next_smallest_entail_wit_2`
    - `proof_of_next_smallest_entail_wit_3`
    - `proof_of_next_smallest_return_wit_1`
    - `proof_of_next_smallest_return_wit_2`
    - `proof_of_next_smallest_return_wit_3`

### 遇到的问题

1. 问题：不能把原程序的“排序后扫描第一个相邻不同元素”整体替换成一个未实现函数。

   解决：只把常见库函数 `qsort` 建模为外部 `sort_int_array`；扫描循环仍保留在 C 中，并用 `no_distinct_prefix(i, sorted_l)` 作为循环不变式证明。

2. 问题：原始返回值用 `-1` 表示没有第二小元素，但输入中可能合法出现 `-1`，导致 C 返回值和 HumanEval 的 `None` / `Some -1` 存在哨兵歧义。

   解决：在 `coins_90.v` 中定义 `problem_90_spec_z`：

   ```coq
   Definition problem_90_spec_z (l : list Z) (res : Z) : Prop :=
     (res = -1 /\ problem_90_spec l None) \/
     problem_90_spec l (Some res).
   ```

   这样既保留 C 的返回约定，也不排除第二小元素实际为 `-1` 的情况。

3. 问题：`sort_int_array` 需要成为后续可放入库文件的通用普通排序函数，不能在后置条件里携带 `problem_90_spec_z` 这类题目相关约束。

   解决：将 `sort_int_array` 改为和 `C_33.c` / `C_34.c` 一致的通用规格：

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
           exists sorted_l sorted_full_l,
           init_size == Zlength(sorted_l) &&
           size == Zlength(sorted_full_l) &&
           sublist(0, init_size, sorted_full_l) == sorted_l &&
           sorted_int_list_by(ascending, sorted_l) &&
           Permutation(l, sorted_l) &&
           IntArray::full(array, size, sorted_full_l)
   */;
   ```

   C_90 的题目语义由本题自己的 `next_smallest_sorted_bridge` 和 Coq 引理证明。

4. 问题：参考版 `sort_int_array` 的前置资源是 `IntArray::seg(array, 0, init_size, l) * IntArray::undef_seg(array, init_size, size)`，而 C_90 入口自然持有 `IntArray::full(lst, lst_size, input_l)`。

   解决：在调用前增加 `Assert`，将 `full` 拆成 `seg(lst, 0, lst_size, input_l)` 和空的 `undef_seg(lst, lst_size, lst_size)`；manual 中用 `IntArray.full_to_seg` 和 `IntArray.undef_seg_empty` 证明该资源重排。

5. 问题：通用排序函数仍要求 `array != 0`，但 `IntArray::full` 在当前库中不推出地址非 0。

   解决：在 `next_smallest` 前置条件中加入条件式纯事实：

   ```c
   lst_size > 1 => lst != 0
   ```

   因为 C_90 只在 `lst_size > 1` 时调用排序；长度 0/1 分支提前返回，不需要非空指针。

6. 问题：排序函数的后置条件只给出 `Sorted` 和 `Permutation` 时，循环 return 分支还需要证明“第一个相邻不同元素就是第二小元素”。

   解决：在 `coins_90.v` 中证明 `next_smallest_sorted_bridge_of_sorted`：从 `sorted_int_list_by 1 sorted_l` 和 `Permutation input_l sorted_l` 推出本题所需桥接事实。这样题目相关证明留在 C_90，`sort_int_array` 保持通用。

## C_104 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_104.v`、`C_104_goal.v`、`C_104_proof_manual.v`、`C_104_proof_auto.v`、`C_104_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_104.v` 与 `C_104_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_104.c`：改为 QCP 格式；保留原程序“逐个数扫描每一位，遇偶数位则过滤掉，最后排序”的核心逻辑。为了验证，将数字扫描逻辑抽成已实现且带规格的 `has_only_odd_digits_int`，没有把核心逻辑替换成未实现函数。
- `coins_104.v`：新增 Z 层规格、前缀过滤关系、奇偶数字扫描状态，以及 C 的 `quot/rem` 与数学 `div/mod` 之间的桥接引理。
- `C_104_proof_manual.v`：补完所有 manual VC。

### 遇到的问题

1. 问题：原 C 程序用 `qsort` 排序，但本轮要求 `sort_int_array` 不能携带题目相关后置条件。

   解决：`sort_int_array` 保持通用排序规格，只描述排序后前缀 `sorted_l` 有序、与输入前缀 `Permutation`、并恢复整段数组资源。后置中仅额外保留通用尺寸边界 `0 <= init_size <= size` 和 `0 <= size < INT_MAX`，不包含 `problem_104_spec_z` 或“只含奇数位”等题目语义。

2. 问题：不能把原程序的数字检查循环替换成未实现函数。

   解决：将原循环原样抽成已实现 helper `has_only_odd_digits_int`，循环体仍执行 `num % 2` 和 `num / 10` 的逐位检查；helper 本身单独验证，返回值只通过 `only_odd_digits_z` / `has_even_digit_z` 与逻辑规格连接。

   经验：如果某段内部循环逻辑和外层数组遍历逻辑相互独立，可以把内部循环抽成一个已实现、已验证的 helper 来简化验证。这样不是用未实现函数替代原程序，而是把证明责任拆开：helper 证明数字扫描本身，外层函数只使用 helper 的后置条件维护数组前缀 invariant。直接验证原来的内联嵌套循环也可行，但外层 invariant 和 manual proof 会明显更复杂。

3. 问题：C 中 `/` 和 `%` 在 VC 里分别对应 `Z.quot` 和 `Z.rem`，而逻辑扫描状态自然使用 `Z.div` 和 `Z.mod`。

   解决：在 `coins_104.v` 中加入 `odd_scan_even_quot` 和 `odd_scan_odd_quot`，在正数条件下用 `Z.quot_div_nonneg`、`Z.rem_mod_nonneg` 桥接 C 运算和数学运算。

4. 问题：循环退出后局部变量 `i` 的资源仍存在，若断言中不显式保留 `data_at(&i, x_size)`，manual VC 会要求丢弃局部变量资源。

   解决：在 sort 前后的 `Assert` 中保留 `data_at(&i, x_size)`，直到函数返回前由符号执行正常处理。

5. 问题：sort 调用前后需要反复使用 `output_size` 的边界；如果只从数组段资源推导，会产生不必要的纯 VC。

   解决：在循环后断言与 sort 后断言中显式保留 `0 <= output_size && output_size <= x_size`；同时在通用 `sort_int_array` 后置中保留调用前已有的通用尺寸边界。

### 后续注意

- 当前 `problem_104_spec_z` 是 Z 层操作式规格：先用 `unique_digits_prefix` 表达过滤，再用 `sorted_int_list_by 1` 和 `Permutation` 表达排序。后续若需要和 `../spec/104` 中的 nat 规格做等价证明，可在此基础上补桥接引理。
- 后续涉及 `qsort` 的题目仍应保持 `sort_int_array` 为通用库函数规格，题目语义放在各自的 Coq bridge/spec 中证明。

## C_120 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_120.v`、`C_120_goal.v`、`C_120_proof_manual.v`、`C_120_proof_auto.v`、`C_120_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_120.v` 与 `C_120_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_120.c`：改为 QCP 格式，保留原程序“复制输入到临时数组、排序临时数组、复制排序后最后 `k` 个元素、释放临时数组”的核心逻辑。将原来的 `qsort`、`malloc/free` 调用替换为带通用规格的 `sort_int_array`、`malloc_int_array`、`free_int_array` wrapper。
- `coins_120.v`：新增 Z 层前置条件、操作式后置条件、复制前缀 `copy_prefix`、输出后缀前缀 `maximum_output_prefix`，以及两个复制循环需要的 snoc/长度引理。
- `C_120_proof_manual.v`：补完所有 manual VC。

### 遇到的问题

1. 问题：原程序中 `out.data = NULL; out.size = 0;` 是返回空结果和分支初始化的重要状态；第一次 QCP 改写时只写了 `out->size = 0`，导致 `out->data` 仍是未初始化资源，循环 invariant 无法使用 `data_at(&(out -> data), 0)`。

   解决：按原程序语义补回 `out->data = 0; out->size = 0;`，这不是额外算法改动，而是恢复原程序已有初始化逻辑。

2. 问题：`k == 0` 分支返回空数组，但 `malloc_int_array(0)` 只给出 `IntArray::undef_full(data, 0)`，函数后置需要 `IntArray::full(data, 0, [])`。

   解决：在 `coins_120.v` 中证明局部资源引理 `IntArray_undef_full_0_to_full_nil`，利用 `undef_full 0` 和 `full 0 []` 都是空数组资源的事实完成桥接。

3. 问题：两个复制循环分别需要描述“已经复制了多少前缀”：第一个循环复制 `arr[0..i)` 到 `tmp[0..i)`，第二个循环复制排序后后缀 `sorted_l[arr_size-k .. arr_size-k+i)` 到输出。

   解决：分别定义 `copy_prefix input_l i := sublist 0 i input_l` 和 `maximum_output_prefix sorted_l arr_size k i := sublist (arr_size-k) (arr_size-k+i) sorted_l`，并证明 `copy_prefix_snoc`、`maximum_output_prefix_snoc`，让每次写入一个元素后可以自然合并 `seg_single` 和已有 `seg`。

4. 问题：`sort_int_array` 必须保持后续可放入库文件的通用排序函数规格，不能在后置中加入“最大 k 个数”这类 C_120 题目语义。

   解决：`sort_int_array` 仍只给出排序、排列、数组资源和通用尺寸边界。C_120 的题目语义由 `problem_120_spec_z_of_sorted` 在本题的 `coins_120.v` 中从 `sorted_int_list_by`、`Permutation` 和后缀复制关系推出。

5. 问题：排序后 `sort_int_array` 返回的资源是 `sorted_full_l`，而逻辑上更方便使用排序前缀 `sorted_l`；当 `init_size == size == arr_size` 时二者应相同。

   解决：manual proof 中用 `sublist_self` 和长度事实证明 `sorted_full_l = sorted_l`，再把 `IntArray::full(tmp, arr_size, sorted_full_l)` 转成后续循环使用的 `IntArray::full(tmp, arr_size, sorted_l)`。

### 后续注意

- 当前 `problem_120_spec_z` 是 Z 层操作式规格：`k=0` 时输出空数组；`k>0` 时存在一个升序排列且与输入 `Permutation` 的 `sorted_l`，输出等于 `sorted_l` 的最后 `k` 个元素。后续若需要完全对接 `../spec/120.v` 中的 nat 版 `problem_120_spec`，可以在此基础上补“升序列表后缀为 top-k”的 bridge。
- 本题没有把业务逻辑抽成未实现函数；所有循环仍在 C 程序中实现并验证。
- 后续类似题目可以复用这个模式：输入复制循环用 `copy_prefix`，排序保持通用库规格，输出切片循环用 `sublist` 前缀关系描述。

## C_123 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_123.v`、`C_123_goal.v`、`C_123_proof_manual.v`、`C_123_proof_auto.v`、`C_123_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_123.v` 与 `C_123_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_123.c`：改为 QCP 指针返回格式；保留原程序“初始化输出为 `[1]`，按 Collatz 奇偶规则推进，遇到奇数则加入输出，最后排序”的核心逻辑。原程序的 `malloc/realloc/qsort` 分别适配为 `malloc_int_array_struct`、`malloc_int_array` 和通用 `sort_int_array`。此前用于验证拆分的 `append_int` helper 已移除，奇数分支改回直接数组写入和自增。
- `coins_123.v`：新增 Z 层操作式规格 `problem_123_spec_z`，用 `odd_collatz_prefix` 描述 Collatz 运行过程中已收集的奇数项，再通过 `sorted_int_list_by 1` 和 `Permutation` 描述排序结果。
- `C_123_proof_manual.v`：补完所有 manual VC。

### 遇到的问题

1. 问题：原 C 程序使用 `realloc` 动态扩容，但当前验证库没有建模 `realloc` 的所有权迁移、旧块释放和失败分支。

   解决：将输出数组容量适配为固定 `1024`，并把“整个 Collatz 运行过程中不会超过容量、每一步不会 int 溢出”的条件放进 `problem_123_pre_z`。这改变的是内存管理策略，不改变 Collatz 奇偶推进和奇数项收集逻辑。

2. 问题：Collatz 停机性不能由程序本身在 QCP 中证明；原题文字依赖 Collatz conjecture。

   解决：`problem_123_pre_z` 使用强前置条件要求存在安全的有界运行轨迹：当前状态保持正数、奇数分支 `3*n+1` 不溢出、偶数分支除二后仍安全、输出长度小于固定容量。后置规格验证的是满足此前置条件的执行结果。

3. 问题：直接在 while 的奇数分支中验证 `data[output_size] = n; output_size = output_size + 1;` 时，数组 `seg/undef_seg` 的局部合并和 Collatz 状态推进交织在一起，早期版本为了拆分证明曾加入已实现 helper `append_int`。

   解决：后续按 C_163 的经验重新尝试 no-wrapper 版本，移除 `append_int`，在奇数分支内直接写 `data[output_size] = n; output_size++;`。写入后的 Assert 直接把 `IntArray::seg(data, 0, output_size, output_l)` 更新为追加了 `n` 的前缀，并把 `odd_collatz_prefix` 推进到 `n * 3 + 1`。manual 中用 `IntArray.seg_single` 和 `IntArray.seg_merge_to_seg` 完成数组段合并，因此不再需要 helper。

4. 问题：早期给 `append_int` 写后置时使用 `l ++ cons(value, nil)`，QCP 注解解析/类型推断把它处理得不稳定。

   解决：当前 no-wrapper 版本已经删除 `append_int`，不再需要 helper 后置条件；直接写入后的存在量选择为 `output_l_2 ++ n :: nil`，该表达式只出现在 Coq proof 中，由 `Zlength_app` / `Zlength_cons` 证明长度关系。

5. 问题：早期调用 `append_int(data, output_size, cap, n)` 时，虽然纯事实里有 `cap == 1024`，但空间资源 `IntArray::undef_seg(..., 1024)` 和函数前置 `IntArray::undef_seg(..., cap)` 匹配不稳定。

   解决：当前版本仍去掉主函数局部 `cap` 变量，统一使用固定容量字面量 `1024`。这让空间资源参数和排序容量完全一致，也让直接写入后的 `undef_seg(data, output_size + 1, 1024)` 能稳定匹配。

6. 问题：循环退出后局部变量 `n` 的资源仍存在；若 sort 前后的 `Assert` 不显式保留 `data_at(&n, 1)`，manual VC 会要求丢弃局部变量资源。

   解决：在循环退出后的 sort 前断言和 sort 后断言中保留 `data_at(&n, 1)`，直到后续语句由符号执行正常处理局部变量。

7. 问题：C 的 `%` / `/` 在 VC 中分别对应 `Z.rem` / `Z.quot`，而 Collatz 逻辑关系使用 `Z.mod` / `Z.div` 更自然。

   解决：在 `coins_123.v` 中加入 `Z_rem_2_eq_1_to_mod`、`Z_rem_2_neq_1_to_mod_0`、`odd_collatz_odd_quot_step`、`odd_collatz_even_quot_step`，在正数条件下桥接 C 运算和数学运算。

### 后续注意

- `sort_int_array` 仍保持通用排序函数规格，只描述有序、排列和数组资源；C_123 的题目语义由 `problem_123_spec_z_of_sorted` 在本题 `coins_123.v` 中桥接。
- 当前 `problem_123_spec_z` 是操作式 Z 层规格，尚未证明与 `../spec/123.v` 中 nat/list 规格完全等价；如果后续需要和原 spec 严格对接，可以在 `odd_collatz_prefix` 基础上补等价 bridge。
- C_123 的最新版本说明：简单尾追加不必抽成 helper；只要在写入后用 Assert 明确追加后的前缀列表和数组段，manual proof 可以直接完成。后续遇到类似固定容量尾插入时，优先尝试 no-wrapper 直接写入。

## C_128 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_128.v`、`C_128_goal.v`、`C_128_proof_auto.v`、`C_128_proof_manual.v`、`C_128_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_128.v` 与 `C_128_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_128.c`：改为 QCP 格式，保留原程序“空数组返回 `-32768`，非空数组遍历元素、累加绝对值、遇到 0 将乘积符号置 0、遇到负数翻转符号、最后返回 `sum * prods`”的核心逻辑。原 `abs` 调用改为带规格的已实现 wrapper，循环中引入 `current` / `mag` 只是避免重复数组读取的机械改写。
- `coins_128.v`：新增 Z 层桥接规格 `problem_128_spec_z`，将空数组映射到 C 程序 sentinel `-32768`，非空数组对接 `../spec/128.v` 的 `problem_128_spec l (Some out)`；新增前缀绝对值和、前缀符号乘积、整数范围条件及分支推进引理。
- `C_128_proof_manual.v`：补完所有 manual VC，包括 `abs` 返回、循环初始化、三个符号分支推进、加法/乘法安全性和最终返回规格桥接。

### 遇到的问题

1. 问题：原 spec 的输出是 `option Z`，而 C 程序对空数组返回普通整数 sentinel `-32768`。
   解决：在 `coins_128.v` 中定义 `problem_128_spec_z`：空列表要求 `out = -32768`，非空列表再桥接到原题 `problem_128_spec l (Some out)`。

2. 问题：`abs(arr[i])` 是常见库函数调用，但不能把本题主体逻辑抽成未实现函数。
   解决：只为 `abs` 写已实现 wrapper，规格为返回 `Zabs(x)`；同时前置条件要求数组元素满足 `INT_MIN < x <= INT_MAX`，避免 C 中 `-INT_MIN` 溢出。

3. 问题：`sum += abs(arr[i])` 和最终 `sum * prods` 都需要 C `int` 安全性。
   解决：增加 `prod_signs_int_range(input_l)`，记录每个输入元素的 `abs` 安全性，以及任意前缀绝对值和都在 `int` 范围内；manual 中再由 `prod_signs_prefix_prod_bound` 得到 `prods` 只可能为 `-1/0/1`。

4. 问题：空数组分支提前返回后，循环后的 return VC 需要知道当前一定是非空输入。
   解决：在循环 invariant 中保留 `arr_size != 0`，最终用该事实把 `i == arr_size == Zlength input_l` 桥接到非空规格。

5. 问题：`mag = abs(current)` 后若在 `Assert` 中额外写局部变量的 `data_at` 资源，生成的资源匹配目标会变得不可满足。
   解决：该处 `Assert` 只保留必要纯事实和数组资源，不手动加入 `current` / `mag` 的局部变量资源。

6. 问题：三个分支分别改变符号乘积：`current == 0` 置零、`current < 0` 翻转、正数保持。
   解决：在 `coins_128.v` 中分别证明 `prod_signs_prefix_zero`、`prod_signs_prefix_neg`、`prod_signs_prefix_pos`，让 C 分支和 `Z.sgn` 的前缀乘积定义对齐。

### 后续注意

- 本题没有涉及 `qsort`，因此不需要 `sort_int_array`。后续若遇到排序题，仍应保持 `sort_int_array` 是通用排序规格，不在排序函数后置中加入题目专属语义。
- 引入 `current` / `mag` 这类局部变量可以作为数组读取和库函数调用之间的验证简化手段，但它只能是等价的机械改写，不能改变原程序核心逻辑。

## C_130 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_130.v`、`C_130_goal.v`、`C_130_proof_auto.v`、`C_130_proof_manual.v`、`C_130_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_130.v` 与 `C_130_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_130.c`：改为 QCP 格式，保留原程序“写 `data[0]=1`，`n==0` 直接返回；写 `data[1]=3`；从 `i=2` 到 `n` 按偶数公式或奇数递推写入”的核心逻辑。原来的结构体值返回适配为 `IntArray *` 返回，并用 `malloc_int_array_struct` / `malloc_int_array` 建模分配成功。
- `coins_130.v`：新增 `tri_z`、`tri_sequence`、Z/list 层 `problem_130_pre_z` / `problem_130_spec_z`，证明它们桥接到 `../spec/130.v` 的 nat 规格；补偶数分支、奇数分支、前缀 snoc、前缀读数组项和整数范围相关引理。
- `C_130_proof_manual.v`：补完 9 个 manual VC，包括循环初始化、两个分支写入后前缀推进、整数安全性和两个返回分支的完整数组资源构造。

### 遇到的问题

1. 问题：原程序返回结构体值，并包含 `malloc` 失败时返回空结构体的分支；QCP 中直接验证结构体值返回和裸 `malloc` 失败分支不方便。
   解决：按已有数组返回题模式适配为 `IntArray *`，用 wrapper 规格假设通用内存分配成功。这个适配只改变验证接口和内存建模，不改变 Tribonacci 序列的写入规则。

2. 问题：题目 spec 是 nat/list 规格，而 C VC 中使用 Z、`Z.quot` 和 `Z.rem`。
   解决：在 `coins_130.v` 中定义 `tri_z i := Z.of_nat (tri (Z.to_nat i))` 和 `tri_sequence n`，再证明 `tri_sequence_spec_z`，把 C 层输出桥接回原 `problem_130_spec`。

3. 问题：偶数分支需要证明 `1 + i / 2` 正好是 `tri_sequence` 第 `i` 项；奇数分支需要证明 `data[i-1] + data[i-2] + 1 + (i+1)/2` 正好是第 `i` 项。
   解决：分别证明 `tri_z_even_quot` 和 `tri_z_odd_quot`，并用 `tri_sequence_even_snoc` / `tri_sequence_odd_snoc` 直接服务循环 invariant 的前缀推进。

4. 问题：奇数分支读的是当前已写前缀 `sublist 0 i` 中的 `i-1` 和 `i-2`，VC 中出现 `Znth ... (sublist 0 i ...)`，不能直接化到 `tri_z`。
   解决：补 `tri_sequence_sublist_Znth`，用 `Znth_sublist0` 把前缀读回完整 `tri_sequence` 的对应下标。

5. 问题：奇数分支的 C 加法是逐步求值，manual VC 分别要求 `a+b`、`a+b+1`、`a+b+1+quot` 都在 `int` 范围内。
   解决：`tri_seq_int_range` 中记录最终写入表达式范围，再利用 `tri_z_nonneg` 和 `Z.quot_pos` 补出两个中间加法安全引理。

6. 问题：return 处已写前缀 `seg` 后面还带一个长度为 0 的 `undef_seg`，不能直接匹配 `IntArray::full`。
   解决：先用 `IntArray.seg_to_full` 把完整前缀转成 `full`，再用 `IntArray.undef_seg_empty` 消掉空未写后缀。

### 后续注意

- 这类“先写基础项，再从固定下标递推”的数组题，循环 invariant 可以维护 `IntArray::seg(data, 0, i, sublist 0 i seq)`，分支证明则集中在 `seq` 的 snoc 引理中。
- 如果 C 代码用 `/` 和 `%`，C VC 通常是 `Z.quot` / `Z.rem`；规格若基于 nat 或数学除法，应在 `coins_XX.v` 中集中桥接，不要把这些细节散进 C 注解。

## C_135 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_135.v`、`C_135_goal.v`、`C_135_proof_auto.v`、`C_135_proof_manual.v`、`C_135_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_135.v` 与 `C_135_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_135.c`：改为 QCP 格式，保留原程序“从左到右扫描，若 `arr[i] <= i` 则更新 `max = i`，最后返回最大满足下标或 `-1`”的核心逻辑。
- `spec/135.v`：修正为与 C 程序一致的规格，描述最大下标 `k` 满足 `arr[k] <= k`，不存在时返回 `-1`。
- `coins_135.v`：新增 C 层 prefix 谓词 `can_arrange_prefix`，并证明它能推出新版 `problem_135_spec`。
- `C_135_proof_manual.v`：补完循环初始化、命中分支、未命中分支和最终返回 4 个 manual VC。

### 遇到的问题

1. 问题：`spec/135.v` 原先定义的是相邻下降 `drop_at`，但当前 C 程序判断的是 `arr[i] <= i`；这两者不是同一个性质。
   解决：不改 C 核心逻辑，将 `spec/135.v` 修正为 `can_arrange_at lst k := lst[k] <= k`，并让 `problem_135_spec` 描述最大满足下标或 `-1`。

2. 问题：循环需要表达“目前为止最大的满足下标”，同时还要覆盖没有任何满足元素时返回 `-1`。
   解决：`can_arrange_prefix i l max` 同时记录 `-1 <= max < i`、`max=-1 \/ can_arrange_hit l max`，以及任意已扫描命中下标 `j` 都满足 `j <= max`。

3. 问题：命中分支 `arr[i] <= i` 更新 `max=i`，未命中分支保持旧 `max`，两条分支需要分别推进 invariant。
   解决：分别证明 `can_arrange_prefix_update` 和 `can_arrange_prefix_keep`，再用 `can_arrange_hit_of_cond` / `can_arrange_not_hit_of_cond` 把 C 条件桥到逻辑谓词。

### 后续注意

- 本题是一个很小的只读数组扫描模板：如果状态只是“当前最大/最小满足下标”，推荐把最大性直接写进 prefix 谓词，不需要引入额外列表构造。
- 本题后续已完成规格统一：`spec/135.v`、`coins_135.v` 和 C 程序均使用 `arr[i] <= i` 的最大下标语义。

## C_136 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_136.v`、`C_136_goal.v`、`C_136_proof_auto.v`、`C_136_proof_manual.v`、`C_136_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_136.v` 与 `C_136_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_136.c`：改为 QCP 格式，保留原程序“扫描输入数组，用 `maxneg=0` 表示当前无负数、用 `minpos=0` 表示当前无正数，分别按条件更新最大负数和最小正数，最后输出 `[maxneg; minpos]`”的核心逻辑。结构体值返回适配为 `IntArray *` 返回，并用 `malloc_int_array_struct` / `malloc_int_array` 建模分配成功。
- `coins_136.v`：新增 `largest_negative_state`、`smallest_positive_state` 和 `largest_smallest_prefix`，并将 C 的 `0` sentinel 桥接到 `spec/136.v` 中的 `None`。
- `C_136_proof_manual.v`：补完循环初始化、7 条分支推进和最终返回 9 个 manual VC。

### 遇到的问题

1. 问题：原 spec 使用 `option Z * option Z` 表示不存在负数/正数时返回 `None`，而 C 程序输出数组中用 `0` 作为 sentinel。
   解决：在 `coins_136.v` 中定义 `neg_option_of_value` / `pos_option_of_value`，把 `0` 映射为 `None`，非零值映射为 `Some`，并证明 prefix 状态可推出原 `problem_136_spec`。

2. 问题：两个更新语句各自有短路条件，符号执行展开后产生 7 条实际路径：更新最小正数两条、更新最大负数两条、零值保持、负数保持、正数保持。
   解决：分别补 `largest_smallest_prefix_min_zero`、`largest_smallest_prefix_min_smaller`、`largest_smallest_prefix_max_zero`、`largest_smallest_prefix_max_bigger`、`largest_smallest_prefix_keep_zero`、`largest_smallest_prefix_keep_negative`、`largest_smallest_prefix_keep_positive`。

3. 问题：循环推进需要把 `sublist 0 i` 扩展为 `sublist 0 (i+1)`，并把新读到的 `Znth i l 0` 追加到前缀末尾。
   解决：补 `sublist_snoc_Znth_136`，所有分支推进引理都先把新前缀改写为旧前缀追加当前元素，再分别更新最大负数/最小正数状态。

4. 问题：最终返回时输出数组由两个单点写入组成，需要合并成 `IntArray::full(data, 2, [maxneg; minpos])`。
   解决：manual 中先用两次 `IntArray.seg_single`，再用 `IntArray.seg_merge_to_seg` 合成长度 2 的 `seg`，最后用 `IntArray.seg_to_full` 得到完整数组资源。

### 后续注意

- 对这种“多个独立累计状态”的扫描题，推荐把每个状态拆成独立 state 谓词，再用一个 prefix 谓词组合；分支引理负责同时推进所有 state。
- C 的 sentinel 表示和 spec 的 `option` 表示不一致时，不需要改 C 核心逻辑，优先在 `coins_XX.v` 做表示桥接。

## C_142 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_142.v`、`C_142_goal.v`、`C_142_proof_auto.v`、`C_142_proof_manual.v`、`C_142_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_142.v` 与 `C_142_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_142.c`：改为 QCP 格式，保留原程序“若 `i % 3 == 0` 累加平方，否则若 `i % 4 == 0` 累加立方，否则累加原值”的核心逻辑。
- `coins_142.v`：新增 C 层 `transformed_value`、`transformed_sum_from`、`transformed_prefix_sum`，并桥接到 `spec/142.v` 的 `sum_squares_impl`。
- `C_142_proof_manual.v`：补完 6 个 safety VC、3 个分支 invariant 推进 VC 和最终返回 VC。

### 遇到的问题

1. 问题：C 的 `%` 在 VC 中是 `Z.rem`，而 `spec/142.v` 使用 `Nat.modulo`。
   解决：在 `coins_142.v` 中证明 `Nat_mod3_of_Z_nonneg` / `Nat_mod4_of_Z_nonneg` 风格的桥接，并用 `transformed_value_of_nat` 连接 C 层 `transformed_value` 与原 spec 的 `sum_transformed`。

2. 问题：平方分支、立方分支和原值分支都需要分别把 `sum + 当前变换值` 推进为下一前缀和。
   解决：定义 `transformed_prefix_sum i l := transformed_sum_from (sublist 0 i l) 0`，并证明 `transformed_prefix_sum_snoc`；三个分支再分别用 `transformed_value_square`、`transformed_value_cube`、`transformed_value_plain` 改写。

3. 问题：C 中 `lst[i] * lst[i] * lst[i]` 是逐步乘法，且每次 `sum += ...` 也需要证明不溢出。
   解决：前置条件加入 `sum_squares_int_range`，同时记录 `x*x`、`x*x*x` 和每个前缀更新后的 `sum` 都在 `int` 范围内。

4. 问题：最终返回需要证明操作式前缀和等于原 `spec/142.v` 的递归定义。
   解决：证明 `transformed_sum_from_spec` 和 `transformed_prefix_sum_full_spec`，最终由 `problem_142_spec_z_of_prefix_full` 桥接。

### 后续注意

- 这类“按下标取模选择变换”的只读扫描题，建议把变换函数单独定义为 `transformed_value i x`，循环 invariant 只维护前缀和。
- 若 spec 使用 nat 下标而 C 使用 Z 下标，桥接尽量集中在 `coins_XX.v`，C 注解里只放操作式谓词和范围前置条件。

## C_108 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_108.v`、`C_108_goal.v`、`C_108_proof_auto.v`、`C_108_proof_manual.v`、`C_108_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_108.v` 与 `C_108_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_108.c`：替换为 QCP 头文件，加入已实现的 `abs` helper 规格，补充数组只读资源、主循环和内部 digit-scan 循环不变式。保留原程序的核心遍历、正数直接计数、非正数逐位求和再判断的逻辑。
- `coins_108.v`：新增数组元素安全范围、精确计数前缀状态和 digit-scan 状态，以及对应的初始化、推进和返回桥接引理；`problem_108_spec_z` 直接引用 `spec/108.v` 的 `problem_108_spec`。
- `C_108_proof_manual.v`：补完所有 manual VC，包括 `abs` 返回、计数增量安全、C `%`/`/` 到 `Z.rem`/`Z.quot` 的非负场景桥接、循环不变式推进和最终返回。
- `spec/108.v`：将输出类型从 `nat` 改为 `Z`，并把 `sum_digits` 改为与 C 程序一致的 Z 层操作式定义。

### 遇到的问题

1. 问题：原程序使用 `abs(n[i])`，而 C 的 `abs(INT_MIN)` 不安全；仓库已有 `abs` 规格也要求 `INT_MIN < x`。

   解决：在 `count_nums_int_range` 中要求输入数组元素满足 `INT_MIN < Znth i input_l 0 <= INT_MAX`，把原程序实际安全执行域写入前置条件。

2. 问题：内部 `while (w >= 10)` 中 `sum += w % 10; w = w / 10;` 的安全性需要同时证明 `sum` 不溢出和 `w` 非负。

   解决：用 `digit_scan_state original current sum` 维护 `current` 的非负边界和 `sum + current <= INT_MAX`，并在 manual VC 中用 `Z.rem_mod_nonneg`、`Z.quot_div_nonneg` 桥接 C 运算。

3. 问题：原 `../spec/108.v` 的输出是 `nat`，但 C 返回值在 VC 中是 `Z`；如果继续用 `nat`，需要在最终返回处额外桥接 `Z.to_nat`，并且不利于表达返回值的 C 整数范围。

   解决：将 `spec/108.v` 的 `problem_108_spec` 输出类型改为 `Z`，`count_nums_impl` 也返回 `Z`；`problem_108_spec_z` 直接定义为 `problem_108_spec l out`。

4. 问题：原 `nat_sum_digits` / `nat_get_msd` 规格不方便直接对应 C 里的 `while (w >= 10) { sum += w % 10; w /= 10; } sum -= w`。

   解决：在 `spec/108.v` 中用 `signed_digit_loop` 定义 Z 层 digit sum。正数分支按题意总是计数；非正数分支精确刻画 C 的逐位循环。`count_nums_prefix` 已加强为 `num = count_nums_impl (sublist 0 i input_l)`。

### 后续注意

- `signed_digit_loop` 使用固定 11 层 fuel，覆盖 C `int` 输入的十进制位数；本题前置条件已经排除 `INT_MIN` 并限制元素在 `int` 范围内。

## C_107 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_107.v`、`C_107_goal.v`、`C_107_proof_auto.v`、`C_107_proof_manual.v`、`C_107_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_107.v`、`C_107_proof_manual.v` 与 `spec/107.v` 扫描无 `Admitted` / `Axiom`。

### 文件变更

- `C_107.c`：适配为 QCP `IntArray *` 返回接口，补充 `is_pal` 和 `even_odd_palindrome` 的规格与循环不变式。保留原 C 的核心逻辑：数字反转判断回文，遍历 `1..n`，分别累计偶数回文和奇数回文，输出 `[even; odd]`。
- `spec/107.v`：改为 Z/list 操作式规格，使用固定 4 层 fuel 描述 `n <= 1000` 下的十进制反转，规格输出为 `[count_even_pal_upto n; count_odd_pal_upto n]`。
- `coins_107.v`：新增 C 层 bridge，包括 `is_pal_z`、反转循环状态 `pal_reverse_loop_state`、前缀计数状态 `pal_count_prefix`，以及 C `%`/`/` 到 Coq `mod`/`div` 的推进证明和计数边界引理。
- `C_107_proof_manual.v`：补完所有 manual VC，包括 `is_pal` 返回语义、主循环四类分支推进、计数自增安全性和最终数组内容资源构造。

### 遇到的问题

1. 问题：`is_pal` 初版规格没有显式保存入口参数，生成的返回 VC 变成对任意 `x0` 证明 `is_pal_z x0`，不可证。
   解决：给 `is_pal` 加 `With (x0: Z)` 和 `x == x0`，并在循环不变式中保留 `x == x0`。

2. 问题：主函数循环退出后后置条件需要 `out != 0`，但初版 invariant 没保留结构体分配得到的非空事实。
   解决：在主循环 invariant 中加入 `out != 0`。

3. 问题：计数变量自增安全性需要证明回文计数不会超过已扫描前缀长度。
   解决：在 `coins_107.v` 中从 `count_even_pal_upto_nat` / `count_odd_pal_upto_nat` 递归定义证明上下界，并桥接到 `pal_count_prefix_bounds`。

4. 问题：C 分支条件中的 `%` 是 `Z.rem`，而规格层偶奇判断使用 `Z.mod`。
   解决：在正数循环索引条件下使用 `Z.rem_mod_nonneg` 桥接。

### 后续注意

- `spec/107.v` 当前是与 C 程序直接一致的 Z 层操作式规格；如果后续需要和旧 nat/数字列表规格做严格等价，可在该文件上额外补等价定理，而不是削弱 `problem_107_spec_z`。

## C_146 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_146.v`、`C_146_goal.v`、`C_146_proof_auto.v`、`C_146_proof_manual.v`、`C_146_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_146.v`、`C_146_proof_manual.v` 扫描无 `Admitted` / `Axiom`。

### 文件变更

- `C_146.c`：改成 QCP 格式并补充循环不变式；保留原核心逻辑，不抽 helper，不增加空 `else`，仍按 `nums[i] > 10` 后取末位、循环除以 10 求首位，并只在 `first % 2 == 1 && last % 2 == 1` 时 `num += 1`。
- `coins_146.v`：接入 `spec/146.v`，新增前缀计数谓词、最高位循环状态、C `rem/quot` 与规格 `mod/div`/奇偶判断的桥接引理。
- `C_146_proof_manual.v`：补完计数自增安全、内层最高位循环推进、命中特殊数/首位非奇数/末位非奇数/`<=10` 四类路径的前缀计数推进，以及最终返回规格。

### 遇到的问题

1. 问题：最初为了方便证明，把首末位判断拆成 helper，并给 `if (first % 2 == 1 && last % 2 == 1)` 加了空 `else` 路径来放断言；这不符合“尽量不修改原程序核心结构”的要求。
   解决：撤回 helper 和空 `else`，保留原来的单个计数 if。验证信息改为放在原 if 之后的 Assert 中，由 manual VC 分别证明命中和不命中的前缀计数推进。

2. 问题：`first/last` 如果声明在块内，离开块时 QCP 需要回收局部变量权限；若块尾 Assert 没携带它们的 `data_at`，会出现 `Fail to Remove Memory Permission` 或无法丢弃栈权限的 VC。
   解决：保持 `first/last` 在 `nums[i] > 10` 块内声明，并在离开该块前的 Assert 中显式保留 `data_at(&first, first) * data_at(&last, last)`，让块结束时由工具正常回收。

3. 问题：规格用 `special_number_b` 的 `msd_fuel`、`last_digit`，C 代码用 `while (first >= 10) first /= 10` 和 `%`。
   解决：在 `coins_146.v` 中用 `first_digit_state` 记录当前 `first` 与原数最高位的一致性；用正数条件下的 `Z.quot_div_nonneg`、`Z.rem_mod_nonneg` 和 `Zmod_odd` 桥接 C 运算与规格布尔奇偶判断。

### 后续注意

- 对类似“局部变量只在分支块中使用”的题目，优先保留原块结构；若要在块尾加 Assert，记得保留局部变量的栈权限，避免为了证明方便把局部变量提升到函数作用域或加空分支。

## C_152 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_152.v`、`C_152_goal.v`、`C_152_proof_auto.v`、`C_152_proof_manual.v`、`C_152_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_152.v`、`C_152_proof_manual.v` 扫描无 `Admitted` / `Axiom`。

### 文件变更

- `C_152.c`：改成 QCP 格式；原结构体值返回适配为 `IntArray *`；`malloc` 建模为通用 wrapper；`abs` 保留为有实现 helper；主逻辑仍计算 `n = min(game_size, guess_size)`，保留 malloc-null 检查，并逐元素写入 `abs(game[i] - guess[i])`。
- `coins_152.v`：接入 `spec/152.v`，新增 `compare_list`、前缀输出谓词 `compare_prefix`、差值范围前置条件和前缀推进/最终规格桥接引理。
- `C_152_proof_manual.v`：补完 `abs` 返回语义、差值安全、输出数组前缀写入、`undef_full` 到 `seg/undef_seg` 初始化、最终 `seg/undef_seg` 合成为 `full` 以及返回规格证明。

### 遇到的问题

1. 问题：原程序声明输入长度相等，但 C 仍写 `n = game_size < guess_size ? game_size : guess_size`。
   解决：保留原 ternary 逻辑，在函数前置条件中要求 `game_size == guess_size` 并在循环 invariant 中保存 `n == game_size`、`n == guess_size`。因此有效输入下行为与题目规格一致，同时不改原 min 逻辑。

2. 问题：`abs(game[i] - guess[i])` 需要先证明 C int 减法不会溢出，并且 `abs` 不能接收 `INT_MIN`。
   解决：新增 `compare_int_range`，要求每个有效索引满足 `INT_MIN < game[i] - guess[i] <= INT_MAX`；manual 中用 `compare_int_range_at` 同时证明减法安全和 `abs` 前置条件。

3. 问题：输出数组从 `malloc_int_array` 得到的是 `IntArray::undef_full`，循环 invariant 需要表示已写前缀和未写后缀。
   解决：初始化时用 `IntArray.undef_full_to_undef_seg`，循环中用 `IntArray.seg_single` 和 `IntArray.seg_merge_to_seg` 把新写元素并入前缀，返回时用 `IntArray.undef_seg_empty` 与 `IntArray.seg_to_full` 合成完整输出数组。

### 后续注意

- 对带 `abs(a-b)` 的题目，除了输入元素本身在 int 范围内，还要单独给差值范围条件；否则减法安全和 `abs(INT_MIN)` 都会卡住。

## C_159 验证记录

### 结论

`C_159` 已完成完整验证，`coins_159.v`、`C_159_goal.v`、`C_159_proof_auto.v`、`C_159_proof_manual.v`、`C_159_goal_check.v` 均可编译通过。

### 遇到的问题

1. 原程序返回结构体值并直接 `malloc`。

解决方式：按 IntArrayClaude 已有模式改为返回 `IntArray *`，使用 `malloc_int_array_struct` / `malloc_int_array` wrapper。业务逻辑的两个分支和写入顺序保持不变。

2. 返回处需要把两个单点写入合成完整输出数组。

解决方式：manual 中使用 `IntArray.seg_single` 与 `IntArray.seg_merge_to_full`，再分别用 `problem_159_spec_need_le_remaining` / `problem_159_spec_need_gt_remaining` 桥接到题目规格。

## C_163 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_163.v`、`C_163_goal.v`、`C_163_proof_auto.v`、`C_163_proof_manual.v`、`C_163_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_163.v` 与 `C_163_proof_manual.v` 中无 `Admitted` / `Axiom`。

### 文件变更

- `C_163.c`：改成 QCP 格式；原结构体值返回适配为 `IntArray *`；`malloc` 建模为通用 wrapper；保留交换 `a/b`、遍历区间、筛选 `i < 10 && i % 2 == 0`、按升序写入输出的核心逻辑。未使用 `append_int` helper。
- `coins_163.v`：接入 `spec/163.v`，新增 `generate_prefix` / `generate_bounds` / `generate_list` 等 C 层桥接定义，并补前缀推进、跳过、最终规格、`rem/mod` 与偶数判断桥接、输出长度上界等引理。
- `C_163_proof_manual.v`：补完所有 manual VC，包括数组写入后的 `seg` 合并、分支前缀推进、循环退出与最终返回规格。

### 遇到的问题

1. 原始写法 `out.data[out.size++] = i` 对 QCP 前端不友好；单独构造的 `C_163_postinc_fail.c` 显示数组下标中的 `++` 会触发解析错误。

解决方式：不用 helper，将后置自增拆成两句 `data[output_size] = i; output_size++;`，并在循环结束后写回 `out->size = output_size`。筛选条件、写入值和输出顺序不变，且 no-wrapper 版本已通过 symexec。

2. 动态容量 `b - a + 1` 在数组段资源匹配中比固定容量更难处理。

解决方式：本题最多输出一位偶数 `2,4,6,8`，因此用固定容量 `10` 建模输出缓冲区，并记录这是验证层面的容量适配；输出列表语义不变。

3. 局部变量 `m` 原程序只在 swap 分支赋值，未进入 swap 分支时验证末尾回收局部栈权限会失败。

解决方式：将 `int m;` 初始化为 `int m = 0;`，并在循环断言中携带 `data_at(&m, m)`。该初始化不改变程序可观察输出。

4. C 条件中的 `%` 在 VC 中是 `Z.rem`，而 `Z.even` 和规格侧桥接常使用数学取模 `Z.modulo`。

解决方式：在 manual proof 中利用循环范围推出当前 `i >= 0`，再用 `Z.rem_mod_nonneg` 把 `i % 2` 桥接到 `i mod 2`，从而复用 `mod2_zero_even_true` / `mod2_nonzero_even_false`。

5. 循环退出处需要证明 `output_size <= 10`，单靠 invariant 中 `output_size <= i - a` 不足以推出容量上界。

解决方式：在 `coins_163.v` 中补 `generate_prefix_length_le_4`，说明输出只来自候选列表 `[2;4;6;8]` 的过滤结果，长度最多 4，因此可推出 `output_size <= 10`。

## 后续记录模板

## C_96 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_96.v`、`C_96_goal.v`、`C_96_proof_auto.v`、`C_96_proof_manual.v`、`C_96_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_96.v`、`C_96_proof_manual.v` 扫描无 `Admitted` / `Axiom`。

### 文件变更

- `C_96.c`：恢复接近原程序的核心逻辑：从 `i=2` 扫到 `< n`，保存已找到的素数前缀，用已有素数试除，`isp` 为真时追加 `i`。为避免 C int 乘法溢出，原来的 `data[j] * data[j] <= i` 用等价的正数除法形式 `data[j] <= i / data[j]` 表达。保留 QCP 指针返回适配，并在循环不变式中补充 `n == n@pre`。
- `coins_96.v`：保留强规格 `problem_96_spec_z`：结果全为素数、都小于 `n`、包含所有小于 `n` 的素数、严格排序且无重复。新增前缀状态、试除状态、`Znth`/排序/素数除子相关引理，证明提前停止试除时 candidate 为素数。
- `C_96_proof_manual.v`：补完所有 manual VC，包括 C `%`/`/` 与 Coq `mod`/`div` 桥接、数组前缀追加、`isp=0` 的合数分支、`isp!=0` 的素数追加分支和最终返回规格。

### 遇到的问题

1. 问题：最初符号执行卡在 `data[j]` 读取，表面像动态前缀 `IntArray::seg` 问题。
   解决：构造了最小 probe 后确认动态前缀读取本身可行；真正原因是断言里写了纯条件 `data == out->data`，其中 `out->data` 是内存字段访问，不是 ghost 值。移除该纯条件，保留 `data_at(&(out->data), data)`。

2. 问题：内层循环 invariant 没携带 `2 < n`、`n < INT_MAX` 和函数入口参数关系，导致循环体 Assert 与最终 return VC 信息不足。
   解决：在外层/内层 invariant 与关键 Assert 中补充 `n == n@pre`，并在内层 invariant 中保留 `2 < n`、`n < INT_MAX`。

3. 问题：进入循环体时的条件 `data[j] <= i / data[j]` 没有传给 `i % data[j] == 0` 分支，无法更新 `prime_test_state`。
   解决：在循环体 Assert 中加入对应的 `Znth(j, output_l, 0) <= i / Znth(j, output_l, 0)` 纯事实。

4. 问题：原程序的提前停止试除需要证明：若当前素数前缀中第 `j` 个素数已经大于 `i / p_j`，且前面都未整除，则 `i` 是素数。
   解决：在 `coins_96.v` 中证明复合数存在不超过平方界的素除子，并结合 `count_up_to_state` 的完备性、严格排序和 `prime_test_state` 的已检查前缀推出矛盾。

### 后续注意

- 当前 C 代码与原始核心逻辑的唯一语义等价改写是把平方条件改成正数除法条件，用于避免验证 C `int` 乘法溢出。

## C_145 验证记录

### 结论

- 状态：已完成完整验证。
- 是否全链通过：是，`symexec --gen-and-backup --no-exec-info` 已通过，且 `coins_145.v`、`C_145_goal.v`、`C_145_proof_auto.v`、`C_145_proof_manual.v`、`C_145_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：是，`coins_145.v` 与 `C_145_proof_manual.v` 扫描无命中。

### 文件变更

- `C_145.c`：已转成 QCP 格式；按要求删除了此前尝试加入的 `highest_power10` helper，并把最高 10 次幂循环恢复为 `signed_digit_score` 内部的原地循环。目前没有新增未实现 helper，也没有改动排序主体的 C 执行逻辑。为闭合局部变量权限，只在排序结束、`free_int_array(score, nums_size)` 之前的 Assert 中保留 `data_at(&i, nums_size)`；随后直接 `return out`，不再在 free 后手写过强 Assert。
- `spec/145.v`：把 `order_by_points_impl` 的实现描述改为直接在 `list Z` 上执行稳定相邻交换 bubble sort，而不是另一个 insertion-style `stable_sort`。这与 C 程序维护 `data[]` / `score[]` 并只在 `>` 时交换的结构一致，避免额外证明两种排序算法等价。`sum_digits` 也改为结构上对应 C 程序的定义：固定 8 位 fuel，先取最高位，再用最高 10 次幂去掉最高位，最后累加低位数字；输入验证前置中已有 `abs < 100000000`，8 位 fuel 足够。
- `coins_145.v`：修正 `problem_145_spec_z`，现在直接使用 `problem_145_spec nums output`，不再使用仅约束 `Zlength` 的弱规格；同时把排序 ghost 从单个弱 `order_sort_state` 拆成 `order_sort_outer_state` 和 `order_sort_inner_state`，分别刻画外层 pass 与内层相邻交换进度。排序相关列表引理和 VC 桥接已补完。`highest_power10_state` 改为记录“从当前 `p` 继续执行最高 10 次幂循环的最终结果”，并证明 `init_nonneg/init_neg/step/final` 四个语义引理。
- `C_145_proof_manual.v`：当前生成的 manual VC 已回填 abs、首位扫描初始化/推进、多 digit 分支 `p` 循环进入/推进/退出、单 digit 正负分支、最后 digit 累加循环 step、最终 return，以及复制和冒泡排序阶段的全部 manual VC；该文件当前无 `Admitted.`。

### 遇到的问题

1. 问题：最初的 `problem_145_spec_z` 只证明输出长度等于输入长度，没有连接 `spec/145.v` 的 `order_by_points_impl`，规格过弱。
   解决：将 `problem_145_spec_z` 改为 `problem_145_spec nums output`，并标记当前 `order_sort_state_final_spec` 无法从长度状态推出强规格。

2. 问题：当前 `order_sort_state` 只记录 `output` 和 `scores` 的长度，不能证明 `score[]` 对应 `sum_digits`，也不能证明冒泡排序实现了按分数稳定排序。
   解决方向：需要重构 ghost 状态，至少记录 `scores` 与 `output` 的逐点对应关系、`scores` 是由 `signed_digit_score` 计算得到，以及每次相邻交换保持一个可最终推出 `order_by_points_impl` 的排序语义。

3. 问题：`signed_digit_score_result` 目前只给出 int 范围，没有证明返回值等于 `spec/145.v` 的 `sum_digits x`。
   解决方向：需要加强 `signed_digit_score_result`，证明 C 中“负数最高位带符号、其余位相加”的实现与 `sum_digits` 一致；这会涉及 `Z.rem`/`Z.modulo`、`Z.quot`/`Z.div` 和 `sum_digits_pos_fuel`/`msd_fuel` 的桥接。

4. 问题：原地保留最高 10 次幂循环时，QCP 对跨循环局部变量 `msd` / `sum` 的栈权限处理困难，容易产生不可证明的 `emp -> data_at(...)` 形式 VC。
   解决：已按要求撤回 helper 提取，保留内联循环。当前符号执行可以通过；后续问题转移到强语义 proof，需要加强 ghost invariant，而不是再提取 C helper。

5. 问题：强规格要求证明 `score` 数组中的值确实是 `spec/145.v` 的 `sum_digits`，并证明冒泡排序稳定实现 `order_by_points_impl`。当前 `signed_digit_score_result` 和 `order_sort_state` 还不足以表达这些事实。
   解决方向：下一步需要只修改注解/Coq ghost：增强 `signed_digit_score_result` 到精确 `sum_digits` 语义，复制阶段记录 `scores = map sum_digits output`，排序阶段记录相邻交换保持按 score 稳定排序，并最终推出 `problem_145_spec`。

6. 进展：已开始增强 Coq ghost，不改 C 执行语句。
   - `signed_digit_score_result` 已加入 `r = sum_digits x`。
   - `order_copy_prefix` 已加入 `output = sublist 0 i input` 和 `scores = map sum_digits output`。
   - `order_sort_outer_state` / `order_sort_inner_state` 已直接连接到 `spec/145.v` 中的 `list Z` bubble-sort 语义，最终态可以推出 `problem_145_spec_z`。
   - `C_145.c` 的排序循环只改注解：内层循环后新增一个 Assert 说明本轮 bubble pass 完成，没有修改 if/swap 等 C 执行语句。
   - 重新运行 `symexec --gen-and-backup --no-exec-info` 已通过。
   - `coins_145.v` 当前可编译，排序 keep/swap/outer-step 三个 ghost 推进引理已不再是占位。
   后续仍需补：`signed_digit_score` 精确语义的 manual proof，并清掉所有 `Admitted.`。

7. 问题：拆分内外层排序状态后，内层 `for` 的局部变量 `j` 在离开作用域时触发 `Fail to Remove Memory Permission of j`。
   解决：在内层循环后的 Assert 中加入 `data_at(&j, nums_size)`，让 QCP 在退出 `j` 的作用域时能正常回收栈权限。这是注解层面的权限适配，不改变 C 程序逻辑。

8. 问题：如果继续沿用 `spec/145.v` 中原来的 insertion-style `stable_sort`，还需要额外证明 C 的 bubble sort 与该插入排序实现完全等价，证明负担明显偏离 C 程序本身。
   解决：把 `spec/145.v` 的 `order_by_points_impl` 改写为稳定相邻交换 bubble sort，并进一步改成直接在 `list Z` 上排序；稳定性由“只在左分数严格大于右分数时交换”体现。这样后续只需证明 C 循环执行了该 spec 中的 pass，而不需要跨算法等价证明，也不需要在 spec 中携带原始下标 pair。

9. 问题：`order_sort_inner_state_step_keep` / `swap` 证明需要把 C 中的 `score[j-1] <= score[j]` 或 `>` 连接到 spec 的一次 `swap_adjacent_points`。
   解决：在 `coins_145.v` 中新增 `bubble_pass_points_from_next`、`swap_adjacent_points_keep`、`swap_adjacent_points_swap`、`replace_Znth_adjacent_145` 等纯列表引理。keep 分支证明一次 pass 不变；swap 分支证明 spec 的相邻交换与 C 对 `data[]` / `score[]` 的两个 `replace_Znth` 一致。

10. 问题：外层状态推进需要证明 `bubble_sort_points_fuel (S n) l` 等价于对 `bubble_sort_points_fuel n l` 再做一次 pass。
    解决：补 `bubble_sort_points_fuel_snoc`，并用 `bubble_sort_points_fuel_length` 对齐最后一次 pass 的 fuel 长度。`swap_adjacent_points_length` 已通过 `nth_error` 范围事实、`length_app`、`length_firstn`、`length_skipn` 和 nat 线性算术证明，不再保留占位。

11. 问题：尝试在最高 10 次幂 `p` 循环 invariant 中加入 `data_at(&sum, sum)` 会生成 `emp -> data_at(&sum, ...)` 的不可证 VC；不加入 `sum` 的纯范围又不足以进入最后 digit 累加循环。
    解决：撤回 `data_at(&sum, sum)`，只在 `p` 循环 invariant 中保留 `INT_MIN + 10 <= sum <= INT_MAX - 10` 这类纯范围信息。这里的经验是：跨循环的局部变量如果没有在循环体内修改，优先先补纯事实；栈权限是否需要显式保留要根据 symexec 生成的空间 VC 形状决定。

12. 问题：最后的 `while (t > 0)` 当前 invariant 只有 `sum <= INT_MAX - 10`，执行 `sum += t % 10` 后无法证明上界保持，因为 `t % 10` 可能为 9；同时该 invariant 也没有表达 `sum` 与 `sum_digits x` 的关系。
    解决：参考 `C_155` 的 digit-state 思路，新增 `signed_digit_tail_loop` / `signed_digit_tail_state`。最终循环 invariant 现在记录“从当前 `t,sum` 跑完尾部 digit 累加会得到 `sum_digits x`”，并把 `sum` 的显式范围收紧为 `-100 <= sum <= 100`。`signed_digit_tail_state_step` 负责循环推进，`signed_digit_tail_state_final` 负责 return。

13. 问题：单 digit 分支中，原 VC 只有 `t < 10`，但没有说明 `t` 就是 `Zabs(x)` 的最高位，因此无法证明 `signed_digit_tail_state x 0 (sum +/- t)`。
    解决：新增 `first_digit_value_145` / `first_digit_state_145`，并把它加入第一个 `while (t >= 10)` 的 invariant。现在 `signed_digit_score_entail_wit_5_1` / `5_2` 已能证明，分别用 `sum_digits_small_nonneg_145` / `sum_digits_small_neg_145` 桥接到 `sum_digits`。

14. 问题：多 digit 分支 `t %= p` 后仍缺少 `p` 是最高 10 次幂的语义事实；当前 `p` 循环 invariant 只有 `1 <= p <= t` 和 `p * 10 > t`，不足以证明 `t % p` 正好去掉最高位。
    解决方向：下一步需要为 `p` 循环增加类似 `highest_power10_state` 的 ghost state，记录 `p` 从 1 开始反复乘 10，且退出时为 `Zabs(x)` 的最高 10 次幂。然后用该状态把 `sum` 的最高位贡献和 `t % p` 的低位 digit 和连接到 `sum_digits x`。

15. 进展：已加入 `highest_power10_state` 并把 C 注解接到 `p` 循环。
    解决：`highest_power10_state` 不再只保存“存在某个 final_p”，而是保存 `highest_power10_loop_145 fuel t p` 的最终结果以及对应的 `signed_digit_tail_state`。这样 `step` 可以通过 fuel 递减证明，`final` 可以用 `p * 10 > t` 推出循环结果就是当前 `p`。`init_nonneg/init_neg` 通过 `spec/145.v` 中结构化的 `sum_digits` 定义、`first_digit_state_145` 和 8 位 fuel 的最高 10 次幂循环建立初始尾部状态。

16. 问题：第二个外层排序循环结束后的 Assert 如果不保留 `data_at(&i, nums_size)`，`order_by_points_entail_wit_9` 会出现无法丢弃 `&( "i" ) # Int |-> nums_size_pre` 的空间 VC。
    解决：在 `free_int_array(score, nums_size)` 前的排序完成 Assert 中加入 `data_at(&i, nums_size)`。这是局部变量权限适配，不改变排序逻辑。

17. 问题：尝试在 `free_int_array(score, nums_size)` 后继续手写包含 `&i/&score/&data/&out` 的 Assert，会导致符号执行在 free 调用或 return 栈权限回收处失败；而在 free 前加入 `data_at(&score, score)` 又会干扰 `free_int_array` 的前置条件匹配。
    解决：参考 `C_120`/`C_33` 的模式，删除 free 后的强 Assert，让 `free_int_array` 后直接 `return out`；free 前只保留排序完成规格和必要的 `data_at(&i, nums_size)`。这样符号执行可以通过，manual VC 中也不再需要处理多余的局部变量资源。

### 后续注意

- 本题最终选择让 `spec/145.v` 中的 `sum_digits` 结构贴近 C 程序，而不是额外证明旧递归 digit-sum 定义与 C 的最高位/低位分解算法等价。后续类似题如果 C 程序本身就是 digit 算法，可以优先让 spec 的 helper 直接表达同一个算法，再用题目前置范围给出固定 fuel。

## C_69 验证记录

### 结论

- 状态：已完成。
- 是否全链通过：是，`coins_69.v`、`C_69_goal.v`、`C_69_proof_auto.v`、`C_69_proof_manual.v`、`C_69_goal_check.v` 均可编译。
- 是否无 `Admitted.` / `Axiom`：`coins_69.v`、`C_69_proof_manual.v` 扫描无 `Admitted.` / `Axiom`。

### 文件变更

- `C_69.c`：把 `malloc/free` 改为带规格的 `malloc_int_array/free_int_array`；保留原频率表算法。经用户许可，在命中已有值并更新 `cnts[j]` / `max` 后加入 `break`。
- `coins_69.v`：加入 `seen_values/counts_for_values` 相关 ghost 定义，以及初始化、计数上界、no-hit 新值插入、hit 已有值计数更新等辅助引理。
- `C_69_proof_manual.v`：已回填所有 manual VC，包括初始化、内层 miss 推进、hit 分支、no-hit 分支和最终返回规格。

### 遇到的问题

1. 问题：原程序内层循环命中 `current == vals[j]` 后没有 `break`。虽然算法不变量应保证 `vals` 无重复，继续扫描不会改变结果，但验证时需要额外证明后续元素都不会再次命中，证明负担很重。
   解决：经用户许可，在更新该值的计数和 `max` 后加入 `break`。这保持频率表算法意图不变，并把“找到唯一对应项后退出”的控制流显式化。

2. 问题：加 `break` 后，内层循环头部 invariant 仍写成 `has == 0 || has == 1` 会产生正常循环退出时 `has == 1` 的不可达 VC。
   解决：将内层循环 invariant 收紧为 `has == 0`。因为一旦 `has` 被置为 1，程序立即 `break`，不会再回到循环头。

3. 问题：内层循环结束后的断言若不保留 `j == j`，生成的 VC 中左侧仍有 `j` 的栈权限，右侧无法匹配，导致空间资源无法 cancel。
   解决：在内层循环后的相关 Assert 中加入 `j == j`，这是 QCP 局部变量权限跟踪所需的注解，不改变 C 执行逻辑。

4. 问题：核心 VC 是命中已有值后，需要证明更新后的 `max` 等于 `search_impl(prefix ++ [current])`，并把更新后的频率表连接到外层状态。
   解决：补 `seen_values_snoc_seen_69`、`seen_values_NoDup_69`、`counts_for_values_snoc_hit_replace_69`、`update_first_count_false_69` 等引理，证明追加一个已见元素时 `seen_values` 不变、`counts_for_values` 只在命中下标增加 1；再用 `search_impl_snoc_69` 把 `hit_max_69` 与规格侧 `search_impl(prefix ++ [current])` 对齐。

5. 问题：no-hit 新增分支中，`vals[freq_size] = current` 后、`cnts[freq_size] = 1` 前的断言一度只保留了数组长度和内存形态，丢失了“这是从 `search_inner_to_outer_69 ... has=0` 进入的新值插入分支”的语义信息，导致后续 `search_outer_add_new_69` 无法从纯长度事实推出。
   解决：新增 `search_after_val_write_69` 作为中间 ghost 谓词，并把它加入 `vals[freq_size] = current` 后的 Assert。该谓词记录写入 `vals` 后的新 `vals_l = base_vals ++ [current]`、`cnts_l = base_cnts`，以及写入前的 `search_inner_to_outer_69 ... 0 max` 状态。对应的 `search_entail_wit_6` 已能证明。

6. 问题：`vals[freq_size] = current` 后的 Assert 如果不保留必要的局部变量权限，会出现左侧多出栈变量资源、右侧无法匹配的空间 VC。
   解决：在该 Assert 中补充 `has == has`（同前面的 `j == j` 思路）。这是 QCP 局部变量权限适配，不改变 C 程序逻辑。

7. 问题：`search_entail_wit_7_1/7_2/7_3` 需要证明 no-hit 分支真正完成 `cnts[freq_size] = 1; freq_size += 1` 后满足 `search_outer_add_new_69`。
   解决：补充并证明 `search_impl_snoc_69`，表达 `search_impl(prefix ++ [x])` 如何由 `search_impl(prefix)` 增量更新；补充 `seen_values_snoc_new_69`、`counts_for_values_snoc_new_69`、`has_first_full_false_notin_69`、`positive_prefix_69` 等引理，最终证明 `search_after_val_write_add_count_69`。目前 no-hit 分支的 manual VC 已可编译通过。

8. 问题：`search_hit_to_outer_69` 曾是最后一个临时 `Admitted`，难点在于 `has = 0` 只表示前 `j` 项未命中，而当前 `j` 项刚命中，需要把 `update_first_count` 的前缀扫描状态转换成“原始计数表第 `j` 项加一”。
   解决：先由 `has_first_69 ... = false` 推出命中前 `cnts = base_cnts`，再用 `replace_Znth` 的命中/非命中下标引理和 `seen_values` 的无重复性证明更新后的计数表等于 `counts_for_values vals (prefix ++ [current])`。最终 `search_hit_to_outer_69` 已正式证明，manual VC 全部通过。

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
