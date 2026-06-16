# multi_dimensional_arrays 验证进度记录

更新时间：2026-06-05

这份文档记录 `QCP_examples/humaneval/multi_dimensional_arrays` 下多维数组程序的验证进展、建模方式和当前阻塞点。状态口径沿用 `StringClaude/STRINGCLAUDE_VERIFICATION_PROGRESS.md`。

## 状态说明

- `已全链通过`：`symexec`、manual 证明、`goal_check` 编译均通过，且 `coins_XX.v` / `C_XX_proof_manual.v` 无 `Admitted.` / `Axiom`。
- `验证中`：已开始 QCP 转换或验证试跑，但尚未达到全链验收。
- `待确认`：原 C、题面注释或原始 `spec/XX.v` 存在语义冲突，继续前需要用户确认。
- `待建模`：尚未建立完整 QCP 规格和验证文件。
- `试跑阻塞`：已有试验性建模，但当前工具链或策略/证明基础设施不足以继续。

## 当前总览

| 题目 | 类型 | 当前状态 | 备注 |
| --- | --- | --- | --- |
| `C_95` | 字符串数组 `char **` | 试跑阻塞 | 选作字符串数组试点。已改成 QCP 头文件、`int` 返回布尔值、`PtrArray::full + string_rows_full` 两层资源模型，并新增 `coins_95.v`。`symexec` 已能解析到目标函数，但在 `strlen(key)` 处无法从整体 `string_rows_full` 派生当前 `CharArray::full`。 |
| `C_115` | 整数矩阵 `int **` | 试跑阻塞 | 选作整数矩阵试点。已保持核心双层循环，增加 `row = grid[i]` 将二维访问拆成行指针读取和行元素读取，并新增 `coins_115.v`。`symexec` 已能进入目标函数，但在 `row[j]` 处无法从整体 `int_matrix_rows_full` 派生当前 `IntArray` 行元素资源。 |
| `C_12` | 字符串数组 `const char **` | 待确认 | 原注释/spec 要求空输入返回 `None`，但 C 程序初始化 `out = ""` 并在空输入时返回空字符串；不适合作为第一个验证试点。 |

其它题目暂按 `待建模` 处理。

## 本轮试点目标

1. 字符串数组试点先验证 `C_95`，目标是确认 `char **keys` 是否能用：
   `PtrArray::full(keys, n, ptrs) * string_rows_full(ptrs, lens, key_ls)`
   表示。
2. 整数矩阵试点先验证 `C_115`，目标是确认 `int **grid` 是否能用：
   `PtrArray::full(grid, rows, row_ptrs) * int_matrix_rows_full(row_ptrs, cols, grid_l)`
   表示。
3. 两个试点都必须最终直接桥接原始 `spec/95.v` / `spec/115.v` 的 `problem_XX_pre` / `problem_XX_spec`。

## 已发现的通用问题

1. 当前 `../SKILL.md` 只覆盖一维 `IntArray` / `CharArray`，没有说明 `PtrArray` 外层和每行资源的组合谓词。
2. `PtrArray::full` 可以表示第一层指针数组，但访问 `a[i][j]` 需要额外策略或桥接谓词把“第 i 行资源”临时借出并恢复。
3. 字符串数组还需要同时维护每个字符串的长度列表 `lens`，否则 `strlen` wrapper 和 `CharArray::full(p, len + 1, row ++ [0])` 无法稳定匹配。
4. 原始 spec 中常见 `list string` / `list (list nat)`，C 层内存更自然是 `list (list Z)`；`coins_XX.v` 中必须提供纯 wrapper，例如 `map string_of_list_z` 或 `map (map Z.to_nat)`，不能把 C 层操作式规格直接当最终规格。

## 2026-06-05 试跑记录

### `C_95` 字符串数组试点

已做：

- 将普通头文件替换为 QCP 头文件：`verification_stdlib.h`、`verification_list.h`、`char_array_def.h`、`ptr_array_def.h`。
- 将 `bool check_dict_case(const char **keys, ...)` 适配为 `int check_dict_case(char **keys, ...)`，返回 `0/1`；核心大小写检查逻辑保持不变。
- 在 `coins_95.v` 中定义：
  - `problem_95_pre_z : list (list Z) -> Prop`
  - `problem_95_spec_z : list (list Z) -> Z -> Prop`
  - `string_lengths_z`
  - `string_rows_full`
- 函数前后条件使用：
  `PtrArray::full(keys, dict_size, ptrs) * string_rows_full(ptrs, lens, key_ls)`。

试跑命令：

```bash
linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95.c \
  -IQCP_examples/LLM_friendly_cases \
  --gen-and-backup \
  --no-exec-info
```

当前阻塞：

```text
Cannot derive the precondition of function strlen for spec (null)
in QCP_examples/humaneval/multi_dimensional_arrays/C_95.c:86:8
```

含义：`keys[k]` 之后虽然 C 层有 `key = ptrs[k]` 这类纯事实，但现有策略不能从 `string_rows_full(ptrs, lens, key_ls)` 中按 `k` 借出：

```c
CharArray::full(key, lens[k] + 1, app(key_ls[k], cons(0, nil)))
```

因此 `strlen(key)` 的 wrapper 前置条件无法建立。

### `C_115` 整数矩阵试点

已做：

- 将普通头文件替换为 QCP 头文件：`verification_stdlib.h`、`verification_list.h`、`int_array_def.h`、`ptr_array_def.h`。
- 保留原双层循环和 `(sum - 1) / capacity + 1` 计算逻辑，只增加局部 `row = grid[i]`，方便把 `grid[i][j]` 拆成两步访问。
- 在 `coins_115.v` 中定义：
  - `problem_115_pre_z : list (list Z) -> Z -> Prop`
  - `problem_115_spec_z : list (list Z) -> Z -> Z -> Prop`
  - `int_matrix_rows_full`
  - `matrix_rect01_z`
  - `row_sum_prefix_z`
  - `matrix_required_trips_prefix_z`
- 函数前后条件使用：
  `PtrArray::full(grid, grid_rows, row_ptrs) * int_matrix_rows_full(row_ptrs, grid_cols, grid_l)`。

试跑命令同 `C_95`，替换为 `C_115` 文件名。

当前阻塞：

```text
Cannot derive the precondition of Memory Read.
in QCP_examples/humaneval/multi_dimensional_arrays/C_115.c:112:12
```

含义：`row = grid[i]` 后，现有策略不能从 `int_matrix_rows_full(row_ptrs, grid_cols, grid_l)` 中按 `i` 借出当前行：

```c
IntArray::full(row, grid_cols, grid_l[i])
```

因此后续 `row[j]` 的内存读取前置条件无法建立。

### 自定义策略第一版失败经验

最初尝试写 `multi_string_array_95.strategies` 和 `multi_int_matrix_115.strategies`，让策略直接从整体行谓词中读出当前行/字符。但策略语言要求 `check` 中使用的变量必须出现在左侧或右侧匹配模式里，不能自由使用当前循环变量：

```text
Cannot find variable k in the pattern variable and in environment.
Cannot find variable i in the pattern variable and in environment.
```

后续应改为显式 missing/borrow 谓词，而不是让策略直接从 `string_rows_full` / `int_matrix_rows_full` 用自由下标取行。

建议新增的通用谓词形状：

```coq
string_rows_missing_i ptrs lens rows i p len row
int_matrix_rows_missing_i ptrs cols rows i rowp row
```

借出流程应类似 `C_19` 的 `number_words_full/number_words_missing`：

1. 从整体 `*_full` 和纯下标范围推出当前行资源与 `*_missing_i`。
2. 在内层循环或 `strlen` 调用期间持有当前行 `CharArray::full` / `IntArray::full`。
3. 内层结束后用 merge lemma 恢复整体 `*_full`。

本轮失败的空 `C_95_goal.v` / `C_115_goal.v` 等生成文件已经清理；当前未产生可用的正式 goal/proof 文件。
