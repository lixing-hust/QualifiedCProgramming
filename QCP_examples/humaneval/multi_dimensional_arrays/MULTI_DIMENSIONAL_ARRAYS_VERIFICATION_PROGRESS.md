# multi_dimensional_arrays 验证进度记录

更新时间：2026-06-17

这份文档记录 `QCP_examples/humaneval/multi_dimensional_arrays` 下多维数组程序的验证进展、建模方式、踩坑和后续继续时需要注意的事项。状态口径参考 `StringClaude/STRINGCLAUDE_VERIFICATION_PROGRESS.md`。

它和下面几份文档分工不同：

- `../SKILL.md`：记录 HumanEval C 验证的完整流程、原始 spec wrapper 约束、ledger 成本记录要求。
- `../ledger.md`：记录每次 case 的 token 与耗时成本。
- 本文档：记录每一道多维数组题当前做到哪里、踩过哪些坑、最后如何解决。

## 状态说明

- `已全链通过`：已经完成 `symexec`、manual 证明、`goal_check` 编译，且 `coins_XX.v` / `C_XX_proof_manual.v` 无 `Admitted.` / 新增 `Axiom`，最终 `problem_XX_pre_z/spec_z` 直接桥接原始 `../spec/XX.v`。
- `已有生成文件`：目录中已有 `C_XX_goal.v` / `C_XX_proof_auto.v` / `C_XX_proof_manual.v` / `C_XX_goal_check.v`，但本文档尚未确认完整验收。
- `验证中`：已建立 QCP 建模或通过部分工具链检查，但尚未达到全链验收标准。
- `试跑阻塞`：已有试验性建模，但当前工具链、策略或证明基础设施不足以继续。
- `待确认`：原 C、题面注释或原始 `spec/XX.v` 存在语义冲突，继续前需要用户确认。
- `待建模`：尚未建立完整 QCP 规格和验证文件。

## 当前总览

| 题目 | 类型 | 当前状态 | 备注 |
| --- | --- | --- | --- |
| `C_95` | 字符串数组 `char **` | 已全链通过 | `problem_95_spec_z` 已直接 wrapper 原始 `spec/95.v` 的 `problem_95_spec`；使用 `CharPtrArray2.full/missing_i` 和 `CharArray.full` 表示二维字符串数组资源；已通过 `coins_95.v`、`C_95_goal.v`、`C_95_proof_auto.v`、`C_95_proof_manual.v`、`C_95_goal_check.v` 编译，`coins/manual/goal_check` 无 `Admitted.` 或新增 `Axiom`。成本见 `../ledger.md` 的 `C_95` 与 `C_95_continuation`。 |
| `C_115` | 整数矩阵 `int **` | 已全链通过 | `problem_115_spec_z` 直接 wrapper 原始 `spec/115.v` 的 `problem_115_spec`；使用 `IntPtrArray2.full/missing_i` 和 `IntArray.full` 表示二维 `int **` 矩阵资源；已通过 `coins_115.v`、`C_115_goal.v`、`C_115_proof_auto.v`、`C_115_proof_manual.v`、`C_115_goal_check.v` 编译，`coins/manual/goal_check` 无 `Admitted.` 或新增 `Axiom`。成本见 `../ledger.md` 的 `C_115`。 |
| `C_12` | 字符串数组 `const char **` | 已全链通过 | 用户确认按原注释/spec 语义处理空输入，C 实现已改为空输入返回 `NULL`；`problem_12_pre_z/spec_*_z` 直接 wrapper 原始 `spec/12.v` 的 `problem_12_pre/spec`；使用 `CharPtrArray2.full/missing_i`、`CharArray.full` 和 `QCP_examples/stdlib/string.h` 的 `strlen`/`store_string` 表示二维字符串数组与行长度；已通过 `coins_12.v`、`C_12_goal.v`、`C_12_proof_auto.v`、`C_12_proof_manual.v`、`C_12_goal_check.v` 编译，`coins/manual/goal_check` 无 `Admitted.` 或新增 `Axiom`。成本见 `../ledger.md` 的 `C_12_continuation`。 |
| `C_29` | 字符串数组过滤 `char **` | 已全链通过 | `problem_29_pre_z/spec_z` 直接 wrapper 原始 `spec/29.v` 的 `problem_29_pre/spec`；使用 `CharPtrArray2.full/missing_i` 和 `CharArray.full/store_string` 表示输入二维字符串数组，使用公共 `PtrArray` 谓词表示返回的借用指针数组；使用 `QCP_examples/stdlib/string.h` 的 `strlen`/`strncmp`；已通过公共 `ptr_array2_strategy_*`、`coins_29.v`、`C_29_goal.v`、`C_29_proof_auto.v`、`C_29_proof_manual.v`、`C_29_goal_check.v` 编译，`coins/manual/goal_check/strategy_proof` 无 `Admitted.` / `Abort` / 新增 `Axiom`。成本见 `../ledger.md` 的 `C_29`。 |

其它题目暂按 `待建模` 处理。

## C_12 longest 验证记录

### 当前状态

`C_12` 已全链通过。

已完成：

```bash
opam exec --switch=coq8201 -- linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_12_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_12_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_12_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  -slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM \
  --strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/ \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_12.c \
  -IQCP_examples/LLM_friendly_cases \
  -IQCP_examples/QCP_demos_LLM \
  -IQCP_examples/stdlib \
  --gen-and-backup \
  --no-exec-info
```

并通过 `coins_12.v`、`C_12_goal.v`、`C_12_proof_auto.v`、`C_12_proof_manual.v`、`C_12_goal_check.v` 编译。编译时需要额外给 `string_lib` 与 unqualified `string_strategy_*` 加 load path：

```bash
coqc -Q ../../../SeparationLogic/stdlib "" \
     -R ../../../SeparationLogic/stdlib SimpleC.StdLib \
     $COQINCLUDES C_12_goal_check.v
```

扫描结果：

```bash
rg -n "Admitted\.|^\s*Axiom\b" \
  coins_12.v C_12_proof_manual.v C_12_goal_check.v
```

无输出。

### 语义与建模约束

1. 空输入语义按原注释和 `spec/12.v`：返回 `None`。用户已确认将 C 实现从返回空字符串改为空输入返回 `NULL`。
2. 最终 spec 直接桥接原始 `spec/12.v`：`problem_12_pre_z` 调用 `problem_12_pre`，`problem_12_spec_none_z` / `problem_12_spec_some_z` 调用 `problem_12_spec` 的 `None` / `Some` 返回形式。
3. 行内存使用 `CharPtrArray2.full/missing_i` 和 `CharArray.full`。调用 `strlen` 前，把当前行资源转换成 `store_string(cur, row_payload_z_12 row)`，使用 `QCP_examples/stdlib/string.h` 的规格。
4. 非空返回时后置条件保持 split 形态：`CharPtrArray2.missing_i * data_at(strings + best_idx * sizeof(char *)) * CharArray.full`。这样既保留完整二维数组所有权，也暴露 `__return == row_ptr` 与 `best_idx` 的关系。

## C_95 check_dict_case 验证记录

### 当前状态

`C_95` 已全链通过。

已完成：

```bash
linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  -slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM \
  --strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/ \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_95.c \
  -IQCP_examples/LLM_friendly_cases \
  -IQCP_examples/QCP_demos_LLM \
  --gen-and-backup \
  --no-exec-info
```

并通过：

```bash
cd QCP_examples/humaneval/multi_dimensional_arrays
COQINCLUDES="$(tr "\n" " " < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_95.v
coqc $COQINCLUDES C_95_goal.v
coqc $COQINCLUDES C_95_proof_auto.v
coqc $COQINCLUDES C_95_proof_manual.v
coqc $COQINCLUDES C_95_goal_check.v
```

扫描结果：

```bash
rg -n "Admitted\.|^\s*Axiom\b" \
  coins_95.v C_95_proof_manual.v C_95_goal_check.v
```

无输出。

### 语义与建模约束

1. 最终 spec 必须直连原始 `spec/95.v`。

最终 `coins_95.v` 中：

```coq
Definition problem_95_pre_z (rows : list (list Z)) : Prop :=
  problem_95_pre (rows_to_dictionary_z rows).

Definition problem_95_spec_z (rows : list (list Z)) (ret : Z) : Prop :=
  problem_95_spec (rows_to_dictionary_z rows) (bool_of_z ret).
```

中间用到的 `rows_have_uniform_case_z`、`invalid_char_seen_z`、`mixed_case_seen_z`、`scan_state_z` 都只是 C annotation / invariant / bridge lemma 的内部状态，不能作为最终 `_z` 规格替代原 spec。

2. C 层表示是 `list (list Z)`。

每一行表示一个以 `0` 结尾的 C 字符串。`row_payload_z row` 去掉最后一个终止符，再通过：

```coq
string_of_list_z (row_payload_z row)
```

转成原始 spec 里的 Coq `string`。`rows_to_dictionary_z` 把每一行映射为：

```coq
(KeyString (string_of_list_z (row_payload_z row)), EmptyString)
```

因为本题原 spec 只检查 key，value 内容无关。

3. 内存资源使用 `CharPtrArray2`。

本题没有继续使用早期自定义 `string_rows_full`。实际通过的是 QCP demos 中已有的二维 char pointer array 策略：

```coq
CharPtrArray2.full keys_pre dict_size_pre rows
CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows
CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)
```

核心证明模式是：

- 外层循环从 `CharPtrArray2.full` 借出第 `k` 行：
  `full_split_to_missing_i`
- 内层持有当前行的 `CharArray.full`
- 内层结束或提前返回时用：
  `missing_i_merge_to_full`
  把当前行资源合回完整二维数组。

4. 返回值用 `int` 表示 bool。

C 函数返回 `0/1`，Coq wrapper 中用：

```coq
Definition bool_of_z (z : Z) : bool := Z.eqb z 1.
```

桥接到原始 `problem_95_spec` 的 bool 返回值。

### 主要踩坑与解决办法

1. 早期自定义 `string_rows_full` 方案无法喂给 `strlen` / 当前行访问。

早期试点使用：

```coq
PtrArray.full keys n ptrs * string_rows_full ptrs lens rows
```

但 symexec/strategy 无法从整体 `string_rows_full` 按 `k` 自动借出：

```coq
CharArray.full row_ptr len row
```

于是 `strlen(key)` 或 `key[i]` 的前置条件无法建立。

解决办法：改用现有 demo 的 `CharPtrArray2` 策略和 `missing_i` 资源模型。二维数组不要只写一个自定义整体谓词；要有“借出当前行 / 合回当前行”的 missing 谓词和 merge lemma。

2. strategy import 路径需要额外 `-slp`。

`C_95_goal.v` 生成后会 import：

```coq
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
```

因此 symexec 命令必须带：

```bash
-slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM
--strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/
-IQCP_examples/QCP_demos_LLM
```

否则生成文件会找不到相关 strategy 逻辑路径。

3. 策略依赖本身需要先编译。

如果 `coqc C_95_goal.v` 报找不到 `ptr_array2_strategy_goal` / `char_array_strategy_goal` 之类路径，需要先编译策略依赖：

```bash
opam exec --switch=coq8201 -- bash -lc '
COQBASE="$(head -n -1 QCP_examples/humaneval/IntClaude/_CoqProject | tr "\n" " ")"
coqc $COQBASE SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_goal.v
coqc $COQBASE SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_proof.v
coqc $COQBASE SeparationLogic/examples/QCP_demos_LLM/char_array_strategy_goal.v
coqc $COQBASE SeparationLogic/examples/QCP_demos_LLM/char_array_strategy_proof.v
'
```

这里用 `head -n -1` 是为了避免 `_CoqProject` 最后一行 `-R . SimpleC.EE` 把当前目录映射干扰到 `SeparationLogic/examples` 的编译。

4. QCP core / 依赖混用会导致“看似 coqc 有问题”的报错。

本轮中 `coins_95.v` 可以编译，但 `C_95_goal.v` / strategy 相关文件编译失败。根因不是 `coqc` 本身坏了，而是 QCP core / examples 依赖处在 stale 或混编状态。重新刷新依赖并重编 QCP core 后，strategy 和生成文件能正常编译。

这类开销已单独记在 `../ledger.md` 的 infrastructure 行，不计入 `C_95_continuation` 验证成本。

5. 过早在 C annotation 中写 return 前 `Assert` 会生成难处理的资源丢弃 VC。

本题早期在几个 `return 0` / `return 1` 前手写了完整后置条件式 `Assert`，symexec 生成了类似要从局部栈资源推出最终后置条件的畸形 VC，出现 `full ** locals |-- full` 这类不自然目标。

解决办法：删掉 return 前那些重复的显式 `Assert`，让 QCP 的 return rule 自己处理局部变量和函数后置条件。语义证明放在对应 `return_wit_*` manual proof 中完成。

6. 曾短暂证明过 rows-level spec，但不能算完整通过。

中途为了让 C proof 闭环，曾把 `problem_95_spec_z` 写成：

```coq
if ret = 1 then rows <> nil /\ rows_have_uniform_case_z rows else ...
```

这能证明 C 层操作式语义，但违反 `../SKILL.md` 的硬要求：最终 `_z` spec 必须直接 wrapper 原始 `spec/95.v`。

最终解决办法：恢复：

```coq
problem_95_spec (rows_to_dictionary_z rows) (bool_of_z ret)
```

然后补充 bridge lemma：

- `row_all_lower_is_lowercase_95`
- `row_all_upper_is_uppercase_95`
- `dictionary_all_lower_from_rows_95`
- `dictionary_all_upper_from_rows_95`
- `dictionary_all_lower_char_95`
- `dictionary_all_upper_char_95`
- `problem_95_spec_z_invalid`
- `problem_95_spec_z_mixed`
- `problem_95_spec_z_success`

这些 bridge 把 C 层扫描状态、无效字符、混合大小写和成功统一大小写，连接回原始 dictionary/string/ascii 规格。

7. ascii 比较 bridge 不要展开到位级结构。

原 spec 中大小写判断使用：

```coq
(("a" <=? c)%char && (c <=? "z")%char) = true
```

C 层证明的是 Z 字符码范围：

```coq
97 <= c <= 122
65 <= c <= 90
```

如果直接 `compute`，Coq 会把 ascii 展开成巨大的 bit/N 表达式，目标非常难读。

解决办法：局部建立 `Ascii.leb` 与 `nat_of_ascii` / `N_of_ascii` 的桥：

- `ascii_leb_true_to_Z_le_95`
- `ascii_leb_true_of_Z_le_95`
- `nat_of_ascii_ascii_of_z_95`
- `lower_ascii_of_z_95`
- `upper_ascii_of_z_95`
- `lower_ascii_of_z_inv_95`
- `upper_ascii_of_z_inv_95`

并用：

```coq
change (Z.of_nat (nat_of_ascii "a"%char)) with 97.
```

这类定向化简，避免整坨 bit 表达式进入上下文。

8. `row_payload_z` 的长度和元素关系要单独封装。

`row_payload_z row = firstn (Z.to_nat (Zlength row - 1)) row`，证明 payload 中第 `i` 个字符等于 row 中第 `i` 个字符时，`firstn_length` / `Nat.min` / `Z.to_nat` 的算术容易让 `lia` 找不到 witness。

解决办法：封装：

- `Znth_firstn_95`
- `Zlength_row_payload_z_95`
- `row_payload_index_z_95`
- `Znth_row_payload_z_95`

之后桥接原 spec 时只 rewrite 这些 lemma，不在主证明里反复展开 `firstn`。

9. `split_goal_*` 和 manual 中的 `Abort` 不是未完成 VC。

`symexec` 会在 `C_95_goal.v` 中生成很多辅助定义：

```coq
check_dict_case_entail_wit_7_split_goal_1
check_dict_case_entail_wit_7_split_goal_spatial
```

manual 文件里也可能保留：

```coq
Lemma proof_of_check_dict_case_entail_wit_7_split_goal_1 : ...
Proof. Abort.
```

这些是可选的“拆分后子目标证明路线”。最终 `C_95_goal_check.v` 需要的是主 witness：

```coq
proof_of_check_dict_case_entail_wit_7 : check_dict_case_entail_wit_7
```

本题选择直接证明主 witness，因此 split goal 的 `Abort` 不进入 Coq 环境，不是 `Admitted`，也不影响 `goal_check`。如果某个 split goal proof 真被接口需要，`coqc` 会报找不到对应常量，不会静默通过。

10. return 分支里的 `||` 是 separation logic or，不是 Coq 普通 `or`。

`return_wit_2` 到 `return_wit_6` 最初用过 `left.`，会失败。目标中的：

```coq
P || Q
```

是 separation logic 的 `orp`，应使用：

```coq
eapply derivable1_trans with (y := ...).
- ...
- apply derivable1_orp_intros1.
```

成功返回 `1` 的分支对应右侧，用：

```coq
apply derivable1_orp_intros2.
```

### manual 证明结构

关键 witness：

- `entail_wit_3`：从完整二维数组借出第 `k` 行。
- `entail_wit_6_1`：扫描到小写字符时推进 `scan_state_z`。
- `entail_wit_6_2`：扫描到大写字符时推进 `scan_state_z`。
- `entail_wit_7`：当前行扫描完后合回完整二维数组，并推进到下一行。
- `return_wit_1`：所有行扫描完成，证明 rows 统一大小写，再桥接原始 spec 返回 true。
- `return_wit_2/3`：发现大小写混合，合回二维数组，桥接原始 spec 返回 false。
- `return_wit_4/5/6`：发现非字母 key 字符，合回二维数组，桥接原始 spec 返回 false。

合回当前行的常用模式：

```coq
pose proof (CharPtrArray2.missing_i_merge_to_full
      keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
unfold StorePtrAsElement.storeA in Hmerge.
try rewrite sizeof_ptr in Hmerge.
change (CharPtrArray2.ElemArray.full row_ptr
  (Zlength (Znth k rows nil)) (Znth k rows nil))
  with (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)) in Hmerge.
try rewrite sizeof_ptr.
sep_apply Hmerge; try lia.
rewrite replace_Znth_Znth by lia.
entailer!.
```

### 成本记录

本题成本已经写入 `../ledger.md`：

- `C_95`：早期 partial 记录，包含 QCP 转换和首次 symexec，但 manual 尚未完成。
- `QCP_core_rebuild_for_C_95`：基础设施开销，单独记录，不计入 case。
- `C_95_continuation`：本轮正式补完 C_95，状态 `full-chain passed`，包含从 2026-06-17 02:28 CST 到 03:29 CST 的时间和 token delta。

后续继续验证其它多维数组题时，也应按 `../SKILL.md` 在 `../ledger.md` 中单独开行，不要把 core rebuild / 工具链修复混入 case 成本。

## C_115 max_fill 验证记录

### 当前状态

`C_115` 已全链通过。旧试点中“无法从整体矩阵借出当前行”的阻塞已解决：本轮直接复用 `QCP_examples/QCP_demos_LLM/2DIntPtrArray.c` 对应的整数二维指针数组模型，即 `IntPtrArray2.full/missing_i` 加 `IntArray.full`。

已完成：

```bash
linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_115_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_115_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_115_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  -slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM \
  --strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/ \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_115.c \
  -IQCP_examples/LLM_friendly_cases \
  -IQCP_examples/QCP_demos_LLM \
  --gen-and-backup \
  --no-exec-info
```

并通过：

```bash
cd QCP_examples/humaneval/multi_dimensional_arrays
COQINCLUDES="$(tr "\n" " " < ../IntClaude/_CoqProject) -R ../../QCP_demos_LLM SimpleC.EE.QCP_demos_LLM"
coqc $COQINCLUDES coins_115.v
coqc $COQINCLUDES C_115_goal.v
coqc $COQINCLUDES C_115_proof_auto.v
coqc $COQINCLUDES C_115_proof_manual.v
coqc $COQINCLUDES C_115_goal_check.v
```

扫描结果：

```bash
rg -n "Admitted\.|^\s*Axiom\b" \
  coins_115.v C_115_proof_manual.v C_115_goal_check.v
```

无输出。

### 语义与建模约束

1. 最终 spec 直连原始 `spec/115.v`。

`coins_115.v` 中 `problem_115_pre_z/spec_z` 分别把 `list (list Z)` 和 `capacity : Z` 转成原始 spec 使用的 `list (list nat)` 和 `nat`，最终 theorem `problem_115_spec_z_of_trips_prefix` 把 C 层累加出的 `trips_prefix_z rows (Zlength rows) capacity` 桥接回原始 `problem_115_spec`。

2. C 层循环不改变原始算法。

函数主体仍是双层循环：内层统计当前行的 `sum`，外层在 `sum > 0` 时累加 `(sum - 1) / capacity + 1`。annotation 中新增的 `row_sum_prefix_z`、`row_trip_z`、`trips_prefix_z` 只服务 invariant 和 bridge proof。

3. 内存资源使用 `IntPtrArray2`。

外层 invariant 持有：

```coq
IntPtrArray2.full grid_pre grid_rows_pre rows
```

进入内层前借出当前行：

```coq
IntPtrArray2.missing_i grid_pre grid_rows_pre i row_ptr rows *
data_at (grid_pre + i * sizeof(int *)) int* row_ptr *
IntArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)
```

内层结束后用 `IntPtrArray2.missing_i_merge_to_full` 合回完整矩阵。

### 主要踩坑与解决办法

1. `sum` 的更新需要显式行前缀 lemma。

内层循环 invariant 使用：

```coq
sum == row_sum_prefix_z(Znth(i, rows, nil), j)
```

manual proof 中用 `row_sum_prefix_z_step` 证明 `sum + grid[i][j]` 正好对应 `j + 1` 前缀。

2. `nil` 默认行和生成器默认行需要用 `Znth_indep` 对齐。

生成的 VC 中有时是 `Znth i rows nil`，有时是 `Znth i rows __default__List_Z`。在 manual proof 的行资源、前缀和以及 return bridge 中，都需要在 `0 <= i < Zlength rows` 条件下用 `Znth_indep` 同步这两种写法。

3. `sum > 0` 分支要把 C 的除法表达式桥到 trips prefix。

`trips_prefix_z_step_from_sum` 把：

```coq
trips_prefix_z rows (i + 1) capacity
```

展开成当前累计值加当前行所需次数；`trips_prefix_z_nonneg_bound_step` 负责 `out` 的上下界，避免直接让 `lia` 处理带 `Z.quot` 的目标。

### 成本记录

本题成本已经写入 `../ledger.md` 的 `C_115` 行。本轮按用户要求只参考 `../SKILL.md` 和 `2DIntPtrArray.c`，未使用 `.agents` 下的 skill 或 subagent。

## 通用经验

1. 多维数组验证的关键不是 list 语义，而是资源生命周期。

`list (list Z)` 语义通常好写，真正困难在：

- 从外层指针数组借出当前行；
- 内层循环期间保留当前行资源；
- 提前返回时合回完整资源；
- 循环继续时恢复外层 invariant。

2. `missing_i` 比“大整体谓词 + 自由下标策略”可靠。

早期自定义 strategy 试图让策略从整体谓词里自由使用循环变量 `k/i`，容易报：

```text
Cannot find variable k in the pattern variable and in environment.
```

更稳定的做法是把借出关系显式表达成 `missing_i` 谓词和 split/merge lemma。

3. C annotation 中不要过度提前断言最终 postcondition。

return 前的最终 postcondition 可以交给 return witness 证明；提前写复杂 `Assert` 可能让 symexec 生成局部资源无法自动丢弃的目标。

4. rows-level 操作式规格可以帮助设计 invariant，但不能作为最终验收规格。

可以先在 Coq 中定义：

```coq
rows_have_uniform_case_z
invalid_char_seen_z
mixed_case_seen_z
scan_state_z
```

帮助证明 C 循环，但最终 `problem_XX_spec_z` 必须回到原始 `problem_XX_spec`。

5. 看到 `split_goal_*` 不必恐慌。

它是 symexec 生成的可选拆分目标。若直接证明主 witness，manual 中的 split goal `Abort` 可以保留或清理；验收看 `goal_check` 和主 witness proof，不看被 `Abort` 废弃的 split lemma。

## C_28 concatenate 验证记录

### 当前状态

`C_28` 已全链通过。本轮按用户要求只参考 `../SKILL.md`、`QCP_examples/QCP_demos_LLM/2DCharPtrArray.c` 和 `QCP_examples/stdlib/string.h`，未使用 `.agents` 下的 skill 或 subagent。

已完成：

```bash
linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_28_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_28_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_28_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  -slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM \
  --strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/ \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_28.c \
  -IQCP_examples/LLM_friendly_cases \
  -IQCP_examples/QCP_demos_LLM \
  -IQCP_examples/stdlib \
  --gen-and-backup \
  --no-exec-info
```

并通过：

```bash
cd QCP_examples/humaneval/multi_dimensional_arrays
COQINCLUDES="$(tr "\n" " " < ../IntClaude/_CoqProject)"
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES coins_28.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_28_goal.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_28_proof_auto.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_28_proof_manual.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_28_goal_check.v
```

扫描结果：

```bash
rg -n "Admitted\.|Abort\.|^\s*Axiom\b" \
  coins_28.v C_28_proof_manual.v C_28_goal_check.v
```

无输出。

### 语义与建模约束

1. 最终 spec 直连原始 `spec/28.v`。

`coins_28.v` 中 `problem_28_pre_z/spec_z` 只是把 `list (list Z)` 转换为原始 spec 使用的 `list string` / `string`，最终 `problem_28_spec_z_intro` 把拼接后的 payload 桥回 `problem_28_spec`。

2. C 层保持原始双循环拼接算法。

函数主体仍先用 `strlen` 统计总长度，再分配输出缓冲区，第二个循环用 `strlen` 和 `memcpy` 逐行复制，最后写入 `'\0'`。新增的 `total_prefix_state_28`、`copy_prefix_state_28`、`concat_prefix_payload_28` 只服务 invariant 和 bridge proof。

3. `char **` 资源使用 `CharPtrArray2`。

外层持有：

```coq
CharPtrArray2.full strings_pre strings_size_pre rows
```

需要访问当前字符串时借出：

```coq
CharPtrArray2.missing_i strings_pre strings_size_pre i row_ptr rows *
data_at (strings_pre + i * sizeof(char *)) char* row_ptr *
store_string row_ptr (row_payload_z_28 (Znth i rows nil))
```

用完后通过 `CharPtrArray2.missing_i_merge_to_full` 合回完整二维指针数组。

### 主要踩坑与解决办法

1. 行内容需要显式表示为 C string。

`rows_well_formed_28` 要求每行 `row = c_string payload`，并保存 `valid_string`、`all_ascii`、`string_length payload < INT_MAX`。这让 `strlen`/`memcpy` 的库规格可以直接使用 `row_payload_z_28`。

2. 循环退出后的局部变量 frame 要在 C annotation 中保留。

第二个循环退出后，如果断言过薄，symexec 会生成一个试图从参数栈槽加输出尾段推出单独输出尾段的空间目标。最终在退出断言和写零后的断言里保留 `strings_size == strings_size@pre` 与 `strings == strings@pre`，让局部 frame 被自然处理。

3. return witness 只需要长度等式和原始 spec bridge。

`copy_prefix_state_28 rows strings_size k out_l` 给出 `k = Zlength out_l`；`rows_well_formed_28` 给出 `Zlength rows = strings_size`；两者合起来可用 `problem_28_spec_z_intro` 直接证明原始 concat spec。

### 成本记录

本题成本已经写入 `../ledger.md` 的 `C_28` 行：`2026-06-17 13:51 CST` 到 `2026-06-17 15:19 CST`，88 分钟，token delta `44134773`。

## C_29 filter_by_prefix 验证记录

### 当前状态

`C_29` 已全链通过。本轮按用户要求只参考 `../SKILL.md`、`QCP_examples/QCP_demos_LLM/2DCharPtrArray.c` 和 `QCP_examples/stdlib/string.h`，未使用 `.agents` 下的 skill 或 subagent。

已确认 `QCP_examples/stdlib/string.h` 提供本题需要的 `strlen` 和 `strncmp`。

注意：`C_29.c` 文件头示例把 `"vector"` 写进 prefix `"a"` 的输出，但 `spec/29.v` 的示例、正式 `problem_29_spec` 和 C 实现本身都是标准前缀过滤语义。本轮证明按正式 `spec/29.v` 与实际 C 前缀过滤逻辑完成。

已完成：

```bash
opam exec --switch=coq8201 -- linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_29_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_29_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_29_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  -slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM \
  --strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/ \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_29.c \
  -IQCP_examples/LLM_friendly_cases \
  -IQCP_examples/QCP_demos_LLM \
  -IQCP_examples/stdlib \
  --gen-and-backup \
  --no-exec-info
```

并通过：

```bash
COQINCLUDES_COMMON="$(head -n -1 QCP_examples/humaneval/IntClaude/_CoqProject | tr "\n" " ")"
coqc -Q SeparationLogic/stdlib "" -R SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES_COMMON SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_goal.v
coqc -Q SeparationLogic/stdlib "" -R SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES_COMMON SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_proof.v

cd QCP_examples/humaneval/multi_dimensional_arrays
COQINCLUDES="$(tr "\n" " " < ../IntClaude/_CoqProject)"
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES coins_29.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_29_goal.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_29_proof_auto.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_29_proof_manual.v
coqc -Q ../../../SeparationLogic/stdlib "" -R ../../../SeparationLogic/stdlib SimpleC.StdLib $COQINCLUDES C_29_goal_check.v
```

扫描结果：

```bash
rg -n "\b(Admitted|Abort|Axiom)\b" \
  coins_29.v C_29_proof_manual.v C_29_goal_check.v \
  ../../../SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_proof.v
```

无输出。

### 语义与建模约束

1. 最终 spec 直连原始 `spec/29.v`。

`coins_29.v` 中 `problem_29_pre_z` 和 `problem_29_spec_z` 只是把 C 层 `list (list Z)` / `list Z` 转换成原始 spec 使用的 `list string` / `string`，定义体直接调用 `problem_29_pre` 和 `problem_29_spec`。

2. C 层保持原始过滤逻辑。

函数仍按原逻辑先计算 `plen = strlen(prefix)`，遍历 `strings[i]`，用 `strncmp(cur, prefix, plen) == 0` 判断前缀匹配，匹配时把原行指针写入输出数组。

3. `char **` 输入资源使用 `CharPtrArray2`。

外层持有 `CharPtrArray2.full strings strings_size rows`。访问当前行时用 `missing_i` 借出当前指针槽和行字符串资源，调用 `strncmp` 后再合回完整输入数组。

4. 返回数组是借用指针数组。

`PtrArray` 已整合进公共 `QCP_examples/QCP_demos_LLM/ptr_array2_def.h`，并由公共 `ptr_array2.strategies` / `ptr_array2_strategy_*` 支撑，用 `PtrArray.seg` 和 `PtrArray.undef_seg` 表示已写输出指针前缀与未初始化后缀。

### 主要踩坑与解决办法

1. `strncmp` 结果需要和原始 string prefix 规格桥接。

在 `coins_29.v` 中补了 `strncmp_result_prefix_match_29` / `strncmp_result_prefix_nomatch_29` 等局部 bridge，把 C 层 `list Z` 前缀比较连接到原始 `Coq.Strings.String.prefix` 语义。

2. 返回指针数组需要公共 `PtrArray` 策略。

输出数组只存放已有行指针，不拥有行字符串内容；因此使用公共 `PtrArray` 指针数组谓词和 split/merge strategy，比把它混入 `CharPtrArray2` 更稳定。

3. 循环 invariant 分成两条线。

语义线用 `filter_prefix_state_29 rows prefix_l i output_rows` 描述已处理前缀的过滤结果；内存线用 `PtrArray.seg data 0 output_size output_ptrs * PtrArray.undef_seg data output_size strings_size` 描述输出数组写入进度。

### 成本记录

本题成本已经写入 `../ledger.md` 的 `C_29` 行：`2026-06-17 15:39 CST` 到 `2026-06-17 16:32 CST`，53 分钟，token delta `30555449`。后续把 `PtrArray` 整合进公共 `ptr_array2_def.h` / `ptr_array2.strategies` 属于验证后的整理，不计入本题验证成本。
