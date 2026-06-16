# Builtin Array / String 支持

这个文档是 array / string annotation 的入口。遇到连续数组、字符缓冲区、C 字符串或字符串字面量时，先读本页；需要更细的数组谓词选型时继续读 `array-predicate-selection.md`。

## 代码入口

Rocq 侧 builtin 定义以本次更新后的 `annotated_simplec` 为准：

- `annotated_simplec/SeparationLogic/ArrayLib.v`
- `annotated_simplec/SeparationLogic/ArrayLibCore.v`
- `annotated_simplec/SeparationLogic/StringLib.v`
- 总入口：`annotated_simplec/SeparationLogic/SeparationLogic.v`

symbolic execution / strategy 侧 builtin 实现以本次更新后的 `sac_c_parser` 为准：

- builtin registry：`sac_c_parser/SymExec/Builtin/StrategyRegistry.c`
- array providers：`sac_c_parser/SymExec/Builtin/Strategies/ArrayProviders.*` 及其生成 / provider 相关源码
- string literal / string read rules：`sac_c_parser/SymExec/Builtin/Strategies/StringLiteral.c`
- string memory oracle 辅助：`sac_c_parser/SymExec/SymExec/MemOracle.c`
- helper / predicate 注册：`sac_c_parser/compiler/env.c`

proof 参考以本次更新后的 `annotated_simplec` / `sac_c_parser` 为准：

- 数组策略 goal / proof：`annotated_simplec/examples/uint_array_strategy_goal.v`、`annotated_simplec/examples/uint_array_strategy_proof.v`
- 未初始化数组 goal / proof：`annotated_simplec/examples/undef_uint_array_strategy_goal.v`、`annotated_simplec/examples/undef_uint_array_strategy_proof.v`
- 字符串基础 goal / proof：`sac_c_parser/stringlib_strategy_goal.v`、`sac_c_parser/stringlib_strategy_proof.v`

不要以 `qcp-binary-democases/QCP_examples/...` 中的旧 demo 为准；那些例子可能会被后续修掉或替换。

## Array 谓词

常用数组谓词来自 `ArrayLib.v`，按元素类型分模块：

- `IntArray`
- `UIntArray`
- `CharArray`
- `UCharArray`
- `ShortArray` / `UShortArray`
- `Int64Array` / `UInt64Array`
- `PtrArray`

核心谓词：

- `TArray::full(p, n, l)`：从地址 `p` 开始的长度 `n` 数组，精确内容为 `l`。
- `TArray::seg(p, lo, hi, l)`：同一基址 `p` 上 `[lo, hi)` 区间，精确内容为 `l`。
- `TArray::full_shape(p, n)` / `seg_shape(p, lo, hi)`：只描述可访问 shape，不追踪元素值。
- `TArray::undef_full(p, n)` / `undef_seg(p, lo, hi)`：未初始化数组或区间。
- `TArray::missing_i(...)` / `undef_missing_i(...)`：策略打开单个元素时的中间形态，通常不手写。

选择规则详见 `array-predicate-selection.md`。简要原则：

- 需要元素语义、`Znth`、`sublist`、`Permutation`、`sum`、排序等性质时，用 `full` / `seg`。
- 只需要内存存在和可访问时，用 `full_shape` / `seg_shape`。
- 未初始化后逐步写入时，用 `undef_full` 起步，循环中维护“已写前缀 + 未写后缀”。
- 多游标 / 区间算法优先用 `seg`，不要把所有区间硬塞进一个 `full`。

## String 与字符缓冲区

新版 `StringLib.v` 区分两类对象：

- C 字符串数组 / 可变字符缓冲区：逻辑内容用 `list Z` 表示，不包含结尾 `0`。
- 字符串字面量 / string literal：逻辑字面量保留 Rocq `string`，用于 interning 和字面量打印。

### 可变 C 字符串：`store_string`

```coq
store_string : Z -> list Z -> Assertion
```

语义：

```coq
store_string(p, s)
  = valid_string(s) &&
    CharArray.full(p, string_length(s) + 1, c_string(s))

c_string(s) = s ++ [0]
string_length(s) = Zlength(s)
```

annotation 中用于 `char *s` 或 `char a[]` 表示“这是一个可读写 C 字符串缓冲区，逻辑内容是 `s`，内存中另有终止符 `0`”。

示例：

```c
/*@ With str
    Require valid_string(str) && string_length(str) < INT_MAX && store_string(s, str)
    Ensure __return == string_length(str) && store_string(s, str)
*/
int strlen(char *s);
```

需要谈底层数组区间时，也可以直接用：

```c
CharArray::full(s, n + 1, app(str, cons(0, nil)))
```

但当程序语义就是 C 字符串时，优先用 `store_string(s, str)`。当前 `sac_c_parser` builtin 策略支持直接从 `store_string` 读取字符。

### 字符串字面量：`store_stringLit`

```coq
store_stringLit : Z -> string -> Assertion
```

语义：

```coq
store_stringLit(p, s)
  = valid_stringLit(s) &&
    CharArray.full(p, StringLength(s) + 1,
                   StringToList(s, StringLength(s) + 1))
```

约定：

- `StringLength(s)` 是 Rocq string 长度，不包含结尾 `0`。
- `StringToList(s, StringLength(s) + 1)` 包含结尾 `0`。
- `ListToString(StringToList(s, StringLength(s))) = s`；如果长度取 `StringLength(s)+1`，会多出 NUL 字符，不应期望回到原 string。

annotation 中用于只读字符串字面量，例如 `char *p = "abc"` 的底层全局常量资源。可写局部数组初始化如 `char a[] = "abc"` 应生成可变数组 / `store_string` 或 `CharArray::full`，不要用 `store_stringLit` 表示局部可写内存。

### 全局字符串池

```coq
GlobalStrings : (string -> Z) -> Assertion
GlobalStrings_missing : (string -> Z) -> list string -> Assertion
```

`LitMap : string -> Z` 表示 string interning 地址。`GlobalStrings(LitMap)` 可由策略 / proof 拆出：

```coq
store_stringLit(LitMap(s), s)
```

同一个字面量应映射到同一个地址；默认不假设不同字面量地址不同，除非 case 自己额外声明。

## 自动化策略会做什么

数组策略由 `sac_c_parser/SymExec/Builtin/StrategyRegistry.c` 中的 array provider 按使用到的数组类型加载。通常在以下场景触发：

- 读 `p[i]`：从 `TArray::full` / `seg` 拆出当前单元，产生 `missing_i` 和 `v == Znth ...`。
- 写 `p[i] = v`：把 `missing_i` 与当前 `store` 合回 `full` / `seg`，精确内容用 `replace_Znth` 更新。
- 只关心 shape：从 `full_shape` / `seg_shape` / `undef_*` 拆出或合回对应单元资源。
- 追加写入末尾：部分 `CharArray` 规则支持从长度 `n` 的 `full` 写入第 `n` 个字符后扩成长 `n+1`。

字符串 / 字面量策略由 `sac_c_parser/SymExec/Builtin/Strategies/StringLiteral.c` 注册，当前包含以下 builtin 规则：

- `GlobalStrings(LitMap)` 与右侧需要的 `store_stringLit(addr, s)` 匹配时，若可推出 `addr == LitMap(s)`，可拆出 `store_stringLit(LitMap(s), s)`，并留下 `GlobalStrings_missing`。
- `GlobalStrings_missing(LitMap, l)` 可继续拆出新的 `store_stringLit(LitMap(s), s)`，也可和已拆出的 `store_stringLit` 合回。
- 已经有 `store_stringLit(addr, s)` 时，可把 `GlobalStrings(LitMap)` 改成缺失该字面量的 `GlobalStrings_missing`，避免重复拆分。
- 同地址的 `store_stringLit(addr, s1)` 与 `store_stringLit(addr, s2)` 可推出 `s1 == s2`。
- 读取 `store_stringLit(addr, s)` 下的 `addr[i]`，可推出读到的值为 `Znth(i, StringToList(s, i + 1), 0)`，并要求 `0 <= i` 与 `i < StringLength(s)+1`。
- 读取 `store_string(addr, zs)` 下的 `addr[i]`，可推出读到的值为 `Znth(i, c_string(zs), 0)`，并要求 `0 <= i` 与 `i < string_length(zs)+1`。
- 当前 builtin 没有全局的整块 `store_string(p, s) -> CharArray::full(p, string_length(s)+1, c_string(s))` 展开规则；需要整块数组资源时，应在 annotation 中直接使用 `CharArray::full`，或确认当前 case 显式加载了额外策略。

策略依赖边界事实：

- 数组读写通常需要 `0 <= i < n`。
- `store_string` 读取通常需要 `0 <= i < string_length(s)+1`。
- `store_stringLit` 读取通常需要 `0 <= i < StringLength(s)+1`。

这些范围最好在 `Require` / `Assert` / `Inv Assert` 中显式可推，不要指望策略猜出复杂循环边界。

## Annotation 建议

- 普通 int/uint/ptr 数组：优先按 `array-predicate-selection.md` 选择 `full`、`seg`、`shape` 或 `undef_*`。
- `char *` 表示 C 字符串且要以“不含终止符的逻辑内容”证明时，用 `store_string(p, s)`。
- 字符数组只是普通字节数组时，用 `CharArray::full/seg/undef_*`。
- 字符串字面量地址由 `LitMap("...")` 或生成器对应形式表示；读取前需要 `GlobalStrings(LitMap)` 或已拆出的 `store_stringLit(LitMap("..."), "...")`。
- 不要把 `String` 直接当成 `list Z`。需要内存列表时通过 `StringToList`，需要普通 C 字符串列表时用 `list Z`。
- 写入 `store_stringLit` 代表写字符串字面量，语义上不应成功；如果程序确实写入该地址，annotation 应重新建模为可写缓冲区。

## Rocq proof 入口

常用 lemma / tactic 线索：

- `prop_apply TArray.full_Zlength`、`TArray.seg_Zlength`：从数组资源得到列表长度。
- `sep_apply TArray.full_split_to_missing_i`、`seg_split_to_missing_i`：手工打开当前元素。
- `sep_apply TArray.missing_i_merge_to_full`、`missing_i_merge_to_seg`：写回后合并。
- `sep_apply TArray.undef_full_to_undef_seg`、`undef_missing_i_merge_to_undef_seg`：处理未初始化区间。
- `store_string_split_to_missing_i`、`store_stringLit_split_to_missing_i`：新版字符串库中的读拆分入口。
- `ListToString_StringToList`、`StringToList_c_length`、`c_string_Zlength`：字符串 helper 的纯性质。

证明案例：

- 数组 builtin goal / proof：`annotated_simplec/examples/uint_array_strategy_goal.v`、`annotated_simplec/examples/uint_array_strategy_proof.v`
- 未初始化数组 goal / proof：`annotated_simplec/examples/undef_uint_array_strategy_goal.v`、`annotated_simplec/examples/undef_uint_array_strategy_proof.v`
- 字符串 builtin goal / proof：`sac_c_parser/stringlib_strategy_goal.v`、`sac_c_parser/stringlib_strategy_proof.v`

如果 proof 中发现必须新增 string/array 的基础语义定义，先确认是不是 builtin 已经提供；若 builtin 缺失，应返回 annotation / library 设计问题，而不是在单个 witness proof 里私自新增顶层定义。
