---
name: humaneval-c-verification-zh-compact
description: "中文精简流程：用于 humaneval/IntClaude、IntArrayClaude 与 StringClaude 下 C_XX 端到端验证，覆盖原始 C 程序到 QCP 格式转换、核心逻辑保护、不变式重建、symexec 重生成、manual 证明补全、无 Admitted 或 Axiom、goal_check 编译通过，并补充数组与字符串内存验证要点。"
---

# HumanEval C 验证技能（中文精简版）

适用场景：验证 `QCP_examples/humaneval/IntClaude`、`QCP_examples/humaneval/IntArrayClaude` 与 `QCP_examples/humaneval/StringClaude` 下的 `C_XX.c` 任务，完成从原始 C 程序适配 QCP 格式，到注解、符号执行、Coq 证明的全流程闭环。

## 目标

- 通过符号执行与 Coq 编译链。
- `C_XX_proof_manual.v`（以及手写桥接文件）中无 `Admitted.`、无 `Axiom`。
- `C_XX_goal_check.v` 编译成功。
- 对数组程序，内存所有权与数组内容约束保持一致，无未初始化读取。
- 对字符串程序，明确 `CharArray` 内容、终止符、输出缓冲区和字符编码约束。

## 强约束

1. 先把原始 C 程序改成 QCP 支持格式，再开始正式验证；格式转换参考 `QCP_examples/humaneval/QCP_FORMAT_CONVERSION_GUIDE.md`。
2. 格式转换只能做接口与验证环境适配：替换 QCP 头文件、结构体指针返回适配、增加 `malloc/free/sort/qsort` 等通用库函数 wrapper 规格、添加目标函数前后条件骨架和 `coins_XX.v` 桥接定义。
3. 未经用户确认，不修改原 C 程序的核心业务逻辑。若为了验证需要改变循环结构、分支行为、容量策略、提前返回语义、过滤/排序/计算规则，必须暂停并告诉用户原因、原逻辑、拟改逻辑和影响。
4. 不允许把原程序核心逻辑替换成未实现函数规格。只有 `malloc/free/qsort/sort` 这类通用库函数可以用未定义 wrapper 规格表示。
5. 原程序已有 helper 可以保留并补规格；如需新抽 helper，helper 必须有 C 实现并单独验证，且只能拆分局部机械操作或独立子逻辑，不能隐藏题目主逻辑。
6. `sort_int_array` 必须保持通用排序函数规格，不得在后置条件加入当前题目的语义约束；题目相关结论放在 `coins_XX.v` 的 bridge 引理中证明。
7. 优先复用题目规格文件已有定义，少造新谓词和大引理。
8. 每次改注解、C 语句或桥接逻辑后，必须重新 symexec 生成 goal 文件。
9. 证明失败先回查信息是否不足，避免盲目堆引理。
10. 数组程序禁止在未说明内存所有权的情况下读取数组元素。
11. 数组程序若涉及写入，必须在 invariant 中区分“已写前缀/未写后缀”。
12. 字符串程序禁止把 Coq `string` 规格直接当作 `CharArray` 内存规格，必须明确二者表示桥接。
13. 字符串输出必须显式证明末尾 `0` 终止符。
14. **验证时必须使用原始规格文件中的 pre 和 spec，这是硬验收标准。**
   - 目标题目的函数规格必须以 `QCP_examples/humaneval/spec/XX.v` 中已有的 `problem_XX_pre` / `problem_XX_spec` 为题意来源。
   - 在 `coins_XX.v` 中可以定义 `problem_XX_pre_z` / `problem_XX_spec_z` 作为 C 层 `list Z`、`Z`、数组内存表示到原始规格的桥接 wrapper，但 wrapper 的定义体必须直接调用原始 `problem_XX_pre` / `problem_XX_spec`。
   - wrapper 必须是“纯原规格桥接”：除必要的格式转换、类型转换、`bool_of_z` / `Z.to_nat` / `string_of_list_z` 等表示转换外，不得额外加入题目语义条件、C 层操作式条件或加强后的结果性质。
   - 允许额外补充的内容只有：
     - `CharArray` / `IntArray` / 指针资源条件；
     - `Z` 与 `nat`、`list Z` 与 Coq `string/ascii`、C 数组与原始 list 表示之间的表示转换关系；
     - C signed int 溢出安全前提、长度非负、分配大小安全等运行安全条件。
     这些条件应写在 C annotation 的 `Require`、循环 invariant 或内部 bridge lemma 前提中，不写进最终 `problem_XX_pre_z` / `problem_XX_spec_z` wrapper。
   - 禁止把题目语义重新写成一个独立的操作式 `_z` 规格后直接用于 C 后置条件。例如禁止只写：
     ```coq
     Definition problem_XX_spec_z (...) : Prop := (* 自己重写算法语义 *)
     ```
     然后让 C 的 `Ensure` 只证明这个新规格。
   - 合格写法必须能在 `coins_XX.v` 中直接看到原始规格调用，例如字符串题应类似：
     ```coq
     Definition problem_XX_pre_z (l : list Z) : Prop :=
       problem_XX_pre (string_of_list_z l).

     Definition problem_XX_spec_z (input output : list Z) : Prop :=
       problem_XX_spec (string_of_list_z input) (string_of_list_z output).
     ```
     如果需要保证 `string_of_list_z` 对底层 `Z` 字符码的单射性，应在 C annotation 中加入 `ascii_range_z(l)`，再在内部引理中由 `problem_XX_pre_z l /\ ascii_range_z l` 推出 C 层需要的范围事实。不要把 `ascii_range_z` 或逐点 C 语义塞进 wrapper。
     数组题也必须类似地通过表示关系调用原始 `problem_XX_pre` / `problem_XX_spec`。
   - 如果原始 `spec/XX.v` 与文件开头题意注释或原 C 可观察行为不一致，必须暂停验证并询问用户；未经用户许可不得修改原 spec，也不得绕过原 spec 自建 `_z` 规格继续标记为“已验证”。
   - 如果因工具限制临时证明了一个 C 层操作式规格，状态只能记为“C 层规格通过，未完成原始 spec 桥接”，不得记为“已全链通过”。

## 端到端流程

### 1) 约束确认与资料读取

- 确认目标文件 `C_XX.c`。
- 默认允许做 QCP 格式转换和验证注解/证明修改；默认不允许改核心逻辑。
- 读取 `QCP_FORMAT_CONVERSION_GUIDE.md`、目标文件、对应 `spec/XX.v`、相邻已验证例子和进度文档。
- 确认用户偏好：是否要求先展示格式转换结果、是否禁止复用旧不变式、是否要求最小新增引理。

### 2) 原始代码审查与核心逻辑标记

- 先读原始 C 程序，明确哪些语句属于题目核心逻辑：
  - 主循环/递归结构
  - 业务分支条件
  - 元素过滤、计数、计算、比较、复制规则
  - 排序前后的题目语义
  - 提前返回和错误分支行为
- 明确哪些语句属于通用库/内存管理：
  - `malloc/calloc/free`
  - `qsort` 或项目统一 `sort_int_array`
  - 纯粹的结构体分配 wrapper
- 如果格式转换会改变核心逻辑或可观察行为，立即暂停询问用户。

### 3) QCP 格式转换

- 替换为 QCP 头文件，按目标目录选择 `verification_stdlib.h`、`verification_list.h`、`int_array_def.h`、字符串相关头文件等。
- 将裸 `malloc/free/qsort` 改为带规格的通用 wrapper；排序 wrapper 必须保持通用。
- 返回 `IntArray` 值的程序可参考已验证例子改为 `IntArray *` 加结构体分配 wrapper，但不得借此改变输出内容、顺序或大小语义。
- 给目标函数补最小前后条件骨架；数组资源必须写清 `full/seg/undef_seg`。
- 新增或更新 `coins_XX.v`，至少包含 `Load "../spec/XX".` 和 C 层需要的 Z/list bridge 定义；最终 `problem_XX_pre_z` / `problem_XX_spec_z` 必须直接调用原始 `problem_XX_pre` / `problem_XX_spec`，不能只重新定义题意。
- 格式转换阶段不要主动堆复杂 loop invariant，也不要生成正式 `goal/proof` 文件，除非用户明确要求直接进入验证。

格式转换后快速自检：

- 核心循环和业务分支是否仍在 C 程序中。
- 是否只把通用库函数做成未实现 wrapper。
- 是否没有把题目语义塞进通用 `sort_int_array`。
- 临时数组若不返回，是否有释放或后置条件中保留资源。
- `coins_XX.v` 中最终用于 C 前后条件的 wrapper 是否能直接看到原始 `problem_XX_pre` / `problem_XX_spec` 调用；只有 `Load "../spec/XX".` 不算使用原 spec。

### 4) 规格与初始注解审查

- 检查 `C_XX.c` 中每个函数是否有明确的 function specification（输入输出说明）。
- 若缺失，先补充规格注解，再进行后续步骤。
  - 数组程序必须显式写出内存谓词（`IntArray::full/seg/undef_*`）。
  - 字符串程序必须显式写出 `CharArray::full` 与末尾 `0` 终止符。

### 5) 基线阅读

- 读取：`C_XX.c`、`coins_XX.v`、`Coins/spec/human/input/XX.v`、现有 `C_XX_goal.v` 和 `C_XX_proof_manual.v`。
- 判断问题类型：
  - 不变式信息不足
  - rem/mod/div 或 nat/Z 桥接不足
  - 规格映射不一致
  - 目标文件过期（stale goal）
  - 数组所有权表达错误（`full`/`seg`/`missing_i`/`undef_*`）
  - 访问元素缺边界/溢出安全条件
  - 字符串的 `string/ascii` 规格与 `list Z` 内存模型不一致
  - 输出字符串缺少 `app(out_l, cons(0, nil))` 终止符
  - `coins_XX.v` 只加载了 `spec/XX.v`，但最终后置条件没有直接调用原始 `problem_XX_spec`

### 6) 重建不变式与桥接

- 在 C 注解里建立最小状态模型，所有 loop invariant 必须以 **`Inv Assert`** 形式给出完整不变式。保证：
  - 安全边界可证
  - 循环状态能映射到规格
  - 关键蕴含关系明确（如 `has==0 -> prod==1`）
- 在 `coins_XX.v` 只补必要桥接引理（局部、可解释、可维护）。
- 可以定义操作式辅助函数来帮助证明循环不变式，但最终暴露给 C 前后条件的 `problem_XX_pre_z` / `problem_XX_spec_z` 必须是原始 `problem_XX_pre` / `problem_XX_spec` 的表示桥接 wrapper；否则不能标记为完整验证。
- 数组程序 invariant 必须同时包含：
  - 语义线：前缀/累计量与 `list` 语义的关系
  - 内存线：数组所有权与已写/未写区间的分割
- 字符串程序 invariant 必须同时包含：
  - 输入字符串保留：`CharArray::full(s, n + 1, app(l, cons(0, nil)))`
  - 输出前缀：`CharArray::full(out, i, out_l)`
  - 未写后缀：`CharArray::undef_seg(out, i, out_n + 1)` 或等价所有权
  - 最终终止符写入后的完整字符串形态
- 如需修改 C 程序语句（非注解）且涉及核心逻辑，必须暂停，与用户讨论修改方案并获得确认后再继续。

### 7) 强制重生成

进入正式验证后，改动 C 注解、C 语句或 bridge 后立即重新 symexec，更新：

- `C_XX_goal.v`
- `C_XX_proof_auto.v`
- `C_XX_proof_manual.v`
- `C_XX_goal_check.v`

禁止在旧 goal 上继续证明。**每次修改注解或 coins 文件后文件行数会变化，必须重新 symexec 到文件尾获取最新完整 witness 列表。**

HumanEval 目录下生成文件命名以当前仓库为准：`IntArrayClaude` 已有样例使用 `C_XX_proof_auto.v` / `C_XX_proof_manual.v`，不要误写成旧的 `C_XX_auto.v` / `C_XX_manual.v`。

`IntArrayClaude` 常用重生成命令形状：

```bash
linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/IntArrayClaude/C_XX_goal.v \
  --proof-auto-file=QCP_examples/humaneval/IntArrayClaude/C_XX_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/IntArrayClaude/C_XX_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/IntArrayClaude SimpleC.EE \
  --input-file=QCP_examples/humaneval/IntArrayClaude/C_XX.c \
  -IQCP_examples/LLM_friendly_cases \
  --gen-and-backup \
  --no-exec-info
```

注意：

- `--coq-logic-path` 对 `IntArrayClaude` 应使用 `SimpleC.EE`，这样生成文件中是 `From SimpleC.EE Require Import C_XX_goal.`，能配合现有 `_CoqProject` 编译。不要写成 `SimpleC.EE.humaneval.IntArrayClaude`，否则会生成无法解析的 import 路径。
- `-IQCP_examples/LLM_friendly_cases` 必须带上，否则 `verification_stdlib.h` / `int_array_def.h` 可能找不到。
- 如果 `--gen-and-backup` 生成了 `C_XX_proof_manual_backup*.v`，补完新 manual 后应清理这些 backup 文件。

### 8) manual 逐项证明

- 通过 symexec symbolic 到文件尾来获得完整的 witness 列表。
- 依次使用 **qcp-mcp 的 `proof`** 打印对应的 witness 到 Rocq，单个 witness 证明结束后再进行下一个。
- 可补充必要的辅助引理和定义，可通过 Coq `Search` tactic 查找可用引理。
- **不能引入 Axioms**，使用 **rocq-mcp 的 `rocq-verify`** 检查是否引入了 Axioms。
- **本步骤只能使用 qcp-mcp / rocq-mcp 工具，不得使用其他工具。**
- 单个 witness 连续卡住时，按顺序回查：
  - goal 是否过期（需重新 symexec）
  - 不变式是否缺信息
  - 是否缺最小桥接引理
  - 数组元素访问是否缺 `0 <= i < n` 或 `INT_MIN/INT_MAX` 边界
  - 字符串是否缺 `n + 1` 长度界、字符集约束或 `0` 终止符证明

### 9) 全链编译验收

先做原始 spec 直连验收：

- 打开 `coins_XX.v`，检查最终用于 C `Require` / `Ensure` 的 `problem_XX_pre_z` / `problem_XX_spec_z`。
- 必须确认它们直接调用 `spec/XX.v` 中的原始 `problem_XX_pre` / `problem_XX_spec`。
- 仅出现 `Load "../spec/XX".` 不合格；仅有同名 `_z` 操作式定义也不合格。
- 若存在操作式中间规格，必须同时有无 `Admitted` 的桥接定理，并在最终 wrapper 或最终证明路径中连接到原始 spec。

依次编译：

1. `coins_XX.v`
2. `C_XX_goal.v`
3. `C_XX_proof_auto.v`
4. `C_XX_proof_manual.v`
5. `C_XX_goal_check.v`

可接受 load-path remap warning，但必须整体编译通过。

### 10) 清理编译产物

- 在确认第 9 步全部编译通过后，删除本题编译产生的中间文件，例如：
  - 隐藏的 Coq `.aux` 文件，例如 `.C_XX_goal.aux`、`.C_XX_proof_auto.aux`、`.C_XX_proof_manual.aux`、`.C_XX_goal_check.aux`、`.coins_XX.aux`
  - `.glob`
  - `.vo`
  - `.vok`
  - `.vos`
  - `C_XX_proof_manual_backup*.v`
- 只清理本题相关的编译产物，不删除源码和证明源文件。
- 必须保留：
  - `C_XX.c`
  - `coins_XX.v`
  - `C_XX_goal.v`
  - `C_XX_proof_auto.v`
  - `C_XX_proof_manual.v`
  - `C_XX_goal_check.v`

### 11) 记录与交付

- 检查无 `Admitted.`/`Axiom`：
  - `grep -nE "Admitted\\.|Axiom[[:space:]]" coins_XX.v C_XX_proof_manual.v || true`
  - 同时用 **rocq-mcp 的 `rocq-verify`** 二次确认无 Axiom 引入。
- 将本题遇到的问题、解决办法、是否有格式转换中的行为适配，更新到对应 progress 文档。
- progress 中必须明确写清：
  - “已直接桥接原始 `spec/XX.v` pre/spec”；或
  - “仅 C 层规格通过，尚未完成原始 spec 桥接”。
  不能把后者写成“已全链通过”。
- 汇报：改了什么、为什么、编译结果、扫描结果、剩余风险。

## 标准命令模板

在目标目录执行（`IntClaude`、`IntArrayClaude` 或 `StringClaude`）。`IntClaude` 有本目录 `_CoqProject` 时可直接使用：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
COQINCLUDES="$(tr '\n' ' ' < _CoqProject)"
coqc $COQINCLUDES coins_XX.v
coqc $COQINCLUDES C_XX_goal.v
coqc $COQINCLUDES C_XX_proof_auto.v
coqc $COQINCLUDES C_XX_proof_manual.v
coqc $COQINCLUDES C_XX_goal_check.v
```

`IntArrayClaude` 目录本身没有 `_CoqProject`，必须复用 `../IntClaude/_CoqProject`：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/IntArrayClaude
COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_XX.v
coqc $COQINCLUDES C_XX_goal.v
coqc $COQINCLUDES C_XX_proof_auto.v
coqc $COQINCLUDES C_XX_proof_manual.v
coqc $COQINCLUDES C_XX_goal_check.v
```

不要在仓库根目录直接执行 `coqc QCP_examples/humaneval/IntArrayClaude/coins_XX.v`：`coins_XX.v` 常用 `Load "../spec/XX".`，相对路径会按当前工作目录解析，容易找不到 spec。也不要在 `IntArrayClaude` 目录直接裸跑 `coqc coins_XX.v`，否则会缺 `AUXLib` / `SimpleC.SL` 等 load-path。

## 完成判定

同时满足以下三条才算完成：

1. `C_XX_goal_check.v` 编译通过。
2. 手写证明文件无 `Admitted.`。
3. 手写证明文件无 `Axiom`。

## 数组程序补充要点（IntArrayClaude）

### A. 必用谓词与常见组合

- 只读输入数组：
  - `IntArray::full(a, n, l)`
- 输出数组（未初始化）：
  - `IntArray::undef_full(out, n)`
- 写入后输出数组：
  - `IntArray::full(out, n, out_l)`
- 中间/切片数组：
  - `IntArray::seg(a, lo, hi, l)`
- 读写单元的桥接：
  - `IntArray::missing_i(a, i, lo, hi, l)`

### B. invariant 的两条线必须同时写

1. 语义线：前缀与列表语义关系，例如
   - `acc == sum(sublist(0, i, l))`
2. 内存线：已写/未写区间或切片的所有权分割，例如
   - `IntArray::seg(out, 0, i, done) * IntArray::undef_seg(out, i, n)`

### C. 访问元素前必须保证边界与溢出

- 元素读取需要：
  - `0 <= i && i < n`
- 元素值必须是合法 `int`：
  - `INT_MIN <= Znth(i, l, 0) <= INT_MAX`
- 如果有累加或多项求和：
  - 需要前缀和/组合和的 `INT_MIN/INT_MAX` 约束

### D. 常用桥接引理位置

- `SeparationLogic/SeparationLogic/ArrayLib.v`
  - `full_split_to_missing_i`
  - `missing_i_merge_to_full`
  - `seg_split_to_missing_i`
  - `seg_merge_to_seg`
  - `full_shape_split_to_missing_i_shape`
  - `missing_i_shape_merge_to_full_shape`
- 自动化规则：
  - `QCP_examples/int_array.strategies`
  - `QCP_examples/array_shape.strategies`

### E. 只读 vs 写数组的判别

- 只读：后置条件必须保留 `IntArray::full(...)`
- 写入：必须显式描述“前缀已写、后缀未写”或“全数组新列表”

### F. 近期验证经验

- 排序：
  - 涉及 `qsort` 的题目统一倾向使用通用 `sort_int_array` wrapper。
  - wrapper 后置只写 `sorted_int_list_by(ascending, sorted_l)`、`Permutation(l, sorted_l)`、长度和数组资源。
  - 不把“top-k”“unique”“公共元素”“题目最终 spec”写进排序函数后置。
- helper：
  - 可以把局部独立逻辑抽成已实现 helper，例如数字逐位检查、数组尾追加。
  - helper 必须有 C 函数体并单独通过验证；不能只声明一个规格把原程序核心逻辑吞掉。
  - 如果 helper 只是机械内存操作，应避免名字和规格暗示题目语义。
- 数组追加：
  - 写 `data[output_size] = value; output_size++` 时，常用资源形态是 `seg(data,0,output_size,l) * undef_seg(data,output_size,cap)`。
  - 单次写入证明通常用 `IntArray.seg_single` 与 `IntArray.seg_merge_to_seg`。
  - 注解里追加单元素列表优先写 `app(l, cons(value, nil))`，不要混用解析不稳定的 Coq notation。
- 局部变量资源：
  - 循环退出后，局部变量如 `i`、`n`、`j` 的 `data_at(&i, ...)` 仍可能在空间资源里。
  - sort 前后或 return 前的 `Assert` 如果不保留这些资源，manual VC 可能变成“丢弃局部变量资源”而不可证。
- C 算术：
  - C 的 `/`、`%` 在 VC 中常对应 `Z.quot`、`Z.rem`；数学规格常用 `Z.div`、`Z.mod`。
  - 对非负/正数状态，优先在 `coins_XX.v` 中用 `Z.quot_div_nonneg`、`Z.rem_mod_nonneg` 做局部 bridge。
  - 有加法、乘法、`3*n+1`、前缀和、乘积时，前置条件或 invariant 要明确 int 范围安全。
- 动态扩容：
  - `realloc` 属于通用库函数，但它涉及旧块所有权迁移、失败分支和容量变化，当前验证中通常不宜随手改成固定容量。
  - 如果必须把动态扩容适配为固定容量、强前置条件或其他内存策略，这属于可能影响可观察行为的容量策略变化，必须先暂停询问用户。
- 操作式 Z 层辅助定义：
  - 当 `../spec/XX.v` 的 nat/list/string 规格不方便直接用于循环 invariant，可以在 `coins_XX.v` 中建立 Z 层操作式辅助函数或中间谓词。
  - 这些辅助定义只能服务于证明过程，不能替代最终题意规格。
  - 最终 `problem_XX_pre_z` / `problem_XX_spec_z` 必须直接桥接到原始 `problem_XX_pre` / `problem_XX_spec`；未桥接时写清剩余风险，并且不得标记为“已全链通过”。

### G. 参考文档

- 数组验证总览：
  - `QCP_examples/humaneval/IntArrayClaude/INTARRAY_VERIFICATION_GUIDE.md`
  - `QCP_examples/humaneval/IntArrayClaude/INTARRAY_SPEC_WRITING_GUIDE.md`

## 字符串程序补充要点（StringClaude）

### A. 核心表示

- QCP 中 C 字符串不是直接用 Coq `string` 表示，而是用字符码列表：
  - `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- 其中：
  - `l : list Z` 是不含终止符的字符串内容
  - `0` 是 C 字符串末尾的 `'\0'`
  - `n` 是逻辑长度，内存长度是 `n + 1`

### B. 常用外部函数规格

- `strlen` 推荐规格：
  - `Require CharArray::full(s, n + 1, app(l, cons(0, nil)))`
  - `Ensure __return == n && CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- 调用 `strlen` 时通常需要 `where`：
  - `strlen(s) /*@ where l = str_l, n = n */`
- 输出字符串分配推荐用指定 helper：
  - `char *malloc_char_array(int n)`
  - `Ensure exists l, __return != 0 && CharArray::full(__return, n, l)`

### C. 字符编码

- `CharArray` 内容是 `list Z`，常见字符码：
  - `0`: `'\0'`
  - `32`: 空格
  - `40`: `'('`
  - `41`: `')'`
  - `48`: `'0'`
  - `49`: `'1'`
- 若 `spec/*.v` 使用 Coq `string/ascii`，必须在 `coins_XX.v` 中建立从 `list Z` 到原始 `string/ascii` 的表示桥接。
- 禁止只定义“等价的 `list Z` 版本规格”后直接作为最终规格；最终 wrapper 必须调用原始 `problem_XX_pre` / `problem_XX_spec`。
- `problem_XX_pre_z` / `problem_XX_spec_z` 必须保持纯原规格 wrapper。`ascii_range_z`、底层小写范围、二进制字符码 `48/49`、C 层逐点变换、membership、palindrome 等操作式条件只能写在 C annotation 或内部 bridge lemma 前提中。

### D. 字符串 invariant 模板

- 只读输入字符串：
  - 保留 `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- 构造输出字符串：
  - `CharArray::full(out, i, out_l) * CharArray::undef_seg(out, i, out_n + 1)`
- 最终写入终止符后：
  - `CharArray::full(out, out_n + 1, app(out_l, cons(0, nil)))`

### E. 字符串安全条件

- 必须检查：
  - `0 <= n`
  - `n < INT_MAX`
  - `n + 1 <= INT_MAX`
  - 输出长度表达式不溢出，如 `2 * n + 1`、`n + add + 1`
  - 循环访问满足 `0 <= i && i < n`
- 针对题目字符集补前提：
  - 如果原 pre 已经在 Coq `string` 层限制字符集，C annotation 通常只补 `ascii_range_z(l)`，再由原 pre 加 `ascii_range_z` 推出底层 `Z` 字符码范围。
  - 如果原 pre 没有提供足够字符集信息，暂停询问用户是否修改原 pre；不要私自在 wrapper 中加题目语义条件。
  - 二进制字符串的底层 `48/49`、小写字母的底层 `97..122` 等事实应作为内部引理结论使用，不作为最终 wrapper 的额外 conjunct。

### F. 参考依据

- 主要参考 QCP 原生例子和库：
  - `QCP_examples/chars.c`
  - `QCP_examples/kmp_rel.c`
  - `QCP_examples/char_array_def.h`
  - `QCP_examples/char_array.strategies`
  - `SeparationLogic/examples/char_array_strategy_proof.v`
- StringClaude 专用指南：
  - `QCP_examples/humaneval/StringClaude/STRING_VERIFICATION_GUIDE.md`
- 注意：`QCP_examples/humaneval/String/C_11.c` 只是历史尝试，不作为主要依据。
