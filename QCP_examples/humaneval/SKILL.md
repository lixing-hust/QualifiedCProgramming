---
name: humaneval-c-verification-zh-compact
description: "中文精简流程：用于 humaneval/IntClaude、IntArrayClaude 与 StringClaude 下 C_XX 验证，覆盖不变式重建、symexec 重生成、manual 证明补全、无 Admitted 或 Axiom、goal_check 编译通过，并补充数组与字符串内存验证要点。"
---

# HumanEval C 验证技能（中文精简版）

适用场景：验证 `QCP_examples/humaneval/IntClaude`、`QCP_examples/humaneval/IntArrayClaude` 与 `QCP_examples/humaneval/StringClaude` 下的 `C_XX.c` 任务，完成从注解到 Coq 证明的全流程闭环。

## 目标

- 通过符号执行与 Coq 编译链。
- `C_XX_proof_manual.v`（以及手写桥接文件）中无 `Admitted.`、无 `Axiom`。
- `C_XX_goal_check.v` 编译成功。
- 对数组程序，内存所有权与数组内容约束保持一致，无未初始化读取。
- 对字符串程序，明确 `CharArray` 内容、终止符、输出缓冲区和字符编码约束。

## 强约束

1. 未经用户确认，不修改 C 程序语句，只改注解和证明文件。
2. 优先复用题目规格文件已有定义，少造新谓词和大引理。
3. 每次改注解或桥接逻辑后，必须重新 symexec 生成 goal 文件。
4. 证明失败先回查信息是否不足，避免盲目堆引理。
5. 数组程序禁止在未说明内存所有权的情况下读取数组元素。
6. 数组程序若涉及写入，必须在 invariant 中区分“已写前缀/未写后缀”。
7. 字符串程序禁止把 Coq `string` 规格直接当作 `CharArray` 内存规格，必须明确二者表示桥接。
8. 字符串输出必须显式证明末尾 `0` 终止符。

## 八步流程

### 1) 约束确认

- 确认目标文件 `C_XX.c`。
- 确认允许改动范围：仅注解 / 注解+coins / 允许改 C 语句。
- 确认用户偏好：是否禁止复用旧不变式，是否要求最小新增引理。

### 2) 代码审查

- 检查 `C_XX.c` 中每个函数是否有明确的 function specification（输入输出说明）。
- 若缺失，先补充规格注解，再进行后续步骤。
  - 数组程序必须显式写出内存谓词（`IntArray::full/seg/undef_*`）。
  - 字符串程序必须显式写出 `CharArray::full` 与末尾 `0` 终止符。

### 3) 基线阅读

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

### 4) 重建不变式与桥接

- 在 C 注解里建立最小状态模型，所有 loop invariant 必须以 **`Inv Assert`** 形式给出完整不变式。保证：
  - 安全边界可证
  - 循环状态能映射到规格
  - 关键蕴含关系明确（如 `has==0 -> prod==1`）
- 在 `coins_XX.v` 只补必要桥接引理（局部、可解释、可维护）。
- 数组程序 invariant 必须同时包含：
  - 语义线：前缀/累计量与 `list` 语义的关系
  - 内存线：数组所有权与已写/未写区间的分割
- 字符串程序 invariant 必须同时包含：
  - 输入字符串保留：`CharArray::full(s, n + 1, app(l, cons(0, nil)))`
  - 输出前缀：`CharArray::full(out, i, out_l)`
  - 未写后缀：`CharArray::undef_seg(out, i, out_n + 1)` 或等价所有权
  - 最终终止符写入后的完整字符串形态
- 如需修改 C 程序语句（非注解），必须暂停，与用户讨论修改方案并获得确认后再继续。

### 5) 强制重生成

改动后立即重新 symexec，更新：

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

### 6) manual 逐项证明

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

### 7) 全链编译验收

依次编译：

1. `coins_XX.v`
2. `C_XX_goal.v`
3. `C_XX_proof_auto.v`
4. `C_XX_proof_manual.v`
5. `C_XX_goal_check.v`

可接受 load-path remap warning，但必须整体编译通过。

### 8) 清理编译产物

- 在确认第 7 步全部编译通过后，删除本题编译产生的中间文件，例如：
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

### 9) 收尾与交付

- 检查无 `Admitted.`/`Axiom`：
  - `grep -nE "Admitted\\.|Axiom[[:space:]]" coins_XX.v C_XX_proof_manual.v || true`
  - 同时用 **rocq-mcp 的 `rocq-verify`** 二次确认无 Axiom 引入。
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

### F. 参考文档

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
- 若 `spec/*.v` 使用 Coq `string/ascii`，必须在 `coins_XX.v` 中建立桥接，或先定义等价的 `list Z` 版本规格。

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
  - 二进制字符串：每个字符是 `48` 或 `49`
  - 括号字符串：每个字符是 `40`、`41` 或 `32`

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
