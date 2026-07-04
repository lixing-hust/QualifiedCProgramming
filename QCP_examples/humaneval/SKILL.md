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
- 在 `QCP_examples/humaneval/ledger.md` 中记录每个题目的验证 token 与耗时。

## Token 与耗时记录

- 每个 `C_XX` case 必须在开始正式 intake 时记录一次成本起点，在完成、暂停、blocked、skipped 或切换到另一个 case 前记录一次成本终点。
- 成本记录统一写入 `QCP_examples/humaneval/ledger.md`；progress 文档只记录验证状态和技术经验，不替代 ledger。
- 起点记录应包含：`case`、suite（`IntClaude` / `IntArrayClaude` / `StringClaude`）、`status=in_progress`、`start_time`、当前 Codex `session_id`、`rollout_path`、`token_start`。
- 终点记录应补齐：`end_time`、`elapsed_minutes`、`token_end`、`token_delta`、可取得时的 input/cached input/output/reasoning token delta、最终 `status`、简短 notes。
- 采用 ledger v2 行时，`elapsed_minutes` 记录实际工作时间，不把暂停、等待用户、跨天空档或穿插其他 case 的墙钟时间计入；`start_time` / `end_time` 仍保留本 case 的外层起止时间。
- 若本题使用 `--gen-and-backup` 生成了 `C_XX_proof_manual_backup*.v`，终点记录必须尽量补齐结构化 symexec 计数，不能在 backup 仍可见时写 `unknown`：
  - `total_symexec_runs`：取最高 backup 编号；例如最高是 `C_XX_proof_manual_backup12.v`，则填 `12`。
  - `first_vc_symexec_runs`：清理 backup 前用 `wc -l C_XX_proof_manual_backup*.v` 或等价命令找第一份非空 manual backup 的编号；若 `backup1` 到 `backup10` 为 0 行、`backup11` 非空，则填 `11`。
  - `vc_annotation_regens_after_first_vc`：默认用 `total_symexec_runs - first_vc_symexec_runs`，表示第一次非空 VC 之后因 annotation、loop invariant、函数规格、frame 条件或 coins/spec bridge 调整导致的重新 symexec 次数；若 rollout 日志有更精确的分类证据，按精确证据填写。
  - 若 backup 已被清理但需要回填，应先查 `rollout_path` 中的 `ls` / `wc -l` / `git status` / `symexec` 输出；只有确实找不到证据时才写 `unknown`，并在 progress 或最终汇报中说明原因。
- token 优先从当前 Codex thread 的 `event_msg` / `token_count` 或 `/status` 暴露的 context usage 中读取；本地回查使用 `~/.codex/history.jsonl` 定位 session id，再读取 `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl`。
- 如果一次 thread 中连续验证多个 case，必须在每次 case 切换前关闭上一题 ledger 记录，再为下一题开新记录；不能只记录整轮总 token。
- 如果旧对话没有 case 边界，只能回填估算值，`confidence` 必须写 `estimated`，并在 notes 说明按用户指令时间、文件修改时间、progress 更新时间或 token_count 时间点拆分。
- 如果 token 字段暂时取不到，先记录时间、session id、rollout path 和 `token_start/token_end=unknown`，等 session 日志可读后再回填；不得编造 token 数。

## 强约束

1. 先把原始 C 程序改成 QCP 支持格式，再开始正式验证；格式转换参考 `QCP_examples/humaneval/QCP_FORMAT_CONVERSION_GUIDE.md`。
2. 格式转换只能做接口与验证环境适配：替换 QCP 头文件、结构体指针返回适配、增加 `malloc/free/sort/qsort` 等通用库函数 wrapper 规格、添加目标函数前后条件骨架和 `coins_XX.v` 桥接定义。
3. 未经用户确认，不修改原 C 程序的核心业务逻辑。若为了验证需要改变循环结构、分支行为、容量策略、提前返回语义、过滤/排序/计算规则，必须暂停并告诉用户原因、原逻辑、拟改逻辑和影响。
4. 不允许把原程序核心逻辑替换成未实现函数规格。只有 `malloc/free/qsort/sort` 这类通用库函数可以用未定义 wrapper 规格表示。
5. 原程序已有 helper 可以保留并补规格；如需新抽 helper，helper 必须有 C 实现并单独验证，且只能拆分局部机械操作或独立子逻辑，不能隐藏题目主逻辑。
6. `sort_int_array` 必须保持通用排序函数规格，不得在后置条件加入当前题目的语义约束；题目相关结论放在 `coins_XX.v` 的 bridge 引理中证明。
7. 优先复用题目规格文件已有定义，少造新谓词和大引理。
8. 每次改注解、C 语句或桥接逻辑后，必须重新 symexec 生成 goal 文件。
9. **严禁手动修改 `C_XX_goal.v`、`C_XX_proof_auto.v`、`C_XX_goal_check.v`。**
   - 这三个文件必须始终保持 `symexec` 原样生成状态，只能通过重新运行 `symexec` 更新。
   - 可以阅读它们来定位 VC，但不能手工补 scope、改 import、改定义、改 proof、删改生成内容。
   - 如果这三个生成文件编译失败，必须回到源头修正 `C_XX.c` annotation、`coins_XX.v`、原始 `spec/XX.v`（需用户许可时先询问）或 symexec 调用参数，然后重新生成；不得直接 patch 生成文件。
   - 只有 `C_XX_proof_manual.v` 是允许手写/回填证明的生成配套文件。
10. 证明失败先回查信息是否不足，避免盲目堆引理。
11. 数组程序禁止在未说明内存所有权的情况下读取数组元素。
12. 数组程序若涉及写入，必须在 invariant 中区分“已写前缀/未写后缀”。
13. 字符串程序禁止把 Coq `string` 规格直接当作 `CharArray` 内存规格，必须明确二者表示桥接。
14. 字符串输出必须显式证明末尾 `0` 终止符。
15. **验证时必须使用原始规格文件中的 pre 和 spec，这是硬验收标准。**
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
- 在 `ledger.md` 为本题创建或更新 `in_progress` 起点记录，记录 `start_time`、session id、rollout path 和当前 token 起点。
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

其中 `C_XX_goal.v`、`C_XX_proof_auto.v`、`C_XX_goal_check.v` 只能由 `symexec` 生成，严禁手工编辑；如果它们有 import、scope、VC 形状或编译问题，必须修源文件/规格/桥接/命令参数后重新生成。`C_XX_proof_manual.v` 可以回填手写证明。

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

`multi_dimensional_arrays` 或其它会使用共享 `QCP_examples/QCP_demos_LLM/*.strategies`、`QCP_examples/stdlib/string.strategies` 的 case，必须同时给出 strategy 源目录到 Coq 逻辑路径的 `-slp` 映射，避免 `symexec` 在 `C_XX_goal.v` 中生成短名 `Require Import ptr_array2_strategy_goal` / `Require Import string_strategy_goal`。统一使用：

```bash
opam exec --switch=coq8201 -- linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/multi_dimensional_arrays/C_XX_goal.v \
  --proof-auto-file=QCP_examples/humaneval/multi_dimensional_arrays/C_XX_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/multi_dimensional_arrays/C_XX_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/multi_dimensional_arrays SimpleC.EE \
  -slp QCP_examples/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM \
  -slp QCP_examples/stdlib SimpleC.StdLib \
  --strategy-folder-path=SeparationLogic/examples/QCP_demos_LLM/ \
  --input-file=QCP_examples/humaneval/multi_dimensional_arrays/C_XX.c \
  -IQCP_examples/LLM_friendly_cases \
  -IQCP_examples/QCP_demos_LLM \
  -IQCP_examples/stdlib \
  --gen-and-backup \
  --no-exec-info
```

这会让生成的 shared strategy import 使用 canonical 路径，例如：

```coq
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_goal.
```

不要为了修复短名 import 在 case 目录新增 `*_strategy_goal.v` / `*_strategy_proof.v` shim；应修正 `symexec` 调用参数并重新生成 `C_XX_goal.v` / `C_XX_proof_auto.v` / `C_XX_proof_manual.v` / `C_XX_goal_check.v`。

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
- 超大 `C_XX_proof_manual.v` 的临时加速策略：
  - 如果前面若干 witness 已经在本轮确认通过，而当前只需要修改后面的 VC，可以在**调试阶段**把已确认通过的前置 witness 临时改成 `Admitted.`，用来减少反复编译时间。
  - 这个做法只允许用于临时调试或 scratch 版本；最终交付前必须恢复所有真实证明。
  - 优先在 `.tmp` 下复制一个临时 manual 文件调试，避免把临时 `Admitted.` 混进正式文件。若直接改正式 `C_XX_proof_manual.v`，必须在最终收尾前逐个恢复。
  - 仅对已经完整通过、且后续证明不依赖其证明体的前置 witness 使用。若前置部分包含后续会用到的 helper lemma / definition，不能直接用 `Admitted.` 代替。
  - 恢复后必须重新完整编译 `C_XX_proof_manual.v` 和 `C_XX_goal_check.v`，并执行 `Admitted.` / `Axiom` 扫描。不能带着临时 `Admitted.` 报告完成。

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

如果第 8 步曾用临时 `Admitted.` 加速调试，进入本步骤前必须先恢复完整证明；第 9 步的编译结果必须来自无临时 `Admitted.` 的正式 `C_XX_proof_manual.v`。

### 10) 清理编译产物

- 在确认第 9 步全部编译通过后，删除本题编译产生的中间文件，例如：
  - 隐藏的 Coq `.aux` 文件，例如 `.C_XX_goal.aux`、`.C_XX_proof_auto.aux`、`.C_XX_proof_manual.aux`、`.C_XX_goal_check.aux`、`.coins_XX.aux`
  - `.glob`
  - `.vo`
  - `.vok`
  - `.vos`
  - `C_XX_proof_manual_backup*.v`
- 删除 `C_XX_proof_manual_backup*.v` 前，必须先完成 ledger 的 backup-derived 计数记录：
  - 运行并保留可回查证据：`wc -l C_XX_proof_manual_backup*.v C_XX_goal.v C_XX_proof_manual.v coins_XX.v`，或至少记录每个 backup 是否为空、第一份非空 backup 编号和最高 backup 编号。
  - 将 `first_vc_symexec_runs`、`vc_annotation_regens_after_first_vc`、`total_symexec_runs` 写入 `ledger.md` 后，再清理 backup。
  - 如果后续又重新 symexec 生成了新的 backup，必须重新计算这些字段，不能沿用旧计数。
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
- 更新 `ledger.md` 中本题的成本记录：补齐结束时间、耗时、token 终点、token delta、最终状态和简短 notes。即使本题 blocked、skipped 或只 partial，也必须记录本轮已消耗的 token 与时间。
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

`multi_dimensional_arrays` 同样复用 `../IntClaude/_CoqProject`，并依赖 `SeparationLogic/examples/QCP_demos_LLM` 与 `SeparationLogic/stdlib` 下的 canonical strategy `.vo`。如果相关 strategy 尚未编译，先在仓库根执行：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
COQINCLUDES_ROOT="$(tr '\n' ' ' < _CoqProject)"
coqc $COQINCLUDES_ROOT SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_goal.v
coqc $COQINCLUDES_ROOT SeparationLogic/examples/QCP_demos_LLM/ptr_array2_strategy_proof.v
coqc $COQINCLUDES_ROOT SeparationLogic/examples/QCP_demos_LLM/char_array_strategy_goal.v
coqc $COQINCLUDES_ROOT SeparationLogic/examples/QCP_demos_LLM/char_array_strategy_proof.v
coqc $COQINCLUDES_ROOT SeparationLogic/stdlib/string_strategy_goal.v
coqc $COQINCLUDES_ROOT SeparationLogic/stdlib/string_strategy_proof.v
```

然后在 case 目录编译：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/multi_dimensional_arrays
COQINCLUDES="-R ../../../SeparationLogic/stdlib SimpleC.StdLib $(tr '\n' ' ' < ../IntClaude/_CoqProject)"
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

### B.1 字符串常量与字符串常量数组

- 字符串常量需要使用 QCP 的全局字符串资源：
  - C 文件中声明 `LitMap`、`GlobalStrings`、`GlobalStrings_missing`、`store_stringLit`。
  - 函数前后条件通常保留 `GlobalStrings(LitMap)`。
  - 读字符串常量内容前，需要把 `GlobalStrings(LitMap)` split 成 `GlobalStrings_missing(...) * store_stringLit(ptr, "...")`，读完或返回前再 merge 回 `GlobalStrings(LitMap)`。
- 当前不推荐直接写局部字符串常量数组 initializer：
  ```c
  char *words[2] = {"aa", "bb"};
  ```
  这种写法容易让 QCP 只得到 `PtrArray::undef_full(words, 2)`，没有生成每个元素的写入资源，后续读 `words[i]` 或证明 `PtrArray::full` 会失败。
- 推荐改成显式指针变量加逐项写入，保持 C 可观察语义不变：
  ```c
  char *words[2];
  char *aa = "aa";
  char *bb = "bb";

  /*@ Assert
      aa == LitMap("aa") &&
      bb == LitMap("bb") &&
      PtrArray::undef_full(words, 2) *
      GlobalStrings(LitMap)
  */
  words[0] = aa;
  /*@ Assert
      aa == LitMap("aa") &&
      bb == LitMap("bb") &&
      PtrArray::seg(words, 0, 1, cons(aa, nil)) *
      PtrArray::undef_seg(words, 1, 2) *
      GlobalStrings(LitMap)
  */
  words[1] = bb;
  /*@ Assert
      aa == LitMap("aa") &&
      bb == LitMap("bb") &&
      PtrArray::full(words, 2, cons(aa, cons(bb, nil))) *
      GlobalStrings(LitMap)
  */
  ```
- 如果后续读取某个字符串常量，例如 `char *p = words[0]; int x = p[0];`，读取前的资源形态应包含：
  ```c
  /*@ Assert
      p == aa &&
      aa == LitMap("aa") &&
      PtrArray::full(words, 2, cons(aa, cons(bb, nil))) *
      GlobalStrings_missing(LitMap, cons("aa", nil)) *
      store_stringLit(p, "aa")
  */
  ```
- 证明时常用引理：
  - `GlobalStrings_split` / `GlobalStrings_missing_split`
  - `GlobalStrings_merge` / `GlobalStrings_missing_merge`
  - `PtrArray.undef_full_split_to_undef_missing_i`
  - `PtrArray.undef_seg_split_to_undef_missing_i`
  - `PtrArray.undef_missing_i_to_undef_seg_head`
  - `PtrArray.seg_single`
  - `PtrArray.full_split_to_missing_i`

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
