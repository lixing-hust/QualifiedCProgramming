# HumanEval 原始 spec 问题日志

用途：记录验证过程中发现的 `QCP_examples/humaneval/spec/*.v` 与文件开头题意注释或原 C 可观察行为不一致的问题。除非用户明确许可，否则这里只记录并跳过，不直接修改原 spec。

## StringClaude

### 问题编号：SPEC-C_50-001

- 问题类型：字符取模语义不一致
- 涉及文件：`spec/50.v`、`StringClaude/C_50.c`
- 发现时间：2026-05-20
- 现象：`decode_shift` 的 C 实现对每个字符计算 `((int)s[i] + 21 - 'a') % 26 + 'a'`。在 C 中，负数 `%` 的结果保留被除数符号；而原 spec 使用 `nat` 减法和 `mod`，并且官方 Python 语义也会使用非负模。
- 例子：输入空格字符时，C 的中间值是 `32 + 21 - 97 = -44`，C 风格 `-44 % 26 = -18`，输出 ASCII `79`。原 spec 的 `nat` 语义会得到不同字符。
- 当前处理：已按用户确认的口径修改 `spec/50.v`，将 `problem_50_pre` 从 `True` 收紧为输入字符串所有字符均为小写字母 `a..z`。
- 验证：已完成 `StringClaude/C_50.c` 的全链验证；其中 `decode_shift` 已直接桥接原始 `problem_50_pre/spec`。`encode_shift` 没有对应的原始 `problem_50_spec`，不作为本题原 spec 验证目标。
- 结果：`coins_50.v` 和 `C_50_proof_manual.v` 中无 `Admitted.` / `Axiom`。

### 问题编号：SPEC-C_89-001

- 问题类型：非小写字符语义不一致
- 涉及文件：`spec/89.v`、`StringClaude/C_89.c`
- 发现时间：2026-05-20
- 现象：原 spec 的 `char_relation` 明确要求非小写字母保持不变；C 实现对所有字符执行 `((int)s[i] + 4 - 'a') % 26 + 'a'`，因此非小写字符不会保持不变。
- 例子：输入空格字符时，C 风格计算输出 ASCII `88`，而原 spec 要求输出仍为空格。
- 当前处理：已按用户确认的口径修改 `spec/89.v`，将 `problem_89_pre` 从 `True` 收紧为输入字符串所有字符均为小写字母 `a..z`。
- 验证：已完成 `StringClaude/C_89.c` 的全链验证；`coqtop -l QCP_examples/humaneval/spec/89.v`、`coqc coins_89.v`、`coqc C_89_goal.v`、`coqc C_89_proof_auto.v`、`coqc C_89_proof_manual.v`、`coqc C_89_goal_check.v` 均通过。
- 结果：`coins_89.v` 和 `C_89_proof_manual.v` 中无 `Admitted.` / `Axiom`。

### 问题编号：SPEC-C_67-001

- 问题类型：原 pre 过宽导致原 spec 对任意输入不可满足
- 涉及文件：`spec/67.v`、`StringClaude/C_67.c`
- 发现时间：2026-05-21
- 现象：`spec/67.v` 中 `problem_67_pre` 为 `True`，但 `problem_67_spec` 要求输入字符串能分解为 `"<apples> apples and <oranges> oranges"`。当前 C 实现对任意字符串扫描前两个连续数字段并返回 `total - num1 - num2`，对不符合固定格式的输入也有返回值。
- 例子：输入 `"abc 5 xyz 6"` 时 C 会扫描出两个数字段并返回 `total - 5 - 6`；原 spec 的 `parse_fruit_string` 不成立，因此不存在满足 `problem_67_spec` 的结果。
- 当前处理：已按用户确认收紧 `problem_67_pre`，只要求输入满足数字 fruit string 格式；`problem_67_spec` 保持原定义。C 风格扫描结果到原 `problem_67_spec` 的关系在 `StringClaude/coins_67.v` 中用 bridge lemma 证明，不写进原 pre。
- 验证：已完成 `StringClaude/C_67.c` 的全链验证；`coqtop -quiet -l QCP_examples/humaneval/spec/67.v`、`coqc coins_67.v`、`coqc C_67_goal.v`、`coqc C_67_proof_auto.v`、`coqc C_67_proof_manual.v`、`coqc C_67_goal_check.v` 均通过。
- 结果：`coins_67.v` 和 `C_67_proof_manual.v` 中无 `Admitted.` / `Axiom`。

### 问题编号：SPEC-C_140-001

- 问题类型：连续空格规则不一致
- 涉及文件：`spec/140.v`、`StringClaude/C_140.c`
- 发现时间：2026-05-20
- 现象：文件注释写明“more than 2 consecutive spaces” 才替换为 `-`；C 实现也把恰好两个空格输出为两个下划线。`spec/140.v` 的 `fix_spaces_func` 在看到两个连续空格时直接输出 `dash`，把恰好两个空格也归到 `-` 分支。
- 例子：输入 `"a  b"` 时，C 输出 `"a__b"`；当前 spec 输出 `"a-b"`。
- 当前处理：已按用户确认修正 `spec/140.v`，使用 pending 空格段长度建模：1 个空格输出 `_`，2 个空格输出 `__`，3 个及以上连续空格输出 `-`。
- 验证：修正后已完成 `StringClaude/C_140.c` 的原 spec 直连全链验证；`coqtop -quiet -l QCP_examples/humaneval/spec/140.v`、`coqc coins_140.v`、`coqc C_140_goal.v`、`coqc C_140_proof_auto.v`、`coqc C_140_proof_manual.v`、`coqc C_140_goal_check.v` 均通过。
- 结果：`coins_140.v` 和 `C_140_proof_manual.v` 中无 `Admitted.` / `Axiom`。
