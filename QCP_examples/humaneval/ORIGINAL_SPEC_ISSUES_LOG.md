# HumanEval 原始 spec 问题日志

用途：记录验证过程中发现的 `QCP_examples/humaneval/spec/*.v` 与文件开头题意注释或原 C 可观察行为不一致的问题。除非用户明确许可，否则这里只记录并跳过，不直接修改原 spec。

## StringClaude

### 问题编号：SPEC-C_19-001

- 问题类型：原 pre 过宽导致无效 token 输入不可满足原 spec
- 涉及文件：`spec/19.v`、`StringClaude/C_19.c`
- 发现时间：2026-05-27
- 现象：`spec/19.v` 中 `problem_19_pre` 原为 `True`，但 `problem_19_spec` 要求 `SplitOnSpaces input` 中所有单词都是 `"zero"` 到 `"nine"` 的有效数字词。原 C 对无效 token 会在 `strcmp` 匹配失败后忽略该 token，因此无效输入满足原 pre，却无法同时满足输出是输入 token permutation 的 spec。
- 例子：输入 `"one bad two"` 时，原 C 只统计并输出有效 token `"one two"`；原 spec 若把 `"bad"` 保留在输入 token 列表中，则输出 token 不可能既是输入 token 的 permutation 又全部按数字词排序。
- 当前处理：已按用户确认收紧 `problem_19_pre`，要求 `Forall is_valid_word (SplitOnSpaces input)`；`problem_19_spec` 保持 permutation 与 sorted 语义，不再重复携带该输入有效性条件。
- 验证：待继续完成 `StringClaude/C_19.c` 的 QCP 改写、symexec 与全链证明。

### 问题编号：SPEC-C_103-001

- 问题类型：原 spec 与题面注释不一致
- 涉及文件：`spec/103.v`、`StringClaude/C_103.c`
- 发现时间：2026-05-22
- 现象：题面注释要求把平均值转换为不带前缀的二进制字符串，且 `n > m` 时返回字符串 `"-1"`；原 `spec/103.v` 使用了带 `0b` 前缀的结果形态，并且返回类型/失败分支与字符串结果不一致。
- 例子：题面示例 `rounded_avg(1, 5) => "11"`，不是 `"0b11"`；`rounded_avg(7, 5) => "-1"` 是字符串。
- 当前处理：按用户确认的口径，以文件开头注释为正确程序语义，已修正 `spec/103.v`：`to_binary` 不再添加 `0b` 前缀，`rounded_avg_impl` 和 `problem_103_spec` 的输出为 `string`。
- 验证：`coqtop -quiet -l QCP_examples/humaneval/spec/103.v` 已通过；`StringClaude/C_103.c` 尚未进入全链验证。

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

### 问题编号：SPEC-C_127-001

- 问题类型：原 spec 无法加载
- 涉及文件：`spec/127.v`、`StringClaude/C_127.c`
- 发现时间：2026-05-21
- 现象：执行 `coqtop -quiet -l QCP_examples/humaneval/spec/127.v` 失败。`problem_127_pre` 中 `s1 <= e1 /\ s2 <= e2` 的变量类型为 `Z`，但文件后面打开了 `nat_scope`，导致 `<=` 被解析成 nat 比较。
- 报错：`The term "s1" has type "Z" while it is expected to have type "nat".`
- 当前处理：已按用户确认修正 `spec/127.v`，将 `problem_127_pre` 中的两个区间端点比较显式标注为 `%Z`，并在 scope 声明块末尾重新打开 `Z_scope`，避免 `Load "../spec/127"` 后让 `nat_scope` 污染后续生成文件。
- 验证：`coqtop -quiet -l QCP_examples/humaneval/spec/127.v` 已通过。

### 问题编号：SPEC-C_38-001

- 问题类型：不足三字符尾段语义不一致
- 涉及文件：`spec/38.v`、`StringClaude/C_38.c`
- 发现时间：2026-05-21
- 现象：按用户澄清，`spec/38.v` 的 `problem_38_spec` 是针对 `decode_cyclic`，不是 `encode_cyclic`；完整三字符组的方向与 C 的 `decode_cyclic` 一致。但当输入长度为 1 或 2 时，原 spec 中 `let n := ((String.length input / 3) * 3 - 1)%nat` 因 nat 减法截断得到 `0`，导致第 0 个字符被错误地当成完整三字符组位置处理。C 的 `decode_cyclic` 对不足 3 个字符的尾段保持原样。
- 例子：输入 `"a"` 时，C 的 `decode_cyclic` 输出 `"a"`；原 spec 要求第 0 位输出 `get_char input 2`，即默认空格字符。
- 当前处理：已按用户确认修正 `spec/38.v`，将 `problem_38_spec` 改为直接使用 `decode_cyclic_source_index` 的点态规格；不足三字符尾段保持原样，完整三字符组仍按 `decode_cyclic` 方向取源字符。
- 验证：已完成 `StringClaude/C_38.c` 中 `decode_cyclic` 的全链验证；`encode_cyclic` 不作为本题验证目标。

### 问题编号：SPEC-C_144-001

- 问题类型：原 pre 过宽，无法保证 C 的分数字符串解析语义
- 涉及文件：`spec/144.v`、`StringClaude/C_144.c`
- 发现时间：2026-05-21
- 现象：`problem_144_pre` 只要求 `Parse_Fraction` 成立并且解析出的分子/分母为正，但当前 `Parse_Fraction` 对分子和分母字符列表没有限制为十进制数字。原转换版 C 使用 `sscanf("%d/%d")`，只按 C 的十进制整数格式解析；验证版 C 已按 `CPP_144.cpp` 改为循环解析。
- 例子：如果分子或分母部分含有非数字字符，原 spec 的解析关系可能仍无法精确刻画 `sscanf` 的实际行为；直接验证会把表示层解析差异混入程序语义。
- 当前处理：已按用户确认收紧原 `problem_144_pre`。新增 `is_digit_ascii` / `all_digits`，要求两个输入分数的分子和分母字符列表均只包含 `'0'..'9'`，同时保留原有正整数约束。
- 验证：`coqtop -quiet -l QCP_examples/humaneval/spec/144.v` 已通过；`StringClaude/C_144.c` 已完成全链验证。
