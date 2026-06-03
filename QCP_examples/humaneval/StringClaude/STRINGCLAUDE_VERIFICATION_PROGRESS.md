# StringClaude 验证进度记录

更新时间：2026-06-01

这份文档用于记录 `QCP_examples/humaneval/StringClaude` 下各题的验证进度，以及每题验证时遇到的问题、采用的建模方式和后续继续时需要注意的事项。

它和下面几份文档分工不同：

- `STRING_VERIFICATION_GUIDE.md`：记录字符串程序验证的一般方法。
- `../SKILL.md`：记录完整验证流程、命令顺序和交付要求。
- 本文档：记录每一道题当前做到哪里、踩过哪些坑、最后如何解决。

## 状态说明

- `已全链通过`：已经完成 `symexec`、`manual` 证明、`goal_check` 编译，且 `coins_XX.v` / `C_XX_proof_manual.v` 无 `Admitted.` / `Axiom`。
- `已有生成文件`：目录中已有 `C_XX_goal.v` / `C_XX_proof_auto.v` / `C_XX_proof_manual.v` / `C_XX_goal_check.v`，但本文档尚未确认完整验收。
- `验证中`：已建立 QCP 建模或通过部分工具链检查，但尚未达到全链验收标准。
- `待确认`：原 C、题面注释或原始 `spec/XX.v` 之间存在可验证前必须先确认的语义冲突；未经用户确认不得修改原 spec 或核心 C 逻辑。
- `待建模`：尚未建立完整 QCP 规格和验证文件，通常需要先将 C 程序改写成 QCP 可接受的格式。

## 当前总览

| 题目 | 当前状态 | 备注 |
| --- | --- | --- |
| `C_6` | 已全链通过 | parse nested parentheses；已按用户确认修复原 C 的错误分组输出，改为按空格/字符串末尾输出每个非空 token 的最大深度，并记录到 `ORIGINAL_C_ISSUES_LOG.md`。`problem_6_pre_z/spec_z` 直接 wrapper 原始 `spec/6.v`；`spec/6.v` 的实现定义改成等价单趟扫描形式，便于和 C 循环 bridge。已完成 `symexec`、manual 证明和 `goal_check` 编译，`coins/manual` 无 `Admitted`/`Axiom`。 |
| `C_10` | 已全链通过 | make palindrome；已完成 QCP 格式转换，将 `is_palindrome(str+i)`/`memcpy` 改为显式 suffix 检查和输出写入循环；`problem_10_pre_z/spec_z` 直接 wrapper 原始 spec，`coins_10.v` 已补 `first_pal_suffix_z`、`make_pal_output_z` 与原始最短回文 spec 的 bridge；`symexec` 重新生成后，`coins_10.v`、`C_10_goal.v`、`C_10_proof_auto.v`、`C_10_proof_manual.v`、`C_10_goal_check.v` 均已通过，`coins/manual` 无 `Admitted`/`Axiom`。 |
| `C_11` | 已全链通过 | 二进制字符串 XOR；`problem_11_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_15` | 已全链通过 | string sequence；已改成 QCP 支持的显式写缓冲区版本，复用 `coins_44` 的十进制 digit 状态，补充 `sequence_output_z` 到原 `string_sequence_impl` 的纯 bridge；`symexec`、goal/auto/manual/goal_check 均已通过。 |
| `C_16` | 已全链通过 | 忽略大小写后的不同字符个数；已将 `tolower + seen[256]` 改为显式双层循环，`problem_16_pre_z/spec_z` 为纯原 wrapper，C 层 `lower_seen_state_z/count_distinct_lower_upto` 只作为 invariant 和内部 bridge 使用。 |
| `C_17` | 已全链通过 | parse music；已改为 QCP 支持的 `IntArray *` 返回形式，C 层显式状态机扫描音符 token，`coins_17.v` 已桥接到原 `SplitOnSpaces` / `parse_note` 语义。 |
| `C_18` | 已全链通过 | substring 重叠出现次数；已将 `memcmp` 改为显式双层循环，`problem_18_pre_z/spec_z` 为纯原 wrapper，C 层 `count_matches_upto/match_progress_z` 只作为 invariant 和内部 bridge 使用。 |
| `C_19` | 已全链通过 | sort number words；按用户要求保留真实 `words[10]` 指针数组和本地 `w0..w9` 字符数组，不使用 `strcmp_number_word`、`words_get` 或按数字词语义建模的自定义 wrapper；`strlen` / `malloc_char_array` / `free_char_array` / `strcmp` / `strcat` 均为普通库函数 wrapper。`number_word_z` 仅作为 annotation/Coq 中的数字词内容描述。为避免把程序改成显式 `tlen == 0` 分支，新增 C 层 bridge `token_empty_start_z`，记录空 token 时扫描起点与当前位置对齐，并在普通非空字符扩展处用 `token_unsat_end_extend_z` 桥接。已重新 `symexec --gen-and-backup`，并通过 `coins_19.v`、`C_19_goal.v`、`C_19_proof_auto.v`、`C_19_proof_manual.v`、`C_19_goal_check.v` 编译；`coins/manual` 无 `Admitted`/`Axiom`。`problem_19_pre_z/spec_z` 已直接桥接原始 `spec/19.v` pre/spec。 |
| `C_23` | 已全链通过 | `strlen` 薄包装；已直接桥接原始 `spec/23.v` 的 `problem_23_pre/spec`。 |
| `C_27` | 已全链通过 | 大小写翻转；已直接桥接原始 `spec/27.v` 的 `problem_27_pre/spec`。 |
| `C_38` | 已全链通过 | 只验证 `decode_cyclic`；已按用户确认修正原 `spec/38.v` 的短尾段语义，`problem_38_pre_z/spec_z` 为纯原 wrapper。 |
| `C_44` | 已全链通过 | 基数转换；`problem_44_pre_z/spec_z` 为纯原 wrapper，输出缓冲区先全初始化再反向填充，避免生成未导出的 `CharArray.mixed_full`，`symexec`、manual 证明和 `goal_check` 均已通过。 |
| `C_48` | 已全链通过 | 回文判断；`problem_48_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_51` | 已全链通过 | 删除元音；`problem_51_pre_z/spec_z` 为纯原 wrapper，`char_range_z` 作为 C annotation 表示条件。 |
| `C_54` | 已全链通过 | same characters；`problem_54_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_56` | 已全链通过 | 尖括号匹配；`problem_56_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_61` | 已全链通过 | 圆括号匹配；`problem_61_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_64` | 已全链通过 | 元音计数；`problem_64_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_65` | 已全链通过 | circular shift digits；已移除 `sprintf_decimal`/`sprintf` 依赖，改为 C 循环统计十进制位数并反向填充数字；`circular_shift_output_z` 与原 `spec/65.v` 对齐，`problem_65_pre_z/spec_z` 直接 wrapper 原始 spec；已重新 `symexec --gen-and-backup` 并通过 `coins_65.v`、`C_65_goal.v`、`C_65_proof_auto.v`、`C_65_proof_manual.v`、`C_65_goal_check.v` 编译，`coins/manual` 无 `Admitted`/`Axiom`。 |
| `C_66` | 已全链通过 | 大写字母 ASCII 求和；`problem_66_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_67` | 已全链通过 | 已按用户确认收紧原 `problem_67_pre`；`problem_67_pre_z/spec_z` 为纯原 wrapper，安全条件作为 C annotation 表示条件。 |
| `C_78` | 已全链通过 | 十六进制 prime digit 计数；`problem_78_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_79` | 已全链通过 | decimal to binary；`coins_79.v` 使用原 `problem_79_pre/spec` wrapper，并建立 `nat_to_binary_string`、二进制填充状态与最终 decorated string 的桥接；`symexec`、`C_79_goal.v`、`C_79_proof_auto.v`、`C_79_proof_manual.v`、`C_79_goal_check.v` 均已通过。 |
| `C_80` | 已全链通过 | 经用户许可修复原 C 的第一组三字符漏检；`problem_80_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_82` | 已全链通过 | 字符串长度素数判断；已直接桥接原始 `spec/82.v` 的 `problem_82_pre/spec`。 |
| `C_84` | 已全链通过 | 十进制各位数字之和再转二进制；`problem_84_pre_z/spec_z` 为纯原 wrapper，十进制位和状态和二进制填充状态只作为 C annotation/invariant 使用。 |
| `C_86` | 已全链通过 | anti shuffle；已改成 QCP 支持的显式扫描版本，用通用 `sort_char_array` / `copy_char_array` wrapper 表示排序和拷贝；`problem_86_pre_z/spec_z` 直接 wrapper 原始 spec，`coins_86.v` 已证明排序/前缀状态输出 `anti_shuffle_output_z` 与原 `anti_shuffle_impl` 对齐；`symexec`、`coins_86.v`、`C_86_goal.v`、`C_86_proof_auto.v`、`C_86_proof_manual.v`、`C_86_goal_check.v` 均已通过，`coins/manual` 无 `Admitted`/`Axiom`。 |
| `C_91` | 已全链通过 | boredom 计数；`problem_91_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_93` | 已全链通过 | encode；`problem_93_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_98` | 已全链通过 | 偶数下标大写元音计数；`problem_98_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_103` | 已全链通过 | rounded average；按文件开头注释语义返回 `"-1"` 或 floor average 的二进制字符串，`problem_103_pre_z/spec_z` 为纯原 wrapper，二进制计数和反向填充只作为 C annotation/invariant 使用。 |
| `C_110` | 已全链通过 | exchange；返回 `"YES"`/`"NO"` 由 `1/0` 桥接，`problem_110_pre_z/spec_z` 为纯原 wrapper，非负 list-Z 到 nat 转换条件放在 C annotation。 |
| `C_118` | 已全链通过 | closest vowel；`problem_118_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z`/`alpha_range_z` 作为 C annotation 表示条件。 |
| `C_119` | 已全链通过 | 两字符串括号拼接匹配；返回 `"Yes"`/`"No"` 由 `1/0` 桥接，`problem_119_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_124` | 已全链通过 | 固定格式日期校验；`problem_124_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_127` | 已全链通过 | 闭区间交集长度素数判断；返回 `"YES"`/`"NO"` 由 `1/0` 桥接，`problem_127_pre_z/spec_z` 为纯原 wrapper，区间长度和整数范围作为 C annotation 条件。 |
| `C_132` | 已全链通过 | 经用户许可修复原 C 为 `[[]]` 子序列四状态自动机；`problem_132_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_134` | 已全链通过 | 最后字符是否为空格分隔的单字母词；`problem_134_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_50` | 已全链通过 | 仅 `decode_shift` 作为原 spec 目标；`problem_50_pre_z/decode_spec_z` 为纯原 wrapper，`ascii_range_z` 放在 C annotation。 |
| `C_89` | 已全链通过 | encrypt；`problem_89_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_140` | 已全链通过 | 已按用户确认修正原 spec 的连续空格规则；`problem_140_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_141` | 已全链通过 | 文件名合法性检查；`problem_141_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件；已完成后缀 `.txt/.exe/.dll` 与原始 `exists prefix suffix` spec 的双向桥接。 |
| `C_143` | 已全链通过 | words in sentence；`problem_143_pre_z/spec_z` 为纯原 wrapper；C 层使用显式扫描、素数长度 helper 和逐字符输出拷贝，`coins_143.v` 已补 Z-list `split_words/join_words` 与原始 `spec/143.v` 的桥接；`coins_143.v`、`C_143_goal.v`、`C_143_proof_auto.v`、`C_143_proof_manual.v`、`C_143_goal_check.v` 均已编译通过，`coins/manual` 无 `Admitted`/`Axiom`。 |
| `C_144` | 已全链通过 | simplify fraction product；已按用户确认收紧原 `problem_144_pre` 的数字字符约束，`sscanf` 改为循环解析；`problem_144_pre_z/spec_z` 为纯原 wrapper。 |
| `C_154` | 已全链通过 | cyclic pattern substring；用户已允许修正空串分支，C 层在 `b = ""` 时返回 true，以匹配原 spec。已改为显式 shift/position 双层搜索，`problem_154_pre_z/spec_z` 直接 wrapper 原始 `spec/154.v`；`coins_154.v` 已补 `rotation_any_search_z`、旋转/子串双向桥接和 `ascii_range_z` 注入证明；`coins_154.v`、`C_154_goal.v`、`C_154_proof_auto.v`、`C_154_proof_manual.v`、`C_154_goal_check.v` 均已编译通过，`coins/manual` 无 `Admitted`/`Axiom`。 |
| `C_156` | 已全链通过 | int to mini Roman；`problem_156_pre_z/spec_z` 为纯原 wrapper，Roman 千位/百位/十位/个位拼接状态只作为 C annotation 和内部 bridge 使用；`sprintf`/字符串库逻辑改为显式写缓冲区。 |
| `C_161` | 已全链通过 | 大小写翻转；无字母时反转字符串。`problem_161_pre_z/spec_z` 为纯原 wrapper，`ascii_range_z` 作为 C annotation 表示条件。 |
| `C_162` | 跳过 | MD5；用户要求暂且跳过，不验证本题。原 `spec/162.v` 用抽象 `Parameter md5_hash`，原 C 又在 OpenSSL MD5 与 fallback hash 间按环境切换；除非后续确认信任外部 oracle 或改写为可证明规格，否则不继续。 |

其它只有 `.c` 的题目暂按 `待建模` 处理。

## 原 spec 桥接返工记录

本轮发现旧的 StringClaude “已全链通过”多数只证明了 C 层 `list Z` 操作式规格，没有把最终 `problem_XX_pre_z/spec_z` 直接桥接到 `../spec/XX.v` 的原始 `problem_XX_pre/spec`。按当前 `../SKILL.md`，这些题不能再算原 spec 完整通过。

后续验证统一采用以下规则：

1. `coins_XX.v` 中的最终 `problem_XX_pre_z/spec_z` 必须是纯原 spec wrapper，只做 `string_of_list_z`、`bool_of_z`、`Z.to_nat` 等格式转换，并直接调用 `../spec/XX.v` 的 `problem_XX_pre/spec`。
2. `ascii_range_z`、底层字符范围、C 层点态变换、membership、palindrome、状态机前缀等操作式条件不写进最终 wrapper；这些条件只放在 C annotation 的 `Require` / invariant 或内部 bridge lemma 前提中。
3. 如果原始 pre/spec 无法推出题意所需语义，必须暂停询问用户是否修改原 `spec/XX.v`；不得私自加强 wrapper 后继续标记为“已全链通过”。
4. 每次调整 wrapper 或 C annotation 后必须重新 symexec，并重新编译 `coins_XX.v`、`C_XX_goal.v`、`C_XX_proof_auto.v`、`C_XX_proof_manual.v`、`C_XX_goal_check.v`。

已完成原 spec 直连返工：

- `C_11`：`problem_11_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l1/l2)` 放在 `C_11.c` 的函数 `Require` 和循环 invariant 中，并完成重新 symexec 与全链编译。
- `C_16`：已将原 `tolower + seen[256]` 实现改为 QCP 友好的显式双层循环：外层枚举字符，内层扫描此前前缀判断当前小写字符是否已出现。`problem_16_pre_z/spec_z` 为纯原 spec wrapper，`ascii_range_z(l)` 放在 C annotation 中；`coins_16.v` 建立 `lower_z`、`lower_seen_state_z`、`count_distinct_lower_upto`、前缀 seen/new 计数推进，并将最终 distinct list-Z witness 桥接到原始 `problem_16_spec` 的 `list ascii` witness。已完成 symexec 与全链编译。
- `C_17`：`problem_17_pre_z/spec_z` 已建为纯原 spec wrapper，直接调用原始 `problem_17_pre/spec (string_of_list_z input)`，输出用 `map Z.to_nat` 桥接。为适配 QCP，将原 parse music 实现改为显式状态机，扫描 `"o"`、`"o|"`、`".|"` 和空格分隔 token，返回 `IntArray *`；`ascii_range_z(l)` 放在 C annotation 中。`coins_17.v` 建立状态机输出与原 `SplitOnSpaces` / `parse_note` 的桥接，并完成 `symexec`、`coins_17.v`、`C_17_goal.v`、`C_17_proof_auto.v`、`C_17_proof_manual.v`、`C_17_goal_check.v` 全链编译。
- `C_18`：`problem_18_pre_z/spec_z` 已建为纯原 spec wrapper，直接调用原始 `problem_18_pre/spec (string_of_list_z input) (string_of_list_z substring)`，输出用 `Z.to_nat` 桥接。为适配 QCP，将原 `memcmp(str+i, substring, m)` 改为显式双层循环，外层 invariant 记录 `out = count_matches_upto i l sub`，内层 invariant 用 `match_progress_z` 记录当前候选位置的匹配/失配前缀。已补全 `count_matches_upto` 到原始 existential `indices` spec 的桥接，并完成 symexec 与全链编译。
- `C_19`：`problem_19_pre_z/spec_z` 已建为纯原 spec wrapper，直接调用原始 `problem_19_pre/spec (string_of_list_z input) (string_of_list_z output)`。按用户要求保留真实 `words[10]` 指针数组和本地 `w0..w9` 字符数组，普通库函数只用带前后条件的 `strlen` / `malloc_char_array` / `free_char_array` / `strcmp` / `strcat` wrapper；C 层 token 扫描状态、计数和输出前缀只作为 annotation / 内部 bridge 使用。已完成重新 symexec 与全链编译。
- `C_23`：`problem_23_pre_z/spec_z` 均为纯原 spec wrapper；`problem_23_spec_z` 只调用原始 `problem_23_spec (string_of_list_z input) (Z.to_nat output)`，并完成全链编译。
- `C_27`：`problem_27_pre_z/spec_z` 均为纯原 spec wrapper；C 层点态 `flip_char_z` 只在内部 intro 引理中用于推出原始 `problem_27_spec`，并完成全链编译。
- `C_38`：只验证 `decode_cyclic`，不验证 `encode_cyclic`。按用户确认修正原 `spec/38.v`，将 `problem_38_spec` 改为 `decode_cyclic_source_index` 点态规格；完整三字符组按 decode 方向取源字符，不足三字符尾段保持原样。`problem_38_pre_z/spec_z` 为纯原 spec wrapper；C 层 `full_decode_len_z/decode_source_index_z/decode_char_z` 只作为内部 bridge lemma 和 invariant 使用。为适配 QCP，将原三字符块循环改为逐下标写入，返回语义保持一致，并完成 symexec 与全链编译。
- `C_48`：`problem_48_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_48.c` 的函数 `Require` 和循环 invariant 中，并完成重新 symexec 与全链编译。
- `C_50`：只验证 `decode_shift`；`problem_50_pre_z/decode_spec_z` 已改为纯原 spec wrapper。`ascii_range_z(l)` 放在 `C_50.c` 的函数 `Require` 和循环 invariant 中，结合原 pre 推出底层小写 `Z` 范围；`encode_shift` 只保留 C 层辅助规格，不作为本题原 spec 验证目标。
- `C_51`：`problem_51_pre_z/spec_z` 已改为纯原 spec wrapper；`char_range_z(l)` 放在 `C_51.c` 的函数 `Require` 和循环 invariant 中，C 层 `remove_vowels_prefix_z` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_54`：`problem_54_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l0/l1)` 放在 `C_54.c` 的函数 `Require` 和循环 invariant 中，并完成重新 symexec 与全链编译。
- `C_56`：`problem_56_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_56.c` 的函数 `Require` 和循环 invariant 中，C 层 `angle_level_upto/angle_nonnegative_prefix` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_61`：`problem_61_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_61.c` 的函数 `Require` 和循环 invariant 中，C 层括号深度模型只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_64`：`problem_64_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_64.c` 的函数 `Require` 和循环 invariant 中，C 层 `count_regular_vowels_upto + last_y_add` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_66`：`problem_66_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_66.c` 的函数 `Require` 和循环 invariant 中，C 层 `sum_upper_upto` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_67`：按用户确认，原 C 对题面固定格式输入可认为正确；已将原 `problem_67_pre` 从 `True` 收紧，`problem_67_pre_z/spec_z` 改为纯原 spec wrapper。`ascii_range_z(l)`、`fruit_state_safe_z(l)`、`fruit_output_safe_z(l,total)` 放在 `C_67.c` 的函数 `Require` 和循环 invariant 中，C 层扫描状态只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_78`：`problem_78_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_78.c` 的函数 `Require` 和循环 invariant 中，C 层 `count_prime_hex_upto` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_80`：经用户许可修复原 C，长度至少为 3 时先检查 `s[0] != s[1]`，循环中继续检查当前字符和前两个字符都不同；`problem_80_pre_z/spec_z` 已改为纯原 spec wrapper。`ascii_range_z(l)` 放在 `C_80.c` 的函数 `Require` 和循环 invariant 中，C 层 `happy_prefix_z/happy_adjacent_z` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_82`：`problem_82_spec_z` 已改为纯原 spec wrapper，只调用原始 `problem_82_spec (string_of_list_z s) (bool_of_z output)`；C 层 `prime_len_z` 只作为内部证明引理使用，并完成全链编译。
- `C_84`：`problem_84_pre_z/spec_z` 已建为纯原 spec wrapper，输入整数用 `Z.to_nat` 桥接到原始 `problem_84_pre/spec`。为适配 QCP，将 `sprintf`/helper 返回改为显式循环：先维护 `decimal_sum_state_z` 计算十进制位和，再复用 `binary_count_state_z` / `binary_fill_full_state_z` 构造二进制字符串；这些状态只作为 C annotation 和内部 bridge 使用。已完成 symexec 与全链编译。
- `C_86`：`problem_86_pre_z/spec_z` 已建为纯原 spec wrapper，直接调用原始 `problem_86_pre/spec (string_of_list_z l)`。为适配 QCP，将原 `qsort`/`memcpy`/指针偏移实现改为显式扫描当前 word，并通过 `sort_char_array`、`copy_char_array` wrapper 表示排序和拷贝；`anti_out_prefix_z` / `anti_cur_prefix_z` 只作为循环 invariant 状态。`coins_86.v` 已证明最终 `anti_shuffle_output_z` 等于原 `anti_shuffle_impl`，并完成 symexec 与全链编译。
- `C_89`：`problem_89_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_89.c` 的函数 `Require` 和循环 invariant 中，结合原 pre 推出底层小写 `Z` 范围，并完成重新 symexec 与全链编译。
- `C_91`：`problem_91_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_91.c` 的函数 `Require` 和循环 invariant 中，C 层三状态前缀模型只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_93`：`problem_93_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_93.c` 的函数 `Require` 和循环 invariant 中，结合原 pre 推出底层字母/空格 `Z` 范围；C 层 `encode_char_z` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_98`：`problem_98_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_98.c` 的函数 `Require` 和循环 invariant 中，C 层 `count_upper_even_upto` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_110`：`problem_110_pre_z/spec_z` 已建为纯原 spec wrapper，输入数组通过 `map Z.to_nat` 转为原始 `list nat`，`nonnegative_list_z` 作为表示转换前提放在 `C_110.c` 的函数 `Require` 和循环 invariant 中，不写进 wrapper。为适配 QCP，将原 C 返回 `"YES"` / `"NO"` 改为返回 `1` / `0`，由 `yesno_of_z_110` 桥接；原核心算法保持为统计 `lst1` 和 `lst2` 中的偶数总数，并与 `lst1_size` 比较。循环 invariant 使用 `count_even_upto` 记录前缀偶数计数，并完成 symexec 与全链编译。
- `C_118`：`problem_118_pre_z/spec_z` 已建为纯原 spec wrapper，直接调用原始 `problem_118_pre/spec (string_of_list_z ...)`。`ascii_range_z(l)` 和 `alpha_range_z(l)` 放在 C annotation 中；C 层用 `closest_vowel_candidate_z` 和 `no_candidate_after_z` 表示从右向左扫描时“右侧没有更近候选”的循环状态，并由 bridge lemma 连接到原 spec。已完成 symexec 与全链编译。
- `C_119`：`problem_119_pre_z/spec_z` 已建为纯原 spec wrapper，直接调用原始 `problem_119_pre/spec [string_of_list_z l1; string_of_list_z l2]`，返回 `"Yes"` / `"No"` 用 `1` / `0` 桥接。`ascii_range_z(l1/l2)` 放在 C annotation 中；C 层使用 `paren_level_upto` 和 `paren_good_prefix_flag` 分别记录当前括号深度和前缀非负性。反向扫描前需要把第一种拼接的“总 level 为 0、prefix flag 为 0”作为 `Assert` 带入后续 invariant，否则最终反向返回 VC 缺少两种拼接之间的桥接事实。已完成 symexec 与全链编译。
- `C_124`：`problem_124_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_124.c` 的函数 `Require` 和循环 invariant 中，C 层 `valid_date_z` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_127`：`problem_127_pre_z/spec_z` 已建为纯原 spec wrapper，输入区间用 `interval_pair_z` 从长度为 2 的 `list Z` 转成原始 `Z * Z`，返回 `"YES"` / `"NO"` 用 `1` / `0` 桥接。`interval_int_range` 和循环中的 `prime_prefix_z` 只作为 C annotation / 内部证明条件使用；已完成 `coins_127.v`、`C_127_goal.v`、`C_127_proof_auto.v`、`C_127_proof_manual.v`、`C_127_goal_check.v` 全链编译。
- `C_132`：经用户许可修复原 C，将 `count/maxcount` 深度下降判定改为四状态子序列自动机；`problem_132_pre_z/spec_z` 已改为纯原 spec wrapper，`ascii_range_z(l)` 放在 `C_132.c` 的函数 `Require` 和循环 invariant 中，C 层 `subseq_state_prefix_z` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_134`：`problem_134_pre_z/spec_z` 已改为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_134.c` 的函数 `Require` 和中间 `Assert` 中，C 层 `ends_with_single_letter_z` 只作为内部 bridge lemma 前提使用，并完成重新 symexec 与全链编译。
- `C_140`：按用户确认修复原 `spec/140.v`，使连续空格段长度 1/2/>2 分别输出 `_`、`__`、`-`；`problem_140_pre_z/spec_z` 已改为纯原 spec wrapper。`ascii_range_z(l)` 放在 `C_140.c` 的函数 `Require` 和循环 invariant 中，C 层 `fix_spaces_prefix_z/fix_spaces_pending_z` 只作为内部 bridge lemma 前提使用，并完成 symexec 与全链编译。
- `C_141`：已修复原 `spec/141.v` 中 `"Yes"` / `"No"` 的 string scope 编译问题，并建立 `problem_141_pre_z/spec_z` 纯原 spec wrapper。`ascii_range_z(l)` 放在 C annotation 中；C 层使用 `file_name_checks_z` 记录长度、首字符、后缀、digit 计数和 dot 计数条件。已补全后缀 `.txt/.exe/.dll` 与原始 `exists prefix suffix` spec 的双向桥接，并完成 `coins_141.v`、`C_141_goal.v`、`C_141_proof_auto.v`、`C_141_proof_manual.v`、`C_141_goal_check.v` 全链编译。
- `C_144`：按用户确认收紧原 `spec/144.v` 的 `problem_144_pre`，要求两个分数字符串的分子/分母字符均为十进制数字。为适配 QCP，将原 C 中 `sscanf("%d/%d")` 按 `CPP_144.cpp` 的思路改写为四段循环解析，返回语义保持一致。`problem_144_pre_z/spec_z` 为纯原 spec wrapper；`fraction_parts_z`、`fraction_values_safe_z`、各前缀解析上界只作为 C annotation / safety proof 条件使用，并完成 symexec 与全链编译。
- `C_156`：`problem_156_pre_z/spec_z` 已建为纯原 spec wrapper，输入整数用 `Z.to_nat` 桥接到原始 `problem_156_pre/spec`，输出用 `string_of_list_z` 桥接。为适配 QCP，将 Roman numeral 构造改成显式写入 64 字节输出缓冲区，并用已实现 helper `append_roman_digit` 分别处理百位、十位、个位；`roman_digit_z`、`roman_prefix*_z`、`roman_output_z` 只作为 C annotation / 内部 bridge 使用。已完成 symexec 与全链编译。
- `C_161`：`problem_161_pre_z/spec_z` 已建为纯原 spec wrapper；`ascii_range_z(l)` 放在 `C_161.c` 的函数 `Require` 和循环 invariant 中，C 层 `contains_letter_prefix_z/contains_letter_z/flip_char_z` 只作为内部 bridge lemma 前提使用。为适配 QCP，将原程序的“先构造翻转大小写结果、无字母时另分配反转结果”改为“先扫描是否含字母，再一次性构造最终返回结果”，返回语义保持一致，并完成 symexec 与全链编译。

已按规则跳过：

- `C_162`：用户要求暂且跳过，不验证本题。当前原始 `spec/162.v` 用 `Parameter md5_hash : string -> string` 抽象 MD5，原 C 又根据编译环境在 OpenSSL MD5 与 fallback hash 之间切换；除非后续确认将 `md5_hash` 作为可信外部 oracle，或改写原 spec/C 使哈希语义可在当前 Coq/QCP 环境中证明，否则不继续。

## C_19 sort number words 验证记录

### 当前状态

`C_19` 已全链通过。

已完成：

```bash
linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/StringClaude/C_19_goal.v \
  --proof-auto-file=QCP_examples/humaneval/StringClaude/C_19_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/StringClaude/C_19_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/StringClaude SimpleC.EE \
  --input-file=QCP_examples/humaneval/StringClaude/C_19.c \
  -IQCP_examples/LLM_friendly_cases \
  --gen-and-backup \
  --no-exec-info
```

并通过：

```bash
coqc coins_19.v
coqc C_19_goal.v
coqc C_19_proof_auto.v
coqc C_19_proof_manual.v
coqc C_19_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_19.v C_19_proof_manual.v
```

无输出。

### 语义与建模约束

1. 保留真实 `words[10]` 数组。

用户明确要求不要把 `number_word` 改成脱离 C 程序的数据模型，也不要用 `words_get` 之类的语义 wrapper。最终版本保留本地 `w0..w9` 字符数组和真实 `char *words[10]` 指针数组：

```c
char w0[5]; ... char w9[5];
char *words[10];
words[0] = w0; ... words[9] = w9;
```

`number_word_z` 只描述这些真实字符数组的内容，用于 annotation 和 Coq bridge，不替代 C 里的真实数组。

2. 常见库函数只用普通 wrapper。

最终没有使用 `strcmp_number_word`、`words_get` 或按数字词语义定制的 wrapper。`strcmp` / `strcat` / `strlen` 都按普通库函数规格写前后条件：

```c
strcmp(token, word)
strcat(out, word)
strlen(word)
```

验证时通过 `PtrArray.full words 10 [w0..w9]`、`number_words_missing/full` 和 `CharArray.full wk ...` 证明当前 `word` 指向的真实字符串内容，而不是让 wrapper 偷带数字词语义。

3. `free_char_array` 不需要按对象拆多个 wrapper。

早期曾把不同释放场景拆成多个 wrapper，后来回退为一个通用 wrapper：

```c
void free_char_array(char *p, int used, int cap)
```

用 `CharArray.full(p, used, l) * CharArray.undef_seg(p, used, cap)` 表示已用前缀和剩余容量，`token` 和 `space_word` 都复用同一个规格。

### 主要失败经验

1. 自定义语义 wrapper 会让验证变快，但偏离原程序。

最早尝试过 `strcmp_number_word`、`words_get`、或者直接用数字词语义描述 `word = number_word(d)`。这些方式能绕开 `PtrArray` 和 `CharArray` 资源拆合，但实际等于把普通 `strcmp(token, word)` 建模成题目专用 oracle，不符合“常见库函数用普通 wrapper”的要求，因此全部回退。

2. 真实 `words[10]` 的资源拆合是第一个大坑。

`word = words[d]` 后，`strcmp` 需要：

```coq
CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ [0])
```

但原资源是：

```coq
PtrArray.full words 10 [w0; ...; w9]
number_words_chars_full_z w0 ... w9
```

工具不能自动从变量下标 `d` 抽出对应 `wk` 的字符数组。最终做法是使用 `number_words_missing` 表示“指针数组缺当前下标，同时字符数组缺当前 word”，在 manual 中用 `number_words_missing_merge_vc` 按 `d = 0..9` 分支合回 `number_words_full`。这比展开 10 条 C 分支稳定，且保留真实数组。

3. 展开 10 个数字分支会造成路径和 proof 爆炸。

中途尝试过在 C annotation 或 C 结构里显式展开 10 个分支来帮助 `strcmp` 前置条件。单分支资源匹配会变容易，但 `symexec` 路径数量和后续 `manual` obligation 明显膨胀，最终撤回。经验是：真实数组问题应放在 separation bridge lemma 中处理，而不是把 C 控制流改成 proof 辅助结构。

4. `tlen = 0` 不能改成 C 程序里的显式分支。

扫描循环中，原程序只有：

```c
if (ch == 32) {
    if (tlen > 0) { ...; tlen = 0; }
} else if (tlen < 31) {
    token[tlen] = ch;
    tlen = tlen + 1;
}
```

没有额外的 `tlen == 0` 程序分支。证明里曾临时用 `assert (tlen = 0) by lia` 处理空 token 路径，但这只是局部 arithmetic，不足以说明下一轮 token 起点。不能为了证明方便把 C 程序改成新分支，否则会改变控制流结构，也偏离用户要求。

5. 真正缺的是“空 token 起点”的 bridge。

旧 invariant 只有：

```coq
token_unsat_end_z i tlen l :=
  tlen = 0 \/ scan_word_start_z i l + tlen = i
```

当 `tlen = 0` 时，这个性质太弱，只说明 token 是空的，不能推出 `scan_word_start_z i l = i`。因此读到非空字符后，无法证明新 token 满足：

```coq
scan_word_start_z (i + 1) l + (tlen + 1) = i + 1
```

最终补的最小 bridge 是：

```coq
Definition token_empty_start_z (i tlen : Z) (input : list Z) : Prop :=
  tlen = 0 -> scan_word_start_z i input = i.
```

并在读入非空字符时用：

```coq
token_unsat_end_extend_z
```

把 `token_empty_start_z i tlen l`、旧的 `token_unsat_end_z i tlen l` 和 `scan_char_z i l <> 32` 桥接到下一轮。

6. `ch == 32` 要带进内层 `d` 循环 invariant。

进入 `if (ch == 32)` 后，内层 `for (d = 0; d < 10; d++)` 仍需要知道当前路径确实是空格分隔符，否则内层循环结束、`tlen = 0`、外层扫描推进时缺少路径事实。最终在内层 invariant 中把无信息的 `ch == ch` 改成 `ch == 32`。这不改变程序语义，只是保留已知路径条件。

7. 备份文件多的直接原因。

本题一共生成到 `C_19_proof_manual_backup87.v`，主要不是因为单个 Coq 引理复杂，而是反复在以下几类方案之间回退：

- 题目专用 `strcmp_number_word` / `words_get` wrapper，后因不符合建模约束撤回。
- 将数字词建模成数组外的抽象 getter，后因用户要求保留真实 `words` 数组撤回。
- 多个 `free` wrapper，后统一为普通 `free_char_array`。
- 显式展开 10 个数字词分支，后因路径爆炸撤回。
- 在 proof 中直接 `assert (tlen = 0)`，后发现缺少 `scan_word_start` 语义，改为 `token_empty_start_z` bridge。
- 每次修改 C annotation 或 bridge 后按 `SKILL.md` 重新 `symexec --gen-and-backup`，因此 backup 数量快速增长。

### 最终可复用做法

1. 对真实指针数组，优先写 `full/missing/merge` 型 separation bridge。

`number_words_full` 表示完整资源，`number_words_missing` 表示读取 `words[d]` 后暂时拿出当前 `word` 对应的字符数组。`strcmp` / `strlen` / `strcat` 调用后再用 merge lemma 合回完整资源。

2. 对 token 扫描状态，分别记录“内容”和“扫描起点”。

`token_prefix_z` 描述当前 token 内容，`token_unsat_end_z` 描述非饱和 token 的右端对齐，`token_empty_start_z` 单独补足空 token 时的左端信息。空 token 情况不能只靠 `tlen = 0 \/ ...`。

3. 不要为了证明方便改普通库函数语义。

本题最终通过的关键不是更强 wrapper，而是在 C annotation 和 Coq bridge 中补足资源拆合与 token 扫描事实。后续类似题应优先保留 `strcmp` / `strcat` 这类库函数的通用规格。

4. 生成文件路径注意。

`C_19_goal.v` 直接 `Require Import char_array_strategy_goal`，本目录编译时应避免同时把 `SeparationLogic/examples` 和 `SeparationLogic/examples/LLM_friendly_cases` 都作为无前缀路径加入，否则会出现同名 `.vo` 二义性。可用本次通过的形式：

```bash
COQINCLUDES="-R ../../../SeparationLogic/SeparationLogic SimpleC.SL \
-R ../../../SeparationLogic/unifysl Logic \
-R ../../../SeparationLogic/sets SetsClass \
-R ../../../SeparationLogic/compcert_lib compcert.lib \
-R ../../../SeparationLogic/auxlibs AUXLib \
-R ../../../SeparationLogic/StrategyLib SimpleC.StrategyLib \
-R ../../../SeparationLogic/Common SimpleC.Common \
-R ../../../SeparationLogic/fixedpoints FP \
-R ../../../SeparationLogic/MonadLib MonadLib \
-R ../../../SeparationLogic/listlib ListLib \
-R . SimpleC.EE \
-R ../../../SeparationLogic/examples/LLM_friendly_cases \"\""
```

## C_143 words in sentence 验证记录

### 当前状态

`C_143` 已全链通过。

已完成：

```bash
coqtop -quiet -l ../spec/143.v
coqc string_bridge.v
coqc coins_143.v
symexec --gen-and-backup C_143.c
coqc coins_143.v
coqc C_143_goal.v
coqc C_143_proof_auto.v
coqc C_143_proof_manual.v
coqc C_143_goal_check.v
```

其中 `coins_143.v` 的最终 wrapper 直接桥接原始 `spec/143.v`：

```coq
Definition problem_143_pre_z (sentence : list Z) : Prop :=
  problem_143_pre (string_of_list_z sentence).

Definition problem_143_spec_z (sentence output : list Z) : Prop :=
  problem_143_spec (string_of_list_z sentence) (string_of_list_z output).
```

`C_143.c` 已去掉 `memcpy` / `bool` / 裸 `malloc`，改为：

- `malloc_char_array` 规格化输出缓冲区；
- `is_prime_len` 显式循环判断词长是否为素数；
- 主函数先跳过空格，再扫描一个单词，若词长为素数则逐字符复制到输出。

### 证明要点

`symexec` 已能完整生成：

```bash
C_143_goal.v
C_143_proof_auto.v
C_143_proof_manual.v
C_143_goal_check.v
```

已完成的关键桥接：

- `is_prime_len_entail_wit_1/2_1/2_2` 和 `is_prime_len_return_wit_1/2/3` 已证明；当前实现改为枚举 `2 <= j < len`，避免平方根因子配对证明。
- `coins_143.v` 已补 `has_divisor_from_true_iff`、`prime_loop_state_z_flag_0/1`，把 C 层除数枚举状态接到原始 `is_prime_bool`。
- `words_in_sentence_entail_wit_1/3/4/5/6_1/6_2/6_3/6_4/7/8_2/8_3/8_4`、`words_in_sentence_return_wit_1` 已证明。
- 输出缓冲区分配和 annotation 改为 `len + 2` 容量；copy loop 容量 invariant 使用 `out_len + word_len - k <= len + 2`，final NUL 仍由外层 `out_len <= i + 1` 约束。
- 已新增 `scan_ready_z` / `word_start_z` / `word_chars_z` / `word_copy_prefix_z`，其中 `scan_ready_z` 记录外层扫描是否位于开头、末尾、空格或空格之后，`word_start_z` 排除从单词中间开始的伪状态。
- `coins_143.v` 中使用 Z-list 操作式 `selected_words_z` / `join_words_z` 证明循环 step，再通过 `split_words_z_ascii`、`filter_prime_ascii_z`、`join_words_z_ascii` 桥接回原始 `spec/143.v` 的 `words_in_sentence_impl`。
- 已证明跳过空格、非素数单词不改变输出、素数单词 copy 后等于 spec prefix 三类 step lemma。

验收检查：`coins_143.v` 和 `C_143_proof_manual.v` 均无 `Admitted.` / `Axiom`，`C_143_goal_check.v` 编译通过。

## C_144 fraction simplify 验证记录

### 结论

`C_144` 已完成完整验证。验证版不再使用 `sscanf`，而是参考 `CPP_144.cpp` 将 `x` 和 `n` 分别用循环解析成 `a/b`、`c/d`，再判断 `(a * c) % (b * d) == 0`。

已通过的验收链：

```bash
opam exec --switch=coq8201 -- coqtop -quiet -l ../spec/144.v
coqc string_bridge.v
coqc coins_144.v
coqc C_144_goal.v
coqc C_144_proof_auto.v
coqc C_144_proof_manual.v
coqc C_144_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|^[[:space:]]*Axiom[[:space:]]" coins_144.v C_144_proof_manual.v
```

无输出。

### 语义与适配

1. 原 `problem_144_pre` 已按用户确认收紧。

问题记录在 `../ORIGINAL_SPEC_ISSUES_LOG.md` 的 `SPEC-C_144-001`。修复后原 pre 要求两个输入的分子/分母字符列表均只包含 `'0'..'9'`，同时保留原来的 `Parse_Fraction` 和正整数约束。

2. `coins_144.v` 使用纯原 pre/spec wrapper。

```coq
Definition problem_144_pre_z (x n : list Z) : Prop :=
  problem_144_pre (string_of_list_z x) (string_of_list_z n).

Definition problem_144_spec_z (x n : list Z) (output : Z) : Prop :=
  problem_144_spec (string_of_list_z x) (string_of_list_z n) (bool_of_z output).
```

3. C 层额外条件只用于解析和溢出安全。

`fraction_parts_z` 描述 slash 位置、两侧数字、解析出的分子分母和所有前缀解析上界；`fraction_values_safe_z` 将四个正整数限制在 `1..46340`，用于证明 `a * c`、`b * d` 不溢出 `int`。这些条件没有写进最终 wrapper。

## C_50 encode/decode_shift 验证记录

### 结论

`C_50` 已完成完整验证。`encode_shift` 和 `decode_shift` 均在小写字母输入前提下通过。

已通过的验收链：

```bash
coqtop -quiet -l QCP_examples/humaneval/spec/50.v
coqc coins_50.v
coqc C_50_goal.v
coqc C_50_proof_auto.v
coqc C_50_proof_manual.v
coqc C_50_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_50.v C_50_proof_manual.v
```

无输出。

### 文件变更

- `../spec/50.v`
  - 按用户确认，将 `problem_50_pre` 从 `True` 收紧为输入字符串所有字符均为小写 ASCII 字母 `a..z`。
  - 这样 C 的 `%` 与原 spec/Python 的非负模语义在输入域内一致。
- `C_50.c`
  - 替换为 QCP 头文件并声明 `malloc_char_array`、`strlen` 外部规格。
  - 为 `encode_shift` 和 `decode_shift` 分别补充函数规格和循环 invariant。
  - 只做 QCP 适配：`size_t` 改为 `int`，`malloc` 改为验证包装函数，字符常量改成 ASCII 数值；核心移位公式保持原样。
- `coins_50.v`
  - `Load "../spec/50".`
  - `problem_50_pre_z` 和 `problem_50_decode_spec_z` 均为纯原 spec wrapper。
  - `ascii_range_z` 不写进 wrapper，而是写在 `C_50.c` 的 `Require` / invariant；`lower_char_z_from_problem_50_pre` 从原 pre 加表示范围推出底层小写 `Z` 范围。
  - `encode_shift_char_z` 和 `problem_50_encode_spec_z` 只作为 `encode_shift` 的 C 层辅助规格；`decode_shift_char_z` 只在内部 bridge lemma 中使用。
- `C_50_goal.v` / `C_50_proof_auto.v` / `C_50_proof_manual.v` / `C_50_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. 对移位字符程序，pre 要保证 C `%` 的被除数非负。

本题中小写输入给出：

```coq
97 <= Znth i l 0 <= 122
```

因此 encode 的 `c + 5 - 97` 在 `5..30`，decode 的 `c + 21 - 97` 在 `21..46`。这时 C 风格 `Z.rem` 与通常的非负取模结果一致，输出也落在 `97..122`。

2. 写入 `char` 时需要证明移位结果在 signed 8-bit 范围内。

VC 中会出现：

```coq
signed_last_nbits ((Znth i l 0 + shift - 97) % 26 + 97) 8
```

先用 `Z.rem_bound_pos` 证明结果在 `0..127`，再用 `signed_last_nbits_eq` 化简。

3. 返回 VC 要同时处理空 `undef_seg` 和最终点态规格。

循环结束后从 `i >= len`、`i <= len` 得到 `i = len`，选择最终 `out_l` 作为 witness；再把 `CharArray.undef_seg out (len + 1) (len + 1)` 化成空段。最后用 `problem_50_encode_spec_z_intro` 或 `problem_50_spec_z_intro` 把 invariant 中的点态前缀性质桥接到函数后置规格。

## C_89 encrypt 验证记录

### 结论

`C_89` 已完成完整验证。

已通过的验收链：

```bash
coqtop -quiet -l QCP_examples/humaneval/spec/89.v
coqc coins_89.v
coqc C_89_goal.v
coqc C_89_proof_auto.v
coqc C_89_proof_manual.v
coqc C_89_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_89.v C_89_proof_manual.v
```

无输出。

### 文件变更

- `../spec/89.v`
  - 按用户确认，将 `problem_89_pre` 从 `True` 收紧为输入字符串所有字符均为小写 ASCII 字母 `a..z`。
- `C_89.c`
  - 替换为 QCP 头文件并声明 `malloc_char_array`、`strlen` 外部规格。
  - 将 `const char *`、`size_t`、`malloc` 等改为当前验证框架可处理的形式。
  - 核心移位公式保持为 `((s[i] + 4 - 97) % 26 + 97)`，只把字符常量改成 ASCII 数值。
- `coins_89.v`
  - `Load "../spec/89".`
  - `problem_89_pre_z/spec_z` 均为纯原 spec wrapper。
  - `ascii_range_z` 不写进 wrapper，而是写在 `C_89.c` 的 `Require` / invariant；`lower_char_z_from_problem_89_pre` 从原 pre 加表示范围推出底层小写 `Z` 范围。
  - `encrypt_char_z` 只作为内部 C 层点态模型，由 `problem_89_spec_z_intro` 桥接到原始 `problem_89_spec`。
- `C_89_goal.v` / `C_89_proof_auto.v` / `C_89_proof_manual.v` / `C_89_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. `C_89` 可以复用 `C_50` 的 Caesar shift 模板。

区别只是 shift 从 `5/21` 变成 `4`，且只有一个函数。循环 invariant 仍维护：

```c
Zlength(out_l) == i &&
forall k, 0 <= k < i ->
  Znth(k, out_l, 0) == encrypt_char_z(Znth(k, l, 0))
```

2. 小写 pre 同时解决规格一致性和写入范围。

小写输入给出 `97 <= c <= 122`，所以 `c + 4 - 97` 在 `4..29`，`Z.rem_bound_pos` 可直接证明输出在 `97..122`，从而满足 `signed_last_nbits_eq` 的范围要求。

3. 编译顺序要先 `C_89_goal.v` 再 `C_89_proof_manual.v`。

manual 文件导入 `From SimpleC.EE Require Import C_89_goal`。如果并行编译时 manual 先启动，会短暂报找不到 `C_89_goal` 的 logical path；按顺序重跑即可。

## C_91 验证记录

### 结论

`C_91` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_91.v
coqc C_91_goal.v
coqc C_91_proof_auto.v
coqc C_91_proof_manual.v
coqc C_91_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_91.v C_91_proof_manual.v
```

无输出。

### 文件变更

- `../spec/91.v`
  - 按用户确认的“原 C 程序正确”原则，将原先 `split/trim/prefix "I"` 的规格改成与原 C/官方 Python 行为一致的状态机规格。
  - 新规格中只有句首 `I` 后面遇到空格时才计数；因此 `"I"`、`"I."`、`"I?"`、`"I!"` 结果为 `0`，`"I am here."` 结果为 `1`。
- `C_91.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 状态适配为 `int` 的 `1/0`。
  - 缓存当前字符 `int chr = S[i]`，避免同一循环轮次多次读取 `CharArray`；计数和状态更新顺序保持原 C 行为。
  - 为纯原 spec 桥接补充 `ascii_range_z(l)`，放在函数 `Require` 和循环 invariant 中；不写进最终 wrapper。
  - 循环 invariant 维护 `sum/isstart/isi` 分别等于 `bored_*_prefix_z(i, l)`，并保留 `0 <= sum <= i`。
- `coins_91.v`
  - `Load "../spec/91".`
  - `problem_91_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_91_pre/spec`；`spec_z` 只做 `string_of_list_z` 和 `Z.to_nat` 转换。
  - 新增 `bored_state_after_nat`，用 `(sum, isstart, isi)` 三元组刻画处理前缀后的状态。
  - 新增 `bored_sum_prefix_z`、`bored_isstart_prefix_z`、`bored_isi_prefix_z` 和三个 step 引理。
  - 新增 `bored_sum_prefix_z_correct`，在 `ascii_range_z` 前提下证明 C 层三状态前缀模型等价于原始 `is_bored_impl`。
- `C_91_goal.v` / `C_91_proof_auto.v` / `C_91_proof_manual.v` / `C_91_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. 不要在 invariant 里保留不必要的布尔状态析取。

最初 invariant 写了：

```c
(isstart == 0 || isstart == 1) &&
(isi == 0 || isi == 1)
```

这会让每个循环推进 VC 都生成四个分离逻辑析取。删除后只保留状态函数等式，manual witness 从 24 个循环分支降到 8 个，证明显著简化。

2. 多个独立 `if` 的状态机程序适合用“前缀最终状态”建模。

`C_91` 每轮会依次更新 `sum`、`isi`、`isstart`，而不是一个简单计数器。用：

```coq
bored_state_after_nat : nat -> list Z -> Z * Z * Z
```

统一描述处理完前 `i` 个字符后的三状态，比给每个变量分别写递推定义更容易维护。

3. 当前字符缓存是字符串验证里的低风险适配。

把多处 `S[i]` 改成一处：

```c
int chr = S[i];
```

不改变可观察行为，但能减少 `CharArray` 读资源和 `app_Znth1` 重写压力。

4. 状态机返工到原 spec 时，先证明“C 层 fold = 原 ascii fold”。

`C_91` 的最终 wrapper 是：

```coq
problem_91_spec (string_of_list_z s) (Z.to_nat output)
```

内部证明分三步：先把 `bored_state_after_nat` 转成对前缀列表的 fold；再用 `ascii_range_z` 证明 `Z.eqb c 32/73/46/63/33` 和原 spec 中的 `Ascii.eqb` / `is_sentence_delimiter` 一致；最后推出 `bored_sum_prefix_z_correct`，供 return VC 使用。

## C_54 验证记录

### 结论

`C_54` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_54.v
coqc C_54_goal.v
coqc C_54_proof_auto.v
coqc C_54_proof_manual.v
coqc C_54_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_54.v C_54_proof_manual.v
```

无输出。

### 文件变更

- `C_54.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 的 `1/0`。
  - 为通用库函数 `strchr` 增加规格：返回 `0` 当且仅当目标字符不在字符串 payload 中，返回非零表示目标字符存在。
  - 将原先以 `'\0'` 为循环条件的两段扫描改为先调用 `strlen` 后按长度遍历；在 C 字符串模型中通过 `no_zero_z` 表示 payload 内无提前终止的 `0`，业务语义仍是双向字符集合包含。
  - 第一个循环 invariant 维护 `same_chars_prefix_z(i,l0,l1)`，第二个循环 invariant 维护 `same_chars_all_z(l0,l1)` 和 `same_chars_prefix_z(i,l1,l0)`。
- `coins_54.v`
  - `Load "../spec/54".`
  - 新增 `char_in_z`、`same_chars_prefix_z`、`same_chars_all_z`、`same_chars_set_z`，作为 C 层 membership 状态。
  - `problem_54_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_54_pre/spec`。
  - `ascii_range_z s0/s1` 放在 `C_54.c` 的 `Require` 和两个循环 invariant 中；false 分支桥接引理通过 `ascii_of_z_inj_range_54` 使用这些表示条件处理 `Z` 到 `ascii` 的单射。
  - 新增前缀初始化、前缀推进、true 返回和左右两种 false 返回桥接引理；C 层 membership 规格只出现在内部引理前提中，不出现在最终 wrapper 定义里。
- `C_54_goal.v` / `C_54_proof_auto.v` / `C_54_proof_manual.v` / `C_54_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. `strchr` 适合建模成通用 membership 查询。

本题不使用 `strchr` 返回的具体地址，只判断是否为 `NULL`。因此规格只需要：

```coq
__return = 0  -> ~ char_in_z c l
__return <> 0 ->   char_in_z c l
```

不要把题目语义写进 `strchr` 的规格，题目相关的“双向包含”仍放在 `coins_54.v` 的 bridge 引理中。

2. 双向集合相等可以拆成两个前缀包含循环。

第一个循环证明：

```coq
same_chars_all_z l0 l1
```

第二个循环在此基础上证明：

```coq
same_chars_all_z l1 l0
```

最终返回 `1` 时组合成 `same_chars_set_z l0 l1`。

3. `Zlength` 非负有时需要显式提供。

某些 `entailer!` 后留下 `0 <= Zlength l` 目标，`lia` 不一定能直接找到库事实。可用：

```coq
pose proof (Zlength_nonneg l); lia.
```

4. membership 类字符串规格的 false 分支需要字符范围。

true 分支从 `In z s0` 推出 `In (ascii_of_z z) (map ascii_of_z s0)` 不需要单射；但 false 分支要从“某个 `Z` 字符不在另一个列表”推出“对应 `ascii` 字符也不在另一个字符串”时，必须排除不同整数映射到同一个 `ascii` 的情况。因此 `C_54.c` 的 annotation 中保留 `ascii_range_z s0 /\ ascii_range_z s1`，而 `problem_54_pre_z/spec_z` 保持纯原 wrapper。

## C_82 验证记录

### 结论

`C_82` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_82.v
coqc C_82_goal.v
coqc C_82_proof_auto.v
coqc C_82_proof_manual.v
coqc C_82_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_82.v C_82_proof_manual.v
```

无输出。

### 文件变更

- `C_82.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 的 `1/0`。
  - 保留原始试除逻辑 `for (i = 2; i * i <= n; i++)` 和 `n % i == 0` 分支。
  - 前置条件增加 `len <= 2147302921`，用于证明循环条件里的 `i * i` 以及循环自增后的下一次条件检查不会产生 C signed int overflow；这不改变算法判断规则。
  - 循环 invariant 维护 `prime_prefix_z(i, n)`，表示 `[2, i)` 中没有 `n` 的因子。
- `coins_82.v`
  - `Load "../spec/82".`
  - 新增 `prime_prefix_z` 和 `prime_len_z` 作为 C 层长度素数规格。
  - `problem_82_pre_z` 直接调用原始 `problem_82_pre (string_of_list_z s)`。
  - `problem_82_spec_z` 是纯原 spec wrapper，只调用 `problem_82_spec (string_of_list_z s) (bool_of_z output)`，不额外暴露 C 层 `prime_len_z` 条件。
  - 新增 `prime_to_prime_len_z`、`prime_len_z_to_prime`、`prime_len_z_iff_prime`，仅在 `problem_82_spec_z_true/false` 内部用于把循环证明得到的 `prime_len_z` 桥接到原始 `Znumtheory.prime`。
  - 注意 C 的 `%` 在 VC 中对应 `Z.rem`，因此规格和引理也使用 `Z.rem`，不要写成 Coq 的 `Z.modulo`。
  - 新增前缀初始化、循环推进、true/false 返回分支和乘法安全边界引理。
- `C_82_goal.v` / `C_82_proof_auto.v` / `C_82_proof_manual.v` / `C_82_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. 保留 `i * i <= n` 时需要给长度一个溢出安全边界。

即使当前循环体内有 `i * i <= n`，自增后下一次条件检查仍可能计算 `(i + 1) * (i + 1)`。使用 `len <= 46339 * 46339 = 2147302921` 可以让 invariant 里维持 `i <= 46340`，从而证明条件表达式安全。

2. C `%` 与 Coq `mod` 不是同一个符号。

本题 VC 中的 `len % i` 对应 `Z.rem len i`。如果 `coins_82.v` 中把素数定义写成 `len mod i`，manual 里会出现无法统一：

```text
Zlength l % i <> 0
Zlength l mod i <> 0
```

解决方式是 C 层规格统一使用 `Z.rem`。

3. 桥到原始 `Znumtheory.prime` 时用 `prime_alt`。

`prime_len_z` 只排除 `d * d <= n` 的小因子。证明它等价于 `prime` 时：

- `prime -> prime_len_z`：用 `prime_divisors` 排除任何满足 `2 <= d` 且 `d * d <= n` 的整除因子。
- `prime_len_z -> prime`：用 `prime_alt` 展开为 `prime'`；若存在大因子 `d`，由整除关系取商 `q`，可证明 `1 < q` 且 `q * q <= n`，再与 `prime_len_z` 矛盾。

## C_132 验证记录

### 结论

`C_132` 已按文件开头注释和原 `spec/132.v` 的语义完成修复与完整验证。

原问题：原 `spec/132.v` 的语义是判断是否包含 `[[]]` 作为子序列；旧 C 程序使用 `count/maxcount` 的深度下降条件，弱于子序列语义。反例 `[][]]` 按原 spec 可取下标 `0,2,3,4` 形成 `[[]]`，应返回 true；旧 C 最大深度始终为 1，会返回 false。该问题已记录到 `../ORIGINAL_C_ISSUES_LOG.md`。

修复方式：经用户许可，将原 C 核心逻辑改为四状态子序列自动机，按顺序识别 `[`, `[`, `]`, `]`；最终 `state == 4` 时返回 `1`，否则返回 `0`。

已通过的验收链：

```bash
coqc coins_132.v
coqc C_132_goal.v
coqc C_132_proof_auto.v
coqc C_132_proof_manual.v
coqc C_132_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_132.v C_132_proof_manual.v
```

无输出。

### 文件变更

- `C_132.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 的 `1/0`。
  - 将旧的 `count/maxcount` 深度下降逻辑改为四状态子序列自动机，状态 0 到 4 分别表示已匹配 `[[]]` 的前缀长度。
  - 前置条件要求输入字符只包含 `[` / `]`，对应原题注释里的 bracket-only 输入。
  - 循环 invariant 维护 `state == subseq_state_prefix_z(i,l)` 和 `0 <= state <= 4`。
- `coins_132.v`
  - `Load "../spec/132".`
  - `problem_132_pre_z/spec_z` 为纯原 spec wrapper，只做 `string_of_list_z` 和 `bool_of_z` 格式转换。
  - 新增 C 层四状态模型 `subseq_step_z` / `subseq_state_prefix_z`，并用 bridge lemma 连接到原始 `problem_132_spec`。
  - `ascii_range_z` 不写入最终 wrapper，只作为 C annotation 和 bridge lemma 前提使用。
- `C_132_goal.v` / `C_132_proof_auto.v` / `C_132_proof_manual.v` / `C_132_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. 题意是“子序列”时，不能用括号栈深度近似。

旧程序检查的是扫描过程中是否出现过：

```c
count <= maxcount - 2
```

但原 spec 的 `contains_subseq` 允许跨过已经闭合的片段，例如 `[][]]` 可以取下标 `0,2,3,4` 形成 `[[]]`。因此 C 层语义必须直接建模“已匹配目标子序列前缀长度”。

2. 对子序列状态机，循环不变式保持“前缀状态”最稳。

本题的关键 invariant 是：

```coq
state = subseq_state_prefix_z i l
```

每轮用 `subseq_state_prefix_step` 推进；循环结束时根据 `state = 4` 或 `state <> 4` 分别调用 `problem_132_spec_z_true` / `problem_132_spec_z_false`。

3. 原 spec wrapper 保持纯格式转换。

```coq
Definition problem_132_spec_z (s : list Z) (output : Z) : Prop :=
  problem_132_spec (string_of_list_z s) (bool_of_z output).
```

`ascii_range_z` 和四状态 C 模型只出现在 annotation、invariant 和内部 bridge lemma 中，不额外加强最终 spec wrapper。

## C_134 验证记录

### 结论

`C_134` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_134.v
coqc C_134_goal.v
coqc C_134_proof_auto.v
coqc C_134_proof_manual.v
coqc C_134_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_134.v C_134_proof_manual.v
```

无输出。

### 文件变更

- `C_134.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 的 `1/0`。
  - 经用户许可修复原 C 语义：`n > 1` 时成功条件从“倒数第二个字符不是英文字母”改为“倒数第二个字符是空格 `32`”，与文件头注释中 space-separated word 的定义一致。
  - 为纯原 spec 桥接补充 `ascii_range_z(l)`，放在函数 `Require` 和第二次读取前的 `Assert` 中；不写进最终 wrapper。
  - 在第二次读取 `txt[n - 2]` 前加入完整 `Assert`，显式保留 `1 < n`、最后字符 `is_alpha_z`、`Zlength(l) == len` 和 `CharArray::full` 资源。
- `coins_134.v`
  - `Load "../spec/134".`
  - `problem_134_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_134_pre/spec`；`spec_z` 只做 `string_of_list_z` 与 `bool_of_z` 转换。
  - 新增 `is_alpha_z` 和 `ends_with_single_letter_z`，其中 C 层语义为：长度至少为 1，最后字符是英文字母，且长度为 1 或倒数第二个字符为空格。
  - 新增 `ends_with_single_letter_z_to_pred` / `pred_to_ends_with_single_letter_z`，在 `ascii_range_z` 前提下把 C 层 `Z` 字符模型桥接到原始 `ends_with_single_letter_pred`。
  - true/false 分支引理只把 C 分支事实接到纯原 wrapper；`ascii_range_z` 通过 C annotation 提供。
- `C_134_goal.v` / `C_134_proof_auto.v` / `C_134_proof_manual.v` / `C_134_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。
- `../ORIGINAL_C_ISSUES_LOG.md`
  - 新增 `C_134-001`，记录原 C 程序弱化空格分隔词语义的问题、复现示例、修复方案和验证结果。

### 经验

1. `return` 的冗余范围后置条件会制造不必要的析取 VC。

最初写了：

```c
(__return == 0 || __return == 1) &&
problem_134_spec_z(l, __return)
```

这会让每个返回 witness 带一层分离逻辑 `||`。由于 C 程序所有分支本身只返回 `0/1`，最终去掉范围条件，只保留题目语义规格，manual 证明更直接。

2. 提前返回后的安全事实不一定能自动流到下一次数组读取。

`if (n == 1) return 1;` 之后读取 `txt[n - 2]`，需要显式 `Assert 1 < n`，同时把最后字符已是字母的事实保留下来：

```c
chr == Znth(n - 1, l, 0) &&
is_alpha_z(chr)
```

否则后续既可能缺读取边界，也可能在 return 分支缺少最后字符字母性的语义桥接。

3. 原 spec 使用 `list_ascii_of_string` / `space` / `is_alpha`，C 层使用 `list Z`。

最终 wrapper 仍必须保持：

```coq
problem_134_spec (string_of_list_z s) (bool_of_z output)
```

`ascii_range_z` 只用于证明 `ascii_of_z` 与原 `ascii` 谓词对应：最后字符通过 `is_alpha_z_to_is_alpha`，倒数第二个空格通过 `ascii_of_z_space` / `ascii_of_z_eq_space_to_z`。不要把 `ends_with_single_letter_z` 直接写进 `problem_134_spec_z`。

## C_23 验证记录

### 结论

`C_23` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_23.v
coqc C_23_goal.v
coqc C_23_proof_auto.v
coqc C_23_proof_manual.v
coqc C_23_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_23.v C_23_proof_manual.v
```

无输出。

### 文件变更

- `C_23.c`
  - 替换为 `verification_stdlib.h`、`verification_list.h`、`char_array_def.h`。
  - 声明 `strlen` 外部规格，输入字符串使用 `CharArray::full(str, n + 1, app(l, cons(0, nil)))`。
  - 目标函数前置条件加入 `0 <= n`、`n < INT_MAX`、`Zlength(l) == n` 和输入字符串资源。
  - 后置条件保留输入字符串资源，并要求 `problem_23_spec_z(l, __return)`。
- `coins_23.v`
  - `Load "../spec/23".`
  - 复用 `string_bridge.v` 的 `string_of_list_z`，把输入 `list Z` 映射到原始 Coq `string`。
  - `problem_23_pre_z` 直接调用原始 `problem_23_pre (string_of_list_z input)`。
  - `problem_23_spec_z` 是纯原 spec wrapper，只调用原始 `problem_23_spec (string_of_list_z input) (Z.to_nat output)`。
- `C_23_goal.v` / `C_23_proof_auto.v` / `C_23_proof_manual.v` / `C_23_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成。
  - manual 只有 `string_length_return_wit_1`，证明中展开 `problem_23_spec_z` 后由纯事实和空间资源自动完成。

### 经验

1. 对纯 `strlen` 包装类题目，最小建模足够。

只要调用处显式写：

```c
int ret = strlen(str) /*@ where l = l, n = n */;
```

符号执行即可把返回值 `ret = n` 和输入资源保留下来。

2. `Zlength(l) == n` 对 return 规格桥接很关键。

如果 `problem_23_spec_z` 写成 `output = Zlength input`，manual return 处需要同时知道 `retval = n` 和 `Zlength l = n`。

## C_48 验证记录

### 结论

`C_48` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_48.v
coqc C_48_goal.v
coqc C_48_proof_auto.v
coqc C_48_proof_manual.v
coqc C_48_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_48.v C_48_proof_manual.v
```

无输出。

### 文件变更

- `C_48.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 返回：`true` 对应 `1`，`false` 对应 `0`。
  - 将 `size_t` 改为 `int`，便于 QCP 处理索引和溢出条件。
  - 循环 invariant 维护：
    - `0 < n`、`Zlength(l) == n`。
    - 双指针关系 `i + j == n - 1`。
    - 当前边界 `0 <= i <= n`、`0 <= j < n`。
    - 只读输入资源 `CharArray::full(text, n + 1, app(l, cons(0, nil)))`。
    - 已检查区域性质：`forall k, 0 <= k < i -> Znth k l 0 = Znth (n - 1 - k) l 0`。
- `coins_48.v`
  - `Load "../spec/48".`
  - 新增 C 层 `palindrome_z`，使用 `k < Zlength input - 1 - k` 表示只检查左半边，避免在 VC 中处理除法。
  - `problem_48_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_48_pre/spec`。
  - `ascii_range_z input` 放在 `C_48.c` 的 `Require` 和循环 invariant 中；C 层 `palindrome_z` 只作为内部桥接引理前提，不出现在最终 wrapper 定义里。
  - 新增三个 return 桥接引理：
    - `problem_48_spec_z_empty`
    - `problem_48_spec_z_true`
    - `problem_48_spec_z_false`
- `C_48_goal.v` / `C_48_proof_auto.v` / `C_48_proof_manual.v` / `C_48_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。

### 经验

1. 回文规格在 C 层避免使用 `length / 2` 更顺滑。

原始 `spec/48.v` 用 `String.length input / 2`。C 层循环不变式仍可用更适合双指针证明的等价形式：

```coq
k < Zlength input - 1 - k
```

这样 loop exit 时从 `i >= j` 和 `i + j = n - 1` 可以直接用 `lia` 推出任意待检查 `k` 已经落入 `k < i` 的已验证区域。

返工到原 spec 时，再用 `half_index_mirror_z` 和 `mirror_index_half_nat` 在 `nat` 的 `length / 2` 与 `Z` 的 `k < n - 1 - k` 之间转换。

2. 双指针 invariant 的核心是 `i + j == n - 1`。

它同时服务三件事：

- 读 `text[i]` / `text[j]` 的边界证明。
- mismatch 分支把当前 `i` 映射成规格里的反例位置。
- 正常退出时从 `i >= j` 推出所有左半边位置都已检查。

3. 读取字符时，VC 中的值来自带终止符的数组。

分支条件形如：

```coq
Znth i (app l (cons 0 nil)) 0 = Znth j (app l (cons 0 nil)) 0
```

而规格使用 payload `l`。manual 中需要在 `i < n`、`j < n` 下用：

```coq
rewrite app_Znth1 in H by lia.
rewrite app_Znth1 in H by lia.
```

把等式或不等式转回 `Znth i l 0` / `Znth j l 0`。

4. 空串分支单独用引理处理更干净。

`strlen` 返回 `0` 时直接 `return 1`，对应 `problem_48_spec_z_empty`。该引理只需用 `Zlength input = 0` 证明 `palindrome_z` vacuous。

## C_66 验证记录

### 结论

`C_66` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_66.v
coqc C_66_goal.v
coqc C_66_proof_auto.v
coqc C_66_proof_manual.v
coqc C_66_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_66.v C_66_proof_manual.v
```

无输出。

### 文件变更

- `C_66.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `strlen(s)` 提前保存为 `int n`，避免在循环条件中重复调用外部函数；核心求和逻辑不变。
  - 循环 invariant 维护 `sum == sum_upper_upto(i, l)` 和只读输入资源。
  - `ascii_range_z(l)` 写在函数 `Require` 和循环 invariant 中，作为 `string_of_list_z` 的底层字符表示条件。
  - 前置条件加入 `digit_sum_int_range(l)`，用于证明 `sum + s[i]` 不溢出。
- `coins_66.v`
  - `Load "../spec/66".`
  - `problem_66_pre_z(s) := problem_66_pre (string_of_list_z s)`。
  - `problem_66_spec_z(s, output) := problem_66_spec (string_of_list_z s) (Z.to_nat output)`，只做格式转换并直接调用原 spec。
  - 新增 `is_upper_z`、`sum_upper_upto` 及 `sum_upper_list_z_correct`，用于从 C 层前缀求和推出原始 `digitSum_impl`。
  - 新增 `sum_upper_upto_step_upper` / `sum_upper_upto_step_not_upper` 支持循环分支推进。

### 经验

1. 前缀累计类字符串循环可以复用数组求和题的形状。

核心 invariant：

```c
0 <= i && i <= n &&
sum == sum_upper_upto(i, l) &&
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

2. 外部函数调用的 ghost 参数不要和局部变量重名。

最初写成 `With l n` 且局部变量也叫 `n`，`strlen` 调用处 prefill 失败。改为：

```c
/*@ With l len */
int n = strlen(s) /*@ where l = l, n = len */;
```

即可稳定生成 VC。

3. 分支条件来自带终止符数组，进入 step 引理前要改回 payload。

manual 中典型写法：

```coq
rewrite app_Znth1 in * by lia.
rewrite sum_upper_upto_step_upper by lia.
```

4. 对涉及累加的题，建议单独建模安全前提。

`digit_sum_int_range(l)` 同时给出当前累计值和执行加法后的范围，专门服务 `sum = sum + s[i]` 的 C int 安全 VC。

## C_80 验证记录

### 结论

`C_80` 已按用户许可修复原 C 后完成原 spec 直连验证。

已通过的验收链：

```bash
coqtop -quiet -l QCP_examples/humaneval/spec/80.v
coqc coins_80.v
coqc C_80_goal.v
coqc C_80_proof_auto.v
coqc C_80_proof_manual.v
coqc C_80_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_80.v C_80_proof_manual.v
```

无输出。

### 文件变更

- `C_80.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 返回：`true` 对应 `1`，`false` 对应 `0`。
  - 修复原 C 语义缺陷：长度至少为 3 时先检查 `s[0] != s[1]`，避免 `"aab"` 这类第一组三字符漏检。
  - 循环中继续检查 `s[i] != s[i-1]` 与 `s[i] != s[i-2]`，并在 invariant 中维护 `happy_prefix_z(i, l)` 与 `happy_adjacent_z(i, l)`，共同表示已覆盖窗口的三对字符都不同。
- `coins_80.v`
  - `Load "../spec/80".`
  - `problem_80_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_80_pre/spec`。
  - `ascii_range_z` 不写入 wrapper，只作为 C annotation 表示条件；用于把 C 层 `Znth` 不等式桥接到原 spec 的 `String.get` / `ascii` 不等式。
  - 新增 `happy_prefix_z` / `happy_adjacent_z` 支持循环初始化与推进。
  - 新增 `problem_80_spec_z_short`、`problem_80_spec_z_false_first_pair`、`problem_80_spec_z_false_prev1`、`problem_80_spec_z_false_prev2`、`problem_80_spec_z_true` 处理五类返回。

### 经验

1. 修复第一组三字符的漏检后，循环 invariant 要额外保存相邻前两字符不同。

原 C 只检查：

```c
if (s[i] == s[i - 1]) return 0;
if (s[i] == s[i - 2]) return 0;
```

这不能覆盖第一组三元组里的 `s[0] != s[1]`。修复后在进入循环前增加：

```c
if (s[0] == s[1]) return 0;
```

并在循环 invariant 中维护：

```coq
happy_adjacent_z i l
```

表示进入当前 `i` 时，`s[i-1] != s[i-2]` 已知。

2. 三字符窗口检查适合用“已检查前缀”谓词。

```coq
Definition happy_prefix_z (i : Z) (s : list Z) : Prop :=
  forall k, 2 <= k < i -> happy_window_end_z k s.
```

`happy_window_end_z k s` 包含三对不等式：`k` 与 `k-1`、`k` 与 `k-2`、`k-1` 与 `k-2`。每次循环 step 用两个新分支条件加旧的 `happy_adjacent_z i l` 推进完整窗口事实。

3. 对同一个 `app(l,[0])` 里多个 `Znth`，可能需要 `repeat rewrite`。

`i - 1`、`i - 2` 位置都在 payload 内时：

```coq
repeat rewrite app_Znth1 in * by lia.
```

比单次 `rewrite` 更稳。

## C_56 验证记录

### 结论

`C_56` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_56.v
coqc C_56_goal.v
coqc C_56_proof_auto.v
coqc C_56_proof_manual.v
coqc C_56_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_56.v C_56_proof_manual.v
```

无输出。

### 文件变更

- `C_56.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 返回：`true` 对应 `1`，`false` 对应 `0`。
  - 将 `strlen(brackets)` 保存为局部 `n`。
  - 将两个独立字符判断改成等价的 `if / else if`，便于减少不可达分支 VC。
  - 为纯原 spec 桥接补充 `ascii_range_z(l)`，放在函数 `Require` 和循环 invariant 中；不写进最终 wrapper。
  - 循环 invariant 维护 `level == angle_level_upto(i, l)`、`angle_nonnegative_prefix(i, l)`，以及 `0 <= level <= i`。
- `coins_56.v`
  - `Load "../spec/56".`
  - `problem_56_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_56_pre/spec`；`spec_z` 只做 `string_of_list_z` 和 `bool_of_z` 转换。
  - 新增 `angle_delta`、`angle_level_upto`、`angle_nonnegative_prefix` 和 `angle_balanced_z`。
  - 新增 `check_angle_aux_z` 和 `correct_bracketing_aux_check_angle`，在 `ascii_range_z` 前提下证明 C 层 level checker 与原始 `correct_bracketing_aux` 一致。
  - 新增 open/close step 引理和 return 桥接引理；C 层 level 条件只作为内部证明前提使用。

### 经验

1. 括号匹配类题目的 C 层规格适合用“level 最终为 0 + 所有前缀非负”。

```coq
Definition angle_balanced_z (l : list Z) : Prop :=
  angle_level_upto (Zlength l) l = 0 /\
  angle_nonnegative_prefix (Zlength l) l.
```

2. 除语义不变式外，必须保留数值安全不变式。

`level == angle_level_upto(i,l)` 不足以证明 C 层 `level + 1` / `level - 1` 安全。循环 invariant 中额外加入：

```c
0 <= level && level <= i
```

生成的 safety VC 就能自动或用 `lia` 解决。

3. 字符范围前提可以消掉“不可能字符”分支。

纯原 `problem_56_pre_z` 只约束 `string_of_list_z l` 里的 `ascii` 字符；需要结合 `ascii_range_z(l)`，通过 `problem_56_pre_z_char` 才能推出底层 `Znth i l 0` 必为 `60` 或 `62`。在 neither-branch 的 manual 中：

```coq
repeat rewrite app_Znth1 in * by lia.
destruct (problem_56_pre_z_char l i Hrange Hpre ltac:(lia)) as [Hopen | Hclose];
congruence.
```

4. return 处要注意 `Zlength l` 和局部 `len` 的方向。

目标通常是 `angle_level_upto (Zlength l) l = 0`，上下文里是 `Zlength l = len` 和 `0 = angle_level_upto len l`，证明时先 `rewrite Hlen` 再 `symmetry`。

5. 括号匹配返工到原 spec 时，先桥接两个 checker。

最终 wrapper 是：

```coq
problem_56_spec (string_of_list_z brackets) (bool_of_z output)
```

内部证明保留 C 层 level 模型；用 `correct_bracketing_aux_check_angle` 连接原始递归 checker 和 `check_angle_aux_z`，再用 `check_angle_aux_z_true/sound_*` 连接 level 的最终为 0、前缀非负、负前缀和最终非 0 三类 return 情况。

## C_61 验证记录

### 结论

`C_61` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_61.v
coqc C_61_goal.v
coqc C_61_proof_auto.v
coqc C_61_proof_manual.v
coqc C_61_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_61.v C_61_proof_manual.v
```

无输出。

### 文件变更

- `C_61.c`
  - 与 `C_56.c` 使用同一验证结构。
  - 字符编码改为 `40` (`(`) 和 `41` (`)`)。
- `coins_61.v`
  - 与 `coins_56.v` 同构，定义 `paren_delta`、`paren_level_upto`、`paren_nonnegative_prefix` 和 `paren_balanced_z`。
- `C_61_proof_manual.v`
  - 由 `C_56` manual proof 机械替换得到，并经全链编译确认。

### 经验

`C_56` 的 level-prefix 模板可以直接复用到同构 bracket 题。需要同步替换：

- 规格名：`problem_56_*` -> `problem_61_*`
- 前缀函数：`angle_*` -> `paren_*`
- 字符码：`60/62` -> `40/41`
- goal import：`C_56_goal` -> `C_61_goal`

## C_78 验证记录

### 结论

`C_78` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_78.v
coqc C_78_goal.v
coqc C_78_proof_auto.v
coqc C_78_proof_manual.v
coqc C_78_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_78.v C_78_proof_manual.v
```

无输出。

### 文件变更

- `C_78.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `strchr(key, num[i]) != NULL` 展开为固定 ASCII 字符比较：`2/3/5/7/B/D`。
  - `ascii_range_z(l)` 写在函数 `Require` 和循环 invariant 中，作为 `string_of_list_z` 的底层字符表示条件。
  - 循环 invariant 维护 `out == count_prime_hex_upto(i, l)`，并保留输入 `CharArray::full`。
- `coins_78.v`
  - `Load "../spec/78".`
  - `problem_78_pre_z/spec_z` 只做格式转换并直接调用原始 `problem_78_pre/spec`。
  - 新增 `is_prime_hex_z`、`count_prime_hex_upto` 和 `count_prime_hex_list_z_correct`，用于从 C 层前缀计数推出原始 `hex_key_impl`。
  - 新增 hit/miss step 引理，用于循环分支推进。
- `C_78_proof_manual.v`
  - 对命中分支抽出本地 tactic `solve_hex_hit`，miss 分支使用 `count_prime_hex_upto_step_miss`。
  - return 处把 `i = len` 与 `Zlength l = len` 桥接到最终规格。

### 经验

1. 固定集合查询比调用 `strchr` 更适合当前字符串验证流程。

原始 `strchr("2357BD", c)` 的语义需要额外建模库函数和常量字符串资源。对于这种固定短集合，展开成等价字符比较可以保持核心语义不变，同时把 VC 化成普通 `Znth` 相等/不等式。

2. 计数类题目可以复用“前缀计数 + hit/miss step”模板。

循环 invariant 中保存：

```c
out == count_prime_hex_upto(i, l)
```

命中分支用 `count_prime_hex_upto_step_hit`，否则用 `count_prime_hex_upto_step_miss`。多个命中分支可用一个本地 tactic 统一处理。

## C_64 验证记录

### 结论

`C_64` 已完成纯原 spec wrapper 返工并通过完整验证。

已通过的验收链：

```bash
coqc coins_64.v
coqc C_64_goal.v
coqc C_64_proof_auto.v
coqc C_64_proof_manual.v
coqc C_64_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_64.v C_64_proof_manual.v
```

无输出。

### 文件变更

- `C_64.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将普通元音集合查询展开为 ASCII 字符比较。
  - `ascii_range_z(l)` 写在函数 `Require` 和循环 invariant 中，作为 `string_of_list_z` 的底层字符表示条件。
  - 循环 invariant 维护 `count == count_regular_vowels_upto(i, l)`；循环后保留原程序对末尾 `y/Y` 的额外计数逻辑。
- `coins_64.v`
  - `Load "../spec/64".`
  - `problem_64_pre_z/spec_z` 只做格式转换并直接调用原始 `problem_64_pre/spec`。
  - 新增 `is_regular_vowel_z`、`count_regular_vowels_upto`、`last_y_add` 和 `vowels_count_model_correct`，用于证明 C 层模型等价于原始 `vowels_count_func`。
  - 新增普通元音 hit/miss step 引理，以及 `last_y_add_zero/hit/miss` 三类 return 桥接引理。
- `C_64_proof_manual.v`
  - 对十个普通元音命中分支抽出本地 tactic `solve_vowel_hit`。
  - return 分为末尾 `y`、末尾 `Y`、空串/非正长度、不命中四类证明。

### 经验

1. “循环内普通集合计数 + 循环后特殊末尾规则”适合拆成两个规格函数。

```coq
output = count_regular_vowels_upto (Zlength s) s + last_y_add s
```

这样循环只维护普通元音计数，末尾 `y/Y` 的规则集中在 return VC 中处理，避免把最后一个字符的特殊性塞进循环 invariant。

2. 末尾访问的桥接引理要同时带上 `Zlength` 与当前局部长度。

`last_y_add_hit/miss` 使用参数 `n := len`，证明时先把 `Zlength l = len` 代入，再用 `Znth (len - 1)` 的分支事实完成。

## C_98 验证记录

### 结论

`C_98` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_98.v
coqc C_98_goal.v
coqc C_98_proof_auto.v
coqc C_98_proof_manual.v
coqc C_98_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_98.v C_98_proof_manual.v
```

无输出。

### 文件变更

- `C_98.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将原 helper `is_upper_vowel` 展开为固定 ASCII 比较。
  - 将 `i += 2` 的 stride 循环规范化为 `i++` 扫描，并用 `i % 2 == 0` 保留“只计偶数下标”的语义。
  - `ascii_range_z(l)` 写在函数 `Require` 和循环 invariant 中，作为 `string_of_list_z` 的底层字符表示条件。
  - 循环 invariant 维护 `count == count_upper_even_upto(i, l)`，并保留输入 `CharArray::full`。
- `coins_98.v`
  - `Load "../spec/98".`
  - `problem_98_pre_z/spec_z` 只做格式转换并直接调用原始 `problem_98_pre/spec`。
  - 新增 `is_upper_vowel_z`、`is_even_index_z`、`count_upper_even_upto` 和 `count_upper_even_upto_nat_correct`，用于证明 C 层计数模型等价于原始 `count_upper_impl` 中的 `String.get/seq/filter` 定义。
  - 注意 C 的 `%` 对应生成目标中的 `Z.rem`，偶数下标谓词应使用 `Z.rem i 2`，不要误用 `Z.modulo`。
- `C_98_proof_manual.v`
  - 五个命中分支共用 `solve_upper_hit`。
  - 偶数非元音分支使用 `count_upper_even_upto_step_even_miss`。
  - 奇数分支使用 `count_upper_even_upto_step_odd`。

### 经验

1. 对偶数下标计数，逐下标扫描比直接证明 `i += 2` 更稳。

直接维护 stride 循环需要在 Coq 中处理 `Z.to_nat (i + 2)`、`Pos.of_succ_nat` 和奇偶编码，证明成本明显上升。改成：

```c
for (i = 0; i < n; i++) {
    if (i % 2 == 0) { ... }
}
```

可观察语义仍是偶数下标计数，循环 step 也变成普通的 `i + 1`。

2. C `%` 生成的是 `Z.rem` 风格目标。

如果 Coq 辅助定义写成 `i mod 2`，manual 中 `assumption` 不能匹配生成目标里的 `i % 2 = 0`。这里统一写：

```coq
Definition is_even_index_z (i : Z) : bool :=
  Z.eqb (Z.rem i 2) 0.
```

## C_124 验证记录

### 结论

`C_124` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_124.v
coqc C_124_goal.v
coqc C_124_proof_auto.v
coqc C_124_proof_manual.v
coqc C_124_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_124.v C_124_proof_manual.v
```

无输出。

### 文件变更

- `C_124.c`
  - 替换为 QCP 头文件并声明 `strlen` 外部规格。
  - 将 `bool` 返回适配为 `int` 的 `1/0`，日期校验规则和所有业务分支保持不变。
  - 将 `strlen(date) != 10` 保存为局部 `n` 后判断，便于实例化 `strlen` 规格。
  - 将 `for (int i = 0; ...)` 改为使用已有局部 `i` 的 `for (i = 0; ...)`，这是 QCP 解析适配。
  - 将字符常量写成 ASCII 数值 `45/48/57`，语义等价。
  - 删除原程序中计算后完全未使用的 `yy`，并把 `mm/dd` 声明移动到首次赋值处，避免早退路径清理未初始化局部权限；不改变返回结果。
- `coins_124.v`
  - `Load "../spec/124".`
  - 新增 `date_prefix_valid`、`date_format_z`、`month_z/day_z`、`days_in_month_z` 和 `valid_date_z`。
  - 新增前缀格式推进、固定位置数字/分隔符、月份/日期范围等局部引理。
- `C_124_proof_manual.v`
  - 安全 VC 使用前缀格式事实推出固定位置字符是数字，从而证明解析月份/日期不会溢出。
  - return VC 分为合法返回、长度不为 10、格式错误、月份越界、日期越界、大小月/FEB 特判等情况。

### 经验

1. 固定长度格式校验适合用“已检查前缀”谓词。

```coq
Definition date_prefix_valid (i : Z) (l : list Z) : Prop :=
  forall k, 0 <= k < i -> date_char_valid k l.
```

循环每次只推进当前下标的格式事实；退出后由 `i = 10` 得到完整 `date_format_z`。

2. 早退路径会暴露未参与断言的局部变量权限问题。

原程序的 `yy` 只计算不使用。早退路径上 QCP 会尝试清理局部变量权限，死代码局部容易造成 `Fail to Remove Memory Permission`。删除无可观察效果的 `yy`，并把 `mm/dd` 的声明移到实际赋值处，可以保持业务逻辑不变同时让符号执行稳定。

3. 这题没有改日期判断规则。

所有 `mm/dd` 范围判断、大小月判断和 2 月 29 日规则都保持原程序逻辑。改动只属于 QCP 适配或死代码/局部变量生命周期整理。

## C_11 验证记录

### 结论

`C_11` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_11.v
coqc C_11_goal.v
coqc C_11_proof_auto.v
coqc C_11_proof_manual.v
coqc C_11_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_11.v C_11_proof_manual.v
```

无输出。

本轮按用户要求暂不删除编译产物和备份文件；后续清理时再删除 `.aux/.glob/.vo/.vok/.vos` 与 `C_11_proof_manual_backup*.v` 等产物。

### 文件变更

- `C_11.c`
  - 将原始 libc 程序改写为 QCP 可接受的形式。
  - 使用 `verification_stdlib.h`、`verification_list.h`、`char_array_def.h`。
  - 声明 `malloc_char_array`，后置条件返回 `CharArray::undef_full(__return, n)`。
  - 声明 `strlen`，用 `CharArray::full(s, n + 1, app(l, cons(0, nil)))` 表示以 `0` 结尾的字符串。
  - 函数前置条件加入 `Zlength(l1) == na`、`Zlength(l2) == nb`、`na == nb`、`problem_11_pre_z(l1, l2)`，并把 `ascii_range_z(l1/l2)` 作为 C 字符数组表示条件写在 annotation 中。
  - 函数后置条件返回 `out_l` 和 `n`，并要求 `problem_11_spec_z(l1, l2, out_l)`。
  - 原始 `size_t` 改为 `int`，便于 QCP 处理整数范围和数组索引。
  - 原始三目表达式 `a[i] == b[i] ? '0' : '1'` 改为显式 `if`，并使用 ASCII 数值 `48` / `49`。
  - 原始 `'\0'` 改为 `0`。
  - 循环 invariant 维护已经写出的前缀 `out_l`，以及每个位置满足 XOR 规则。
- `coins_11.v`
  - `Load "../spec/11".`
  - 复用 `string_bridge.v` 的 `string_of_list_z`，把 C 层 `list Z` 字符数组映射到原始 Coq `string`。
  - `problem_11_pre_z/spec_z` 均为纯原 spec wrapper，只调用原始 `problem_11_pre/spec`。
  - `problem_11_spec_z_intro` 从循环 invariant 里的逐点性质推出原始 string 规格；底层 `48/49` 事实由原 pre 加 `ascii_range_z` 推出，而不写进 wrapper。
- `C_11_goal.v` / `C_11_proof_auto.v` / `C_11_proof_manual.v` / `C_11_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。
  - 注意本目录当前生成文件命名是 `C_11_proof_auto.v` / `C_11_proof_manual.v`，而不是部分旧文档中的 `C_11_auto.v` / `C_11_manual.v`。

### 遇到的问题

1. QCP 注解中直接使用原始 `spec/11.v` 的 Coq `string` 规格不方便。

原因：C 侧字符串用 `CharArray::full` 表示为 `list Z` 加结尾 `0`，而 `spec/11.v` 中的 `problem_11_pre/spec` 是基于 Coq `string`。QCP 注解和 VC 里直接桥接 `string` 会让目标复杂很多。

解决方式：在 `coins_11.v` 中定义面向 C 字符数组的纯原 wrapper，wrapper 本身只调用原始规格；`list Z` 逐点 XOR 条件只作为循环 invariant 和内部 bridge lemma 前提。

2. `'0'/'1'` 输入域可以直接给出 `ascii` 单射。

原始 spec 在 `String.get` 层比较 `ascii`，C 层 invariant 比较 `Znth` 的整数值。纯原 `problem_11_pre_z` 只约束转换后的 string 是 `'0'/'1'`；再结合 annotation 中的 `ascii_range_z`，`problem_11_pre_z_left_binary/right_binary` 可以推出底层字符确实是 `48/49`，随后 `ascii_of_z_inj_binary` 把 `ascii` 相等安全地反推为整数相等。

3. 原始程序里的三目表达式和字符字面量不适合直接交给 QCP。

原始写法：

```c
output[i] = (a[i] == b[i]) ? '0' : '1';
output[n] = '\0';
```

解决方式：

```c
if (a[i] == b[i]) {
    output[i] = 48;
} else {
    output[i] = 49;
}
output[n] = 0;
```

这样生成的 VC 分支更清晰，循环 invariant 也可以直接写 `48` / `49`。

4. `malloc` 结果必须建模为未初始化数组。

问题：程序随后逐位写入 `output[i]`。如果 malloc 后置条件直接给 `CharArray::full`，写入时资源形状不匹配。

解决方式：

```c
Ensure __return != 0 && CharArray::undef_full(__return, n)
```

循环 invariant 中维护：

```c
CharArray::full(output, i, out_l) *
CharArray::undef_seg(output, i, n + 1)
```

5. 初始循环 invariant 需要把 `undef_full` 拆成空前缀和未初始化段。

manual 中使用：

```coq
sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (na + 1)).
rewrite (CharArray.undef_seg_empty retval 0).
rewrite (CharArray.full_empty retval 0).
```

同时因为 `n` 最终化简到 `na`，需要重写长度等式，避免 `&( "n" ) # Int |-> Zlength l2` 和 `&( "n" ) # Int |-> na` 不匹配。

6. 循环分支的手工证明要根据写入字符分别追加 `48` / `49`。

相等分支：

```coq
Exists (app out_l_2 (cons 48 nil)).
```

不相等分支：

```coq
Exists (app out_l_2 (cons 49 nil)).
```

证明逐点性质时，对 `k < i` 使用旧 invariant，对 `k = i` 使用当前分支条件和刚追加的字符。

7. `++` 会被 `string_scope` 抢走。

表现：Coq 报 `out_l_2` 类型是 `list Z`，但期望 `string`。

解决方式：在 manual 中不用 `++`，改写成显式 `app out_l_2 (cons 48 nil)` / `app out_l_2 (cons 49 nil)`。

8. `app_Znth2` 后不一定能直接 `rewrite Zlength_cons`。

表现：Coq 报找不到 `Zlength (? :: ?)` 子项。

解决方式：先用循环长度事实把索引差化成 `0`：

```coq
rewrite app_Znth2 by lia.
replace (i - Zlength out_l_2) with 0 by lia.
rewrite Znth0_cons.
```

9. return 处 `CharArray.full` 的长度需要显式对齐。

表现：目标需要 `CharArray.full output (na + 1) ...`，上下文里可能是 `CharArray.full output (Zlength out_l_2 + 1) ...`。

解决方式：

```coq
assert (Hout_len : Zlength out_l_2 = na) by lia.
rewrite Hout_len.
```

然后使用 `problem_11_spec_z_intro` 将循环维护的逐点 XOR 性质推出最终 `problem_11_spec_z`。

10. 验证完成后的清理需要包含隐藏 `.aux` 文件。

Coq 编译会生成隐藏文件，例如：

```text
.C_11_goal.aux
.C_11_proof_auto.aux
.C_11_proof_manual.aux
.C_11_goal_check.aux
.coins_11.aux
```

这些也属于编译产物，验证完成后需要删除。此规则已同步补充到 `../SKILL.md` 的清理编译产物章节。

### 关键引理和脚本片段

`problem_11_spec_z_intro` 是 return 处的核心桥接引理：

```coq
Lemma problem_11_spec_z_intro :
  forall a b output n,
    problem_11_pre_z a b ->
    Zlength a = n ->
    Zlength b = n ->
    Zlength output = n ->
    (forall k,
      0 <= k < n ->
      ((Znth k a 0 = Znth k b 0 /\ Znth k output 0 = 48) \/
       (Znth k a 0 <> Znth k b 0 /\ Znth k output 0 = 49))) ->
    problem_11_spec_z a b output.
```

循环推进中追加一个字符的典型证明结构：

```coq
Exists (app out_l_2 (cons 48 nil)).
pre_process.
rewrite (Zlength_app_cons out_l_2 48).
entailer!.
intros k Hk.
destruct (Z_lt_ge_dec k i).
- rewrite app_Znth1 by lia.
  apply H13. lia.
- assert (k = i) by lia. subst k.
  rewrite app_Znth2 by lia.
  replace (i - Zlength out_l_2) with 0 by lia.
  rewrite Znth0_cons.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  left; split; auto.
```

return 处典型证明结构：

```coq
Right.
Exists out_l_2 na.
pre_process.
assert (Hi : i = na) by lia.
subst i.
assert (Hout_len : Zlength out_l_2 = na) by lia.
rewrite Hout_len.
rewrite (CharArray.undef_seg_empty output (na + 1)).
entailer!.
apply problem_11_spec_z_intro with (n := na); try lia.
try assumption.
intros k Hk.
apply H12. lia.
```

### 剩余注意事项

- 当前完整验证已经直接覆盖原始 `spec/11.v` 的 `problem_11_pre/spec`；C 层 `list Z` 规格只作为循环 invariant 和表示桥接的中间条件保留。
- `C_11_proof_auto.v` 是生成的 auto 文件，里面可能保留生成器产生的 `Admitted.`；验收扫描按当前流程检查 `coins_11.v` 和 `C_11_proof_manual.v`。

## C_67 fruit_distribution 验证记录

状态：已完成原 spec 直连端到端验证。

涉及文件：

- `../spec/67.v`
- `C_67.c`
- `coins_67.v`
- `C_67_goal.v`
- `C_67_proof_auto.v`
- `C_67_proof_manual.v`
- `C_67_goal_check.v`

已通过的验收链：

```bash
coqtop -quiet -l QCP_examples/humaneval/spec/67.v
coqc coins_67.v
coqc C_67_goal.v
coqc C_67_proof_auto.v
coqc C_67_proof_manual.v
coqc C_67_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_67.v C_67_proof_manual.v
```

无输出。

### 语义与适配

1. 未修改原 C 核心业务逻辑。

原程序语义是扫描字符串中的前两个连续数字段，最终返回 `total - num1 - num2`。QCP 适配只做了：

- 替换验证头文件和 `CharArray` 内存规格。
- 将 `strlen(s)` 缓存为 `slen`，避免循环条件反复调用外部函数规格。
- 增加 `total == total@pre` 到循环不变式，保证最终返回表达式使用的整数参数和函数后置规格中的旧参数一致。
- 使用 ASCII 数字范围 `48..57` 表示 `'0'..'9'`。

2. `../spec/67.v` 中的原 pre 已按用户确认收紧。

原 `problem_67_pre=True` 会让不符合固定格式的字符串也进入规格，但 `problem_67_spec` 要求存在 `"<apples> apples and <oranges> oranges"` 分解。现在 `problem_67_pre` 只要求输入满足数字 fruit string 格式；`problem_67_spec` 保持原定义，C 风格扫描结果是否满足原 spec 由 `coins_67.v` 中的 bridge lemma 证明。

`../spec/67.v` 只保留原 helper、`problem_67_pre` 和 `problem_67_spec` 的定义，不放 bridge lemma 或证明。

3. `coins_67.v` 的最终 wrapper 已经直连原 pre/spec。

```coq
Definition problem_67_pre_z (s : list Z) (total : Z) : Prop :=
  problem_67_pre (string_of_list_z s) (Z.to_nat total).

Definition problem_67_spec_z (s : list Z) (total output : Z) : Prop :=
  problem_67_spec (string_of_list_z s) (Z.to_nat total) (Z.to_nat output).
```

`ascii_range_z`、`fruit_state_safe_z` 和 `fruit_output_safe_z` 只作为 C annotation 的表示/安全条件，不写进最终 wrapper。

4. C 层扫描模型只用于 bridge lemma。

`fruit_num1_prefix_z`、`fruit_num2_prefix_z`、`fruit_cur_prefix_z` 用三元状态描述扫描到前缀 `i` 后的两个已提交数字段和当前数字段；`fruit_output_z` 在循环结束后执行最后一次 flush，再把缺失数字段补成 `0`。

return 处通过 `problem_67_spec_z_intro` 把 `fruit_output_z` 桥接回原始 `problem_67_spec`。

### 证明经验

1. 返回规格里涉及未修改的值参数时，循环不变式要显式保留旧值和入口数值条件。

本例如果缺少：

```c
total == total@pre
0 <= total
```

否则 return VC 会把 `total_pre` 和当前栈里的 `total` 分开，或者丢失 `Z.to_nat total` 桥接所需的非负事实。

2. 重新 symexec 后必须先重新编译 `C_XX_goal.v`。

本例一度出现 `C_67_goal.v` 已更新但 `.vo` 仍是旧版本，导致 `C_67_proof_manual.v` 导入 stale goal，表现为 return VC 仍有旧的 `total/total_pre` 脱节。正确顺序是：

```bash
coqc coins_67.v
coqc C_67_goal.v
coqc C_67_proof_auto.v
coqc C_67_proof_manual.v
coqc C_67_goal_check.v
```

3. `string_scope` 会干扰布尔比较 notation。

manual proof 中不要写依赖 scope 推断的 `x <=? y` / `x <? y` 匹配，直接匹配 `Z.leb x y` / `Z.ltb x y` 更稳：

```coq
match goal with
| H : x <= y |- context[Z.leb x y] =>
    replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
end.
```

4. 对循环 step 的三个状态分量，不要直接 `rewrite fruit_prefix_step`。

`fruit_prefix_step` 给的是三元组等式：

```coq
(fruit_num1_prefix_z (i + 1) l,
 fruit_num2_prefix_z (i + 1) l,
 fruit_cur_prefix_z (i + 1) l) = ...
```

而 VC 里通常是三个分量的独立等式。做法是 `pose proof` 出三元组等式，展开 `fruit_step_z` 后化简布尔分支，再 `inversion` 得到各分量等式。

5. 输出溢出检查不要在 `entailer!` 前展开大规格。

先让 `entailer!` 去掉空间资源并留下纯算术目标，再从 `fruit_output_safe_from_pre` 取出 bounds，结合当前分支证明 `fruit_final_num1_z/fruit_final_num2_z` 的值。这样比把 `fruit_output_safe_z` 全部展开后交给 `entailer!` 更稳定。

## C_27 filp_case 验证记录

状态：已完成端到端验证。

涉及文件：

- `C_27.c`
- `coins_27.v`
- `C_27_goal.v`
- `C_27_proof_auto.v`
- `C_27_proof_manual.v`
- `C_27_goal_check.v`

### 语义与适配

1. 未修改原 C 核心业务逻辑。

原程序逐字符扫描输入字符串，小写 `a..z` 转大写，大写 `A..Z` 转小写，其它字符保持不变，分配新字符串并补 `0` 终止符返回。QCP 适配只做了：

- 替换验证头文件和 `CharArray` 内存规格。
- 给 `malloc_char_array`、`strlen` 添加验证规格。
- 将局部 `char w` 适配为 `int w`，并用 ASCII 常量 `65/90/97/122/32` 表示字符范围和大小写偏移，避免 QCP/C 字符类型与算术比较混用造成证明噪声。
- 保留原函数名 `filp_case`，未修正拼写，以免改变导出符号。

2. `coins_27.v` 使用 `list Z` 字符模型。

`flip_char_z` 精确描述 C 分支行为；`char_range_z` 约束输入字符在 `0..127`，用于证明非字母字符经 `signed_last_nbits _ 8` 后保持原值。

返工后 `problem_27_pre_z` 直接调用原始 `problem_27_pre (string_of_list_z input)`，`problem_27_spec_z` 只调用原始 `problem_27_spec (string_of_list_z input) (string_of_list_z output)`。C 层点态 `flip_char_z` 条件只保留在内部桥接引理 `problem_27_spec_z_intro` 的前提中，不再出现在最终 wrapper 定义里。

### 证明经验

1. 输出字符串循环不变式使用“已写前缀 + 未写后缀”。

本例 invariant 中保留：

```c
CharArray::full(out, i, out_l) *
CharArray::undef_seg(out, i, n + 1)
```

并用点态性质说明 `out_l` 的每个位置等于 `flip_char_z` 后的输入字符。写入 `out[i]` 后，manual proof 选择 `app out_l (cons v nil)` 作为新前缀 witness。

2. 对 step VC，先拆 pure 条件再选 witness。

如果直接在未 `pre_process` 的分离逻辑蕴含里匹配 `Zlength out_l = i` 和前缀假设，会匹配失败。稳定顺序是：

```coq
pre_process;
repeat rewrite app_Znth1 in * by lia;
Exists (app out_l (cons v nil));
entailer!.
```

随后分别证明追加后点态性质和 `Zlength_app/Zlength_cons/Zlength_nil` 的长度目标。

3. `signed_last_nbits` 需要字符范围假设。

非转换分支生成的写入值可能是：

```coq
signed_last_nbits (Znth i l 0) 8
```

证明前先从 `char_range_z l` 取出 `0 <= Znth i l 0 <= 127`，再用 `signed_last_nbits_eq` 化简；否则 `lia` 没有足够范围信息。

4. 返回 VC 要先统一最终前缀长度。

循环结束时有 `i >= len`、`i <= len` 和 `Zlength out_l = i`，`pre_process` 可能把目标中的长度写成 `Zlength out_l + 1`。先证明并重写 `Zlength out_l = len`，再把 `CharArray.undef_seg out (len + 1) (len + 1)` 化为空段，`entailer!` 才能稳定完成空间目标。

5. 从 C 层字符函数桥接到原 spec 时，分三类证明。

原始 `spec/27.v` 用 `IsLow/Upper`、`IsUp/Lower` 和“既非小写也非大写则保持不变”三个条件描述。桥接时分别证明：

- `IsLow (ascii_of_z c)` 且 `0 <= c <= 127` 推出 `is_lower_z c`，再证明 `Upper (ascii_of_z c) = ascii_of_z (flip_char_z c)`。
- `IsUp (ascii_of_z c)` 同理桥到 `Lower`。
- 两者都不成立时，用 `flip_char_z_other` 证明 C 层结果保持 `c` 不变。

## C_93 encode 验证记录

状态：已完成端到端验证。

涉及文件：

- `C_93.c`
- `coins_93.v`
- `C_93_goal.v`
- `C_93_proof_auto.v`
- `C_93_proof_manual.v`
- `C_93_goal_check.v`

### 语义与适配

1. 未修改原 C 核心业务逻辑。

原程序先对字母翻转大小写，然后判断翻转后的字符是否为元音，若是则再加 `2`。QCP 适配将 `strchr(vowels, w) != NULL` 展开成固定 ASCII 元音比较，等价于原标准库查询，但更适合符号执行。

2. `coins_93.v` 使用纯原 spec wrapper。

`problem_93_pre_z` 只调用原始 `problem_93_pre (string_of_list_z s)`，`problem_93_spec_z` 只调用原始 `problem_93_spec (string_of_list_z input) (string_of_list_z output)`。`encode_char_z` 仍建模 C 层逐点行为，但只作为 `problem_93_spec_z_intro` 的内部前提，不出现在最终 wrapper 定义中。底层字符范围由 `C_93.c` annotation 中的 `ascii_range_z(l)` 提供。

### 证明经验

1. 大分支链适合用统一 tactic。

展开元音判断后会产生 15 个循环 step VC。统一做法是选择 `app out_l [v]` 作为新前缀，再在新增位置展开：

```coq
unfold encode_char_z, swap_case_z, is_vowel_z;
repeat match goal with
| |- context[Z.leb ?x ?y] => destruct (Z.leb_spec x y); simpl
| |- context[Z.eqb ?x ?y] => destruct (Z.eqb_spec x y); simpl
end; lia.
```

2. 输入前置条件可以消掉不可达字符分支。

纯原 `problem_93_pre_z` 只限制转换后的 `string/ascii` 是大小写字母或空格。证明 C 层分支时，需要同时使用 `ascii_range_z(l)`，通过 `problem_93_pre_z_char` 推出底层 `Znth` 也落在字母或空格范围内。对于符号执行中出现的不可达组合，例如字符同时大于 `122`，从该桥接引理取出当前位置字符分类后由 `lia` 关闭。

## C_51 remove_vowels 验证记录

状态：已完成端到端验证。

涉及文件：

- `C_51.c`
- `coins_51.v`
- `C_51_goal.v`
- `C_51_proof_auto.v`
- `C_51_proof_manual.v`
- `C_51_goal_check.v`

### 语义与适配

1. 未修改原 C 核心业务逻辑。

原程序扫描输入字符串，把非元音字符按顺序写入输出。QCP 适配将 `strchr("AEIOUaeiou", text[i]) == NULL` 展开为固定 ASCII 比较；这只是标准库查询的等价展开。

`problem_51_pre_z/spec_z` 已返工为纯原 spec wrapper：pre 只调用原始 `problem_51_pre (string_of_list_z s)`，spec 只调用原始 `problem_51_spec (string_of_list_z input) (string_of_list_z output)`。`char_range_z` 只保留在 C annotation 和内部 bridge lemma 中，用来把底层 `Z` 字符比较接到原始 `is_vowel`。

2. 输出缓冲区的后置条件必须包含剩余空间。

返回字符串的有效长度是 `out_len + 1`，但分配大小是 `len + 1`。因此后置条件写为：

```c
CharArray::full(__return, out_len + 1, app(out_l, cons(0, nil))) *
CharArray::undef_seg(__return, out_len + 1, len + 1)
```

否则 return VC 会多出一段返回缓冲区所有权，无法被丢弃。

### 证明经验

1. 过滤类循环不变式用函数式前缀最稳。

本例 invariant 维护：

```c
Zlength(out_l) == j &&
out_l == remove_vowels_prefix_z(i, l)
```

写入分支用 `remove_vowels_prefix_step` 把 `i + 1` 的过滤前缀化成旧前缀追加当前字符；元音分支则证明前缀保持不变。

2. 写入非元音字符时仍需 `char_range_z`。

`out[j] = c` 会在 VC 中出现 `signed_last_nbits (Znth i l 0) 8`。从 `char_range_z` 取得当前位置字符在 `0..127` 后，用 `signed_last_nbits_eq` 化简回原字符。

## C_140 fix_spaces 验证记录

状态：已完成原 spec 修复后的直连端到端验证。

已通过的验收链：

```bash
coqtop -quiet -l QCP_examples/humaneval/spec/140.v
coqc coins_140.v
coqc C_140_goal.v
coqc C_140_proof_auto.v
coqc C_140_proof_manual.v
coqc C_140_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_140.v C_140_proof_manual.v
```

无输出。

### 语义与适配

1. `../spec/140.v` 已按题意修正。

旧 spec 看到两个连续空格就输出 `dash`，等价于“至少两个空格输出 `-`”。现在使用 pending 空格段长度建模：长度 1 输出 `_`，长度 2 输出 `__`，长度大于 2 输出 `-`。

2. `coins_140.v` 使用纯原 spec wrapper。

```coq
Definition problem_140_pre_z (s : list Z) : Prop :=
  problem_140_pre (string_of_list_z s).

Definition problem_140_spec_z (input output : list Z) : Prop :=
  problem_140_spec (string_of_list_z input) (string_of_list_z output).
```

`fix_spaces_prefix_z` 和 `fix_spaces_pending_z` 只建模 C 层循环状态，不写进最终 wrapper。

3. C 层 invariant 用“已输出前缀 + pending 空格段”。

循环处理到位置 `i` 时，`out_l = fix_spaces_prefix_z i l`，`spacelen = fix_spaces_pending_z i l`，并维护 `k + spacelen <= i`，用于证明输出写入不越界。

## C_127 intersection 验证记录

状态：已完成原 spec 修复后的直连端到端验证。

已通过的验收链：

```bash
coqtop -quiet -l QCP_examples/humaneval/spec/127.v
coqc coins_127.v
coqc C_127_goal.v
coqc C_127_proof_auto.v
coqc C_127_proof_manual.v
coqc C_127_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|^[[:space:]]*Axiom[[:space:]]" coins_127.v C_127_proof_manual.v
```

无输出。

### 语义与适配

1. `../spec/127.v` 已修复解析问题。

原 spec 语义正确，但 `problem_127_pre` 中的 `s1 <= e1 /\ s2 <= e2` 会受后续 `nat_scope` 影响。已将这两个比较显式标成 `%Z`，并在 `ORIGINAL_SPEC_ISSUES_LOG.md` 中记录。

2. `coins_127.v` 使用纯原 pre/spec wrapper。

```coq
Definition problem_127_pre_z (i1 i2 : list Z) : Prop :=
  problem_127_pre (interval_pair_z i1) (interval_pair_z i2).

Definition problem_127_spec_z (i1 i2 : list Z) (output : Z) : Prop :=
  problem_127_spec (interval_pair_z i1) (interval_pair_z i2) (yesno_of_z output).
```

`interval_int_range`、`prime_prefix_z`、`prime_len_z` 只用于 C 层安全性、循环不变式和 proof bridge，不写进最终 wrapper。

3. QCP 适配未改变核心业务语义。

原函数返回 `"YES"` / `"NO"`，验证版返回 `1` / `0`，由 `yesno_of_z` 桥接到原始 string 输出规格。原 `max_int` / `min_int` helper 被展开成显式 `if`，避免未标注函数调用；交集长度和素数判断逻辑保持一致。

### 证明经验

1. 固定长度 int 数组要把入口指针和入口 size 带过早返回和循环。

本例后置条件需要归还入口数组资源：

```c
IntArray::full(interval1, interval1_size, i1) *
IntArray::full(interval2, interval2_size, i2)
```

因此中间 `Assert` 和循环 `Inv Assert` 里必须保留：

```c
interval1 == interval1@pre &&
interval2 == interval2@pre &&
interval1_size == interval1_size@pre &&
interval2_size == interval2_size@pre
```

否则 return VC 中左侧资源是当前 size，右侧资源是入口 size，无法匹配。

2. primality 循环沿用 `C_82` 的前缀不变式。

循环不变式维护：

```c
2 <= i && i <= 46340 &&
prime_prefix_z(i, l)
```

进入循环时用 `prime_prefix_z_2`，未整除分支用 `prime_prefix_z_step` 推进，正常退出用 `prime_len_z_true_from_prefix`，整除早返回用 `prime_len_z_false_divisor`，`l < 2` 分支用 `prime_len_z_false_small`。

3. int 安全性需要单独限制 interval 端点范围。

`interval_int_range` 在 C annotation 中要求两个端点都在 `[-1000000000, 1000000000]`，从而证明 `inter2 - inter1` 落在 `[-2000000000, 2000000000]`，不会溢出 `int`。素数循环中的 `i * i` 通过 `i <= 46340` 保证安全。

4. 生成文件不能手动改；scope 问题应在源 spec/wrapper 侧解决。

本例一开始发现 `C_127_goal.v` 中裸数字 `2` 被按 `nat` 解析，根因不是生成文件本身，而是 `spec/127.v` 中最后打开了 `nat_scope`，通过 `Load "../spec/127"` 影响后续 scope。正确处理方式是修正 `spec/127.v` 的 scope 顺序，让 `Z_scope` 最后打开，然后重新运行 `symexec`。最终保留的 `C_127_goal.v`、`C_127_proof_auto.v`、`C_127_goal_check.v` 均为 `symexec` 原样生成状态，没有手动补丁。

```coq
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope string_scope.
Open Scope Z_scope.
```
