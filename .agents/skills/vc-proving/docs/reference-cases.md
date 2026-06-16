# 参考案例

优先参考本次更新后的 `annotated_simplec` 和 `sac_c_parser` 中的 proof / generated goal。旧 `QCP_demos_LLM` 版本只能作为风格补充，不能作为 array/string builtin 语义依据。

## 普通 separation logic VC

- `SeparationLogic/examples/QCP_demos_LLM/sum_proof_manual.v`
- `SeparationLogic/examples/QCP_demos_LLM/sll_proof_manual.v`
- `SeparationLogic/examples/QCP_demos_LLM/functional_queue_proof_manual.v`

## refinement / safeExec VC

- `SeparationLogic/examples/QCP_demos_LLM/sll_merge_rel_proof_manual.v`
- `SeparationLogic/examples/QCP_demos_LLM/kmp_rel_proof_manual.v`

## Array / String VC

- 数组和字符串 builtin 说明：`.agents/skills/annotation-filling/docs/builtin-array-string-support.md`
- 数组 builtin goal / proof：`annotated_simplec/examples/uint_array_strategy_goal.v`、`annotated_simplec/examples/uint_array_strategy_proof.v`
- 未初始化数组 goal / proof：`annotated_simplec/examples/undef_uint_array_strategy_goal.v`、`annotated_simplec/examples/undef_uint_array_strategy_proof.v`
- 字符串 builtin goal / proof：`sac_c_parser/stringlib_strategy_goal.v`、`sac_c_parser/stringlib_strategy_proof.v`

## 使用建议

- 普通链表、队列目标可模仿对应数据结构案例的证明骨架。
- 数组、字符数组、C 字符串和字符串字面量目标优先看上面的 Array / String VC 入口，不要依赖旧 demo 中的 case-local 策略或旧版字符串建模。
- 遇到 `safeExec`、monad wrapper 或 loop combinator 时，优先对照 refinement 案例，而不是从普通 entailment 证明里生搬 tactic。
