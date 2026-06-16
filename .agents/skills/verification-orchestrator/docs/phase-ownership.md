# Phase Ownership 与回流摘要

这个文件定义主 agent 与 phase subagent 的长期迭代边界。

## 长时间迭代 phase

以下 phase 默认是长时间迭代 phase：

- `annotation`
- `vc-proving`

它们不是“一次给出初版方案”的 phase，而是要在本轮 scratch 上持续迭代，直到拿到可以交给主 agent 的明确结果。

## 谁持有当前 phase

- 一旦主 agent 完成当前轮次的 delegation ticket 并启动绑定 subagent，该 subagent 就是本轮 phase owner。
- 对于 `annotation` / `vc-proving`，phase owner 持有：
  - 本轮 scratch
  - 本轮交互式 MCP 会话
  - 本轮 domain 迭代职责
- 对于 `annotation`，本轮 domain 迭代职责包含 `spec-definition review/edit -> annotation-filling -> annotation-checking`。如果 `annotation-checking` 返回 `failed`，phase owner 必须继续修正 annotation C scratch 或 `annotation_scratch_lib`，而不是把失败候选交给 main 回填或 symexec。
- 对于 `vc-proving`，本轮 domain 迭代职责默认通过脚本化并发 worker pipeline 执行；若已记录 Codex CLI / transport / backend / worker 会话不可恢复，则 phase owner 可保持 ownership 不变，切换到基于 proving scratch 的串行 fallback proof loop。无论哪种模式，main 都不得接管该轮 domain 工作。
- 主 agent 在此期间只做编排动作，不做该 phase 的 domain 分析或交互式推进。

## main-owned phase

以下 phase 默认由主 agent 直接持有，不启动 subagent：

- `intake`
- `goal-frozen`
- `final-check`
- `done`

其中 `final-check` 是正式收尾阶段；main 直接执行结构审计、symexec、coqc、`Admitted` / 额外 `Axiom` review，并维护 `Final Check Checklist`。

## 主 agent 不得做的事

- 不得因为等待时间较长，就频繁催促 subagent“赶紧给结果”。
- 不得因为 subagent 尚未完成，就强行中断它并改由 main 线程继续同一 phase 的 domain 工作。
- 不得把 subagent 的“第一版尝试”视为 main 可以立即接手的半成品。

## 允许结束当前轮次的条件

当前轮次只应在以下情况之一发生时结束：

- `completed`
  - subagent 已完成本轮迭代，返回可交由主 agent 正式集成的结果。
- `blocked`
  - subagent 已完成当前轮次能做的工作，但发现缺少上游修正、输入补充或 phase 回退。
- `stale`
  - 当前轮次输入已被上游变化作废。
- user redirect / cancel
  - 用户显式要求停止或改向。
- unrecoverable tool/session failure
  - 当前交互式工具或会话已无法继续，且不能在当前轮次内部恢复。

注意：

- 即使发生工具失败，主 agent 也应优先重开同名 subagent 轮次，而不是直接在 main 线程接管该 phase。

## `Subagent Return Report`

长时间迭代 phase 在返回主 agent 时，应使用结构化结果：

- `round_outcome`
  - `completed` | `blocked` | `stale`
- `summary`
  - 本轮实际完成了什么
- `ready_for_main`
  - 哪些 patch / proof / lemma 已可由主 agent 正式回填
- `annotation_checking_status`
  - 对 `annotation` 来说，必须是 `passed` 才能把 annotation patch 标为 ready for main；`failed` 时本轮应继续停留在 annotation phase
- `ready_for_main_common_case_formal_lib_spec_update`
  - 对 `annotation` 来说，哪些 `annotation_scratch_lib` spec 定义可由主 agent 回填；若非空，main 必须回填 `common_case_formal_lib` 并刷新 frozen prefix 后再 symexec
- `ready_for_main_proof_manual`
  - 对 `vc-proving` 来说，哪些 witness proofs 可直接回填到正式 `*_proof_manual.v`
- `ready_for_main_common_case_formal_lib_append`
  - 对 `vc-proving` 来说，哪些 migrated helper-suffix imports 与 helper lemmas 可从 `task_local_scratch_lib` 回填到 `common_case_formal_lib` 冻结前缀之后；没有 helper import / helper lemma 时才为空或 `n/a`
- `protected_prefix_respected`
  - 对 `vc-proving` 来说，本轮是否始终保持 `common_case_formal_lib` 冻结前缀不变
- `blocking_reason`
  - 如果未完成，为什么不能继续留在当前 phase
- `recommended_next_phase`
  - 建议主 agent 下一步进入哪个 phase
- `cleanup_status`
  - 本轮 scratch 是否已清理

## `Re-entry Brief`

如果当前 case 是从下游 phase 回流后重新进入 `annotation` 或 `vc-proving`，主 agent 必须在新 ticket 中附带 `Re-entry Brief`。

`Re-entry Brief` 至少应包含：

- `reentered_from_phase`
- `why_reentered`
- `what_failed_last_round`
- `affected_witnesses_or_files`
- `what_changed_since_last_round`
- `must_focus_this_round`

目标是让新一轮 subagent 不需要自己猜测“为什么又回来了”。
