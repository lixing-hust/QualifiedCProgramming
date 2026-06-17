# HumanEval Verification Cost Ledger

本文件用于记录 humaneval 每个 C 题目的验证成本。每个 case 至少记录一次开始行和一次结束/暂停更新；如果一次 Codex thread 中验证多个 case，必须按 case 分开记录 token 起止值和耗时。

## 记录规则

- `token_start` / `token_end` 优先使用当前 Codex thread 的 `token_count.total_token_usage.total_tokens`。
- `input_tokens`、`cached_input_tokens`、`output_tokens`、`reasoning_output_tokens` 能取到时一并记录；取不到时写 `unknown`，不要编造。
- `elapsed_minutes` 使用 `start_time` 到 `end_time` 的实际墙钟时间。
- `rollout_path` 指向本次 Codex session 的本地 `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl`。
- `status` 只使用：`in_progress`、`full-chain passed`、`blocked`、`skipped`、`partial`。
- 如果是从旧 session 回填的近似统计，在 `confidence` 写 `estimated`，并在 `notes` 说明拆分依据。

## Ledger

| case | suite | status | start_time | end_time | elapsed_minutes | session_id | rollout_path | token_start | token_end | token_delta | input_delta | cached_input_delta | output_delta | reasoning_output_delta | confidence | notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| TEMPLATE | IntClaude/IntArrayClaude/StringClaude | in_progress/full-chain passed/blocked/skipped/partial | YYYY-MM-DD HH:MM TZ | YYYY-MM-DD HH:MM TZ | N | session id | ~/.codex/sessions/.../rollout-*.jsonl | N | N | N | N | N | N | N | exact/estimated | 关键修改、final-check 结果、或 blocked 原因 |
| C_95 | multi_dimensional_arrays | partial | 2026-06-17 01:31 CST | 2026-06-17 01:40 CST | 9 | 019ed178-1816-7352-8c1e-57ea23dae0bb | ~/.codex/sessions/2026/06/17/rollout-2026-06-17T01-26-09-019ed178-1816-7352-8c1e-57ea23dae0bb.jsonl | 451643 | 6391888 | 5940245 | 5920239 | 5787648 | 20006 | 5638 | estimated | Verification-only cost, excluding QCP core/toolchain debugging and rebuild. Token split uses nearest token_count events at 2026-06-17 01:31:00 CST and 2026-06-17 01:40:02 CST. Clean QCP conversion without C_95_ reuse; coins_95.v directly wraps spec/95.v; symexec passed and generated C_95_* files. After separate core rebuild, the generated Coq chain compiles, but this case is not full-chain passed because C_95_proof_manual.v still has 17 Admitted. |
| C_95_continuation | multi_dimensional_arrays | full-chain passed | 2026-06-17 02:28 CST | 2026-06-17 03:29 CST | 61 | 019ed178-1816-7352-8c1e-57ea23dae0bb | ~/.codex/sessions/2026/06/17/rollout-2026-06-17T01-26-09-019ed178-1816-7352-8c1e-57ea23dae0bb.jsonl | 25467403 | 79868921 | 54401518 | 54280931 | 53525120 | 120587 | 28556 | exact | Continuation requested by user to finish C_95 verification; excludes earlier QCP core/toolchain rebuild and guardian/approval helper session. Restored problem_95_spec_z as direct wrapper over spec/95.v, proved rows-to-original-spec bridge, compiled coins_95.v through C_95_goal_check.v, and found no Admitted or new Axiom declarations in coins_95.v/C_95_proof_manual.v/C_95_goal_check.v. |
| C_115 | multi_dimensional_arrays | full-chain passed | 2026-06-17 10:53 CST | 2026-06-17 11:34 CST | 41 | 019ed37c-029a-79d3-be93-f7f99f11d838 | ~/.codex/sessions/2026/06/17/rollout-2026-06-17T10-49-40-019ed37c-029a-79d3-be93-f7f99f11d838.jsonl | 85234 | 29768251 | 29683017 | 29625147 | 29139968 | 57870 | 15108 | estimated | Used nearest token_count events at 2026-06-17 10:52:52 CST and 2026-06-17 11:34:29 CST. Verified C_115 per QCP_examples/humaneval/SKILL.md without .agents skills/subagents; reused 2DIntPtrArray.c/IntPtrArray2 memory pattern, kept problem_115_spec_z as a direct wrapper over spec/115.v, ran symexec, compiled coins_115.v through C_115_goal_check.v, found no Admitted or new Axiom declarations in coins_115.v/C_115_proof_manual.v/C_115_goal_check.v, and cleaned C_115 build artifacts/backups. |

## Non-case Infrastructure Costs

这些记录用于解释本轮额外开销，但不计入任何单个 HumanEval case 的验证成本。

| item | status | start_time | end_time | elapsed_minutes | session_id | rollout_path | token_start | token_end | token_delta | input_delta | cached_input_delta | output_delta | reasoning_output_delta | confidence | notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| QCP_core_rebuild_for_C_95 | full-chain passed | 2026-06-17 01:40 CST | 2026-06-17 02:24 CST | 44 | 019ed178-1816-7352-8c1e-57ea23dae0bb | ~/.codex/sessions/2026/06/17/rollout-2026-06-17T01-26-09-019ed178-1816-7352-8c1e-57ea23dae0bb.jsonl | 6391888 | 24676609 | 18284721 | 18235523 | 17300352 | 49198 | 14437 | estimated | Not counted for C_95. Token split uses nearest token_count events at 2026-06-17 01:40:02 CST and 2026-06-17 02:24:27 CST. Diagnosed stale/mixed QCP core dependencies, refreshed SeparationLogic make dependencies, ran make core with coq8201, then confirmed coins_95.v through C_95_goal_check.v compile. |


## 旧记录回填说明

旧对话中未按 case 预先记录 token 起点时，可以从 `~/.codex/history.jsonl` 找到 session id，再到 `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl` 查找 `event_msg` / `token_count`。如果一个 session 混合推进多个 case，只能按用户指令时间、文件修改时间、progress 文档更新时间和 token_count 时间点近似拆分，必须标为 `estimated`。
