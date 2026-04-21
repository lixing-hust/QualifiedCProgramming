---
name: vc-proving
description: 使用 Rocq MCP 证明 QCP 符号执行生成的 VC，包括普通分离逻辑目标和包含 safeExec/refinement proof 目标。
---

# VC Proving

这个 skill 用于证明 `qcp-mcp proof` 导出的 manual VC。它只负责 VC 证明，不负责修改 C annotation；如果 VC 明显不可证，应回到 `annotation-and-symbolic-execution` 调整 spec、assertion 或 loop invariant。所有 manual VC 都在临时文件中证明通过后，才运行 symexec 生成正式 Rocq 文件并回填 proof。

## Hard Rules

- 优先用 `rocq-mcp` 交互式跑通 proof script，并先保存在临时 proof 文件中；正式 `*_proof_manual.v` 由 symexec 生成后再回填。
- 不要手写修改 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`。
- 临时手动证明建议保存在 `SeparationLogic/tmp_vc/`；正式手动证明只在 symexec 生成的 `*_proof_manual.v` 中回填。必要的辅助引理写在对应 `*_lib.v`。
- 不允许使用 `Admitted`、新增 `Axiom` 或修改原始 VC 目标来绕过证明。
- 先判断目标是否可证，再开始写证明；如果缺少资源、纯事实或 refinement 状态不匹配，优先修正 annotation。
- 严格参考 `LLM_friendly_cases` 中已完成证明的风格，优先使用 QCP 提供的 tactics。
- 只处理 manual VC；auto-solved VC 不需要导出、不需要证明、不需要回填。
- 每次重新 symbolic 后，都要重新检查完整 manual witness 列表。旧 VC 也要检查是否变化；未变化可以复用旧证明，变化则必须重新交互式证明。
- 开始 `qcp-mcp proof` 导出前，必须已经逐条检查过 `qcp-mcp symbolic` 返回的所有 manual goal，并确认它们语义上可证明；否则先回到 annotation 或 lib definition 修正。
- manual VC 必须逐个处理：先用 `qcp-mcp proof` 导出一个 VC，再分析并用 `rocq-mcp` 交互式证明，最后保存到临时 proof 文件；完成后再处理下一个 VC。
- 不同函数的 VC 使用相同流程处理。不要因为某个函数后处理或看起来类似，就跳过导出、比较或交互式证明步骤。
- 所有 `qcp-mcp proof` 导出的 manual VC 都证明通过之前，不要运行 symexec 作为正式文件生成步骤。

## Manual VC Workflow

对每个 manual witness 按以下顺序执行：

1. 使用当前 `qcp-mcp symbolic` 结果确认该 VC 仍是 manual witness，并已在 symbolic goal 层面判断语义上可证明。
2. 使用 `qcp-mcp proof` 导出当前 VC，建议保存到 `SeparationLogic/tmp_vc/` 便于比较。
3. 如果已有旧证明，先比较当前 VC 和旧 VC；只有在目标相同或仅有无关变量名变化时才复用旧证明。
4. 如果 VC 有实质变化，先在 `rocq-mcp` 中交互式跑通 proof script。
5. 将跑通的 proof script 保存在临时 proof 文件中，并编译该临时文件。
6. 所有 manual VC 的临时 proof 都通过后，运行 symexec 生成正式 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`。
7. 先只编译 `*_goal.v` 确保 VC 定义能被导入。
8. 按 VC 主体形状匹配临时 proof 和正式 lemma，再回填到 `*_proof_manual.v`；不要只按 witness 编号匹配。
9. 按顺序编译 `*_proof_manual.v`, `*_proof_auto.v` 和最终 `*_goal_check.v`，确认没有留下 `Admitted`。

## Document Routing

- 必须阅读 `references/separation-logic-whole-proof-tactics.md`。
- 目标包含 `safeExec` 等 monad 相关谓词，也要读 `references/refinement-proof-tactics.md`。

## Reference Cases

只参考 `LLM_friendly_cases` 版本：

- 数组：`SeparationLogic/examples/LLM_friendly_cases/sum_proof_manual.v`
- 链表：`SeparationLogic/examples/LLM_friendly_cases/sll_proof_manual.v`
- 队列：`SeparationLogic/examples/LLM_friendly_cases/functional_queue_proof_manual.v`
- refinement/safeExec 证明：`SeparationLogic/examples/LLM_friendly_cases/sll_merge_rel_proof_manual.v`
- 更复杂 loop/refinement 证明：`SeparationLogic/examples/LLM_friendly_cases/kmp_rel_proof_manual.v`
