# Rocq 编译检查

完成 symexec 刷新后，需要按依赖顺序编译相关文件。以下命令以 `examples` 为例：

```bash
coqc -R SeparationLogic/SeparationLogic SimpleC.SL -R SeparationLogic/unifysl Logic -R SeparationLogic/sets SetsClass -R SeparationLogic/compcert_lib compcert.lib -R SeparationLogic/auxlibs AUXLib -R SeparationLogic/examples SimpleC.EE -R SeparationLogic/StrategyLib SimpleC.StrategyLib -R SeparationLogic/Common SimpleC.Common -R SeparationLogic/fixedpoints FP -R SeparationLogic/MonadLib MonadLib -R SeparationLogic/listlib ListLib SeparationLogic/examples/QCP_demos_LLM/examples_lib.v
coqc -R SeparationLogic/SeparationLogic SimpleC.SL -R SeparationLogic/unifysl Logic -R SeparationLogic/sets SetsClass -R SeparationLogic/compcert_lib compcert.lib -R SeparationLogic/auxlibs AUXLib -R SeparationLogic/examples SimpleC.EE -R SeparationLogic/StrategyLib SimpleC.StrategyLib -R SeparationLogic/Common SimpleC.Common -R SeparationLogic/fixedpoints FP -R SeparationLogic/MonadLib MonadLib -R SeparationLogic/listlib ListLib SeparationLogic/examples/QCP_demos_LLM/examples_goal.v
coqc -R SeparationLogic/SeparationLogic SimpleC.SL -R SeparationLogic/unifysl Logic -R SeparationLogic/sets SetsClass -R SeparationLogic/compcert_lib compcert.lib -R SeparationLogic/auxlibs AUXLib -R SeparationLogic/examples SimpleC.EE -R SeparationLogic/StrategyLib SimpleC.StrategyLib -R SeparationLogic/Common SimpleC.Common -R SeparationLogic/fixedpoints FP -R SeparationLogic/MonadLib MonadLib -R SeparationLogic/listlib ListLib SeparationLogic/examples/QCP_demos_LLM/examples_proof_auto.v
coqc -R SeparationLogic/SeparationLogic SimpleC.SL -R SeparationLogic/unifysl Logic -R SeparationLogic/sets SetsClass -R SeparationLogic/compcert_lib compcert.lib -R SeparationLogic/auxlibs AUXLib -R SeparationLogic/examples SimpleC.EE -R SeparationLogic/StrategyLib SimpleC.StrategyLib -R SeparationLogic/Common SimpleC.Common -R SeparationLogic/fixedpoints FP -R SeparationLogic/MonadLib MonadLib -R SeparationLogic/listlib ListLib SeparationLogic/examples/QCP_demos_LLM/examples_proof_manual.v
coqc -R SeparationLogic/SeparationLogic SimpleC.SL -R SeparationLogic/unifysl Logic -R SeparationLogic/sets SetsClass -R SeparationLogic/compcert_lib compcert.lib -R SeparationLogic/auxlibs AUXLib -R SeparationLogic/examples SimpleC.EE -R SeparationLogic/StrategyLib SimpleC.StrategyLib -R SeparationLogic/Common SimpleC.Common -R SeparationLogic/fixedpoints FP -R SeparationLogic/MonadLib MonadLib -R SeparationLogic/listlib ListLib SeparationLogic/examples/QCP_demos_LLM/examples_goal_check.v
```

## 重点

- 这里的 `examples_lib.v` 是该 case 的 `common_case_formal_lib`，包含 annotation-checking 通过并冻结的 spec 定义，以及 vc-proving 迁入的 audited helper-suffix imports / helper lemmas；编译顺序必须先于 `goal.v` / `proof_manual.v`。
- `examples_goal_check.v` 用于确认所有需要的 goal 都已经被 `proof_auto` 或 `proof_manual` 覆盖。
- `examples_proof_manual.v` 最终只应包含 manual witness theorem proofs；若这里混入 helper lemmas、helper definitions、`Admitted` 或额外 `Axiom`，属于 final-check 失败。
- 如果目标文件位于子目录，相关路径和逻辑命名空间也要一并调整。
