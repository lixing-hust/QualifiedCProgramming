---
name: annotation-and-symbolic-execution
description: 为 QCP C 程序补充 annotation，使用 qcp-mcp 做符号执行，并在 manual VC 临时证明全部通过后用 symexec 二进制完整生成 goal/proof 文件。
---

# Annotation And Symbolic Execution

## Hard Rules

- 只参考 `LLM_friendly_cases` 下的示例：
  - `QCP_examples/LLM_friendly_cases`
- loop invariant 必须写成完整的 `Inv Assert`。
- 中间断言必须写成完整的 `Assert`。
- 如果 symbolic execution 产生的 manual VC 语义上不可证，优先修 annotation，不要把问题推给 Rocq proof。
- 修改 annotation 后，必须重新跑 symbolic execution 到文件尾，获得最新 witness 列表。
- 每次重新运行 symbolic execution 后，都必须重新检查完整 witness 列表；manual witness 的编号和内容都可能变化，不能默认旧证明仍对应当前 VC。
- symbolic execution 成功后，必须逐条阅读返回结果中的所有 `manual_witness` goal，先做语义可证性分析；只有确认这些 goal 语义上可证明后，才进入 `qcp-mcp proof` 导出和 Rocq 证明。
- 只把 manual witness 交给后续证明流程；auto-solved witness 不需要导出或手动证明。
- symexec 只能在所有 `qcp-mcp proof` 导出的 manual VC 都已经在临时 Rocq 文件中证明通过后运行；不要把 symexec 生成的 `*_proof_manual.v` 当作 manual VC 证明的起点。

## Documentation Map

- `tutorial/T1-representation-predicates.md`：表示谓词和内存模型。
- `tutorial/T2-pre-post-condition.md`：函数 `Require` / `Ensure`。
- `tutorial/T3-assertion-and-invariant.md`：`Assert` / `Inv Assert`。
- `tutorial/T4-symbolic-execution.md`：符号执行如何产生 VC。
- `tutorial/T6-polymorphism.md`：多态 predicate/spec。
- `tutorial/T8-function-call.md`：函数调用、`where`、multi-spec。

## Reference Cases

普通 annotation：

- `QCP_examples/LLM_friendly_cases/sum.c`
- `QCP_examples/LLM_friendly_cases/sll.c`
- `QCP_examples/LLM_friendly_cases/functional_queue.c`

refinement / `safeExec` annotation：

- `QCP_examples/LLM_friendly_cases/sll_merge_rel.c`
- `QCP_examples/LLM_friendly_cases/kmp_rel.c`
- `QCP_examples/LLM_friendly_cases/int_array_merge_rel.c`

## qcp-mcp

使用 qcp-mcp 提供的工具完成符号执行

符号执行必须跑到目标文件尾部，以获得完整 witness 列表。重新跑 symbolic 后，需要记录或核对 manual/auto-solved 分类；之前证明过的 VC 也要检查是否变化，未变化才可复用旧证明。

`symbolic` 返回的 `manual_witness` 已经包含 goal 文本。symbolic 成功后，先用这些 goal 做自然语言语义分析：检查左侧前提是否足以推出右侧结论，`safeExec` 是否接对，loop invariant、function spec 和 lib definition 是否合理。若某个 goal 语义上不可证，优先修改 annotation 或 lib definition，而不是导出 VC 后硬写 Rocq proof。

## Full symexec Binary

所有 `qcp-mcp proof` 导出的 manual VC 都在临时 Rocq 文件中证明通过后，用 symexec 二进制完整跑一遍，生成或刷新正式 Rocq 文件。

运行 symexec 之后，将临时证明按 VC 主体形状匹配回填到 `*_proof_manual.v`；不要只按 witness 编号盲目复制，因为不同工具的编号可能不稳定。

Linux 常用命令形状：

```sh
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/LLM_friendly_cases/<name>_goal.v \
  --proof-auto-file=SeparationLogic/examples/LLM_friendly_cases/<name>_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/LLM_friendly_cases/<name>_proof_manual.v \
  --coq-logic-path=SimpleC.EE.LLM_friendly_cases \
  -slp QCP_examples/LLM_friendly_cases/ SimpleC.EE.LLM_friendly_cases \
  --input-file=QCP_examples/LLM_friendly_cases/<name>.c \
  --no-exec-info
```

如果目标文件在子目录，例如 `simple_arith/add.c`，对应路径也要带子目录：

```sh
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/LLM_friendly_cases/simple_arith/add_goal.v \
  --proof-auto-file=SeparationLogic/examples/LLM_friendly_cases/simple_arith/add_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/LLM_friendly_cases/simple_arith/add_proof_manual.v \
  --coq-logic-path=SimpleC.EE.LLM_friendly_cases.simple_arith \
  -slp QCP_examples/LLM_friendly_cases/ SimpleC.EE.LLM_friendly_cases \
  --input-file=QCP_examples/LLM_friendly_cases/simple_arith/add.c \
  --no-exec-info
```
