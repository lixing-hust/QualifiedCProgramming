# Proof Reasoning

本样例的 Coq 文件直接来自 `SeparationLogic/examples/`，没有在 `example/sum` 下重新执行生成流程。

证明上，这组文件覆盖：

- 典型数组循环不变式的 witness 证明。
- `which implies` 相关的 entail/return witness。
- 指针式访问和原地更新场景下的 separation-logic 目标恢复。

如果后续题目需要“数组 + 循环不变式 + 中间断言拆装”的现成模板，这个样例通常应优先进入候选集。
