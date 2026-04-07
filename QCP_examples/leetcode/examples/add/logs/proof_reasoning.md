# Proof Reasoning

本样例的 `goal`、`proof_auto` 和 `proof_manual` 直接来自 `SeparationLogic/examples/simple_arith/`，没有在当前目录内重新证明。

证明模式上，这组文件主要展示：

- 纯算术目标如何由自动化和 `lia` 风格策略消化。
- `slow_add` 的循环不变式如何把程序状态压缩成一个守恒等式。
- 指针增量示例中的小规模 heap 目标如何和纯算术目标组合。

它适合作为后续检索“最小纯算术证明模板”的参考样例。
