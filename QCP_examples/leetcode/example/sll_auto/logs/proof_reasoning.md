# Proof Reasoning

`sll_auto` 的 Coq 文件直接来自 `SeparationLogic/examples/`，并额外补入了 `sll_shape_lib.v` 以便阅读手写证明时不缺局部库文件。

这组证明的核心模式是：

- 在 heap 目标中反复拆开和重组 `listrep` / `lseg`。
- 用循环游标处的局部字段事实连接前后两段链表。
- 在多函数模块里复用相近的 list-shape 证明套路。

它适合作为“链表循环 + 段谓词重组”检索模板。
