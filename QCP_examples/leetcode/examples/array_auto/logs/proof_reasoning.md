# Proof Reasoning

相关 Coq 文件直接复制自 `SeparationLogic/examples/array_auto_*`，并补入了 `sll_shape_lib.v` 以保持阅读时的依赖闭包更完整。

证明层面，这组文件重点展示：

- 段谓词在循环中的前缀扩张。
- 数组 shape 目标与少量纯算术边界条件的组合。
- 数组到链表转换时的 heap 结构递增构造。

适合在需要“数组 shape + 分段不变式 + 少量链表桥接”时检索。
