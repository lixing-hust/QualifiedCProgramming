# Proof Reasoning

本目录中的 Coq 文件直接来自上游 `sll_queue` 样例，并补入了 `sll_lib.v` 与 `sll_queue_lib.v`。

证明重点是：

- 把抽象队列谓词拆到 `head/tail` 附近的局部节点事实上。
- 在小范围 heap 更新后恢复整队列抽象。
- 由于控制流简单，主要难点在 heap 谓词重组而不在纯算术。

它是 `functional_queue` 之外另一种非常实用的队列模板。
