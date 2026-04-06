# Annotation Reasoning

本样例整理自 `QCP_examples/functional_queue.c`，展示了“两个单链表表示一个队列”的抽象规格。

它的注释重点是：

- 用 `store_queue(q, l)` 把逻辑队列表示成 `app(l1, rev(l2))`。
- `enqueue` 只操作后端链表，`dequeue` 则在必要时做一次 `reverse`。
- 在 `dequeue` 的两个分支里，用 `which implies` 把抽象队列规格对齐到 `pop` 的前置条件。

如果要检索“抽象数据结构 + app/rev 代数关系”的样例，这个目录非常合适。
