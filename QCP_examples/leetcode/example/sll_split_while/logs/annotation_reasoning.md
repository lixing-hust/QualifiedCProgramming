# Annotation Reasoning

本样例整理自 `QCP_examples/sll_split_while.c`，它的特点是规范不只描述最终 heap，还描述一个关系式程序语义。

annotation 层面的关键点包括：

- 循环不变式同时维护 `safeExec(ATrue, split_rec_rel(...), X)` 和三段链表 shape。
- 每轮从原链表拿一个节点挂到 `p`，条件允许时再拿一个节点挂到 `q`。
- `which implies` 用来把局部节点展开成 `cons` 形式，并把关系语义改写到下一步。

这是“关系式规范 + heap 循环”的代表样例。
