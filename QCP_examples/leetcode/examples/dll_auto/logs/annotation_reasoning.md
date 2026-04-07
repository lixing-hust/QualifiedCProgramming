# Annotation Reasoning

本样例整理自 `QCP_examples/dll_auto.c`，是双链表 shape 程序的系统性样例。

annotation 代表性在于：

- 同时跟踪 `next` 与 `prev` 的一致性。
- 使用 `dlistrep_shape` 和 `dllseg_shape` 表达全链表与局部段。
- 覆盖正向遍历、反向遍历、拼接、合并和反转等多种更新模式。

如果后续题目涉及双链表局部修改，这个样例通常比 `dll_queue` 更接近底层 shape 证明。
