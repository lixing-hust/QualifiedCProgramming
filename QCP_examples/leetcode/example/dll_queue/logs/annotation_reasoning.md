# Annotation Reasoning

本样例来自 `QCP_examples/dll_queue.c`，只有两个操作，但抽象层次很高。

它的 annotation 代表性在于：

- 用 `store_queue` 作为抽象谓词隐藏底层双向链表结构。
- 在 `enqueue` 和 `dequeue` 中用 `which implies` 临时展开成 `dllseg`。
- 通过局部指针域约束恢复尾节点或头节点附近的结构事实。

对于“抽象队列谓词 <-> 具体链表段谓词”的往返，这个样例是很直接的模板。
