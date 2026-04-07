# Annotation Reasoning

本样例整理自 `QCP_examples/sll_queue.c`，展示了单链表队列的更底层表示。

annotation 的关键点是：

- 用 `store_queue(q, l)` 作为队列抽象。
- `enqueue` / `dequeue` 都通过 `which implies` 展开成 `sllseg` 形式。
- 队尾采用哨兵空节点，因此入队只需写最后一个真实元素的位置并延长尾巴。

它适合检索“单链表队列 + frontier update”模式。
