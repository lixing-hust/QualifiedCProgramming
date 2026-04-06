# Proof Reasoning

本目录中的 Coq 文件来自 `SeparationLogic/examples/functional_queue_*`，并补入了 `functional_queue_lib.v` 与 `sll_lib.v`。

证明层面的代表性在于：

- 队列抽象中 `app` 与 `rev` 的关系如何进入 witness。
- `dequeue` 在空前端链表时如何通过一次反转恢复更直接的单链表形状。
- 局部链表操作和全局抽象队列语义之间如何衔接。

它适合作为“函数式队列表示 + 列表代数 + heap reasoning”的参考样例。
