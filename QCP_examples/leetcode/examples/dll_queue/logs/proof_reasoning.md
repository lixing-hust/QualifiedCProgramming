# Proof Reasoning

本目录复制了 `dll_queue` 的 `goal`、自动证明、手写证明以及 `dll_queue_lib.v`。

证明重点包括：

- 如何从抽象 `store_queue` 中取出足够的 `dllseg` 形状信息。
- 在修改 `next` / `prev` 指针后恢复双向链表不变量。
- `return witness` 与 `which implies witness` 如何配合把局部更新重新封装回抽象谓词。

它适合检索“队列抽象 + 双向链表 + which-implies 重封装”的样例。
