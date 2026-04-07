# Annotation Reasoning

本样例整理自 `QCP_examples/bst_delete_rec2.c`，和 `bst_delete_rec` 的主要区别是前驱查找返回 `struct tree **`。

annotation 重点是：

- `get_pre` 返回指向前驱节点槽位的二级指针。
- 删除命中目标后，把前驱的键值复制到当前节点，再原地移除前驱节点。
- 这种写法更接近需要修改“父节点指向哪个孩子”的真实实现。

它适合作为“pointer-to-pointer 树更新”样例。
