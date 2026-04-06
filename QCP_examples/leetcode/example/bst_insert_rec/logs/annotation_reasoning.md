# Annotation Reasoning

本样例整理自 `QCP_examples/bst_insert_rec.c`，它和迭代版 `bst_insert` 相比更接近经典递归树程序。

annotation 的代表性在于：

- 同时保留高层 map 规范和低层 `store_tree` 规范。
- 递归返回新的子树指针，再赋回 `left` 或 `right`。
- `which implies` 用来从整棵树中取出当前根节点及其左右子树结构。

它适合检索“递归树更新 + 规格提升”模板。
