# Annotation Reasoning

本样例整理自 `QCP_examples/bst_fp_insert.c`，是带父指针 BST 的插入模板。

annotation 的关键点包括：

- `store_tree(*b, fa, tr)` 中把父指针也纳入树表示。
- 循环中同时更新当前位置 `b` 和父节点 `fa`。
- 新建节点时除了 `left/right` 以外，还要初始化 `father`。

它适合作为“带父指针树插入”样例。
