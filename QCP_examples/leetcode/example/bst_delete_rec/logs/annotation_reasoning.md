# Annotation Reasoning

本样例整理自 `QCP_examples/bst_delete_rec.c`，覆盖 BST 删除的前驱替换版本。

annotation 的关键点包括：

- `get_pre` 通过一直向右走找到左子树中的最大节点。
- 删除时按 `x < y / x > y / x == y` 分支递归下降。
- 命中后根据左子树是否为空，选择直接提升右子树或做前驱替换。

它适合作为“BST 删除 + 前驱重接”参考样例。
