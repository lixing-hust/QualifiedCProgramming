# Annotation Reasoning

本样例整理自 `QCP_examples/bst_fp_delete.c`，是带父指针 BST 删除的完整版本。

annotation 的关键点包括：

- `replace_min` 在右子树里向左走，并同步维护父指针。
- 主删除流程区分无右子树、无左子树和双子树三种删除情形。
- 每次接回子树时都要把 `father` 修正到新的父节点。

它适合作为“带父指针 BST 删除”样例。
