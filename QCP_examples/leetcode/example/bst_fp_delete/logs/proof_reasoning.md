# Proof Reasoning

本目录中的证明文件直接来自上游 `bst_fp_delete` 样例，并补入了 `bst_fp_lib.v`。

证明代表性在于：

- `replace_min` 的循环不变式同时维护最小元素语义和路径上下文。
- 删除过程里的每个重接分支都要恢复父指针一致性。
- 相比普通 BST 删除，多了一层面向 `father` 字段的局部修复。
