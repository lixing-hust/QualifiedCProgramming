# Proof Reasoning

本目录中的证明文件直接来自上游 `bst_insert_rec` 样例，并补入了 `bst_lib.v`。

证明层面，这个样例强调：

- 递归调用后的子树语义如何向上重组回整棵树。
- 需要同时对齐低层 `tree_insert` 与高层 `map_insert`。
- 与迭代版不同，它不需要路径型循环不变式，但更依赖递归分支上的结构归纳。

它和 `bst_insert` 形成互补的 BST 插入模板。
