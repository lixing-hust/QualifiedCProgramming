# Proof Reasoning

本目录中的证明文件直接复制自 `SeparationLogic/examples/bst_insert_*`，并补入了 `bst_lib.v`。

证明的代表性在于：

- 既要处理低层树节点更新，也要最终导出高层 map 语义。
- 迭代搜索路径上的局部视图需要通过 `combine_tree` 一直和整体树语义保持同步。
- 手写证明集中在 entail、return 和 high-level-spec derivation 这几类 witness。

这是后续检索“BST 插入证明套路”的核心参考样例。
