# Annotation Reasoning

本样例整理自 `QCP_examples/bst_insert.c`，是树结构里最有代表性的迭代插入例子之一。

注释设计的关键点包括：

- 同时给出 `high_level_spec <= low_level_spec` 和低层 `store_tree` 规范。
- 用 `struct tree **b` 游标表达“沿搜索路径向下走”的程序形态。
- 循环不变式通过 `combine_tree` 记录“当前局部子树 + 已走过路径”如何重新组合成整棵插入后的树。

它适合检索“树结构 + 路径不变式 + 规格提升”的 annotation 模板。
