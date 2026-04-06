# Annotation Reasoning

本样例整理自 `QCP_examples/avl_insert.c`，是当前 `example/` 里最偏平衡树维护的一类样例。

annotation 的关键点包括：

- 先分别给 `update_height`、`rotateR/L/RL/LR`、`balance_factor`、`balance` 和 `insert` 写局部 shape 规格。
- 旋转函数的后置条件只承诺局部根变化和 `store_non_empty_tree` 恢复。
- 主插入流程先递归下降，再更新高度并在返回路径上做平衡。

它适合作为“树旋转 + 平衡恢复”模板。
