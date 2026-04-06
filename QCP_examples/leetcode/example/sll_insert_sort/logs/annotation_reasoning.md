# Annotation Reasoning

本样例整理自 `QCP_examples/sll_insert_sort.c`，是单链表排序里最典型的插排模板。

annotation 的关键点包括：

- `insertion` 在保持有序前缀的同时，把新节点插进正确位置。
- `strict_upperbound`、`Permutation` 和 `increasing` 一起表达排序语义。
- 外层 `insertion_sort` 不断把原链表头节点摘下并插入结果链表。

它适合作为“链表排序 + 排列性/有序性”样例。
