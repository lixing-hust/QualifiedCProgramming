# Annotation Reasoning

本样例整理自 `QCP_examples/sll_merge_rel.c`，是链表归并排序的完整关系式版本。

annotation 重点包括：

- `merge` 的三段式不变式：两条剩余链表加一条已构造结果前缀。
- `split_rec` 和 `merge_sort` 用 `safeExec` 描述分裂与归并排序语义。
- 同一文件里同时覆盖合并、切分、递归排序和小规模优化版本。

它适合作为“链表分治排序”样例。
