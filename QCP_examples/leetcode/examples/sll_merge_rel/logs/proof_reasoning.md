# Proof Reasoning

本目录中的证明文件直接来自上游 `sll_merge_rel` 样例，并补入了相关局部库。

证明代表性在于：

- 既要维护 list shape，也要维护 merge/sort 的关系式语义。
- `merge`、`split_rec`、`merge_sort` 三层递归/循环结构相互配合。
- 是当前 `example/` 中最完整的链表排序模板之一。
