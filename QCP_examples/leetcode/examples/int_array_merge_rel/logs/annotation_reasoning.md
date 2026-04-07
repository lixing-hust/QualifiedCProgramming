# Annotation Reasoning

本样例整理自 `QCP_examples/int_array_merge_rel.c`，它把 mergesort 写成了带关系式语义的数组程序。

annotation 的关键点是：

- `merge` 和 `mergeSort` 都用 `safeExec` 风格规格描述关系式语义。
- `merge` 里有多段数组 segment 和多个循环不变式协同推进。
- `mergeSort` 递归地在 `arr` 和 `ret` 两个数组之间来回交换角色。

它适合作为“数组分段 + 关系式排序语义”模板。
