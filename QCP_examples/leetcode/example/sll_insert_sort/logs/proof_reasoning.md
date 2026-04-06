# Proof Reasoning

本目录中的证明文件直接来自上游 `sll_insert_sort` 样例，并补入了相关局部库。

证明重点是：

- `insertion` 里的局部有序前缀不变式。
- 结果链表的 `Permutation` 与 `increasing` 如何被外层循环保持。
- 与普通 shape 题相比，多了排序语义而不是只有结构语义。
