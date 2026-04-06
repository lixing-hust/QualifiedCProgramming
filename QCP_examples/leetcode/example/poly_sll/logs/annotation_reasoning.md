# Annotation Reasoning

本样例整理自 `QCP_examples/poly_sll.c`，它和普通 `sll_auto` 的区别是规格对元素表示完全参数化。

annotation 的关键点是：

- 用 `{A} storeA` 抽象链表元素的存储谓词。
- 循环不变式通过 `app(rev(l1), l2)` 把逻辑列表分成已翻转部分和剩余部分。
- 整个程序不依赖具体元素字段，只依赖链表骨架。

它适合作为“多态链表 shape”模板。
