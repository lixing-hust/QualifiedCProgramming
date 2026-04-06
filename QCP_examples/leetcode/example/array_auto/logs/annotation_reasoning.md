# Annotation Reasoning

本样例来自 `QCP_examples/array_auto.c`，集中展示“只关心 shape，不细追元素语义”的数组验证写法。

它的 annotation 价值主要在于：

- `full_shape`、`undef_full`、`seg_shape`、`undef_seg` 之间的切换。
- 多段数组写入时如何把不变式拆成“已完成前缀 + 未初始化后缀”。
- 数组问题如何桥接到链表构造，如 `array_to_list`。
- `array_max` 中的分支更新和简单存在量词不变式。

这是后续检索“数组 shape 模板”时最应该优先看的参考样例之一。
