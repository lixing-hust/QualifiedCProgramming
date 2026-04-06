# Annotation Reasoning

本样例直接誊抄自 `QCP_examples/sum.c`，它不是单函数，而是一组数组求和变体。

注释设计上的代表性包括：

- 用 `With l` 把数组内容抽象成逻辑列表。
- 对 `while`、`do while`、`for` 三种循环形态分别写出同构不变式。
- 用 `which implies` 在循环体内临时把 `IntArray::full` 拆成单元素与缺口段。
- 在 `arr_sum_update` 中同时跟踪返回值和数组被逐步清零后的新 shape。

它是数组循环题里非常高密度的 annotation 参考样例。
