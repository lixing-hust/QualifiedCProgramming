# Annotation Reasoning

本样例来自 `QCP_examples/chars.c`，展示字符数组上的最小 shape 证明。

annotation 关键点是：

- 用 `CharArray::undef_full` 和 `CharArray::full` 表达初始化前后形状。
- 用 `repeat_Z(m, n)` 表达所有位置都被同一字符填充。
- 循环不变式采用“已初始化前缀 + 未初始化后缀”的标准分段写法。

它适合作为“char buffer 初始化”参考样例。
