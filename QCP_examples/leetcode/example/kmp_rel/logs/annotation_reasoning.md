# Annotation Reasoning

本样例整理自 `QCP_examples/kmp_rel.c`，覆盖 KMP 的前缀函数构造和匹配阶段。

annotation 的代表性包括：

- 字符数组和整数数组在同一个规格里联合出现。
- `inner`、`constr`、`match` 三层函数分别维护不同的关系式语义。
- 既有 `while` 风格的无限循环，也有 `for` 循环和早返回。

它适合作为“字符串搜索 + prefix table + 关系式规格”参考样例。
