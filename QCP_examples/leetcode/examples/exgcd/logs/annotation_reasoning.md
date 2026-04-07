# Annotation Reasoning

本样例整理自 `QCP_examples/simple_arith/exgcd.c`，原文件已经给出了接口规范和更细的 `Proof` 规格。

annotation 的代表性在于：

- 返回值和两个输出指针一起表达 Bezout 等式。
- 递归基 `b == 0` 时区分 `a < 0`、`a == 0`、`a > 0` 三种系数写法。
- 递归步里先交换 `x/y` 的角色，再通过 `*y -= (a / b) * (*x)` 修正系数。

它适合作为“递归 + 输出参数 + 数论规格”的参考样例。
