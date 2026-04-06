# Annotation Reasoning

本样例整理自 `QCP_examples/swap.c`，它的代表性不在算法复杂度，而在别名情形的规格拆分。

注释重点包括：

- 用 `swap_pre` / `swap_post` 定义统一入口规范。
- 通过 `eq <= all` 和 `neq <= all` 给出两个更具体的模式。
- 在实现体前插入 `Assert`，把抽象参数 `para` 细化成等指针或异指针两类。

这是“alias-sensitive heap 规格”最合适的参考样例之一。
