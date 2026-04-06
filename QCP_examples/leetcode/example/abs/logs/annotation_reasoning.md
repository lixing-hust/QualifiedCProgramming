# Annotation Reasoning

本样例直接整理自 `QCP_examples/simple_arith/abs.c`，保留原有注释和 `Extern Coq (Zabs)` 建模。

它的 annotation 重点很单纯：

- 规格只表达 `__return == Zabs(x)`。
- 程序层面只需要一个符号分支 `x < 0`。
- 没有 heap，不涉及循环或别名。

它适合作为“最小 case split 算术题”的检索基准。
