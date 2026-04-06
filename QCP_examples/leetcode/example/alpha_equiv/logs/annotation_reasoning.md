# Annotation Reasoning

本样例整理自 `QCP_examples/alpha_equiv/alpha_equiv.c`，是当前 `example/` 里最偏语法树语义的一类。

annotation 重点包括：

- 用 `store_term` 和 `store_term'` 表达语法树的整体与展开视图。
- 按 `Var / Const / Apply / Quant` 四类节点做精细 case split。
- 在量词变量名不同的分支里，显式调用 `copy_term`、`subst_var` 和 `free_term`。

它适合作为“递归 AST + 结构展开 + 语义比较”参考样例。
