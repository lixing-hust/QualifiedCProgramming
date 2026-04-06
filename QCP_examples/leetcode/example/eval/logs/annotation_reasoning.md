# Annotation Reasoning

本样例整理自 `QCP_examples/eval.c`，展示表达式解释器的递归验证。

annotation 层面的代表性包括：

- 用 `store_expr` / `store_expr_aux` 展开 AST 节点。
- 用 `IntArray::full(var_value, 100, l)` 表示变量环境。
- 对 `AND` / `OR` 做短路控制流，对其它二元运算再做内部 `switch`。

它适合作为“语法树递归 + 数组环境读取”样例。
