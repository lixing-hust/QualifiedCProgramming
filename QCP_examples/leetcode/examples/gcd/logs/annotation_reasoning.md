# Annotation Reasoning

本样例直接誊抄自 `QCP_examples/simple_arith/gcd.c`，保留了它原本的递归规格和外部 Coq 函数声明。

注释层面的关键点是：

- 用 `Extern Coq` 把 `Zgcd` 和 `Zabs` 引入规格语言。
- 把 `abs` 当作已验证的外部函数接口使用。
- 通过 `if (y == 0)` 区分递归基和递归步。

它适合作为后续检索“递归算术函数 + 外部数学模型”的样例。
