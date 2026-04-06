# Proof Reasoning

`avl_insert` 的证明文件和 `avl_shape.v` 直接来自上游样例，没有在当前目录重放。

证明上，这个样例的代表性在于：

- 多个局部旋转函数各自维护小范围 tree shape。
- `balance` 通过平衡因子和子树平衡因子做 case split。
- 主 `insert` 证明把递归更新、高度修正和旋转组合起来。

它是当前目录里最接近“平衡树结构维护”的样例。
