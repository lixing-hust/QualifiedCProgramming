# Proof Reasoning

本目录中的 Coq 文件直接来自上游 `eval` 样例，并补入了 `eval_lib.v`。

证明重点在于：

- AST 节点展开后的 case split。
- 短路逻辑和普通算术/比较运算分开处理。
- 递归调用前后既要保持 AST 资源不变，也要保持数组环境不变。
