# Annotation Reasoning

本样例整理自 `QCP_examples/typeinfer/typeinfer.c`，是当前目录里最偏编译器/类型系统语义的一类。

annotation 的关键点包括：

- 全局 `res` 数组表示解映射，局部 `atype` 结构表示类型树。
- 同时存在 `verify` 与 `final <= verify` 两层规范。
- 递归展开时要处理表示压缩、查表、复制、释放和 occurs check。

它适合作为“类型推断 / 并查集风格表示压缩”参考样例。
