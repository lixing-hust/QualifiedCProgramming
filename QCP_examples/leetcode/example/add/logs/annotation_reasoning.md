# Annotation Reasoning

本样例直接誊抄自 `QCP_examples/simple_arith/add.c`，上游文件本身已经带有完整注释，因此这里不重新设计规格，只保留原注释结构并放入 workspace 目录。

这个文件覆盖三类最小模式：

- 纯标量加法的前后条件。
- 通过 `while` 循环保持 `x + y == x@pre + y@pre` 的不变式。
- 指针与二级指针上的原地自增规格。

它适合作为后续检索“纯算术 + 简单循环不变式 + 小规模 heap 更新”的参考起点。
