# Annotation Reasoning

本样例整理自 `QCP_examples/simple_arith/max3.c`，是一个很短但分支结构不完全平坦的选择题。

注释层面的重点是：

- 后置条件不要求“精确返回哪一个变量”，只要求它不小于三个输入。
- 程序用嵌套 `if` 展开比较顺序，因此 proof 会自然形成多分支。
- 没有 heap，没有循环，是纯控制流选择题。

它适合检索“嵌套比较 + return_max”模式。
