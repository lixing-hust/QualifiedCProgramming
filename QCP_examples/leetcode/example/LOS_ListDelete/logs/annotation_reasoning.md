# Annotation Reasoning

本样例整理自 `QCP_examples/LiteOS/LOS_ListDelete.c`，代表系统代码里的低层双链表操作。

annotation 重点包括：

- 中层规范把整条双链表删除一个节点的效果表达成 `app(l1, cons(...), l2) -> app(l1, l2)`。
- 低层规范则只关注 `prev/node/next` 三个局部节点和 `dllseg_shift`。
- 函数体本身是纯直线型字段更新，没有额外控制流。

它适合作为“系统风格低层 DLL 更新”样例。
