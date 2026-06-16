# QCP Resource Reclaim Errors

这个文档记录 QCP 在局部变量 / 局部数组生命周期结束时回收内存失败的排查方式。典型报错包括 `remove permission failed`，或在 `return`、函数尾、局部 scope 结束处出现的局部变量内存回收失败。

## 触发含义

这类错误通常不是 Rocq proof 问题，而是 annotation 中的 separation logic 资源不完整。QCP 在离开函数或 scope 时需要回收当前 scope 内的局部变量内存；如果 assertion 里缺少某个局部变量的 permission / store，或只保留了局部数组的一部分内存段，回收就会失败。

常见原因：

- annotation 中漏掉了某些 live 局部变量的资源，例如局部 `store_*(&x, v)` 被前面的 `Assert` / `Inv Assert` 丢掉。
- 循环不变量只保留了局部数组的已写前缀或某个 `seg`，但在 `return` 前没有合回完整数组。
- 未初始化局部数组被建模成碎片资源，函数结束前没有完整的 `undef_full` 或 `full`。
- 使用 `by local` 导出纯事实后，误以为它也会保留局部变量的空间资源。
- 为了补权限额外叠加 `has_permission(&x)`，反而和已有 live local store 形成重复资源；应保留精确 store / array 谓词，而不是叠加裸 permission。

## 必查位置

如果报错发生在 `return` 或 scope 结束处，不要只看报错行本身。应使用 `qcp-mcp` 检查失败点上一句的 symbolic state：

1. 在 annotation C scratch 上加载目标文件。
2. 运行到失败附近；如果整体 `symbolic` 在 `return` 行失败，先对 `return` 上一行执行 `check`。
3. 查看 symbolic state 中是否包含当前 scope 的所有局部变量资源。
4. 对局部数组，确认 state 中是完整的一整段数组资源，而不是只剩部分 `seg` / `missing_i` / 前缀后缀碎片。

判断标准是：在进入 `return` / scope 结束前，assertion 必须足以让 QCP 回收该 scope 内全部局部变量和局部数组。

## 局部数组要求

局部数组尤其容易触发这个问题。比如：

```c
int a[2003];
```

在 `return` 前，assertion 中应有完整数组资源，例如：

```c
/*@ IntArray::undef_full(a, 2003) */
```

或者如果数组内容已经被逻辑列表 `l` 精确描述：

```c
/*@ IntArray::full(a, 2003, l) */
```

如果循环中维护的是分段资源，例如“已写前缀 + 未写后缀”，则在离开函数前需要通过 `Assert` 或循环后状态把这些资源合回完整的 `IntArray::full(a, 2003, l)` 或 `IntArray::undef_full(a, 2003)`。不要让 `return` 前只剩：

```c
/*@ IntArray::seg(a, 0, i, l1) ** IntArray::undef_seg(a, i, 2003) */
```

除非当前 QCP 策略能够在该点自动合回完整数组，并且 `check` 的 symbolic state 已确认合回成功。保守做法是在 `return` 前显式放置能得到完整数组资源的 `Assert`。

## 修复方式

- 缺普通局部变量：把对应 `store_*(&x, v)` 保留在需要跨过 `Assert` / `Inv Assert` 的 frame 中。
- 缺局部数组：使用 `IntArray` / `UIntArray` / `CharArray` 等 builtin 谓词，补齐完整 `full` / `undef_full`，或先把分段资源合并。
- 缺纯边界事实导致合并失败：补上数组长度、下标范围、前后缀边界等纯事实。
- scope 内声明的临时变量被 assertion 丢掉：检查最近的 `Assert` 是否只写了算法性质而漏掉 local store。
- 如果报错来自下游 witness 或 proof 阶段，应回流 annotation，不能在 manual proof 中硬证明过去。

## Report 记录

annotation-subagent 返回时，如果本轮修复了这类问题，应在 `qcp-mcp` 摘要中记录：

- QCP 原始失败行号和错误信息。
- `check` 的行号，通常是失败点上一句。
- 失败前 symbolic state 中缺少哪个局部变量 / 数组资源。
- 最终补入或合回的资源形态，例如 `store_int(&x, v)`、`IntArray::undef_full(a, 2003)` 或 `IntArray::full(a, 2003, l)`。
