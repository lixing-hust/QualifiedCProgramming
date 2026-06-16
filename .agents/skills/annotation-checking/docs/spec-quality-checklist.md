# Spec 质量检查清单

本文件给 `annotation-checking` 提供具体判定要点。检查目标不是证明所有 VC，而是在 symexec 之前判断 annotation 和 `annotation_scratch_lib` spec 是否值得进入后续证明流程。

## 先检查 annotation_scratch_lib spec

对每个出现在 C annotation 中的外部 Rocq 谓词，先在 `annotation_scratch_lib` 中确认：

- 定义是否存在。
- 名称和参数是否与 C annotation 中的使用一致。
- 定义是否描述数学性质，而不是重写 C 程序。
- 定义是否足够抽象，能由不同实现满足。
- 定义是否足够强，能推出函数 `Ensure` 想要的结论。
- 定义是否足够弱，不把某个具体实现策略误写成唯一允许行为。

如果定义不存在或不合理，先修改 `annotation_scratch_lib`，再回到 C annotation。

## 再检查函数规格

函数规格按三部分分解：

1. 变量范围约束：支撑整数安全、下标范围和循环界限。
2. 内存相关部分：描述分离逻辑资源，例如数组 full / seg / shape。
3. 逻辑性质部分：描述函数的数学效果。

通过标准是：第三部分必须能回答“这个函数数学上完成了什么”。如果 `Ensure` 只有返回值范围和内存保持，不足以通过 checking。

典型问题：

- `Ensure` 只说 `0 <= ret <= 1`，但没有说明 `ret == 1` / `ret == 0` 分别代表什么。
- 排序函数只说输出数组存在，没有说明 sorted / permutation / 与输入列表关系。
- 搜索函数只说返回下标范围，没有说明找到或未找到的语义。
- 优化问题只说返回值在边界内，没有说明最优性、可行性或极值定义。

## 最后检查 invariant

重点检查 `Inv Assert`，普通 `Assert` 只按其连接作用检查。

loop invariant 至少应包含：

- 执行事实：变量范围、下标关系、整数溢出边界。
- 空间事实：当前持有的数组 / 链表 / buffer 资源。
- 逻辑事实：已经处理部分与整体目标之间的数学关系。

常见失败形态：

- invariant 只有 `0 <= i <= n` 和数组资源，没有描述已处理前缀的语义。
- invariant 直接引用一份 Rocq 版 loop 函数结果，变成“C loop 与 Rocq loop 同步”。
- invariant 的逻辑性质太弱，退出时无法推出函数 `Ensure`。
- invariant 的逻辑性质太强，循环初始化或保持性实际不成立。
- 若是完整 `Assert` / `Inv Assert`，还要额外对照 `../annotation-filling/docs/common-annotation-errors.md`，排查 `@pre` 桥接缺失、读取值绑定缺失、自反恒真式，以及 refinement case 中是否把本应只出现在 `high_level_spec` 的 functional correctness 谓词塞进了 C 侧 invariant / assert。

## 正例：split_array_largest_sum

`split_array_largest_sum` 的正确方向是先在 `annotation_scratch_lib` 中定义数学问题：

- `PartitionMaxSegmentSum` 描述某个合法分段的最大段和。
- `MinimizedMaxSegmentSum` 用 `min_value_of_subset` 描述所有合法分段最大段和中的最小值。
- `CanSplit` / `CannotSplit` 描述 `check` 函数对候选 `cap` 的判定语义。

然后 C annotation 调用这些性质：

- `check` 的 `Ensure` 用返回值连接 `CanSplit` / `CannotSplit`。
- 主二分循环 invariant 用 `exists res, left <= res && res <= right && MinimizedMaxSegmentSum(l, m, res)` 说明真实答案被当前区间夹住。

这个例子的关键是：`annotation_scratch_lib` spec 描述最大段和最小值这个数学对象，C 程序证明自己满足该对象，而不是在 Rocq 中重新定义二分程序。

## 反例：max_sub_array incorrect example

`annotation-filling/docs/incorrect-examples/max_sub_array_lib.v` 展示了不推荐方向：

- 先定义 `kadane_loop` 来复现 C 算法。
- 再让 `max_suffix_sum` / `max_subarray_sum` 依赖这个 loop。
- C annotation 很容易变成追踪这份 Rocq 算法镜像。

checking 时应识别这种模式。正确方向应是使用 `subarray_sum`、`IntuitiveMaxSuffixSum`、`IntuitiveMaxSubArraySum` 这类数学性质定义，再让 C invariant 表达当前前缀上的最大后缀和 / 最大子段和关系。

## 返回建议

- spec 缺失：返回 `failed`，要求在 `annotation_scratch_lib` 中补充数学定义。
- spec 是算法镜像：返回 `failed`，要求重写为性质定义。
- spec 正确但 C annotation 没调用：返回 `failed`，要求修改函数 spec / invariant。
- spec 和 C annotation 都合理，但 qcp 仍失败：返回 `blocked` 或交给后续 VC checking，取决于失败是否已经是生成后 witness 层问题。
