# Predicate-First Annotation

这个文档专门约束一种常见但不希望继续扩散的做法：

- 先在 Rocq 中把 C 算法重新定义一遍
- 再让 annotation 和后续 proof 去追这份 Rocq 算法镜像

对于当前 agent workflow，这种做法通常会带来三个问题：

1. annotation 变弱，真正该在 C 层表达的运行时性质被推迟到了 Rocq proof。
2. VC 结构被迫围绕“算法解释器”组织，证明更脆、更难回流。
3. 一旦 annotation 需要返工，Rocq 侧的算法镜像也会连锁失效，增加无谓维护成本。

## 默认原则

- direct proof:
  - 默认采用 `predicate-first annotation`
  - 优先写“人类会先说出来”的隐藏性质
- refinement proof:
  - 可以保留 proof type 已要求的 `safeExec` / monad 规格
  - 但局部循环状态、前后缀关系、已处理区间、候选最优值，仍应尽量在 annotation 中直接表达

一句话说，就是：

先把程序运行时的局部语义写成谓词，再决定需要哪些 helper lemma；不要先写 Rocq 算法。

在当前 workflow 中，这句话还包含一个前置步骤：先在本轮 `annotation_scratch_lib` 中确认 spec 定义本身是严格数学性质。如果 spec 缺失或是算法镜像，应先修正 `annotation_scratch_lib`，再写 C 侧 annotation。

## 什么叫“隐藏性质”

隐藏性质不是“把代码换一种语言重写”，而是把循环每一步真正维护的数学事实抽出来。

典型形态包括：

- 已处理前缀 / 未处理后缀
- 已归并前缀 / 左右待处理区间
- 当前候选最优值
- 某个边界点对应的 suffix / prefix / subarray 性质
- 已写前缀 + 未写后缀
- permutation / sorted / bounded / shape-preserved

这些性质应该优先出现在：

- `Require`
- `Ensure`
- `Assert`
- `Inv Assert`

而不是优先出现在一个新造的 Rocq 算法递归定义里。

## 正反例

### 反例：`.agents/skills/annotation-filling/docs/incorrect-examples/max_sub_array_*`

反例特征：

- 在 Rocq 中定义 `kadane_loop`
- 进一步定义 `max_suffix_sum` / `max_subarray_sum` 直接追随该递归器
- annotation 依赖这些“算法镜像”来陈述 loop state

这条路线的问题不在于“递归定义写不出来”，而在于它把本该在 annotation 里暴露的局部性质，替换成了对算法执行器的跟踪。

### 正例：`QCP_examples/QCP_demos_LLM/majorityElement.c`

推荐写法的关键点：

- 允许保留很小的性质接口：
  - `count`
  - `IsMajorityElement`
  - `MajorityOnReduced`
- 把核心语义写成直观谓词：
  - 当前候选值和票数表示的约简状态
  - 约简后剩余列表中多数元素仍被保留
- invariant 直接表达：
  - 当前 `vote` 与 `candidate` 的关系
  - 当前剩余后缀 `l2` 与全局多数元素的关系

这里的重点不是“定义数量更少”，而是：

- 定义描述的是性质，不是算法步骤
- annotation 本身已经足够解释 C 程序在干什么

### 二分正例：`docs/split_array_largest_sum/`

`split_array_largest_sum` 用于学习“二分答案 + check 函数”的 annotation 方式。它不是让 Rocq 重写 C 的二分循环，而是先用 `MaxMinLib` 中的 `min_value_of_subset` / `max_value_of_subset` 给出最大段和最小值的数学定义，再用 C annotation 维护二分区间中的答案约束。

关键结构：

- `check` 的 `Ensure` 只暴露判定性质：`CanSplit(l, m, cap)` 或 `CannotSplit(l, m, cap)`。
- 主循环 invariant 只维护答案在 `[left, right]` 内：`left <= res && res <= right && MinimizedMaxSegmentSum(l, m, res)`。
- Rocq helper lemma 负责连接 `CanSplit` / `CannotSplit` 与 `MinimizedMaxSegmentSum` 的上下界，不把 C 二分过程定义成新的 Rocq 程序。

完整教学说明见 `docs/split_array_largest_sum/binary-search-annotation.md`。

## 向 `QCP_demos_LLM` 学什么

可以从下面这些例子学 annotation 风格，而不是照抄 formal 结构：

- `QCP_examples/QCP_demos_LLM/int_array_merge_rel.c`
- `QCP_examples/QCP_demos_LLM/sll_merge_rel.c`

重点观察：

- 它们会先把“当前区间切成哪几段”写清楚
- 会把“已经处理到哪里”写成局部状态
- 会把 safeExec / 纯性质和 spatial 谓词并列组织
- 不会为了描述循环，就先构造一个一比一追随 C 控制流的 Rocq 算法解释器

## 允许 / 警惕 / 阻止

### 允许

- 为了表达性质接口而引入的小定义：
  - `subarray_sum`
  - `suffix_sum`
  - `prefix_sum`
  - 简单的“最优性”存在性谓词
- 为了连接 annotation step 而写的小 lemma
- refinement proof 所必需的 `safeExec` / monad 规格

### 警惕

- 新定义开始一比一复现 loop 里的状态推进
- invariant 里大部分语义都依赖“先跑 Rocq 算法定义再得到的结果”
- 你发现自己在证明“Rocq 算法和 C 算法同步前进”，而不是证明 annotation 的局部性质

### 直接阻止

- 在 direct proof 中新引入明显的算法镜像 `Fixpoint` / 状态机定义，只是为了弥补 annotation 没写出局部性质
- 把 annotation 写成“Rocq 算法定义的投影”，而不是程序运行时状态的说明

## 设计 checklist

开始写 annotation 前，先依次回答：

1. 这个循环每轮真正维护的局部事实是什么？
2. 这些事实能否写成 prefix / suffix / seg / shape / optimality 谓词？
3. 若要引入新定义，它描述的是性质，还是在重放算法？
4. 如果 Rocq proof 失败，应该补 helper lemma，还是说明 annotation 还不够好？

如果第 3 个问题的答案更接近“在重放算法”，就先回退，继续改 annotation。
