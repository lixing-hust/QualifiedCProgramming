# 参考案例

正式模板优先参考 `QCP_demos_LLM`；设计 annotation 风格时，可对照同目录正例与仓库内反例。

## 普通 annotation

- `QCP_examples/QCP_demos_LLM/sum.c`
- `QCP_examples/QCP_demos_LLM/sll.c`
- `QCP_examples/QCP_demos_LLM/functional_queue.c`
- `QCP_examples/QCP_demos_LLM/majorityElement.c`

## refinement / safeExec annotation

- `QCP_examples/QCP_demos_LLM/sll_merge_rel.c`
- `QCP_examples/QCP_demos_LLM/kmp_rel.c`
- `QCP_examples/QCP_demos_LLM/int_array_merge_rel.c`

## 风格正例

- `QCP_examples/QCP_demos_LLM/majorityElement.c`
  - 用 `MajorityOnReduced` 抓投票算法的运行时隐藏性质，而不是在 invariant 里追一份 Rocq 版循环状态机。
- `.agents/skills/annotation-filling/docs/split_array_largest_sum/split_array_largest_sum.c`
  - 用 `CanSplit` / `CannotSplit` 连接 `check` 函数，用 `MinimizedMaxSegmentSum` 描述二分主循环夹住的数学答案；详细说明见 `split_array_largest_sum/binary-search-annotation.md`。
- `QCP_examples/QCP_demos_LLM/int_array_merge_rel.c`
  - 用分段谓词和局部 safeExec 状态描述“已经处理了哪一段”，而不是把 merge 过程再编码一遍。
- `QCP_examples/QCP_demos_LLM/sll_merge_rel.c`
  - 适合学习“人类证明里会先说什么局部性质”，以及如何把这些性质体现在 annotation 上。

## 风格反例

- `incorrect-examples/max_sub_array.c`
- `incorrect-examples/max_sub_array_lib.v`
  - 这些文件展示了不推荐的路径：先在 Rocq 里引入 `kadane_loop` / `max_subarray_sum` 这类算法镜像，再让 annotation 和 proof 去追这个模型。
  - 在 `annotation-checking` 中应把它作为 spec 质量反例：先指出 Rocq 定义在复现算法，再要求回到 `annotation_scratch_lib` 改为严格数学性质。

## 使用建议

- 先选“数据结构形状最接近”的案例，再看控制流是否相似。
- 先确认 `annotation_scratch_lib` spec 定义是否正确，再参考 C annotation 形状；不要在 spec 未审过时直接填 `Require` / `Ensure`。
- 如果算法很容易诱导你去写 Rocq 版递归定义，先看 `majorityElement.c` 和上面的反例对照，再动手写 annotation。
- refinement case 优先对照已有 `safeExec`/monad 映射案例，不要从普通 separation logic case 生搬硬套。
- 参考 `QCP_demos_LLM` 时，学的是隐藏性质和 annotation 表达方式，不是直接照抄 formal 文件边界。
