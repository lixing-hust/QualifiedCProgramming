# VC 检查流程

## 目标

在真正写 Rocq proof 之前，先回答两个问题：

1. 这个 VC 在当前语义下是否应该成立？
2. 如果不成立，问题最可能出在哪一层？

## 推荐流程

1. 先把 VC 看成 `P |-- Q`。
2. 拆出前条件中的空间资源、纯命题、存在量词，以及后条件需要你交付的资源和事实。
3. 判断缺失的是：
   - 形状资源
   - 纯事实
   - witness 选择
   - refinement 状态
   - 循环不变式中的信息
4. 如果前条件本身不可能推出后条件，说明 annotation 或 spec 有问题。
5. 如果目标语义合理，只是证明推进困难，再进入 `vc-proving`。
6. 对每个判为可证的 VC 写出 informal proof；proof 用到的 lemma 必须来自现有 library 或后续明确写入 `*_lib.v` 的 candidate lemma。
7. 对每个 lemma premise 写明 discharge 来源；所有 premise 都必须由当前 VC 前条件推出，不能依赖额外假设。

## Informal proof 细则

- proof 要说明如何从 `P` 构造 `Q`，不能只写“显然”或“由 invariant 得证”。
- `used_lemmas` 必须列出 lemma 名称、来源和关键前提。
- `lemma_sources` 只能是现有 library / 当前 case lib，或本轮 `candidate_lib_lemmas` 中将由 vc-proving 证明并迁入 `*_lib.v` 的 helper lemma。
- `premise_discharge` 必须逐项说明每个 premise 来自当前 VC 前条件中的哪条资源、纯事实、存在量词实例或 spec 展开。
- 如果 proof 需要额外假设、改写冻结前缀、或引入未列入 candidate lib 的 lemma，结论不能是 `proofable` / `needs-lemma`。

## 交接原则

- “不可证” 的结论要回到 annotation 层修复。
- “可证但难证” 的结论才进入 manual proof 阶段。
- lemma 来源不明或 premise 不能由当前 VC 前条件推出时，不能把 VC 判为可证。
