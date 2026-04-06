# Proof Reasoning

本目录的 `goal/proof_auto/proof_manual` 直接复制自上游样例，并补入了 `sll_lib.v` 与 `sll_merge_rel_lib.v`。

证明的代表性在于：

- witness 里不仅有 heap entailment，还有关系式语义的重写。
- 循环每轮都要把 `safeExec` 的目标程序推进到更短的剩余列表。
- 对比普通链表 shape 题，它更接近语义化程序验证。

如果后续要检索“关系式不变式”样例，这个目录应优先进入候选集。
