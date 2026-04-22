# Proof Reasoning for climbStairs

## 当前剩余 witness 与难点
- 当前 `proof_manual.v` 仅手工证明 `proof_of_climbStairs_safety_wit_7`。
- 难点是循环体赋值 `cur = prev1 + prev2` 的整型上界，需证明 `prev1 + prev2 <= INT_MAX`。
- 结合不变式可化为：
  - `prev1 = climb_stairs_z(i-1)`
  - `prev2 = climb_stairs_z(i-2)`
  - `2 <= i <= n_pre + 1` 且 `0 <= n_pre <= 45`
  - 目标变成 Fibonacci 值在 `44/43` 处的上界。

## 证明模式与拆解顺序
- 先 `Intros; subst; entailer!` 拆 heap 与纯命题。
- 对纯算术子目标分两步：
  - 非负性：`climb_stairs_nat_pos` 给出 `1 <= climb_stairs_nat _`，因此和也非负。
  - 上界：用 `climb_stairs_nat_le`（单调）把 `i-1` 和 `i-2` 约束到 `44/43`，再用常量引理 `climb44_val`、`climb43_val` 收束到 `1836311903 <= INT_MAX`。

## 依赖 goal / proof_auto
- 该手工引理直接对齐 `goal.v` 的 `climbStairs_safety_wit_7` 形状：
  - 所有程序变量和不变式约束都来自 `goal`。
  - 其余 witness 仍由 `proof_auto` 提供（不在本轮手工展开）。

## 辅助引理计划
- 需要的辅助引理仅为通用数值性质：
  - `climb_stairs_nat_step`
  - `climb_stairs_nat_pos`
  - `climb_stairs_nat_mono_step`
  - `climb_stairs_nat_le`
  - `climb44_val`、`climb43_val`
- 不新增题外语义引理，不改 `goal/proof_auto`。
