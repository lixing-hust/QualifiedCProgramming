# Annotation Reasoning for climbStairs

## 语义理解
函数计算爬楼梯方案数：每次可走 1 或 2 阶。设 `f(0)=1, f(1)=1`，则 `f(n)=f(n-1)+f(n-2)` (`n>=2`)。
规格已给出返回值应为 `climb_stairs_z(n@pre)`，并且输入范围 `0 <= n <= 45`。

## 规格边界
本阶段不改 `Require/Ensure`，仅补 Verify 负责的中间注解。

## 循环状态建模
循环头维持：
- `prev2 == climb_stairs_z(i-2)`
- `prev1 == climb_stairs_z(i-1)`
- `cur == prev1`
- `2 <= i <= n@pre + 1`
- `n == n@pre`

这样每轮执行 `cur = prev1 + prev2; prev2 = prev1; prev1 = cur;` 后可继续保持状态，且退出时直接得到
`cur == prev1 == climb_stairs_z(n@pre)`。

## 关于 `cur` 初始化
在注释版 C 中将 `cur` 初值设为 `1`，用于让循环不变式在 `i=2` 的循环入口立即成立。
该改动不改变函数可观察语义：
- `n <= 1` 时提前 `return 1`，不读取 `cur`；
- `n >= 2` 时循环首句会覆盖 `cur`。

## 中间断言与退出断言
循环后补 `Assert` 固定返回语义：
- `cur == climb_stairs_z(n@pre)`
- `n == n@pre`

## 风险检查
- 溢出：`n<=45` 时结果在 32-bit `int` 范围内。
- 指针/别名：函数无堆访问，`emp` 保持。
