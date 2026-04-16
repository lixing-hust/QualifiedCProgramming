# Symexec Experience

本文件只记录 symbolic execution / `qcp` 相关经验。

不记录：

- `Assert` / `which implies` 的写法（见 `ASSERTION.md`）
- 循环 invariant 的设计（见 `INV.md`）
- manual proof（见 `PROOF.md`）
- Coq 编译与 load-path（见 `COMPILE.md`）

## 1. 自动 verify 进程卡住时，不要继续空等

典型现象：

- `codex_stderr` 持续出现 `channel closed`
- `Read-only file system`
- stdout/stderr 长时间不再增长
- 外层脚本还活着，但没有新产物

处理方法：

- 先停止自动进程，接管当前 workspace
- 检查当前 workspace 是否已经有：
  - `annotated/<name>.c`
  - `coq/generated/<name>_goal.v`
  - `coq/generated/<name>_proof_auto.v`
  - `coq/generated/<name>_proof_manual.v`
- 如果这些文件已经生成，就不要重开新 workspace，直接在当前 workspace 继续
- 只有当 `annotated/` 或 `coq/generated/` 明显不完整时，才考虑从头再跑

原则：

- 自动流程卡住，优先保住已生成产物
- 不要因为外层脚本假活，就重复启动多个 verify 进程

## 2. 每次注释改动后都必须重新 `symexec`

只要你改了下面任一内容，就必须重新跑 `symexec`：

- `Inv`
- `Assert`
- `which implies`
- loop-exit assertion
- 任何会改变 VC 形状的中间注释

不要继续沿用旧的：

- `goal`
- `proof_auto`
- `proof_manual`
- `goal_check`

## 3. `symexec` 失败时，先检查注释与控制点是否对齐

先检查：

- invariant 写的是“进入循环判断点”的状态，还是“循环体执行后”的状态
- `Assert` 是否放在真正的阶段切换点
- 局部展开是否和当前读写语句匹配
- 退出条件是否已经被显式固定

很多 symbolic 失败不是 proof 问题，而是注释没有贴住程序控制点。

## 4. 头文件路径问题先在 `annotated/<name>.c` 修，不要改 `input/<name>.c`

典型现象：

- `symexec` 在 verify workspace 里一开始就找不到头文件

原因：

- `input/<name>.c` 的相对路径是相对于 `input/`
- verify 真正运行的是 `output/verify_<timestamp>_<name>/annotated/<name>.c`

处理方法：

- 只修改 workspace 内的 `annotated/<name>.c`
- 把头文件改成从 `annotated/` 出发的正确相对路径
- 不要回写 `input/<name>.c`，因为那是 contract 正式输出

这类问题属于 verify workspace 适配，不属于 contract 错误。

## 5. witness 形状脏，通常是注释层信息组织不对

如果生成的 witness 非常绕、重复、纯命题很乱，优先怀疑：

- invariant 缺参数不变关系
- `Assert` 放错位置
- shape/value 语义混写
- 不该展开的谓词提前展开了

先回去整理 `annotated/<name>.c`，通常比在 `proof_manual.v` 里硬扛更便宜。

## 6. 当前 `goal_check` 没过时，不能把任务算完成

即使下面这些都已经存在：

- `goal.v`
- `proof_auto.v`
- `proof_manual.v`

也不能直接判完成。

必须再确认：

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.`
- `proof_manual.v` 无新增 `Axiom`

自动流程曾出现过“前面文件已生成，但 `goal_check` 仍未闭环”的情况，因此完成判断必须以 `goal_check` 为准。

## 7. `metrics.md` 里要单独记 `symexec`

verify 阶段的 `metrics.md` 至少要单列：

- `symexec_start`
- `symexec_end`
- `symexec_elapsed`

不要只记“编译时间”或“proof 时间”。

## 8. `issues.md` 里要保留 symbolic 过程问题

即使最后修好了，也要记：

- 现象
- 原因
- 处理
- 结果

例如：

- invariant 校验点卡住
- witness 数量变化
- 退出断言缺失导致 return_wit 异常
