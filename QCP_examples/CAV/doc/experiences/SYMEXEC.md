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
- stdout/stderr 长时间不再增长
- 外层脚本还活着，但没有新产物

处理方法：

- 先停止自动进程，接管当前 workspace
- 检查是否已经生成：
  - 当前任务对应的 `annotated/verify_<timestamp>_<name>.c`
  - `coq/generated/<name>_goal.v`
  - `coq/generated/<name>_proof_auto.v`
  - `coq/generated/<name>_proof_manual.v`
- 已生成的产物优先复用，不要重复开新 workspace

## 2. 每次注释改动后都必须重新 `symexec`

只要你改了下面任一内容，就必须重新跑 `symexec`：

- `Inv`
- `Assert`
- `which implies`
- loop-exit assertion
- 任何会改变 VC 形状的中间注释

不要继续沿用旧的 `goal`、`proof_auto`、`proof_manual`、`goal_check`。

重新跑当前 workspace 的 `symexec` 之前，必须先清理旧的 generated 文件：

- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_proof_manual.v`
- `coq/generated/<name>_goal_check.v`
- `coq/generated/<name>_proof_check.v`，如果存在

否则工具可能因为旧的 `proof_manual.v` 已存在而拒绝更新，导致新的注释和旧的 witness 混在一起。

## 3. `symexec` 失败时，先检查注释与控制点是否对齐

先检查：

- invariant 写的是进入循环判断点的状态，还是循环体执行后的状态
- `Assert` 是否放在真正的阶段切换点
- 局部展开是否和当前读写语句匹配
- 退出条件是否已经被显式固定

很多 symbolic 失败不是 proof 问题，而是注释没有贴住程序控制点。

## 4. `symexec` 成功后先分流，不要机械回注释层

`symexec` 成功后，先判断剩余问题属于哪一层。

如果剩下的是这些问题，就不要再回注释层：

- 纯 list witness
- 纯 arithmetic witness
- Coq side condition
- 只差 helper lemma、rewrite、case split

这类问题已经进入 proof 阶段，继续改注释通常只会浪费时间。

只有在下面这些现象出现时，才应回注释层：

- witness 明显缺 shape / ownership 信息
- `return_wit` 或 `entail_wit` 反复重建“参数未变”“数组未变”这类语义
- 退出后条件需要大量额外语义，说明 invariant 太弱
- witness 里出现和控制点不对应的旧状态、错位状态

判断原则：

- 缺程序语义，回注释层
- 缺纯命题桥接，不回注释层

## 5. 顶层 `annotated/` 目录就是为避免头文件路径报错

verify 的实际工作副本固定放在：

- `annotated/verify_<timestamp>_<name>.c`

它和 `input/` 是同层目录，所以像 `../../verification_stdlib.h` 这类相对头文件路径通常可以直接沿用，不需要再在每个 workspace 里手改 include。

如果还报头文件找不到，优先检查：

- 当前 `qcp` / `symexec` 跑的是不是这个顶层 `annotated/*.c`
- 是否误用了旧 workspace 里的历史 `annotated` 副本

不要把这类问题回退成修改 `input/<name>.c`。

## 6. 公共 strategy 预编译后，不要再为每题重复 staging `coq/deps/`

如果下面这些公共产物已经存在：

- `SeparationLogic/examples/int_array_strategy_goal.vo`
- `SeparationLogic/examples/int_array_strategy_proof.vo`
- `SeparationLogic/examples/uint_array_strategy_goal.vo`
- `SeparationLogic/examples/uint_array_strategy_proof.vo`
- `SeparationLogic/examples/undef_uint_array_strategy_goal.vo`
- `SeparationLogic/examples/undef_uint_array_strategy_proof.vo`
- `SeparationLogic/examples/array_shape_strategy_goal.vo`
- `SeparationLogic/examples/array_shape_strategy_proof.vo`

后续 verify 应直接复用公共 `examples/`，不要再把这些文件复制到当前 workspace 的 `coq/deps/`。

只有公共编译产物缺失，或当前环境读不到它们时，才回退到 workspace-local `coq/deps/`。

## 7. witness 形状脏，通常是注释层信息组织不对

如果生成的 witness 很绕、重复、纯命题很乱，优先怀疑：

- invariant 缺参数不变关系
- `Assert` 放错位置
- shape/value 语义混写
- 不该展开的谓词提前展开了

先回去整理当前任务的 `annotated/*.c`，通常比在 `proof_manual.v` 里硬扛更便宜。

## 8. 当前 `goal_check` 没过时，不能把任务算完成

即使已经有：

- `goal.v`
- `proof_auto.v`
- `proof_manual.v`

也不能直接判完成。

必须再确认：

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.`
- `proof_manual.v` 无新增 `Axiom`

## 9. `metrics.md` 里要单独记 `symexec`

verify 阶段的 `metrics.md` 至少要单列：

- `symexec_start`
- `symexec_end`
- `symexec_elapsed`

## 10. `issues.md` 里要保留 symbolic 过程问题

即使最后修好了，也要记：

- 现象
- 原因
- 处理
- 结果
