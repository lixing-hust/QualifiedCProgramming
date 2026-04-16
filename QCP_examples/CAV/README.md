# LeetCode Verification Architecture

这个目录是一个两阶段验证流水线，目标是把算法题从原始题意转成可回放的形式化验证结果。

## Pipeline

### 1) `contract` 阶段

职责：把 `raw/*.md`（题意+代码）转成 Verify 可直接消费的规格输入。

输入：
- `raw/<name>.md`

产物：
- `input/<name>.c`（必须）
- `input/<name>.v`（可选，仅当 C 规格依赖额外 Coq 定义）
- `output/contract_<timestamp>_<name>/...`

关键约束：
- 只写 contract（`Require/Ensure/With`）
- 不提前写 `Inv/Assert/which implies`

### 2) `verify` 阶段

职责：消费 `input`，补中间注释并完成 `symexec + proof + goal_check`。

输入：
- `input/<name>.c`
- `input/<name>.v`（若存在）

产物：
- `output/verify_<timestamp>_<name>/annotated/<name>.c`
- `output/verify_<timestamp>_<name>/coq/generated/*.v`
- `output/verify_<timestamp>_<name>/logs/*.md`

关键约束：
- `proof_auto.v` 视为自动产物，不手改
- 手工证明只落在 `coq/generated/<name>_proof_manual.v`
- 最终以 `goal_check.v` 通过为准

## Data Flow

1. `raw/<name>.md`  
2. `scripts/run_codex_contract.py` 调用 `skills/contract/SKILL.md`  
3. 生成 `input/<name>.c`（+可选 `.v`）  
4. `scripts/run_codex_verify.py` 调用 `skills/verify/SKILL.md`  
5. 生成 `verify_<timestamp>_<name>` workspace  
6. `coq/generated/<name>_goal_check.v` 编译通过，任务完成

## Directory Responsibilities

- `skills/contract/SKILL.md`：contract 主流程
- `skills/verify/SKILL.md`：verify 主流程
- `doc/experiences/README.md`：经验文档总入口与职责边界
- `doc/experiences/CONTRACT.md`：contract 经验
- `doc/experiences/SYMEXEC.md`：symbolic 执行与 witness 对齐经验
- `doc/experiences/ASSERTION.md`：`Assert` / `which implies` / bridge assertion 经验
- `doc/experiences/INV.md`：循环 invariant 经验
- `doc/experiences/PROOF.md`：`proof_manual.v` 手工证明经验
- `doc/experiences/COMPILE.md`：Coq 编译与 `goal_check` 校验经验
- `scripts/run_codex_contract.py`：contract 自动执行器
- `scripts/run_codex_verify.py`：verify 自动执行器
- `run_codex_verify.py`：verify 执行器薄封装入口

## Workspace Layout

### Contract workspace

- `output/contract_<timestamp>_<name>/raw/`
- `output/contract_<timestamp>_<name>/input/`
- `output/contract_<timestamp>_<name>/logs/`

### Verify workspace

- `output/verify_<timestamp>_<name>/original/`
- `output/verify_<timestamp>_<name>/annotated/`
- `output/verify_<timestamp>_<name>/coq/generated/`
- `output/verify_<timestamp>_<name>/logs/`

## Common Commands

```bash
# Contract
python3 scripts/run_codex_contract.py raw/<name>.md --function-name <func>

# Verify
python3 scripts/run_codex_verify.py input/<name>.c <func>
```

## Logging and Metrics

两个阶段都要求在各自 workspace 的 `logs/` 下记录：

- `reasoning`（阶段思考）
- `issues`（过程问题：现象/原因/处理/结果）
- `metrics`（整任务时间 + 分阶段时间）

verify 阶段额外要求记录 proof 相关推理与编译回放结果。
