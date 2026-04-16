# Readme Experience

本目录下的 `.md` 文件是任务开始前必须阅读的通用经验。

## 1. 文档列表

- `CONTRACT.md`：contract（`Require` / `Ensure` / `With`）经验
- `SYMEXEC.md`：symbolic 执行、witness 对齐和 `symexec` 经验
- `ASSERTION.md`：`Assert` / `which implies` / bridge assertion 经验
- `INV.md`：循环 invariant 经验
- `PROOF.md`：`coq/generated/<name>_proof_manual.v` 手工证明经验
- `COMPILE.md`：Coq 编译与 `goal_check` 校验经验

## 2. 强制阅读

- 开始 contract 任务前，至少阅读 `doc/experiences/CONTRACT.md`
- 开始 verify 任务前，至少阅读：
- `doc/experiences/SYMEXEC.md`
- `doc/experiences/ASSERTION.md`
- `doc/experiences/INV.md`
- `doc/experiences/PROOF.md`
- `doc/experiences/COMPILE.md`

## 3. 更新规则

- 只写可复用、与单题细节弱耦合的结论
- 不写某一题专属的一次性细节
- 对已有规则做更正时，直接改原条目，不重复堆叠近义规则
