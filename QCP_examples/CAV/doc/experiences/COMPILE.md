# Compile Experience

本文件只记录 verify 阶段的 Coq 编译经验。

## 1. 编译范围

- 只记录 `goal`、`proof_auto`、`proof_manual`、`goal_check` 的编译
- 不记录 invariant/assert/symexec
- 不记录 manual proof 策略

## 2. 工作目录必须在 `SeparationLogic`

- 从 `/home/yangfp/QualifiedCProgramming/SeparationLogic` 运行 `coqc`
- 不要在 `CAV/` 目录直接编译 generated 文件

## 3. 当前 workspace 只用两个目录

- `coq/deps/`
- `coq/generated/`

## 4. 依赖先放到当前 workspace 的 `coq/deps/`

- 公共目录缺 `.vo` 或只读时，不要改公共目录
- 把 strategy `.v` 复制到当前 workspace 的 `coq/deps/`
- 先编译 `coq/deps/`

## 5. 逻辑前缀必须固定

- `-R $DEPS SimpleC.EE`
- `-R $GEN SimpleC.EE.CAV.verify_<timestamp>_<name>`

不要混用不同前缀下编出来的 `.vo`。

## 6. 编译顺序固定

1. `coq/deps/`
2. `goal.v`
3. `proof_auto.v`
4. `proof_manual.v`
5. `goal_check.v`

## 7. 常见报错先查什么

- `Cannot find a physical path ...`
  - 检查当前目录
  - 检查 `-R $DEPS`
  - 检查 `-R $GEN`
  - 检查 `coq/deps/` 是否已生成 `.vo`
- `contains library X and not library Y`
  - 先删当前 workspace 旧 `.vo/.vos/.vok/.glob/.aux`
  - 再用同一套前缀重编
- `goal_check` 失败但前三个通过
  - 检查逻辑前缀
  - 检查 `proof_manual.v` import
  - 检查 `Admitted.` / `Axiom`

## 8. task-local `.v` 本身不合法时先分流

- 如果只是 workspace 副本有问题，可以局部修
- 如果正式输入 `.v` 就不合法，应回退 contract 修

## 9. 完成标准

- `goal.v` 通过
- `proof_auto.v` 通过
- `proof_manual.v` 通过
- `goal_check.v` 通过
- `proof_manual.v` 无 `Admitted.`
- `proof_manual.v` 无新增 `Axiom`

## 10. 编译后必须清理

- `coq/generated/` 下删除非 `.v`
- `coq/deps/` 下删除非 `.v`
- 清不掉时写进 `logs/issues.md`
