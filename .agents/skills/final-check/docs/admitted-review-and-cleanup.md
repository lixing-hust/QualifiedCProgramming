# `Admitted` Review 与收尾清理

## Review 范围

final-check 只做轻量 review，确认正式手写文件没有留下未证明定理或额外假设。

必须检查：

- `*_proof_manual.v` 中不得出现 `Admitted.`。
- `common_case_formal_lib` 中不得出现 `Admitted.`。
- `*_proof_manual.v` / `common_case_formal_lib` 中不得新增额外 `Axiom`。
- `*_proof_manual.v` 中不得混入 helper lemmas 或 helper definitions，最终只允许 manual witness theorem 证明。
- `common_case_formal_lib` 冻结前缀内允许出现 annotation-checking 已通过的数学 spec 定义；冻结前缀之后允许出现 vc-proving 迁入且经脚本审计的 helper-suffix `Require Import` 行与 proved helper lemmas，但不得出现未审计 import、`Admitted`、额外 `Axiom` 或 forbidden top-level declaration。
- `*_goal.v` 的 `Axiom` 与 `*_proof_auto.v` 的 `Admitted` 属工具生成特性，只识别一致性，不计为手写文件失败，也不应手改。

建议使用 `rg` 先做文本扫描，再人工 review 命中项是否来自正式手写文件：

```bash
rg -n '\bAdmitted\.|\bAxiom\b' path/to/case_proof_manual.v path/to/case_lib.v
```

如果有命中，应直接判定 final-check 失败并回退到 `vc-proving`，除非能明确证明命中来自冻结前缀中已记录且允许的用户内容。

## 清理原则

- 不删除 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`、`common_case_formal_lib`。
- 删除这次编译和检查过程中产生的临时文件，例如当前 case 对应的 `.aux` 文件。
- 删除 `.tmp` 下本轮产生的 annotation scratch、`annotation_scratch_lib`、proving scratch、worker workdir、kept manual-goals 副本、merged scratch artifact、migrated manual artifact 和 `task_local_scratch_lib` artifact。
- 删除本轮测试或脚本生成的 `.pytest_cache` / `__pycache__` 等缓存；虚拟环境和第三方依赖缓存不属于 case 交付清理范围，除非它们是本轮 workflow 明确生成且无需保留的缓存。
- 进入 `done` 前必须再次扫描确认没有残留本轮 `.tmp` 内容、`.aux` 文件或 phase scratch。
- `Final Check Checklist` 只有在 frozen prefix、`proof_manual` 结构、symexec、coqc、`Admitted` / 额外 `Axiom` review 和临时文件清理都通过后，才允许标记为可进入 `done`。
