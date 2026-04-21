---
name: example-export
description: 从一个已完成的 verify workspace 中整理可检索的正确例子到 `examples/`，保留验证相关文件，排除统计信息和编译中间产物。
---

这个 skill 只做一件事：把一个已经完成验证的 workspace 整理成 `examples/` 下的标准例子目录，便于后续检索和参考。

开始前先读：

- `doc/PERMISSIONS.md`
- `doc/retrieval/INDEX.md`

## 1. 输入

- 一个 verify workspace 路径：`output/verify_<timestamp>_<name>/`

## 2. 输出

- `examples/<name>/`

## 3. 保留范围

保留所有与验证直接相关的文件：

- `original/<name>.c`
- `original/<name>.v`，如果存在
- `annotated/<name>.c`
- `coq/generated/*.v`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`，如果存在
- `logs/proof_reasoning.md`，如果存在
- `logs/issues.md`，如果存在

## 4. 排除范围

不要复制这些文件：

- `logs/metrics.md`
- `logs/codex_*`
- `logs/*.log`
- `coq/` 下任何非 `.v` 文件
- `.vo`、`.vos`、`.vok`、`.glob`、`.aux`

## 5. 硬规则

- 只有在当前 workspace 已经验证完成时才整理到 `examples/`
- 输出目录名直接使用算法名 `<name>`
- `examples/` 中的内容必须足够支持后续检索和人工阅读
- 导出的 `original/<name>.c` 和 `annotated/<name>.c` 不要保留已内建的验证头文件：`verification_stdlib.h`、`verification_list.h`、`int_array_def.h`、`char_array_def.h`
- 不要把统计信息、CLI 噪声日志、编译产物带进 `examples/`
- 如果目标目录已存在，先整体覆盖为最新版本

## 6. 最短流程

1. 检查 workspace 路径是否合法，且 basename 形如 `verify_<timestamp>_<name>`。
2. 检查 `coq/generated/` 是否存在，并且至少有 `<name>_proof_manual.v`。
3. 在 `examples/` 下创建 `<name>/`。
4. 只复制“保留范围”中的文件。
5. 删除误带入的统计文件和编译中间产物。

## 7. 执行方式

优先直接运行：

```bash
python3 skills/example_export/scripts/export_verify_example.py <workspace>
```

例如：

```bash
python3 skills/example_export/scripts/export_verify_example.py output/verify_20260417_202657_bubble_sort
```
