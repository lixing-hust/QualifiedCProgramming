# LeetCode Verification Workspace

这个目录现在采用两段链路：

- Annotate: 生成验证输入
- Verify: 验证规格输入

## Annotate: 生成验证输入

目标：把原始题意和原始 C 整理成 Verify 可直接消费的正式输入。

入口说明见：
- `skills/annotate/SKILL.md`
- `doc/ANNOTATE.md`

Annotate 的正式输出是：
- `input/<name>.c`
- `input/<name>.v`，如果需要额外 Coq 定义
- `output/annotate_<timestamp>_<name>/raw/<name>.md`
- `output/annotate_<timestamp>_<name>/input/`
- `output/annotate_<timestamp>_<name>/logs/`

## Verify: 验证规格输入

目标：消费 Annotate 产物，补中间断言和循环不变式，完成 symbolic 与证明。

入口说明见：
- `skills/verify/SKILL.md`
- `doc/VERIFY.md`

运行方式：

```bash
python3 run_codex_verify.py input/<name>.c <function_name>
```

脚本会：
- 创建 `output/verify_<timestamp>_<name>/`
- 复制 `input/<name>.c` 到 `original/` 和 `annotated/`
- 如果存在 `input/<name>.v`，复制到 `original/`
- 默认使用 `skills/verify/SKILL.md`
- 要求模型在 `annotated/<name>.c` 中补 `Assert` / `which implies` / `Inv`
- 在 `logs/` 下记录 reasoning、issues、metrics
- 生成并检查 Coq 证明产物

## Layout

- `input/`: Annotate 产出的正式输入
- `output/`: annotate 和 verify 各自独立的运行目录
  annotate workspace 约定为：
  `annotate_<timestamp>_<name>/`
  `raw/` 保存原始 markdown 输入，
  `input/` 保存本次 annotate 产出的输入快照，
  `logs/` 保存 annotate 阶段经验记录；
  verify workspace 约定为：
  `verify_<timestamp>_<name>/`
  `original/`、`annotated/`、`coq/generated/`、`logs/` 保存 verify 阶段产物
- `scripts/run_codex_verify.py`: Verify driver
- `scripts/run_codex_annotate.py`: Annotate driver
- `doc/`: 分阶段文档
- `skills/annotate/SKILL.md`: Annotate skill
- `skills/verify/SKILL.md`: Verify skill
- `SKILL.md`: 总览入口
