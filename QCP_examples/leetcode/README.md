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

## Verify: 验证规格输入

目标：消费 Annotate 产物，补中间断言和循环不变式，完成 symbolic 与证明。

入口说明见：
- `skills/verify/SKILL.md`
- `doc/VERIFY.md`

运行方式：

```bash
python3 run_codex_formal_proof.py input/<name>.c <function_name>
```

脚本会：
- 创建 `output/workspace_<timestamp>_<name>/`
- 复制 `input/<name>.c` 到 `original/` 和 `annotated/`
- 如果存在 `input/<name>.v`，复制到 `original/`
- 默认使用 `skills/verify/SKILL.md`
- 要求模型在 `annotated/<name>.c` 中补 `Assert` / `which implies` / `Inv`
- 在 `logs/` 下记录 reasoning、issues、metrics
- 生成并检查 Coq 证明产物

## Layout

- `input/`: Annotate 产出的正式输入
- `output/`: Verify 生成的 `workspace_<timestamp>_<stem>/`
- `scripts/run_codex_formal_proof.py`: Verify driver
- `doc/`: 分阶段文档
- `skills/annotate/SKILL.md`: Annotate skill
- `skills/verify/SKILL.md`: Verify skill
- `SKILL.md`: 总览入口
