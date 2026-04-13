# LeetCode Workflow Scope

本目录现在采用严格的两段流程：

- Annotate: 生成验证输入
- Verify: 验证规格输入

## Annotate

Annotate 负责：
- 从原始题意、原始代码和自然语言描述出发
- 生成验证友好的 `input/<name>.c`
- 必要时生成 `input/<name>.v`
- 写完整前后条件

## Verify

Verify 负责：
- 消费 `input/<name>.c` 和可选 `input/<name>.v`
- 补 `Assert` / `Inv`
- 运行 symbolic / qcp
- 完成 manual proof

## 核心边界

- 重新设计规格属于 Annotate
- 验证与证明属于 Verify
- 不要在 Verify 中回退成“边修规格边验证”的混合流程
