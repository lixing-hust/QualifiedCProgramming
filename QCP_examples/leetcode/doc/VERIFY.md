# Verify: 验证规格输入

Verify 只消费 Annotate 的正式输出：
- `input/<name>.c`
- `input/<name>.v`，如果存在

## 基本假设

- `input/<name>.c` 已经是验证友好的 C
- 其中已有的 `Require` / `Ensure` / `With` 已经正确
- Verify 默认信任这些前后条件，不把“修规格”当默认任务

## Verify 的工作

- 在 `annotated/<name>.c` 中补 `Assert` / `which implies` / `Inv`
- 运行 symbolic / qcp
- 写 `logs/annotation_reasoning.md`
- 写 `logs/proof_reasoning.md`
- 写 `coq/generated/<name>_proof_manual.v`
- 完成最终检查

## Verify 不负责的内容

- 重写自然语言题意
- 重构原始代码为验证友好形态
- 从题意重新生成前后条件

这些都属于 Annotate。
