---
name: annotate
description: Annotate skill，生成验证友好的 `input/<name>.c` / `input/<name>.v`。
---

Annotate 的职责只有一个：把原始题意、原始 C 代码和自然语言描述整理成 Verify 可直接消费的规格输入。

## 输入

可以来自以下任意组合：
- 原始 C 实现
- 原始题意或自然语言问题描述
- 题目约束、边界条件、示例
- 现有的辅助定义草稿

### Pre-flight requirements

- 阅读 `doc/TASK_FILE_PERMISSIONS.md`、`doc/retrieval/INDEX.md`、`doc/predict/INDEX.md`，掌握权限、检索和谓词模板。  
- 仅基于允许的材料（原始实现 + 描述 + 辅助定义）准备输入。

## 输出

必须输出到：
- `input/<name>.c`
- `input/<name>.v`，如果确实需要额外 Coq 定义

这两个文件就是 Verify 的正式输入。

### 核心约束

- 你要把原始代码改写成验证友好的 C，并写完整、正确、可验证的前后条件。
- 输出包括 `input/<name>.c`（必须）和必要时的 `input/<name>.v`，其中后者只存放额外 Coq 定义；不要把注释/逻辑移到 `.v` 里。  
- `input/<name>.c` 保留原算法语义，摒弃平台 I/O、测试驱动、宏脚本，只保留目标函数和必要辅助。  
- 写完整 `Require` / `Ensure` / `With`，覆盖边界、长度、alias、空指针、溢出等；不需要 `Assert` 或 `Inv`（留给 Verify）。  
- 规格必须与自然语言题意一致，并覆盖边界情况、参数约束、别名/空指针/长度约束、溢出风险。
- `input/<name>.v` 只有在 `input/<name>.c` 的规格确实依赖额外 Coq 定义时才创建。
- `input/<name>.v` 只放题目专用定义、辅助谓词、辅助关系或必要引理声明。
- Annotate 不运行 symbolic/Coq，仅负责生成输入/规格。  
- 确保 Verify 能直接拿这两个文件进入下阶段。

## 强制规则

- `input/<name>.c` 的前后条件必须写完整，不能留 TODO。
- 如果自然语言题意有歧义，按最保守且与现有代码一致的解释写入规格。
- 优先保持原程序语义不变；若必须做验证友好改写，要保持功能等价。
- 不要在 Annotate 中补 `Assert` / `Inv`，这些属于 Verify。
- 不要把本该写进 C 规格的内容随意挪到 `.v`。

### 推荐行动

1. 阅读原始题意和原始代码。  
2. 抽取函数的输入、输出、状态约束、边界行为。  
3. 将原始代码改写成验证友好的命令式 C。  
4. 写完整的 `Require` / `Ensure` / `With`，根据 `doc/predict` 选谓词。  
5. 判断是否真的需要 `input/<name>.v`。  
6. 自检规格是否和自然语言题意一致、是否覆盖异常边界。  
7. 确认最终产物就是 `input/<name>.c` 和可选 `input/<name>.v`。  

### 成功判断

- `input/<name>.c` 形式验证友好，前后条件完整且语义清晰。  
- 规格覆盖所有边界/constraints。  
- 任何 `.v` 仅含额外逻辑定义。  
- Verify 可以直接使用这些文件启动验证流程。
