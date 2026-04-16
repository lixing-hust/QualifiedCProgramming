---
name: contract
description: Contract skill，生成验证友好的 `input/<name>.c` / `input/<name>.v`。
---

Contract 的职责只有一个：把原始题意、原始 C 代码和自然语言描述整理成 Verify 可直接消费的规格输入。

开始当前 contract 任务前，先阅读：

- `doc/experiences/README.md`
- `doc/experiences/CONTRACT.md`

通用经验、细节写法和判断标准统一以 `doc/experiences/` 为准，这里不重复展开。

### 文档使用策略

- 默认先基于原始题意、原始代码和当前任务直接开始 contract，不要一开始就通读所有 doc。  
- 只有在当前步骤确实缺少规则、模板、谓词或检索思路时，才按需读取对应文档。  
- 优先级如下：  
  1. 当前 raw 输入与当前任务材料  
  2. `doc/experiences/CONTRACT.md`，仅当需要确认 contract 写法与 `.v` 桥接细节时  
  3. `doc/predict/INDEX.md`，仅当需要具体谓词模板时，例如数组链表  
  4. `doc/retrieval/INDEX.md`，仅当当前步骤不会写、需要找相似题时  
  5. `doc/TASK_FILE_PERMISSIONS.md`，仅当需要确认读写边界时  
- 不要为了“全面了解”而先扫完整个文档集；文档只解决当前阻塞。  
- 仅基于允许的材料（原始实现 + 描述 + 辅助定义）准备输入。

## 输入

可以来自以下任意组合：
- 原始 C 实现
- 原始题意或自然语言问题描述
- 题目约束、边界条件、示例
- 现有的辅助定义草稿


## 输出

必须输出到：
- `input/<name>.c`
- `input/<name>.v`，如果确实需要额外 Coq 定义
- `output/contract_<timestamp>_<name>/logs/reasoning.md`
- `output/contract_<timestamp>_<name>/logs/issues.md`
- `output/contract_<timestamp>_<name>/logs/metrics.md`

其中：
- `input/<name>.c` 和可选 `input/<name>.v` 是 Verify 的正式输入。
- `output/contract_<timestamp>_<name>/logs/` 是本次 contract 任务的经验记录目录。

### 核心约束

- 你要把原始代码改写成验证友好的 C，并写完整、正确、可验证的前后条件。
- 先推进 `reasoning.md` 和 `input/<name>.c` 主线；不要先花大量时间展开文档或检索例子。  
- 输出包括 `input/<name>.c`（必须）和必要时的 `input/<name>.v`，其中后者只存放额外 Coq 定义；不要把注释/逻辑移到 `.v` 里。  
- 每次 contract 任务都必须额外生成一个 `output/contract_<timestamp>_<name>/logs/` 目录，记录本次规格设计过程。
- `input/<name>.c` 保留原算法语义，摒弃平台 I/O、测试驱动、宏脚本，只保留目标函数和必要辅助。  
- 写完整 `Require` / `Ensure` / `With`，覆盖边界、长度、alias、空指针、溢出等；不需要 `Assert` 或 `Inv`（留给 Verify）。  
- Contract 和 Verify 的边界必须保持硬分离：Contract 只产出完整 contract，不提前写循环 invariant、bridge assert、`which implies`、退出断言或其他 proof-oriented 中间注释。  
- 规格必须与自然语言题意一致，并覆盖边界情况、参数约束、别名/空指针/长度约束、溢出风险。
- `input/<name>.v` 只有在 `input/<name>.c` 的规格确实依赖额外 Coq 定义时才创建。
- `input/<name>.v` 只放题目专用定义、辅助谓词、辅助关系或必要引理声明。
- `output/contract_<timestamp>_<name>/logs/reasoning.md` 必须记录自然语言思考过程。
- `output/contract_<timestamp>_<name>/logs/issues.md` 必须记录本次 contract 阶段踩到的问题、取舍和修复。
- `output/contract_<timestamp>_<name>/logs/metrics.md` 必须记录 contract 阶段各步骤的开始时间、结束时间和耗时。
- Contract 不运行 symbolic/Coq，仅负责生成输入/规格。  
- 确保 Verify 能直接拿这两个文件进入下阶段。

## 强制规则

- `input/<name>.c` 的前后条件必须写完整，不能留 TODO。
- 如果自然语言题意有歧义，按最保守且与现有代码一致的解释写入规格。
- 优先保持原程序语义不变；若必须做验证友好改写，要保持功能等价。
- 不要在 Contract 中补 `Assert` / `Inv`，这些属于 Verify。
- 不要在 Contract 中提前加入 bridge assert、`which implies` 或 loop-exit assertion；这些都属于 Verify 对 witness 形状的控制范围。
- 不要把本该写进 C 规格的内容随意挪到 `.v`。
- 开始写 `input/<name>.c` 之前，必须先写 `output/contract_<timestamp>_<name>/logs/reasoning.md`。
- contract 过程中发现的坑、失败尝试、边界判断和最终取舍，必须写入 `output/contract_<timestamp>_<name>/logs/issues.md`。
- contract 阶段的时间记录必须写入 `output/contract_<timestamp>_<name>/logs/metrics.md`。

### 推荐行动

1. 阅读原始题意和原始代码。  
2. 创建本次任务的 `output/contract_<timestamp>_<name>/logs/` 目录。  
3. 先写 `output/contract_<timestamp>_<name>/logs/reasoning.md`，记录对输入输出、边界行为、规格形状和 Coq 依赖的判断。  
4. 抽取函数的输入、输出、状态约束、边界行为。  
5. 将原始代码改写成验证友好的命令式 C。  
6. 写完整的 `Require` / `Ensure` / `With`，根据 `doc/predict` 选谓词。  
7. 检查输出 C 中是否混入了 `Inv`、`Assert`、bridge assert、`which implies` 或退出断言；如果有，删掉并只保留 contract。  
8. 判断是否真的需要 `input/<name>.v`。  
9. 只有在第 4-8 步遇到具体阻塞时，才按需读取 `doc/` 或检索例子。  
10. 把踩坑、失败尝试、风险点和最终取舍记入 `output/contract_<timestamp>_<name>/logs/issues.md`。  
11. 在 `output/contract_<timestamp>_<name>/logs/metrics.md` 记录本阶段各步骤时间。  
12. 自检规格是否和自然语言题意一致、是否覆盖异常边界。  
13. 确认最终产物就是 `input/<name>.c`、可选 `input/<name>.v` 和本次 `output/contract_<timestamp>_<name>/logs/`。  
14. 任务结束后，选择性更新 `doc/experiences/CONTRACT.md`（只补可复用的通用经验）。  

### 成功判断

- `input/<name>.c` 形式验证友好，前后条件完整且语义清晰。  
- `input/<name>.c` 中没有提前混入 Verify 才应负责的 `Inv`、`Assert`、bridge assert、`which implies` 或退出断言。  
- 规格覆盖所有边界/constraints。  
- 任何 `.v` 仅含额外逻辑定义。  
- `output/contract_<timestamp>_<name>/logs/reasoning.md` 已记录自然语言思考过程。  
- `output/contract_<timestamp>_<name>/logs/issues.md` 已记录本次 contract 阶段的踩坑与取舍。  
- `output/contract_<timestamp>_<name>/logs/metrics.md` 已记录本阶段各步骤时间。  
- Verify 可以直接使用这些文件启动验证流程。
