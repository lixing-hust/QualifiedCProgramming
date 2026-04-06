# Retrieval Index

本文件记录 `QCP_examples/leetcode/` 下所有和“检索”相关的统一约定。

目标有两个：

1. 让后续 workspace 能被稳定检索，而不是依赖自由文本模糊匹配。
2. 让模型和人工都知道 fingerprint 应该怎么写、怎么用、怎么维护。

## 1. 检索入口

每个 workspace 都必须维护：

- `logs/workspace_fingerprint.json`

它是该 workspace 的最小检索单元。

建议检索顺序：

1. 先按受控关键词过滤候选 workspace。
2. 再看 `semantic_description` 判断语义是否真的接近。
3. 最后再读 `annotation_reasoning.md`、`proof_reasoning.md`、`issues.md` 和相关证明文件。

不要一开始就全文扫描所有日志或所有 `.v` 文件。

## 2. Fingerprint 文件职责

`logs/workspace_fingerprint.json` 至少承担四个职责：

1. 标识该 workspace 对应哪个输入程序。
2. 用自然语言概括程序语义。
3. 用受控词表标出算法和证明特征。
4. 为后续检索、聚类、去重提供稳定键。

## 3. 推荐字段

最低建议字段如下：

```json
{
  "fingerprint_version": 1,
  "workspace": "workspace_20260405_233656_sum2",
  "input_file": "input/sum2.c",
  "function_name": "sum2",
  "program_sha256": "193c47db4da37e1576a54e0e0b63bd46eb17f40ef148188f75ad1c9531d90812",
  "semantic_description": "Accumulates the even arithmetic series 2 + 4 + ... + 2n by adding 2 * i for i from 1 to n. For n >= 1 it returns n * (n + 1). For n <= 0 the loop is skipped and the function returns 0.",
  "keywords": {
    "algorithm_family": ["accumulation", "arithmetic_series"],
    "control_flow": ["for_loop"],
    "data_shape": ["scalar_only"],
    "semantic_intent": ["sum_even_series"],
    "proof_pattern": ["pure_arithmetic", "loop_invariant", "closed_form"],
    "numeric_properties": ["nonnegative_input", "overflow_guard", "int_range"],
    "edge_case_behavior": ["returns_zero_on_nonpositive"],
    "verification_status": ["goal_check_passed", "manual_witness_needed", "auto_proof_contains_admitted"]
  }
}
```

说明：

- `semantic_description` 必须是自然语言，不要只写关键词堆砌。
- `keywords` 必须来自下面的受控词表，不要自由发明同义词。
- `program_sha256` 用于识别“同一程序在不同 workspace 的重复验证”。

## 4. Semantic Description 写法

`semantic_description` 建议覆盖：

1. 这个程序在做什么。
2. 输入输出的核心数学关系。
3. 关键控制结构，例如循环、分支、递归。
4. 边界行为，例如 `n <= 0` 时返回什么。
5. 是否有副作用、内存修改或只读行为。

好的例子：

- “Computes the larger of two integer inputs using a single comparison and returns either a or b exactly.”
- “Accumulates the arithmetic series 1 + 2 + ... + n with a loop accumulator and returns the triangular number for nonnegative n.”

不好的例子：

- “loop problem”
- “math”
- “simple function”

## 5. 受控词表

后续所有 fingerprint 的关键词都应该限制在下面范围内。

### 5.1 `algorithm_family`

- `identity`
- `selection`
- `counting`
- `accumulation`
- `arithmetic_series`
- `factorial`
- `prefix_sum`
- `simulation`
- `search`
- `two_pointers`
- `dynamic_programming`
- `greedy`
- `recursion`

### 5.2 `control_flow`

- `straight_line`
- `if`
- `ternary`
- `for_loop`
- `while_loop`
- `do_while`
- `nested_loop`
- `recursion`

### 5.3 `data_shape`

- `scalar_only`
- `array`
- `string`
- `pointer`
- `struct`
- `linked_list`
- `tree`
- `graph`

### 5.4 `semantic_intent`

- `return_input`
- `return_max`
- `count_iterations`
- `sum_1_to_n`
- `sum_even_series`
- `compute_factorial`
- `preserve_input`
- `in_place_update`

### 5.5 `proof_pattern`

- `pure_arithmetic`
- `loop_invariant`
- `case_split`
- `termination_by_bound`
- `closed_form`
- `monotonicity`
- `range_bound`
- `heap_reasoning`

### 5.6 `numeric_properties`

- `nonnegative_input`
- `overflow_guard`
- `int_range`
- `monotone_accumulator`
- `exact_closed_form`

### 5.7 `edge_case_behavior`

- `returns_zero_on_nonpositive`
- `returns_input_on_nonpositive`
- `defined_for_nonnegative_only`
- `branch_on_order`
- `empty_loop_possible`

### 5.8 `verification_status`

- `goal_check_passed`
- `proof_check_passed`
- `manual_witness_needed`
- `auto_proof_contains_admitted`
- `generated_goal_contains_axioms`

## 6. 关键词使用规则

### 6.1 只用受控词表

不要写：

- `sum loop`
- `max logic`
- `easy arithmetic`

应写成结构化词：

- `algorithm_family: accumulation`
- `semantic_intent: sum_1_to_n`
- `proof_pattern: pure_arithmetic`

### 6.2 一个题可以有多个标签

例如 `sum2` 同时属于：

- `accumulation`
- `arithmetic_series`
- `for_loop`
- `pure_arithmetic`
- `closed_form`

### 6.3 关键词要服务检索，不要服务修辞

关键词不是摘要，不追求“好看”，只追求：

- 稳定
- 可过滤
- 可复用
- 可聚类

## 7. 检索建议

## 7A. 给大模型的检索流程

如果你是一个在本目录中工作的模型，默认按下面顺序检索，不要跳步。

### 7A.1 第一步：先读 fingerprint，不要先读全文日志

优先读取：

- 目标 workspace 的 `logs/workspace_fingerprint.json`
- 如果需要找相似题，再读取其他 workspace 的 `logs/workspace_fingerprint.json`

不要一开始就：

- 通读所有 `issues.md`
- 通读所有 `proof_manual.v`
- 通读所有 `goal.v`

原因：

- fingerprint 的成本最低
- fingerprint 已经包含语义摘要和结构化关键词
- 先读 fingerprint 可以把候选范围压到很小

### 7A.2 第二步：先做结构化过滤

先按这些字段过滤候选：

- `function_name`
- `program_sha256`
- `keywords.algorithm_family`
- `keywords.semantic_intent`
- `keywords.control_flow`
- `keywords.proof_pattern`
- `keywords.verification_status`

推荐优先级：

1. 如果是在找“同一个程序”的历史 workspace，先看 `program_sha256`
2. 如果是在找“同类算法题”，先看 `algorithm_family + semantic_intent + control_flow`
3. 如果是在找“同类证明套路”，先看 `proof_pattern + numeric_properties + verification_status`
4. 如果结构化过滤还不够，再对 `semantic_description + keywords` 做 BM25 检索

### 7A.3 第三步：再看自然语言摘要

在结构化过滤后，再读候选 fingerprint 里的：

- `semantic_description`

用它判断：

- 程序的数学语义是否真的接近
- 边界行为是否一致
- 是否属于同一类证明问题

如果 `keywords` 相似但 `semantic_description` 明显不一样，也以 `semantic_description` 为准。

### 7A.4 第四步：只展开少量候选的细节文件

只有在候选缩小之后，才继续读：

- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `coq/generated/<name>_proof_manual.v`

展开顺序建议：

1. 先读 `annotation_reasoning.md`，理解规格与 invariant
2. 再读 `proof_reasoning.md`，理解证明计划
3. 再读 `issues.md`，判断是否有已知坑
4. 最后才读 `proof_manual.v`，找可复用 tactic 或 lemma 结构

### 7A.5 什么时候不该继续展开

如果已经出现下面任一情况，就不要继续深挖该候选：

- `semantic_description` 明显不是同类程序
- `data_shape` 不匹配，例如当前是 `scalar_only`，候选却是 `array` 或 `linked_list`
- `proof_pattern` 不匹配，例如当前是纯算术题，候选却主要依赖 `heap_reasoning`
- `verification_status` 表明该例子本身是失败路径，而且失败原因与你当前问题无关

### 7A.6 推荐的回答式检索策略

当用户提出问题时，大模型应先把问题映射到下面三类之一：

1. “找同一个程序”
   做法：
   先按 `program_sha256` 或 `function_name + semantic_description` 查

2. “找相似算法题”
   做法：
   先按 `algorithm_family + semantic_intent + control_flow` 查

3. “找相似证明套路”
   做法：
   先按 `proof_pattern + numeric_properties + verification_status` 查

只有在上述结构化检索都不够用时，才退回到更宽松的自然语言匹配。

### 7A.7 一个硬规则

检索时，必须优先依赖：

- 结构化 fingerprint
- 受控词表
- 语义摘要

而不是优先依赖：

- 文件名相似
- 时间戳相近
- 日志里某句自然语言偶然相似

文件名和时间戳只能做辅助线索，不能作为主检索依据。

### 7.1 找相似算法题

先按：

- `algorithm_family`
- `semantic_intent`
- `control_flow`

筛候选。

例如找“求和类 `for` 循环题”，可以看：

- `algorithm_family: accumulation`
- `control_flow: for_loop`
- `proof_pattern: loop_invariant`

### 7.2 找相似证明套路

先按：

- `proof_pattern`
- `numeric_properties`
- `verification_status`

筛候选。

例如找“纯算术 witness，`goal_check` 已过”的题，可以看：

- `proof_pattern: pure_arithmetic`
- `verification_status: goal_check_passed`

### 7.3 找已知有坑的例子

可以按：

- `verification_status: auto_proof_contains_admitted`
- `verification_status: generated_goal_contains_axioms`

再结合 `issues.md` 看是流程坑还是证明坑。

## 8. 维护规则

### 8.1 新 workspace

每次新建 workspace 时：

1. 先 seed `workspace_fingerprint.json`
2. 在开始 annotation 前补完 `semantic_description`
3. 给出结构化 `keywords`
4. 在最终检查时确认 fingerprint 完整

### 8.2 同一程序的多个 workspace

如果不同 workspace 对应同一个 `program_sha256`，则：

- `semantic_description` 应尽量保持一致
- `keywords` 的语义标签应尽量一致
- `verification_status` 可以不同，因为它反映的是该次任务状态

### 8.3 修改程序语义时

如果输入程序本体变了：

- 必须更新 `program_sha256`
- 必须重写 `semantic_description`
- 必须重新检查 `keywords`

## 9. 当前实现状态

当前 `leetcode/` 目录已经支持：

- 新 workspace 自动 seed `logs/workspace_fingerprint.json`
- 规则文档中强制要求维护 fingerprint
- 已有 workspace 已补充 fingerprint 文件

如果后续需要更强检索能力，可以继续增加：

- 仓库级汇总索引，例如 `doc/fingerprint_index.json`
- 受控词表校验脚本
- 基于 `program_sha256` 的重复题聚合

## 10. 一个原则

检索系统的核心不是“多写一点信息”，而是：

- 自然语言描述负责表达语义
- 受控词表负责稳定过滤
- 哈希和函数名负责稳定定位

三者缺一不可。
