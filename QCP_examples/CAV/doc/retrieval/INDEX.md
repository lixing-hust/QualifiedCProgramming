# Retrieval Index

本文件只记录检索规则。

## 1. 检索顺序

- 先检索 `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/examples/`
- 如果这里没有足够接近的完整例子，再放宽到整个 `/home/yangfp/QualifiedCProgramming/QCP_examples/`
- 不要一开始就全仓库泛搜

## 2. 什么时候才检索

- 只有当前步骤卡住、缺少相似题思路、谓词用法、witness 结构或 proof pattern 时才检索
- 如果当前输入和当前 workspace 已经足够推进，就不要先去搜例子

## 3. 检索时先看什么

每个 workspace 的最小检索单元是：

- `logs/workspace_fingerprint.json`

建议顺序：

1. 先看 `keywords`
2. 再看 `semantic_description`
3. 最后才读 `annotation_reasoning.md`、`proof_reasoning.md`、`issues.md` 和相关 `.v`

## 4. fingerprint 要写什么

每个 workspace 的 `logs/workspace_fingerprint.json` 至少应包含：

- workspace 名称
- 输入文件
- 函数名
- `semantic_description`
- `keywords`

## 5. `semantic_description` 怎么写

至少写清楚：

- 程序在做什么
- 输入输出的核心关系
- 关键控制结构
- 边界行为
- 是否修改内存

## 6. `keywords` 怎么用

- `keywords` 必须来自受控词表，不要自由发明同义词
- 先用 `keywords` 过滤，再用自然语言描述判断是否真的相似

## 7. 允许展开阅读的样例范围

- `CAV/examples/` 下的样例可以直接展开阅读
- 如果 `CAV/examples/` 不够，再去 `QCP_examples/` 下读取其他相关例子
- 仍然优先选择和当前目标最接近的题型、数据结构、witness 结构或 proof pattern
