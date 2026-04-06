# Curated Examples Index

本目录把 `QCP_examples/` 中有代表性的验证样例整理成和 `leetcode/output/workspace_*` 对齐的目录结构，便于后续检索和复用。

每个样例目录都包含：

- `original/<name>.c`
- `annotated/<name>.c`
- `coq/generated/`
- `logs/workspace_fingerprint.json`
- `logs/annotation_reasoning.md`
- `logs/proof_reasoning.md`
- `logs/issues.md`
- `logs/proof_metrics.md`

说明：

- 这些样例是“誊抄整理”，不是在本目录内重新 symbolic 或重新证明。
- 对于上游本来就带注释的 C 文件，`original/` 与 `annotated/` 会保持一致，目的是让目录结构和 workspace 对齐。
- 检索时先读 `logs/workspace_fingerprint.json`，再看 reasoning，最后再展开 Coq 文件。

## 检索入口

优先使用：

- `fingerprint_index.json`
- 各样例下的 `logs/workspace_fingerprint.json`

先按结构化 `keywords` 过滤，再看 `semantic_description` 判断是否真的相似。

## 样例覆盖

- `add`：纯算术、循环保持和指针自增小例子。
- `abs`：带分支的绝对值规格和最小 case split 模板。
- `exgcd`：扩展欧几里得、递归算术、Bezout 等式和指针返回参数。
- `gcd`：递归整数证明和外部 Coq 数学函数建模。
- `max3`：嵌套条件分支上的最大值选择。
- `swap`：别名分支、参数化规范和原地交换。
- `sum`：数组求和、`while` / `do while` / `for` 不变式、`which implies`、原地更新。
- `array_auto`：数组 shape 证明、分段不变式、数组到链表的桥接。
- `chars`：字符数组初始化和 `repeat_Z` 形状规格。
- `sll_auto`：单链表 `listrep` / `lseg`、反转、拼接、交错合并。
- `sll_queue`：带哨兵尾节点的单链表队列。
- `sll_split_while`：单链表交替切分、`safeExec` 关系和循环中的关系式重写。
- `dll_auto`：双链表 shape、反转、拼接、前后向迭代。
- `dll_queue`：双向链表队列、抽象谓词到段谓词的拆解。
- `functional_queue`：两表表示的函数式队列、`reverse` 归一化。
- `bst_insert`：二叉搜索树插入、低层规范到高层规范、路径不变式。
- `bst_insert_rec`：递归 BST 插入和高低层规范对齐。
- `avl_insert`：AVL 旋转、平衡因子和树形局部重写。

## 维护规则

- 新增样例时，优先选择覆盖新的数据结构或证明套路，而不是重复已有模式。
- `workspace_fingerprint.json` 中的 `keywords` 必须遵守 [doc/INDEX.md](/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/doc/INDEX.md) 的受控词表。
- 如果样例只做誊抄没有重放验证，`logs/issues.md` 和 `logs/proof_metrics.md` 必须明确写出这一点，避免把参考样例误读成新鲜验证结果。
