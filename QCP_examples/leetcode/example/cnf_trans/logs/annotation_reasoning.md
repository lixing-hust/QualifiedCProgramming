# Annotation Reasoning

本样例整理自 `QCP_examples/cnf_trans/cnf_trans.c`，覆盖从逻辑命题到 CNF 子句表的构造。

annotation 的关键点包括：

- 大量 `Extern Coq` 谓词把逻辑语义和堆表示绑定起来。
- 子句由整型数组表示，子句表由单链表结构表示。
- `clause_gen_unary`、`clause_gen_binary` 等函数在更新 `PreData` 时同时维护逻辑含义和堆结构。

它适合作为“重逻辑建模 + 数组与链表混合堆结构”的样例。
