# QCP 能验证的 C 程序范围

本文档说明这个仓库中的 QCP 工具，当前能够验证什么样的 C 程序，以及它明显不适合什么样的程序。

结论先说在前面：

- QCP 不是“对任意 C 程序一键自动证明”的工具。
- 它面向的是“带规格、带断言、带循环不变式、必要时带 Coq 建模”的注释化 C 程序。
- 它特别适合验证：
  - 指针和堆对象操作；
  - 数组与结构化内存；
  - 链表、双向链表、树、队列等典型数据结构；
  - 递归算法、原地修改算法、带循环不变式的命令式程序；
  - 需要用分离逻辑表达内存形状与别名约束的程序。

## 1. 依据

本文结论来自三部分证据：

- 仓库文档与教程：
  - `README.md`
  - `tutorial/T1` 到 `tutorial/T8`
- 主示例集 `QCP_examples/`：
  - 除 `humaneval/` 外共有 55 个 `.c` 示例；
  - 人工分类分布为：
    - `Typical data structure`: 18
    - `LiteOS`: 17
    - `Arithmetic`: 7
    - `Typical algorithms`: 7
    - `Real algorithms`: 7
- 本次最小探测样例：
  - `continue` 通过；
  - `for (int i = ... )` 通过；
  - `goto`/label 失败；
  - 函数指针的间接调用失败。

因此，下面会明确区分：

- “已被仓库示例或本次探测确认支持”
- “未见证据，不建议默认认为支持”

## 2. 先决条件：QCP 验证的不是“裸 C”，而是“带逻辑注释的 C”

一个程序想进入 QCP 的可验证范围，通常需要具备这些元素：

- 函数规格：
  - `Require ...`
  - `Ensure ...`
  - 可带 `With ...` 逻辑变量
- 关键点断言：
  - `Assert`
  - `which implies`
- 循环不变式：
  - `Inv`
- 必要时的 Coq 外部符号声明：
  - `Extern Coq`
  - `Import Coq`
- 必要时的表示谓词与策略文件：
  - 例如链表、树、数组段、缺失片段、前后态关系等

也就是说，QCP 的工作流是：

1. 你给出带注释的 C 程序。
2. QCP 对程序做符号执行。
3. QCP 生成分离逻辑验证条件。
4. 自动证明一部分，剩余部分交给 Rocq/Coq。

如果程序没有规格、没有内存建模、没有循环不变式，通常不在它的强项范围内。

## 3. 已确认支持的 C 程序形态

### 3.1 标量运算与普通命令式代码

已确认支持：

- `int`、`unsigned int`、`char`
- `long long`
- 算术表达式、比较表达式、逻辑表达式
- 类型转换，例如 `(long long)a * (long long)b`
- 局部变量声明与赋值
- `return`

证据：

- `QCP_examples/simple_arith/add.c`
- `QCP_examples/simple_arith/div_test.c`
- `QCP_examples/simple_arith/exgcd.c`
- `QCP_examples/simple_arith/Always_pos.c`

这类程序的验证通常依赖：

- 前置条件约束溢出边界；
- 后置条件描述数值关系；
- 必要时用 Coq 中的数学函数建模结果。

### 3.2 指针、取地址、解引用、二级指针

已确认支持：

- `&x`
- `*p`
- `**pp`
- 指针参数与“指向指针”的参数
- 函数中通过指针原地修改内存

证据：

- `QCP_examples/simple_arith/add.c` 中的 `add1_2`、`add1_3`
- `QCP_examples/functional_queue.c`
- `QCP_examples/bst_insert.c`
- `QCP_examples/bst_delete_rec.c`

这也是 QCP 的核心优势区域，因为它本来就是基于分离逻辑做内存验证。

### 3.3 结构体、联合体、枚举、typedef

已确认支持：

- `struct`
- `union`
- `enum`
- `typedef`
- 字段访问：
  - `p->field`
  - `obj.field`
- 字段地址与字段级内存断言

证据：

- `tutorial/T1-representation-predicates.md` 直接说明断言语言可谈论 `struct`、`union`、`typedef`
- `QCP_examples/eval.c` 使用 `enum` + `union`
- `QCP_examples/typeinfer/tool.h`
- `QCP_examples/alpha_equiv/ast.h`

这意味着 QCP 不只适用于“平坦数组程序”，也能覆盖非平凡的代数型内存布局。

### 3.4 数组、数组段、指针算术、字符数组

已确认支持：

- 一维数组
- 数组下标访问 `a[i]`
- 指针形式访问 `*(a + i)`
- 数组段谓词
- 已初始化/未初始化区间建模
- `char *` 和字符数组

证据：

- `QCP_examples/array_auto.c`
- `QCP_examples/sum.c`
- `QCP_examples/chars.c`
- `QCP_examples/int_array_merge_rel.c`
- `QCP_examples/kmp_rel.c`

实际风格上，QCP 更偏向：

- 通过表示谓词来表达数组整体或区间；
- 用循环不变式维护“前缀已处理、后缀未处理”的结构；
- 在需要时用 `which implies` 展开某个下标位置的权限。

### 3.5 链表、双向链表、树、带父指针树、队列

这是 QCP 最成熟的一类场景。

已确认支持：

- 单链表
- 双向链表
- 链表段
- 二叉搜索树
- AVL
- 带父指针的树
- 函数式队列、链表队列
- 多个堆结构之间的分离组合

证据：

- `QCP_examples/sll_auto.c`
- `QCP_examples/dll_auto.c`
- `QCP_examples/dll_queue.c`
- `QCP_examples/bst_insert.c`
- `QCP_examples/bst_delete_rec.c`
- `QCP_examples/bst_fp_insert.c`
- `QCP_examples/bst_fp_delete.c`
- `QCP_examples/avl_insert.c`
- `QCP_examples/functional_queue.c`

这类程序通常依赖：

- 自定义表示谓词；
- 归纳定义的形状约束；
- 局部修改后的 frame 保留；
- 递归函数规格。

### 3.6 递归函数与递归数据结构

已确认支持：

- 递归函数调用
- 递归数据结构上的递归算法
- 多规格下验证递归函数

证据：

- `QCP_examples/simple_arith/exgcd.c`
- `QCP_examples/bst_delete_rec.c`
- `QCP_examples/sll_merge_rel.c`
- `QCP_examples/eval.c`

### 3.7 控制流：`if` / `while` / `for` / `do-while` / `switch` / `break` / `continue`

已确认支持：

- `if / else`
- `while`
- `for`
- `do { ... } while (...)`
- `switch / case`
- `break`
- `continue`

证据：

- `if / else`: 全仓库大量示例
- `while`: `tutorial/T3`、`QCP_examples/sll_auto.c`
- `for`: `QCP_examples/array_auto.c`、`QCP_examples/sum.c`
- `do-while`: `QCP_examples/sum.c`
- `switch / case`: `QCP_examples/eval.c`、`QCP_examples/cnf_trans/cnf_trans.c`
- `break`: `QCP_examples/simple_arith/Always_pos.c`、`QCP_examples/sll_merge_rel.c`
- `continue`: 本次最小探测已通过

补充说明：

- `for (int i = 0; ... )` 这类 C99 风格循环头，本次探测也已通过；
- 循环基本都需要手工给不变式；
- `break`/`continue` 支持不代表所有复杂跳转都支持，见后文的 `goto` 限制。

### 3.8 函数调用、规格复用、多规格派生

已确认支持：

- 调用带规格的函数
- 自动匹配调用前置条件中的内存部分
- `where` 子句显式实例化逻辑变量或规格名
- 同一函数多个规格
- 规格间派生关系

证据：

- `tutorial/T8-function-call.md`
- `QCP_examples/swap.c`
- `QCP_examples/sll_merge_rel.c`
- `QCP_examples/typeinfer/typeinfer.c`

这说明 QCP 不只是“验证单个函数体”，也支持较系统的模块化验证。

### 3.9 多态表示谓词与抽象数据载荷

已确认支持：

- Coq 层面的参数化表示谓词
- `void *` 风格的数据载荷
- 规格中的隐式类型参数

证据：

- `tutorial/T6-polymorphism.md`
- `QCP_examples/poly_sll.c`

这使它不仅能验证“链表里存 int”，也能验证“链表里存某种抽象对象的地址”。

### 3.10 带关系语义或解释器风格的程序

QCP 不只适合“简单函数结果 = 某个数学表达式”这种规格，也能处理：

- 状态关系；
- 解释器/转换器；
- 算法关系式；
- 分阶段逻辑关系。

证据：

- `QCP_examples/eval.c`
- `QCP_examples/kmp_rel.c`
- `QCP_examples/cnf_trans/cnf_trans.c`
- `QCP_examples/typeinfer/typeinfer.c`
- `QCP_examples/alpha_equiv/*.c`

这说明它可以验证相当复杂的真实算法，但前提仍然是规格和中间断言足够完整。

## 4. 动态内存与外部函数：能验证，但通常要先“规格化”

QCP 可以验证带堆分配的程序，但仓库里的主流做法不是直接验证 libc 的 `malloc/free`，而是：

- 先声明一个带规格的封装函数；
- 在后续程序中把它当作已验证/已知规格的外部函数使用。

例如：

- `malloc_list`
- `free_list`
- `malloc_tree_node`
- `free_tree_node`

所以更准确地说：

- “堆对象分配/释放模式”在范围内；
- “直接理解系统库实现”不在范围内；
- 你通常需要给分配器/释放器写规格。

## 5. 源码层面的限制

### 5.1 原生预处理支持很有限

`README.md` 明确写了：

- 原生只支持 `#include`
- 如果用了 `#define` 等预处理指令，需要先跑 `cpp -C`

因此，下面这些写法不要默认认为能直接吃：

- 大量宏展开
- 复杂条件编译
- 依赖编译器宏环境的源码

更稳妥的做法是：

- 先预处理；
- 再把预处理后的 C 交给 QCP。

### 5.2 断言语言不是任意 C 表达式求值器

教程明确说明：

- 基础断言语言应该是无副作用的；
- 一般不直接在断言里写 C 函数调用；
- 需要时使用逻辑变量、`data_at`、表示谓词和 `which implies` 过渡。

所以它更像“逻辑规格语言 + 少量贴近 C 的简写”，不是把 C 表达式原封不动丢进证明器。

## 6. 当前明确不支持或至少不应默认支持的内容

这一节是最重要的边界说明。

### 6.1 `goto` 和 label

本次最小探测中，`goto` 样例失败，错误为语法层面的 label 解析失败。

可以据此认为：

- `goto`
- `label:`

目前不在 QCP 的可用子集里，至少不应作为正常工作流使用。

### 6.2 函数指针的间接调用

本次最小探测中：

- 函数指针声明本身可以写；
- 但执行 `f(x)` 这种间接调用时失败；
- 失败信息是 `FindFuncInfo: func_info not found`

因此当前应视为：

- 间接调用 `fp(...)` 不支持；
- 需要静态解析目标的普通函数调用才是主流用法。

### 6.3 任意外部库函数调用

如果一个函数没有规格，QCP 一般无法直接验证其调用效果。

因此下面这类代码默认不在范围内：

- 直接调标准库但不给规格；
- 调项目外 API 但不给规格；
- 依赖运行时副作用、IO、副线程、系统调用却不做逻辑建模。

### 6.4 无注释、无建模、无不变式的普通 C 项目

QCP 不是自动推理型黑盒验证器。

如果你的程序具备这些特征：

- 没有函数规格；
- 没有内存表示谓词；
- 有循环但没有循环不变式；
- 有复杂堆结构但没有逻辑抽象；

那么它通常不在“可直接验证”的范围内。

### 6.5 仓库中没有证据支持的特性

以下特性在当前仓库文档、主示例和本次探测中都没有形成正面证据，因此不建议默认认为支持：

- 内联汇编
- `setjmp`/`longjmp`
- `volatile`
- 并发/线程同步
- 函数指针回调风格框架
- GCC 扩展语法
- 复杂的宏元编程

这些特性即使语法上偶尔能过，也很可能不在 QCP 的稳定验证模型里。

## 7. 适合用 QCP 验证的程序画像

如果你的程序满足下面多数条件，通常就比较适合：

- 主要是 C 的顺序命令式代码；
- 内存结构可以用分离逻辑表示；
- 能给每个函数写清楚 `Require/Ensure`；
- 能为每个循环写出不变式；
- 关键数据结构能抽象成表示谓词；
- 外部函数可以补规格；
- 你接受“自动 + 半手工 Coq”这种验证方式。

典型适配场景：

- 单链表/双链表/树的增删改查
- 数组处理、扫描、拷贝、拼接、原地更新
- 递归算法
- 解释器、转换器、符号处理器
- 小型内核/嵌入式数据结构代码

## 8. 不太适合的程序画像

下面这些程序通常不太适合直接上 QCP：

- 严重依赖宏和条件编译的工业 C 工程
- 大量间接调用、回调、函数指针分发
- 大量 IO / 系统交互 / 线程并发
- 想“零注释自动证明”的普通业务代码
- 强依赖编译器扩展或未建模运行时的代码

## 9. 一个实用判断标准

拿一段 C 代码时，可以用下面的标准快速判断它是否在 QCP 的甜蜜点里：

1. 我能不能给每个函数写出清楚的前后条件？
2. 我能不能把堆结构写成表示谓词？
3. 每个循环我能不能写出稳定不变式？
4. 这段代码的关键行为是不是顺序执行、静态可见的？
5. 外部调用能不能都换成“有规格的封装函数”？

如果 1 到 5 大部分答案都是“能”，QCP 通常是合适的。

如果 2、3、5 明显做不到，或者程序严重依赖 `goto`、函数指针回调、多线程和宏系统，那么它大概率超出当前仓库展示出来的可验证范围。

## 10. 最简结论

可以把 QCP 的验证范围概括成一句话：

> 它适合验证“带分离逻辑注释的、以指针/数组/递归数据结构为核心的顺序 C 程序”，而不适合“任意未注释的全功能 C 工程”。

更具体一点：

- 强项：堆内存、别名控制、链表/树/数组、递归、循环不变式、模块化规格。
- 弱项或边界外：`goto`、函数指针间接调用、无规格外部库、复杂预处理、并发和编译器扩展。
