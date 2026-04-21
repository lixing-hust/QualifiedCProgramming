# IntArrayClaude 前后条件书写指南

这份文档只讨论一件事：

- 如何给 `QCP_examples/humaneval/IntArrayClaude` 里的 C 程序写“适合 QCP 验证”的前后条件

它刻意和“后续真正做证明”分开。  
目标是把工作拆成两步：

1. 先把前后条件写对
2. 再基于这些前后条件去做 `symexec` 和 `manual.v`

这里的核心原则是：

- 纯语义尽量沿用你已经写好的 `QCP_examples/humaneval/spec/*.v`
- 但要额外补上：
  - 内存所有权条件
  - C `int` / 下标 / 长度 / 指针偏移 的安全条件

也就是说，`spec/*.v` 提供的是“题目想算什么”，而 QCP 的前后条件还必须补上“这段 C 程序怎样合法地访问内存，以及怎样避免溢出”。

---

## 1. 总原则

对于 `IntArrayClaude` 的每一道题，前后条件的写法都应该来自这三个层面。

### 1.1 纯语义层

来自：

- `QCP_examples/humaneval/spec/<id>.v`

这里的内容应尽量保留，不要轻易改题目的数学含义。

例如：

- `problem_3_spec`
- `problem_9_spec`
- `problem_43_spec`

这些是“这道题本来要实现什么”的核心。

### 1.2 内存层

来自数组程序的 C 访问方式。

你必须说明：

- 哪些数组是输入，因而要求 `IntArray::full(...)`
- 哪些数组是输出但还没初始化，因而要求 `IntArray::undef_full(...)`
- 哪些数组在函数结束后仍保持原值
- 哪些数组被写成了什么新列表

### 1.3 C 安全层

来自真实 C 程序，而不是题目本身。

你必须考虑：

- `0 <= n`
- `n < INT_MAX`
- `i + 1` 会不会溢出
- `p + i * sizeof(int)` 的下标偏移是否合法
- `x + y`、`x - y`、`x * y` 会不会超出 `int`
- 输出长度例如 `2 * n - 1` 会不会溢出

`spec/*.v` 里很多 `pre` 都是 `True`，这在 QCP 验证里通常不够。

---

## 2. 书写流程：先从 spec 出发，再补 QCP 约束

推荐固定流程如下。

### 第一步：先看 `spec/<id>.v`

你先提取两件事：

1. 输入和输出的纯数学对象是什么
2. 题目本身是否已经有纯逻辑前提

例如 `spec/3.v`：

```coq
Definition problem_3_pre (l : list Z) : Prop := True.
Definition problem_3_spec (l : list Z) (output : bool): Prop := ...
```

这说明：

- 输入的纯语义对象是 `l : list Z`
- 输出是布尔值
- 原题没有额外纯前提

### 第二步：把纯对象映射到 C 参数

例如：

```c
int below_zero(int *operations, int operations_size)
```

就可以映射成：

- `operations` 对应列表 `l`
- `operations_size` 对应 `Zlength l`
- `__return` 对应 `output : bool` 的 C 编码

通常数组输入会写成：

```c
/*@ With l */
```

或如果有多个输入/输出列表：

```c
/*@ With input output */
```

### 第三步：补内存谓词

这一步不来自 `spec`，而来自程序访问方式。

最常见的几种：

- 只读输入数组：

```c
IntArray::full(a, n, l)
```

- 输出数组预分配但未初始化：

```c
IntArray::undef_full(out, n)
```

- 输出数组写完后：

```c
IntArray::full(out, n, out_l)
```

- 输入数组保持不变：

```c
... && IntArray::full(a, n, l)
```

同时出现在后置条件里

### 第四步：补 C 安全条件

这是 `IntArrayClaude` 里最容易漏掉的一步。

至少要考虑：

- 长度是否非负
- 长度是否严格小于 `INT_MAX`
- 任何循环变量是否会执行 `i + 1`
- 任何数组长度表达式是否会出现 `2 * n - 1`
- 任意元素值是否能存进 C `int`
- 任意累计值是否会溢出

如果不补，后续很可能在 `safety_wit` 就卡住。

---

## 3. 该从 `spec` 继承什么，不该直接继承什么

## 3.1 应该继承的

- 题目的纯语义输入输出关系
- 原始纯逻辑前提 `problem_i_pre`
- 原始纯逻辑规格 `problem_i_spec`

## 3.2 不该直接照抄的

- `pre = True` 就真的在 C 规格里也写成没有任何前提
- 把 `bool` 规格直接翻译成 `__return = true/false`
- 忽略数组内存和元素范围

更准确地说：

- `problem_i_pre` 和 `problem_i_spec` 是“题意核心”
- QCP 的前后条件是“题意核心 + 内存约束 + C 安全约束”

---

## 4. 只读输入数组：最常见的模板

这类题在 `IntArrayClaude` 里非常多，例如：

- `C_3`
- `C_40`
- `C_43`

函数形状一般是：

```c
int f(int *a, int n)
```

### 4.1 推荐前置条件模板

```c
/*@ With l
    Require
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        (forall (i: Z), 0 <= i && i < n -> INT_MIN <= Znth(i, l, 0) <= INT_MAX) &&
        problem_i_pre(l) &&
        IntArray::full(a, n, l)
*/
```

说明：

- `Zlength(l) == n` 有时可以不显式写，因为 `IntArray::full(a, n, l)` 常能推出
- 但在写规约阶段，显式写出来有时更清晰
- 元素范围约束很重要，因为数组里存的是 C `int`

### 4.2 推荐后置条件模板

如果返回值是布尔编码，用：

```c
/*@ Ensure
        ((__return != 0) <-> problem_i_spec(l, true)) &&
        ((__return == 0) <-> problem_i_spec(l, false)) &&
        IntArray::full(a, n, l)
*/
```

或更常见地直接写成分支式：

```c
/*@ Ensure
        ((__return != 0) && good_case(l) ||
         (__return == 0) && bad_case(l)) &&
        IntArray::full(a, n, l)
*/
```

第二种更接近现在 `IntClaude` / `IntArrayClaude` 里已有写法，也更容易被 `symexec` 处理。

### 4.3 为什么后置条件里要保留 `IntArray::full(...)`

因为程序只读输入数组，不修改它。

如果你不把它放回后置条件，等于丢掉了输入数组的所有权和保持性信息。  
这通常不符合函数真实行为，也会让后续组合验证更差。

---

## 5. 输出写入到预分配数组：第二常见模板

代表：

- `C_9.c`

函数形状一般是：

```c
void f(int *input, int n, int *out)
```

### 5.1 推荐前置条件模板

```c
/*@ With input_l
    Require
        0 <= n && n < INT_MAX &&
        (forall (i: Z), 0 <= i && i < n -> INT_MIN <= Znth(i, input_l, 0) <= INT_MAX) &&
        problem_i_pre(input_l) &&
        IntArray::full(input, n, input_l) *
        IntArray::undef_full(out, n)
*/
```

### 5.2 推荐后置条件模板

```c
/*@ Ensure
        exists output_l,
        problem_i_spec(input_l, output_l) &&
        IntArray::full(input, n, input_l) *
        IntArray::full(out, n, output_l)
*/
```

如果 `spec` 已经唯一确定了输出列表，也可以直接写成：

```c
IntArray::full(out, n, rolling_max_f(0, input_l))
```

也就是说：

- 若已经有方便的 Coq 语义函数，就直接写那个函数
- 若只有关系式 spec，就用 `exists output_l`

### 5.3 输出长度不是 `n` 时怎么办

例如输出长度是 `2 * n - 1`，这时前后条件必须显式补：

```c
0 <= n &&
n < INT_MAX &&
n == 0 || 2 * n - 1 < INT_MAX
```

更稳一点可以直接写：

```c
0 <= n && n <= (INT_MAX + 1) / 2
```

具体写哪种，取决于程序里是否真的会计算 `2 * n - 1`。

只要 C 代码里算了这个表达式，就必须对这个表达式的安全性负责。

---

## 6. 返回新数组/结构体时，前后条件怎么想

例如：

```c
typedef struct {
    int* data;
    int size;
} IntArray;
```

像 `C_5.c` 这种函数：

```c
IntArray intersperse(const int* numbers, int numbers_size, int delimeter)
```

这种题的语义其实是：

- 输入：一个只读数组
- 输出：一个新分配的数组及其长度

如果以后要在 QCP 里认真验证这种题，推荐先把纯输出抽象成：

- 一个新列表 `output_l`
- 一个长度 `m`

再让后置条件描述：

- 返回结构体中的 `size`
- 返回结构体中的 `data`
- `data` 指向一段 `IntArray::full`

这类题比“预分配输出数组”多一层 malloc / 结构体字段处理，所以在第一阶段只写规格时，建议先把纯规格写清楚，不急着一开始就把所有 malloc 细节压进去。

建议先决定：

1. 是否把“分配成功”作为前提保证
2. 还是允许 `malloc == NULL` 作为返回分支之一

如果程序里保留了 `NULL` 分支，后置条件也必须跟着分支化描述。

---

## 7. 写前后条件时必须补的“元素范围”条件

很多 `spec/*.v` 只把输入看成任意 `list Z`。  
但在 C 里，数组元素是真实 `int`。

因此，数组输入通常需要补：

```c
(forall (i: Z), 0 <= i && i < n -> INT_MIN <= Znth(i, l, 0) <= INT_MAX)
```

为什么要补这条：

- 读 `a[i]` 后得到的是 C `int`
- 如果列表里元素超出 `int` 范围，规格虽然在数学上成立，但 C 语义根本不合法

这是数组题里和纯整数题最不同、最容易忽视的一点。

---

## 8. 还必须补哪些“运算结果不溢出”的条件

这要看题目做了什么运算。

## 8.1 只比较元素，不做算术

例如：

- 比较 `a[i] > max`
- 比较 `a[i] == x`

通常只需要元素本身在 `int` 范围内。

## 8.2 前缀和/累计和

例如：

- `num += operations[i]`
- `sum += a[i]`

需要补的是“所有循环中间态都在 int 范围内”。

推荐写法是前缀和界：

```c
(forall (k: Z),
   0 <= k && k <= n ->
   INT_MIN <= sum(sublist(0, k, l)) <= INT_MAX)
```

这类条件对 `C_3` 非常关键。  
否则即使题意对，`num += operations[i]` 也可能在 C 里溢出。

## 8.3 两数和/三数和

例如：

- `l[i] + l[j]`
- `l[i] + l[j] + l[k]`

推荐写法：

```c
(forall (p q: Z),
   0 <= p && p < q && q < n ->
   INT_MIN <= Znth(p, l, 0) + Znth(q, l, 0) <= INT_MAX)
```

三数同理：

```c
(forall (p q r: Z),
   0 <= p && p < q && q < r && r < n ->
   INT_MIN <= Znth(p, l, 0) + Znth(q, l, 0) + Znth(r, l, 0) <= INT_MAX)
```

代表题：

- `C_43`
- `C_40`

## 8.4 乘法、平方、长度扩张

例如：

- `2 * n - 1`
- `i * j`
- `x * x`

必须针对具体表达式加界，而不是笼统写 `n < INT_MAX`。

---

## 9. 前后条件里最好直接复用 `problem_i_pre / spec`

推荐的写法不是“重写一遍 spec 的意思”，而是直接引用。

例如可以在 C 注释里用逻辑组合：

```c
/*@ Require
      ...
      problem_3_pre(l) &&
      IntArray::full(operations, operations_size, l)
    Ensure
      ((__return != 0) <-> problem_3_spec(l, true)) &&
      ((__return == 0) <-> problem_3_spec(l, false)) &&
      IntArray::full(operations, operations_size, l)
*/
```

如果工具链不方便直接引用 `problem_i_spec`，那就把它展开写成当前常用风格，但语义应尽量保持一致。

建议：

- 前置条件尽量直接引用 `problem_i_pre`
- 后置条件可以酌情展开成更利于 `symexec` 的形式

因为后置条件往往会进入 VC，过度抽象有时反而不利于证明。

---

## 10. 写前后条件时，什么叫“跟 IntClaude 差不多”

这里“跟 `IntClaude` 差不多”最合理的理解不是照搬语法，而是照搬思路：

### 10.1 保留题目原始语义

`IntClaude` 里已经形成的习惯是：

- 不随意改题意
- 用最接近题目定义的数学关系写后置条件

`IntArrayClaude` 里应继续保持这一点。

### 10.2 明确返回值的分支语义

比如 bool 返回值，尽量写成：

```c
(__return != 0 && exists witness, ...)
||
(__return == 0 && forall ..., ...)
```

这和 `IntClaude` 里对判定类程序的写法是一致的。

### 10.3 把安全性前提写进前置条件，而不是留到证明阶段“赌能证出来”

这也是 `IntClaude` 后期逐渐稳定下来的经验。

如果 C 程序真的需要某个界，最好在前置条件里明确写出来。

---

## 11. 针对几类常见题目的推荐模板

## 11.1 只读数组，返回 `int` 作为 bool

模板：

```c
/*@ With l
    Require
        0 <= n && n < INT_MAX &&
        (forall (i: Z), 0 <= i && i < n -> INT_MIN <= Znth(i, l, 0) <= INT_MAX) &&
        extra_safety_pre(l, n) &&
        problem_i_pre(l) &&
        IntArray::full(a, n, l)
    Ensure
        ((__return != 0) && good_case(l, n) ||
         (__return == 0) && bad_case(l, n)) &&
        IntArray::full(a, n, l)
*/
```

适用：

- `C_3`
- `C_40`
- `C_43`

## 11.2 只读数组，输出到预分配数组

模板：

```c
/*@ With input_l
    Require
        0 <= n && n < INT_MAX &&
        elem_bound(input_l, n) &&
        extra_safety_pre(input_l, n) &&
        problem_i_pre(input_l) &&
        IntArray::full(input, n, input_l) *
        IntArray::undef_full(out, out_n)
    Ensure
        exists output_l,
        problem_i_spec(input_l, output_l) &&
        IntArray::full(input, n, input_l) *
        IntArray::full(out, out_n, output_l)
*/
```

适用：

- `C_9`

## 11.3 原地修改数组

模板：

```c
/*@ With l
    Require
        0 <= n && n < INT_MAX &&
        elem_bound(l, n) &&
        extra_safety_pre(l, n) &&
        problem_i_pre(l) &&
        IntArray::full(a, n, l)
    Ensure
        exists l',
        problem_i_spec(l, l') &&
        IntArray::full(a, n, l')
*/
```

---

## 12. `C_3` 该怎样写前后条件

文件：

- `QCP_examples/humaneval/IntArrayClaude/C_3.c`
- `QCP_examples/humaneval/spec/3.v`

纯规格给出的是：

- 输入：`l`
- 输出：是否存在一个前缀和小于 0

如果按“前后条件先写好”的思路，这题最合理的方向应该是：

### 12.1 纯语义部分沿用 `spec/3.v`

不要改题意。

### 12.2 内存部分补上

因为程序只读数组，所以要有：

```c
IntArray::full(operations, operations_size, l)
```

并且后置条件中也保留它。

### 12.3 安全部分必须加强

这题最值得提前写进前置条件的是：

```c
(forall (i: Z), 0 <= i && i < operations_size ->
    INT_MIN <= Znth(i, l, 0) <= INT_MAX)
```

以及更关键的前缀和界：

```c
(forall (k: Z), 0 <= k && k <= operations_size ->
    INT_MIN <= sum(sublist(0, k, l)) <= INT_MAX)
```

否则：

```c
num += operations[i];
```

这一句很可能在 `safety_wit` 阶段就失败。

### 12.4 推荐理解

`spec/3.v` 里的 `pre = True` 表示“数学问题没有额外前提”。  
但 QCP 里的 C 程序验证，不应把这理解成“C 实现也没有任何前提”。

对 `C_3` 来说，最自然的做法是：

- 数学语义仍然是 `problem_3_spec`
- C 层面额外补上：
  - 数组内存合法
  - 元素是合法 `int`
  - 任意前缀和也在合法 `int` 范围内

---

## 13. 给大模型的具体操作规则

如果以后要让大模型先“只写前后条件”，建议直接要求它遵守下面几条。

### 规则 1

先读 `QCP_examples/humaneval/spec/<id>.v`，提取：

- `problem_i_pre`
- `problem_i_spec`
- 输入输出是标量、列表还是布尔

### 规则 2

不要直接用 `pre = True` 结束工作。  
必须额外检查并补：

- 数组内存所有权
- 数组长度界
- 元素范围界
- 程序里所有关键算术表达式的溢出界

### 规则 3

只读输入数组要在前后条件都保留：

```c
IntArray::full(...)
```

### 规则 4

写输出数组时，前置条件一般是：

```c
IntArray::undef_full(...)
```

后置条件一般是：

```c
IntArray::full(...)
```

### 规则 5

如果输出语义已经有方便的 Coq 函数，就直接在后置条件里写那个函数；
如果没有，就用 `exists output_l` 加关系式。

### 规则 6

对返回 bool 的题，后置条件优先写成 `IntClaude` 风格的分支式：

```c
(__return != 0 && ...)
||
(__return == 0 && ...)
```

而不是直接把 `__return` 和 Coq 的 `bool` 生硬对应。

### 规则 7

如果程序里有：

- `x + y`
- `x + y + z`
- `acc += a[i]`
- `2 * n - 1`

那么前置条件里就必须有对应的范围约束，不要把这件事留给后续“碰运气”。

---

## 14. 推荐产物形式

后续让模型做第一阶段时，建议它产出两样东西：

1. 修改后的 `C_*.c` 前后条件和 invariant
2. 一小段文字说明：
   - 纯语义继承自哪个 `spec/*.v`
   - 额外补了哪些内存条件
   - 额外补了哪些安全条件
   - 这些安全条件分别对应程序里的哪句 C 代码

这样你检查时会很快。

---

## 15. 最后一句经验

对 `IntArrayClaude` 来说，前后条件写得好不好，往往比后面的 `manual.v` 证明技巧更重要。

很多题如果前后条件阶段没有把：

- 数组资源
- 输出数组 ownership
- 元素界
- 中间表达式界

这些写清楚，那么后面不是 invariant 很难写，就是 `safety_wit` 一开始就爆掉。

所以这批数组题最推荐的工作方式确实就是你现在说的：

1. 先专门把前后条件写对
2. 再进入验证阶段
