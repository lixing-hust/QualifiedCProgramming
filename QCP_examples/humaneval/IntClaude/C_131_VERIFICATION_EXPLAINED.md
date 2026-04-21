# C_131 验证说明

这份说明只针对 `C_131` 这个例子，默认读者已经知道程序验证、循环不变式、VC、`manual.v` 这些基本概念。

相关文件：

- [C_131.c](/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/C_131.c)
- [coins_131.v](/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/coins_131.v)
- [C_131_manual.v](/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/C_131_manual.v)
- [131.v](/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/spec/131.v)

## 1. 程序语义

这题的规格很简单：把 `n` 的十进制 digits 拿出来，只保留奇数位，求乘积；如果没有奇数位，结果是 `0`。

程序实现用了三个状态量：

- `n`：还没处理完的尾部
- `prod`：已经看到的奇数位乘积
- `has`：是否已经见过奇数位

这里最关键的点是：`prod` 初始是 `1`，不是 `0`。  
所以程序语义不是“答案永远等于 `prod`”，而是：

- 若 `has = 0`，最终答案应解释为 `0`
- 若 `has = 1`，最终答案应解释为 `prod`

这就是为什么这题一定需要一个状态解释函数，而不能直接把 invariant 写成“当前答案 = prod”。

## 2. 为什么要定义 `digits_state_z`

在 [coins_131.v](/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/coins_131.v) 里定义了：

```coq
Definition digits_state_z (n prod has : Z) : Z :=
  if Z.eqb has 0 then Z.of_nat (digits_impl (Z.to_nat n))
  else prod * tail_odd_prod_z n.
```

这是整题的核心抽象。

它的作用是把循环中间状态解释成“相对于原规格的当前语义”：

- `has = 0` 时，还没有乘进任何奇数位，所以答案完全来自剩余部分 `n`
- `has = 1` 时，已处理部分贡献 `prod`，未处理部分贡献 `tail_odd_prod_z n`

所以 invariant 不是直接维护最终结果，而是在维护：

```text
当前程序状态通过 digits_state_z 解释后，已经满足最终规格
```

这是这题最重要的建模选择。

## 3. `tail_odd_prod_z` 在这题里的作用

这题里另一个必须理解的对象是：

```coq
tail_odd_prod_z n
```

它表示的是“当前剩余尾部 `n` 的奇数位乘积”。

更准确地说：

- 取 `n` 的十进制 digits
- 只保留奇数位
- 把这些奇数位乘起来

它不是整个程序的最终规格函数，这一点很重要。

和它容易混淆的是 `digits_impl n`：

- `digits_impl n` 是最终题目语义
- 如果没有奇数位，结果是 `0`

而 `tail_odd_prod_z n` 只是“奇数位乘积”本身：

- 如果没有奇数位，它对应空乘积，所以结果是 `1`

例如：

- `digits_impl 4 = 0`
- `tail_odd_prod_z 4 = 1`

这正是这题需要 `has` 的原因。单看 `prod = 1`，无法区分：

- 还没见过奇数位
- 还是见过奇数位，但它们乘起来恰好等于 `1`

所以这题把角色分成了三部分：

- `prod`：已处理前缀的奇数乘积
- `tail_odd_prod_z n`：未处理尾部的奇数乘积
- `has`：是否真的见过奇数位

`tail_odd_prod_z` 在这题里有两个用途。

### 用途 1：状态语义拼接

当 `has <> 0` 时，

```coq
digits_state_z n prod has = prod * tail_odd_prod_z n
```

这表示：

- 已处理部分贡献 `prod`
- 未处理部分贡献 `tail_odd_prod_z n`

所以两者相乘就是“当前状态解释下的总答案”。

### 用途 2：乘法安全预算

循环里有一步：

```c
prod *= d;
```

要证明它安全，仅有 `prod <= INT_MAX` 不够。还需要知道“剩余部分最多还能贡献多少”。

这就是 invariant 里这句的作用：

```text
prod * tail_odd_prod_z(n) <= INT_MAX
```

它的含义是：

- 即使把剩余尾部里的所有奇数位都乘进去
- 总结果仍然不会超过 `INT_MAX`

所以 `tail_odd_prod_z` 同时服务于：

- 语义证明
- safety 证明

## 4. 为什么 invariant 这样写

[C_131.c](/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/C_131.c) 里的循环不变式是：

```c
/*@ Inv
    n >= 0 && 1 <= prod && prod <= INT_MAX && 0 <= has && has <= 1 &&
    (has == 0 => prod == 1) &&
    prod * tail_odd_prod_z(n) <= INT_MAX &&
    problem_131_spec_z(n@pre, digits_state_z(n, prod, has))
*/
```

这几项分别有不同作用。

### `n >= 0`

这是为了让 `% 10`、`÷ 10` 的 Coq 桥接稳定成立。  
后面 `coins_131.v` 里很多引理都依赖这个非负条件。

### `1 <= prod <= INT_MAX`

下界 `1` 很重要，因为：

- 初始 `prod = 1`
- 乘进去的奇数位最小也是 `1`

上界则是 C safety 需要。

### `0 <= has <= 1`

这只是把 `has` 压成布尔标记，方便最后从 `has <> 0` 推到 `has = 1`。

### `(has == 0 => prod == 1)`

这项是必须的，因为程序内部把“尚未见过奇数位”编码成：

- `has = 0`
- `prod = 1`

如果没有这句，返回 `0` 的分支就缺少足够的信息把当前状态和规格对应起来。

### `prod * tail_odd_prod_z(n) <= INT_MAX`

这项不是为了规格，而是为了乘法安全性。

程序里有一步：

```c
prod *= d;
```

当前位 `d = n % 10` 若是奇数，就要证明乘完仍不溢出。  
这时只知道 `prod <= INT_MAX` 不够，必须知道“未来可能乘进去的东西”也在预算内。

这条 invariant 的含义就是：

- 已处理部分的贡献是 `prod`
- 未处理部分未来最多贡献 `tail_odd_prod_z(n)`
- 两者相乘仍不超过 `INT_MAX`

所以它是一个为后续更新准备的 safety invariant。

### `problem_131_spec_z(n@pre, digits_state_z(n, prod, has))`

这是语义 invariant。  
它说明：当前状态已经足够解释成最终规格。

没有这句，这题最终是收不回规格的。

## 5. `coins_131.v` 在做什么

`coins_131.v` 的作用不是“替 manual 证明”，而是把这题需要的几个桥接层补齐。

主要有三类引理。

### A. 十进制递推

比如：

- `get_digits_step`
- `tail_step_odd`
- `tail_step_even`
- `digits_impl_step_odd`
- `digits_impl_step_even`

这些引理把“处理最低位以后，剩余部分怎么解释” formalize 出来。

### B. C 运算和数学运算的桥接

比如：

- `Zquot_eq_Zdiv_pos`
- `rem_rem10_eq_mod2`
- `tail_step_odd_cstyle`
- `tail_step_even_cstyle`

这些引理解决的是：

- 程序里看到的是 `n % 10`、`n /= 10`
- 规格里更像 `mod` / `div`

必须先把这层桥接做好，`manual.v` 才能稳定写。

### C. 安全性引理

比如关于 `tail_odd_prod_z` 的下界、当前 digit 上界等。

这类引理的作用是证明：

- 当前 digit 不会比“剩余奇数位总乘积”更大
- 所以 `prod * digit` 的安全性可以从 invariant 推出来

## 6. `manual.v` 的逻辑结构

这题的 `manual.v` 很干净，基本就对应三件事：

### `digits_entail_wit_1`

证明初始化满足 invariant。

这里最关键的是：

- 初始状态是 `(n_pre, 1, 0)`
- 需要证明 `digits_state_z(n_pre, 1, 0)` 对应最终规格

因此这里直接调用了初始化桥接引理。

### `digits_entail_wit_2_1`

对应“当前位是奇数”的循环一步。

程序状态变化是：

- `has := 1`
- `prod := prod * (n % 10)`
- `n := n / 10`

证明上最关键的是两件事：

1. 用 `digits_state_step_odd_preserve` 证明语义 invariant 继续成立
2. 用 `tail_step_odd_cstyle` 和 digit 上界引理证明新的 safety invariant 继续成立

### `digits_entail_wit_2_2`

对应“当前位是偶数”的循环一步。

这时只更新 `n := n / 10`，`prod` 和 `has` 保持不变。  
因此语义上只需要调用 `digits_state_step_even_preserve`。

### `digits_return_wit_1`

对应退出后 `has = 0` 的返回分支。

这一步的关键是：

- 退出条件给 `n <= 0`
- invariant 给 `n >= 0`
- 所以 `n = 0`

然后展开 `digits_state_z`，在 `has = 0` 情况下它化成 `digits_impl 0`，最后得到返回 `0` 正确。

### `digits_return_wit_2`

对应退出后 `has <> 0` 的返回分支。

这里同样先由退出条件得到 `n = 0`，再由 `0 <= has <= 1` 和 `has <> 0` 得到 `has = 1`。  
此时 `digits_state_z(0, prod, 1)` 化成：

```text
prod * tail_odd_prod_z(0)
```

而 `tail_odd_prod_z(0) = 1`，所以最终就是 `prod`。

## 7. 这题最关键的两个设计点

如果只保留这题最值得复用的两个点，我会选下面两个。

### 设计点 1：先定义“状态语义函数”，再写 invariant

也就是先定义：

```coq
digits_state_z
```

再把 invariant 写成：

```text
problem_131_spec_z(n_pre, digits_state_z(n, prod, has))
```

这比直接在 invariant 里手写一大坨条件清晰很多，也更利于分支证明。

### 设计点 2：把 safety 和语义分开编码

语义 invariant：

```text
problem_131_spec_z(n_pre, digits_state_z(...))
```

safety invariant：

```text
prod * tail_odd_prod_z(n) <= INT_MAX
```

这两条缺一不可：

- 没有前者，收不回规格
- 没有后者，过不了乘法 safety

## 8. 对后续类似题的直接启发

如果之后再遇到 digits / `%10` / 十进制扫描类题，优先检查三件事：

1. 有没有必要像这题一样，定义一个中间状态语义函数
2. invariant 是否既包含语义信息，也包含 future-safe 的乘法上界
3. odd/even 两个分支是否应该分别准备保持引理

对 `C_131` 来说，答案都是“是”。这也是它最后能证明得比较顺的原因。
