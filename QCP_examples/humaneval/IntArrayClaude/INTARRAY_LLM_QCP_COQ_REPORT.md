# 大模型在 QCP + Coq 程序验证中的循环不变式生成能力总结



## 1. 为什么 QCP + Coq 更适合大模型

QCP + Coq 的优势在于，它允许我们把循环不变式拆成两部分：

1. C annotation 中只写清楚当前循环的“控制状态 + 资源状态 + 纯语义状态”。
2. Coq 中单独定义纯语义状态，并用小引理证明它如何初始化、如何单步推进、如何推出最终规格。

这样，大模型不需要一次性猜出一个巨大不变式，而是可以生成类似下面的结构：

```text
循环头：
  i 的范围
  输入数组资源
  当前纯语义状态 P(i, ...)

Coq 侧：
  P_init
  P_step
  P_final
```

也就是说，QCP + Coq 把“生成正确不变式”转化为了“为程序控制流命名一个合适的中间语义状态”。这更接近大模型擅长的程序归纳和模式匹配。

下面用一个完整的小例子说明这条流程。程序功能是求数组所有元素之和：

```c
int sum_array(int *a, int n)
/*@ With input_l
    Require
      0 <= n && n < INT_MAX &&
      n == Zlength(input_l) &&
      sum_int_range(input_l) &&
      IntArray::full(a, n, input_l)
    Ensure
      __return == prefix_sum(input_l, n) &&
      IntArray::full(a, n, input_l)
*/
{
  int s = 0;
  int i;

  /*@ Inv Assert
      0 <= i && i <= n &&
      n == Zlength(input_l) &&
      s == prefix_sum(input_l, i) &&
      sum_int_range(input_l) &&
      IntArray::full(a, n, input_l)
  */
  for (i = 0; i < n; i++) {
    s += a[i];
  }
  return s;
}
```

这个 invariant 有三层含义：

```text
控制状态：0 <= i <= n
资源状态：IntArray::full(a, n, input_l)
纯语义状态：s == prefix_sum(input_l, i)
```

其中最关键的是 `prefix_sum(input_l, i)`，它表示“已经处理过的前 i 个元素的和”。大模型需要做的第一件事，就是为循环中的变量 `s` 找到这个中间语义状态。

Coq 中可以这样定义：

```coq
Definition prefix_sum (l : list Z) (i : Z) : Z :=
  fold_left Z.add (sublist 0 i l) 0.
```

接下来，证明通常分成三类小引理：`init`、`step`、`final`。

### init：证明循环刚开始时不变式成立

循环开始前：

```text
i = 0
s = 0
```

因此需要证明：

```coq
Lemma prefix_sum_init : forall l,
  prefix_sum l 0 = 0.
Proof.
  intros.
  unfold prefix_sum.
  rewrite sublist_nil.
  reflexivity.
Qed.
```

它对应 invariant 中的初始事实：

```c
s == prefix_sum(input_l, 0)
```

### step：证明循环体执行一次后不变式保持

循环体是：

```c
s += a[i];
```

如果循环头有：

```text
s = prefix_sum(input_l, i)
```

执行一次后，新的 `s` 应该等于：

```text
prefix_sum(input_l, i) + input_l[i]
```

也就是：

```text
prefix_sum(input_l, i + 1)
```

Coq 中对应的 step 引理是：

```coq
Lemma prefix_sum_step : forall l i,
  0 <= i < Zlength l ->
  prefix_sum l (i + 1) = prefix_sum l i + Znth i l 0.
Proof.
  intros.
  unfold prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.
```

这个引理正好对应 C 语句 `s += a[i]`。大模型在生成证明时，只要识别出“这是前缀和向后推进一位”，就可以生成这种局部引理。

### final：证明循环结束时推出函数后置条件

循环结束时，由循环条件可知：

```text
i = n
```

而 invariant 中已经有：

```text
s = prefix_sum(input_l, i)
```

所以可以得到：

```text
s = prefix_sum(input_l, n)
```

这正是函数后置条件。Coq 中可以写成：

```coq
Lemma prefix_sum_final : forall l i n s,
  i = n ->
  s = prefix_sum l i ->
  s = prefix_sum l n.
Proof.
  intros.
  subst.
  assumption.
Qed.
```

因此，一个循环的验证任务被拆成了：

```text
1. 选择纯语义状态：
   s == prefix_sum(input_l, i)

2. 证明 init：
   prefix_sum(input_l, 0) = 0

3. 证明 step：
   prefix_sum(input_l, i + 1)
   = prefix_sum(input_l, i) + input_l[i]

4. 证明 final：
   i = n 时，prefix_sum(input_l, i)
   就是最终需要的 prefix_sum(input_l, n)
```

这就是 QCP + Coq + LLM 的典型合作方式：大模型先根据程序结构提出中间语义状态，再生成少量局部 Coq 引理，最后由 QCP 的符号执行和 Coq 的 proof checker 检查整个验证链条。

## 2. 不变式的共同形态

本批数组程序中，成功的不变式基本都有如下三层：

```c
/*@ Inv Assert
    // 控制状态
    0 <= i && i <= n &&
    n == Zlength(input_l) &&

    // 纯语义状态
    loop_state(i, input_l, acc_or_output_l, ...) &&

    // 分离逻辑资源
    IntArray::full(input, n, input_l) *
    IntArray::seg(output, 0, output_size, output_l) *
    IntArray::undef_seg(output, output_size, capacity)
*/
```

其中最关键的是中间的 `loop_state`。它不是最终规格，而是“程序已经执行到当前位置时，数学上发生了什么”。

下面按不变式中的纯语义状态进行分类。

## 3. 前缀折叠状态

这类程序只读数组，并维护累计变量，例如求和、乘积、计数、最大下标等。

典型定义：

```coq
Definition prefix_sum (l : list Z) (i : Z) : Z :=
  fold_left Z.add (sublist 0 i l) 0.

Definition prefix_product (l : list Z) (i : Z) : Z :=
  fold_left Z.mul (sublist 0 i l) 1.
```

循环不变式中写：

```c
sum == prefix_sum(input_l, i) &&
product == prefix_product(input_l, i)
```

相邻关系统计也属于同一类：

```coq
Fixpoint count_descents_prefix_nat (n : nat) (arr : list Z) : Z :=
  match n with
  | O => 0
  | S O => 0
  | S n' =>
      count_descents_prefix_nat n' arr +
      (if Z.ltb (Znth (Z.of_nat n') arr 0)
                (Znth (Z.of_nat n' - 1) arr 0)
       then 1 else 0)
  end.

Definition count_descents_prefix (i : Z) (arr : list Z) : Z :=
  count_descents_prefix_nat (Z.to_nat i) arr.
```

这种定义好处很明显：循环体每执行一次，只需要证明一个 `prefix_step` 引理，例如：

```coq
prefix_sum l (i + 1) = prefix_sum l i + Znth i l 0
```

大模型很容易根据 `sum += a[i]` 生成这种状态。

## 4. 已扫描区域状态

这类程序通常带有提前返回：一旦发现某个 witness 就立即 `return true`，如果整个循环结束都没有返回，则说明 witness 不存在。

因此，不变式要表达的不是“最终不存在 witness”，而是更弱、更适合循环推进的一句话：

```text
到目前为止，程序已经检查过的那部分搜索空间里，没有 witness。
```
例如二重循环：

```c
for (i = 0; i < n; i++) {
  for (j = i + 1; j < n; j++) {
    if (a[i] + a[j] == 0) return 1;
  }
}
return 0;
```

在内层循环执行到某个 `j` 时，我们知道：

```text
固定当前 i，所有 i < q < j 的 q 都已经检查过，
并且都不满足 a[i] + a[q] == 0。
```

写成 Coq 状态大概是：

```coq
Definition pair_sum_zero (l : list Z) (i j : Z) : Prop :=
  Znth i l 0 + Znth j l 0 = 0.

Definition scanned_pair_inner (l : list Z) (n i j : Z) : Prop :=
  forall q,
    i < q ->
    q < j ->
    ~ pair_sum_zero l i q.
```

这就比直接写“整个数组里不存在二元组”更容易保持。因为循环体每前进一步，只需要多排除当前这个 `j`。



## 5. 输出前缀构造状态

这类程序逐步写输出数组，例如生成数组、map、filter、去重输出。

固定公式生成可以直接定义目标列表：

```coq
Definition make_pile (n : Z) : list Z :=
  map (fun i => n + 2 * i) (Zseq 0 (Z.to_nat n)).
```

循环不变式中维护：

```c
IntArray::seg(data, 0, i, sublist(0, i, make_pile(n))) *
IntArray::undef_seg(data, i, n)
```

另一种常见情况是 filter。filter 的特点是：

```text
输入数组已经扫描了前 i 个元素，
但输出数组只写入了其中满足条件的一部分。
```

因此，filter 类不变式里一般不能写 `output_size = i`。例如筛选偶数：

```c
int output_size = 0;
for (i = 0; i < n; i++) {
  if (a[i] % 2 == 0) {
    out[output_size] = a[i];
    output_size++;
  }
}
```

当循环执行到 `i` 时，程序已经看过 `sublist 0 i input`，但输出只包含这个前缀里的偶数。所以纯语义状态应当写成：

```coq
Fixpoint filter_even (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      if Z.even x then x :: filter_even xs else filter_even xs
  end.

Definition filter_even_loop
  (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = filter_even (sublist 0 i input).
```

对应的循环不变式是：

```c
output_size == Zlength(output_l) &&
filter_even_loop(input_l, i, output_l) &&
0 <= output_size && output_size <= i &&
IntArray::seg(out, 0, output_size, output_l) *
IntArray::undef_seg(out, output_size, capacity)
```

这里 `output_l` 表示“目前已经真正写进输出数组的列表”。它的长度是 `output_size`，而不是 `i`。


这里 QCP 的分离逻辑资源很关键：`seg + undef_seg` 正好表达“前缀已经写好，后缀还没初始化”。这使得大模型生成的不变式不仅有数学意义，也能匹配内存状态。

## 6. 剩余值 + 累计值状态

这类程序通过 `%` 和 `/` 拆解整数，例如 digit sum、digit count、bit count。

这类循环和数组循环不一样：数组循环通常有一个下标 `i`，表示“已经处理了前 i 个元素”；而 digit 循环没有数组下标，它是不断把数字本身变小。

先看一个最简单的例子：计算一个整数的各位数字和。

```c
w = abs(num);
acc = 0;
while (w > 0) {
  d = w % 10;
  acc = acc + d;
  w = w / 10;
}
```

以 `num = 123` 为例，循环过程是：

```text
初始：      w = 123, acc = 0
处理 3 后： w = 12,  acc = 3
处理 2 后： w = 1,   acc = 5
处理 1 后： w = 0,   acc = 6
```

所以循环中间的状态不是“`acc` 已经等于最终答案”，而是：

```text
低位中已经被处理掉的部分，贡献了当前 acc；
高位中还没处理的部分，仍然保存在 w 里；
当前 acc + w 剩余所有 digit 的和 = 原始 num 的各位数字和。
```

这就是“剩余值 + 累计值状态”的意思。

在 Coq 中，可以先理解一个简化版本：

```coq
Fixpoint digit_sum (digits : list Z) : Z :=
  match digits with
  | [] => 0
  | d :: rest => d + digit_sum rest
  end.

Definition digit_sum_state_simple (num w acc : Z) : Prop :=
  acc + digit_sum (digits_of w) = digit_sum (digits_of (Z.abs num)).
```

这句话的意思是：

```text
当前已经累计的 acc，加上剩余数字 w 的各位数字和，
等于原始 num 的各位数字和。
```


digit sum 程序，循环不变式就会写成类似：

```c
digit_sum_state(num@pre, w, acc)
```

这类定义把 while 循环的动态过程表达得很清楚：

- `w` 是尚未处理的剩余部分。
- `acc` 是已经处理过的累计结果。
- 当循环执行 `d = w % 10; w = w / 10;` 时，相当于从 `w` 中拿走最低位 digit，并把它的贡献加入累计值。

这类定义也解释了为什么 QCP + Coq 比只依赖 SMT 更稳：涉及 `Z.rem`、`Z.quot`、燃料递归和边界证明时，Coq 可以补专门引理，而不是要求自动证明器一次性猜出所有事实。


## 7. 为什么这些不变式是“大模型友好”的

这些不变式有几个共同特点：

1. **命名清楚**：`prefix_sum`、`scanned_k`、`digit_count_state`、`sort_inner_state` 都直接对应程序片段。
2. **局部推进**：每个循环体只需要证明状态从 `i` 推进到 `i+1`，或从 `j` 推进到 `j+1`。
3. **与控制流同构**：嵌套循环对应嵌套 scanned state，多阶段程序对应多个 state predicate。
4. **内存和语义分离**：数组资源由 QCP 的 `IntArray::full/seg/undef_seg` 表达，数学含义由 Coq predicate 表达。
5. **失败可诊断**：如果 VC 失败，通常能定位为某个 step lemma、range lemma 或 final bridge lemma 缺失。

因此，QCP + Coq 中的大模型验证能力强，并不是因为它一次性生成了完美 proof，而是因为这套生态把任务分解成了稳定的中间层：

```text
C 程序控制流
    -> loop_state 纯语义状态
    -> 小型 Coq 引理
    -> 最终规格
```

这条路径比直接生成 Frama-C 中大而全的 ACSL invariant 更适合大模型。

## 8. 总结

本批 IntArrayClaude 程序验证表明，循环不变式可以归纳为少数几种纯语义状态：

| 类型 | 纯语义状态 | 典型含义 |
| --- | --- | --- |
| 前缀折叠 | `prefix_sum`, `prefix_product`, `count_descents_prefix` | 已处理前缀的累计结果 |
| 已扫描区域 | `scanned_i`, `scanned_j`, `scanned_k` | 已检查区域不存在 witness |
| 输出前缀 | `output = f(sublist 0 i input)` | 输出数组前缀已经构造完成 |
| 剩余值 + 累计值 | `digit_count_state(num, w, even, odd)` | 剩余输入与累计结果共同决定最终值 |

这些状态定义不追求一次性表达最终规格，而是精确表达循环执行中的中间语义。大模型之所以能在 QCP + Coq 中较稳定地生成正确不变式，关键就在于它可以先生成这种中间状态，再通过 Coq 小引理逐步连接到最终规格。
