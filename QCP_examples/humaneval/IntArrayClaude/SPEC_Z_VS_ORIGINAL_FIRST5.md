# IntArrayClaude 自定义 spec_z 与原 spec 对照：前 5 个

本文只比较上一轮列出的 19 个“`problem_*_spec_z` 没有直接引用 `problem_*_spec`”例子中的前 5 个：

`46, 68, 72, 73, 85`

比较口径：

- 原 spec 指 `QCP_examples/humaneval/spec/XX.v` 中的 `problem_XX_spec`。
- 自定义 spec 指 `QCP_examples/humaneval/IntArrayClaude/coins_XX.v` 中的 `problem_XX_spec_z`。
- “等价”不是指文本相同，而是指在 C/QCP 的 `Z` 表示和原 spec 的类型之间做自然编码后，二者描述同一个输入输出关系。
- 本文是人工语义审阅，不是 Coq 形式化等价证明。

## 总览

| 编号 | 结论 | 主要问题 |
| --- | --- | --- |
| 46 | 基本等价，属于合理的 nat 到 Z lifting | `0 <= n` 被放进 spec_z；若采用很粗糙的 `Z.to_nat output` 比较，会和负输出产生差异 |
| 68 | 不等价，除非额外假设输入全非负且输出采用规范编码 | 原 spec 是 `list nat -> option (nat * nat)`；coins 用 `list Z -> list Z`，且 `pre_z` 没限制非负 |
| 72 | 不等价；只在把所有非零整数都视为 `true` 时才等价 | 原输出是 `bool`；coins 输出是 `Z`，允许任意非零值表示真 |
| 73 | 语义上等价 | coins 改写成按左右对称位置计数的循环型定义，没有明显语义改变 |
| 85 | 语义上等价 | coins 改写成只遍历奇数下标的循环型定义，没有明显语义改变 |

## 46

位置：

- 原 spec：`spec/46.v:48`
- 自定义 spec：`IntArrayClaude/coins_46.v:16`

原 spec：

```coq
Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  output = fib4 input.
```

coins 中先定义：

```coq
Definition fib4_z (n : Z) : Z :=
  Z.of_nat (fib4 (Z.to_nat n)).
```

然后定义：

```coq
Definition problem_46_spec_z (n output : Z) : Prop :=
  0 <= n /\ output = fib4_z n.
```

结论：基本等价。`problem_46_spec_z` 是把 `nat` 版 `fib4` 结果提升到 `Z` 的版本，并额外要求输入 `n` 非负。这个非负条件在原 spec 的 `nat` 输入里是类型层面保证的，因此放到 `Z` 版里是合理的。

更精确地说，它等价于如下自然 lifting：

```coq
0 <= n /\
exists out_nat,
  problem_46_spec (Z.to_nat n) out_nat /\
  output = Z.of_nat out_nat
```

差异点：

- `problem_46_spec_z` 没有直接写 `problem_46_spec`，所以后续如果原 spec/46.v 改了，coins 里的 spec_z 不会自动跟着改。
- `0 <= n` 同时出现在 `problem_46_pre_z` 和 `problem_46_spec_z`，这属于重复约束，但不是语义错误。
- 如果错误地把比较口径写成 `problem_46_spec (Z.to_nat n) (Z.to_nat output)`，那会不等价。例如 `output = -1` 会被 `Z.to_nat` 截成 `0`，但 `problem_46_spec_z` 不接受负输出。这不是 coins 的问题，而是 lifting 口径不能丢掉输出的规范 `Z.of_nat` 表示。

是否算完成原任务：可以认为完成。它没有引用原 spec，但语义只是 `nat -> Z` 的搬运。

## 68

位置：

- 原 spec：`spec/68.v:42`
- 自定义 spec：`IntArrayClaude/coins_68.v:44`

原 spec：

```coq
Definition problem_68_spec (arr : list nat) (output : option (nat * nat)) : Prop :=
  match output with
  | None =>
    forall val, In val arr -> Nat.even val = false
  | Some (v, i) =>
    i < length arr /\ nth i arr 1 = v /\
    Nat.even v = true /\
    (forall val, In val arr -> Nat.even val = true -> v <= val) /\
    (forall j, j < i -> nth j arr 1 <> v)
  end.
```

coins 自定义了输出编码和扫描函数：

```coq
Definition output_Z_to_option (l : list Z) : option (nat * nat) :=
  match l with
  | [] => None
  | value :: index :: [] => Some (Z.to_nat value, Z.to_nat index)
  | _ => None
  end.

Definition problem_68_spec_z (arr output : list Z) : Prop :=
  output = pluck_prefix_result arr (Zlength arr).
```

其中 `pluck_prefix_result` 的行为是：扫描 `arr`，找 `Z.rem x 2 = 0` 的最小值；遇到相等值时不更新，因此保留较小下标。

结论：不等价，除非额外加入“输入元素非负”和“输出列表是规范 Z 编码”的前提。

主要差异：

- 原 spec 的输入是 `list nat`，天然非负；coins 的输入是 `list Z`，但 `problem_68_pre_z` 只是 `problem_68_pre (list_Z_to_nat arr)`，而 `problem_68_pre` 是 `True`，所以它没有排除负数。
- 原 spec 的输出是 `option (nat * nat)`；coins 的输出是 `list Z`，用 `[]` 表示 `None`，用 `[value; index]` 表示 `Some (value, index)`。
- coins 里的 `output_Z_to_option` 定义了这种转换，但 `problem_68_spec_z` 本身没有使用原 spec，也没有要求 `problem_68_spec (list_Z_to_nat arr) (output_Z_to_option output)`。

反例：

```coq
arr = [-1]
```

coins 的扫描用 `Z.rem (-1) 2` 判断，`-1` 不是偶数，因此：

```coq
problem_68_spec_z [-1] []
```

成立。

但如果按原 spec 的 nat 输入理解，`list_Z_to_nat [-1] = [0]`。`0` 是偶数，因此原 spec 期望输出 `Some (0, 0)`，也就是规范列表编码 `[0; 0]`，而不是 `[]`。

如果额外假设：

```coq
forall i, 0 <= i < Zlength arr -> 0 <= Znth i arr 0
```

并且输出只允许 `[]` 或 `[Z.of_nat value; Z.of_nat index]` 这种规范编码，那么 coins 的扫描定义和原 spec 描述的“最小偶数值，平手取最小下标”是匹配的。

是否算完成原任务：严格说不算。当前 coins spec_z 没有把原 spec 作为约束，也没有把原 spec 的 `nat` 域约束完整搬到 `Z` 域。

## 72

位置：

- 原 spec：`spec/72.v:27`
- 自定义 spec：`IntArrayClaude/coins_72.v:20`

原 spec：

```coq
Definition problem_72_spec (q : list Z) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0 <= w)).
```

coins 自定义：

```coq
Definition mirror_all (q : list Z) : Prop :=
  forall k,
    0 <= k < Zlength q ->
    Znth k q 0 = Znth (Zlength q - 1 - k) q 0.

Definition problem_72_spec_z (q : list Z) (w out : Z) : Prop :=
  (out <> 0 <-> mirror_all q /\ sum q <= w).
```

结论：不等价。它把原来的 `bool` 输出改成了 C 风格整数 truthiness：`0` 表示假，任意非零整数表示真。

差异点：

- `mirror_all q` 和 `q = rev q` 语义上应当等价。
- `sum q` 和 `fold_left Z.add q 0` 语义上等价，coins 里也有 `fold_left_Zadd_0_sum`。
- 真正不等价的是输出：原 spec 只有 `true` 和 `false` 两个值；coins spec_z 接受任何非零整数作为真。

反例：

```coq
q = []
w = 0
out = 2
```

空列表是回文，和为 `0 <= w`，所以 coins 中：

```coq
problem_72_spec_z [] 0 2
```

成立，因为 `2 <> 0`。

但原 spec 的输出类型是 `bool`，没有一个“值为 2 的 bool 输出”。如果把 C 返回值严格规范为 `0` 或 `1`，则 `out = 2` 应该被排除。

如果额外要求：

```coq
out = 0 \/ out = 1
```

并用 `out = 1` 对应 `true`、`out = 0` 对应 `false`，那么 coins spec_z 与原 spec 语义一致。

是否算完成原任务：严格说不算。它证明的是 truthiness 版本，而不是原 spec 的精确 bool 输出。

## 73

位置：

- 原 spec：`spec/73.v:42`
- 自定义 spec：`IntArrayClaude/coins_73.v:29`

原 spec：

```coq
Definition problem_73_spec (arr: list Z) (n: Z): Prop :=
  n = smallest_change_impl arr.
```

其中 `smallest_change_impl` 取前半段、后半段反转，然后统计对应位置不同的个数。

coins 自定义：

```coq
Definition problem_73_spec_z (arr : list Z) (out : Z) : Prop :=
  exists i,
    0 <= i /\
    2 * i <= Zlength arr /\
    i >= Zlength arr - 1 - i /\
    out = count_half_mismatches_upto i arr.
```

这里的 `i` 由两个边界条件唯一确定为 `floor(length arr / 2)`，`count_half_mismatches_upto i arr` 统计 `j` 和 `length arr - 1 - j` 两侧对称位置的 mismatch。

结论：语义上等价。

差异点：

- 原 spec 是函数式定义：`out = smallest_change_impl arr`。
- coins spec 是循环退出形态：存在一个到达中点的 `i`，输出等于前 `i` 对对称元素的 mismatch 计数。
- 两个定义没有文本复用关系，但描述的是同一个计算。

需要形式化补的等价引理大致是：

```coq
problem_73_spec_z arr out <-> problem_73_spec arr out
```

证明关键是：

- `2 * i <= Zlength arr /\ i >= Zlength arr - 1 - i` 推出 `i = floor(Zlength arr / 2)`；
- `firstn (length arr / 2) arr` 和 `rev (skipn (length arr - length arr / 2) arr)` 的逐项比较，等价于 `Znth j arr 0` 和 `Znth (Zlength arr - 1 - j) arr 0` 的比较。

是否算完成原任务：可以认为完成，但最好在 coins 中补一个桥接引理引用原 spec，避免以后两个定义漂移。

## 85

位置：

- 原 spec：`spec/85.v:26`
- 自定义 spec：`IntArrayClaude/coins_85.v:28`

原 spec：

```coq
Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  output = add_impl lst.
```

`add_impl` 从下标 `0` 开始遍历整表，只累加“奇数下标且元素为偶数”的元素。

coins 自定义：

```coq
Definition problem_85_spec_z (lst : list Z) (output : Z) : Prop :=
  exists i,
    0 <= i /\
    2 * i <= Zlength lst /\
    2 * i + 1 >= Zlength lst /\
    output = sum_even_at_odd_upto i lst.
```

`sum_even_at_odd_upto i lst` 只枚举奇数下标 `1, 3, 5, ...`，并在元素满足 `Z.rem x 2 = 0` 时累加。

结论：语义上等价。

差异点：

- 原 spec 遍历每个下标，用 `Nat.odd idx` 判断是否是奇数下标。
- coins spec 直接枚举奇数下标 `2 * i + 1`，这是同一个集合。
- 原 spec 用 `Z.even h`，coins 用 `Z.rem h 2 = 0`。对整数偶数判断来说二者语义一致。
- 原 `problem_85_pre` 要求 `lst <> []`；coins 的 `problem_85_pre_z` 直接复用这个前置条件。

需要形式化补的等价引理大致是：

```coq
problem_85_spec_z lst output <-> problem_85_spec lst output
```

证明关键是：

- `2 * i <= Zlength lst /\ 2 * i + 1 >= Zlength lst` 唯一确定 `i` 为奇数下标的数量；
- `sum_even_at_odd_upto i lst` 等于从 `idx = 0` 开始遍历整表时对所有奇数下标偶数元素的累加。

是否算完成原任务：可以认为完成，但同样建议补桥接引理直接连回原 spec。

# 追加对照：88, 94, 96, 104, 109

## 88

位置：

- 原 spec：`spec/88.v:25`
- 自定义 spec：`IntArrayClaude/coins_88.v:28`

原 spec：

```coq
Definition problem_88_spec (input output : list nat) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: t =>
    let last_elem := last input h in
    if (h + last_elem) mod 2 =? 1 then
      Sorted le output
    else
      Sorted ge output
  end.
```

coins 自定义：

```coq
Definition problem_88_spec_z (input output : list Z) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: _ =>
      let last_elem := last input h in
      if Z.eqb ((h + last_elem) mod 2) 1 then
        Sorted Z.le output
      else
        Sorted Z.ge output
  end.
```

结论：在输入、输出都是非负整数的前提下，语义上等价；但 `problem_88_spec_z` 本身没有直接调用原 spec，也没有把非负性写进 spec。

差异点：

- 原 spec 的类型是 `list nat`，coins spec 的类型是 `list Z`。
- `problem_88_pre_z` 只是 `problem_88_pre (map Z.to_nat input)`，而原 pre 是 `True`，所以它不提供非负性。
- 文件里另有 `sort_array_input_range` 可以提供非负范围，但这个范围条件没有包含在 `problem_88_spec_z` 中。

如果没有非负前提，二者不是全局等价。例如：

```coq
input = [-1; 1]
output = [1; -1]
```

coins spec 中 `(-1 + 1) mod 2 = 0`，要求降序，`[1; -1]` 满足；但映射到原 spec 后输入变成 `[0; 1]`，首尾和为奇数，要求升序，输出映射为 `[1; 0]`，不满足。

是否算完成原任务：如果验证上下文始终带着 `sort_array_input_range`，算法性质是对的；但 coins 文件仍然没有“直接使用 spec/88.v 的 spec”。更稳妥的写法应当把 `problem_88_spec_z` 改成原 spec 的 Z 包装，并用范围条件证明桥接。

## 94

位置：

- 原 spec：`spec/94.v:38`
- 自定义 spec：`IntArrayClaude/coins_94.v:47`

原 spec：

```coq
Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\
    output = sum_digits p)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).
```

coins 自定义：

```coq
Definition problem_94_spec_z (lst : list Z) (out : Z) : Prop :=
  0 <= out <= 100 /\
  exists largest,
    largest_prime_prefix (Zlength lst) lst largest /\
    digit_sum_int_range largest.
```

结论：不等价，而且 coins spec 明显过弱。

为什么会丢掉核心要求：

`coins_94.v` 里的定义看起来像是把验证中间过程需要的“循环状态/范围不变量”误当成了最终函数规约。

- `largest_prime_prefix` 这个名字像是在描述“当前最大素数”，但实际定义只说明 `largest = 0` 或者 `largest` 是前缀里的某个元素，并没有证明它是素数。
- `largest_prime_prefix` 也没有说明 `largest` 是所有素数中的最大值。
- `digit_sum_int_range` 这个名字像是在描述 digit sum，但实际定义只是 `0 <= n <= INT_MAX`，并没有计算任何数字和。
- `problem_94_spec_z` 只要求 `out` 在 `0..100`，没有把 `out` 和 `largest` 的 `sum_digits` 关联起来。

所以它保留的是程序验证里常见的整数范围事实，例如 `out` 不溢出、`largest` 在 int 范围内；但原题真正的后置条件“返回最大素数的各位数字之和”没有被表达出来。

差异点：

- 原 spec 要求找到列表中最大的素数。
- 原 spec 要求输出等于该最大素数的各位数字之和。
- 如果列表中没有素数，原 spec 要求输出为 `0`。
- coins spec 只要求 `0 <= out <= 100`，并存在一个 `largest` 满足范围性质。
- `largest_prime_prefix` 没有要求 `largest` 是素数，也没有要求它是最大素数，甚至没有把 `out` 和 `largest` 的 digit sum 联系起来。

反例：

```coq
lst = [7]
out = 42
```

原 spec 要求输出为 `sum_digits 7 = 7`，所以 `out = 42` 不满足；coins spec 只要 `0 <= 42 <= 100`，并可取 `largest = 7`，因此满足。

另一个更极端的反例是：

```coq
lst = []
out = 42
```

原 spec 要求没有素数时输出 `0`；coins spec 可取 `largest = 0`，仍允许任意 `0..100` 的输出。

是否算完成原任务：没有完成。这里不是原 spec 不对，而是 coins 自定义 spec 丢掉了核心语义。

## 96

位置：

- 原 spec：`spec/96.v:24`
- 自定义 spec：`IntArrayClaude/coins_96.v:18`

原 spec：

```coq
Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (forall p, In p result -> prime (Z.of_nat p)) /\
  (forall p, In p result -> p < n) /\
  (forall p, prime (Z.of_nat p) -> p < n -> In p result) /\
  Sorted lt result /\
  NoDup result.
```

coins 自定义：

```coq
Definition problem_96_spec_z (n : Z) (result : list Z) : Prop :=
  (forall p, In p result -> prime p) /\
  (forall p, In p result -> p < n) /\
  (forall p, 2 <= p < n -> prime p -> In p result) /\
  Sorted Z.lt result /\
  NoDup result.
```

结论：这是原 spec 的直接 Z 版本，语义上基本等价。

差异点：

- 原 spec 的 `n` 和 `result` 都是 `nat`；coins spec 改成了 `Z`。
- 原 spec 通过 `prime (Z.of_nat p)` 判断自然数素数；coins spec 直接用 `prime p`。
- coins spec 的完备性只量化 `2 <= p < n` 的整数素数。由于 `prime p` 本身会推出 `p > 1`，这个 `2 <= p` 是显式化的范围条件。
- `problem_96_pre_z` 仍只是 `problem_96_pre (Z.to_nat n)`，而原 pre 是 `True`，所以没有额外约束 `n >= 0`；不过当 `n < 0` 时，两边都只允许空结果。

是否算完成原任务：语义上可以认为完成，但形式上仍是自己重写了一份 spec。更符合要求的写法是用原 spec 包装，例如把输出通过 `map Z.to_nat` 传给 `problem_96_spec`，再证明 Z 版本条件与原 spec 等价。

## 104

位置：

- 原 spec：`spec/104.v:109`
- 自定义 spec：`IntArrayClaude/coins_104.v:89`

原 spec：

```coq
Definition unique_digits_impl (x : list nat) : list nat :=
  sort_list (filter_odd_digits x).

Definition problem_104_spec (x y : list nat) : Prop :=
  y = unique_digits_impl x.
```

其中 `filter_odd_digits` 只保留所有十进制数字均为奇数的元素，然后 `sort_list` 升序排序。

coins 自定义：

```coq
Definition problem_104_spec_z (input output : list Z) : Prop :=
  exists filtered,
    unique_digits_prefix input (Zlength input) filtered /\
    sorted_int_list_by 1 output /\
    Permutation filtered output.
```

`unique_digits_prefix` 用两个关系判断当前元素：

```coq
only_odd_digits_z (Znth i input 0)
has_even_digit_z (Znth i input 0)
```

结论：不等价，coins spec 过弱。

关键问题在 `has_even_digit_z`：

```coq
Definition has_even_digit_z (n : Z) : Prop :=
  exists num, odd_digit_scan_state n num 0.
```

而 `odd_digit_scan_state` 有构造子：

```coq
| odd_scan_zero :
    odd_digit_scan_state original 0 0
```

这意味着对任意 `n`，`has_even_digit_z n` 都成立。因此 `unique_digits_prefix_skip` 总是可以跳过当前元素。对于所有数字均为奇数的元素，`only_odd_digits_z` 也可以成立，于是同一个元素既可以被加入，也可以被跳过，过滤结果变成非确定关系。

反例：

```coq
input = [15]
output = []
```

原 spec 中 `15` 的数字 `1` 和 `5` 都是奇数，所以 `unique_digits_impl [15] = [15]`，输出 `[]` 不满足。

coins spec 中 `has_even_digit_z 15` 由 `odd_scan_zero` 直接成立，所以 `unique_digits_prefix_skip` 可以跳过 `15`，取 `filtered = []`，于是 `output = []` 满足。

是否算完成原任务：没有完成。这里看起来不是原 spec 不对，而是 coins 自定义的 digit-scan 关系定义得太宽，导致 spec 接受错误输出。

## 109

位置：

- 原 spec：`spec/109.v:74`
- 自定义 spec：`IntArrayClaude/coins_109.v:35`

原 spec：

```coq
Definition problem_109_spec (arr : list Z) (result : bool) : Prop :=
  result = move_one_ball_impl arr.
```

`move_one_ball_impl` 会检查是否存在某个右移后的列表是非降序。

coins 自定义：

```coq
Definition problem_109_spec_z (arr : list Z) (result : Z) : Prop :=
  (result <> 0 /\ cyclic_descents arr < 2) \/
  (result = 0 /\ cyclic_descents arr >= 2).
```

`cyclic_descents` 统计相邻下降点，并额外统计首尾环形下降点。

结论：排序旋转条件本身在 `NoDup arr` 前提下很可能与原算法等价，但整个 spec 不等价，因为返回值被放宽成了“任意非零都表示 true”。

差异点：

- 原 spec 的结果类型是 `bool`，必须精确等于 `move_one_ball_impl arr`。
- coins spec 的结果类型是 `Z`，true 分支只要求 `result <> 0`，没有要求 `result = 1`。
- `problem_109_pre_z` 确实直接复用了原前置条件 `NoDup arr`。
- `cyclic_descents arr < 2` 是“环形序列至多一个下降点”的刻画；对互异元素列表，这与“某个旋转后非降序”是标准等价条件。

反例：

```coq
arr = []
result = 2
```

原实现对空列表返回 `true`；如果用 C 整数表示 bool，通常应当是 `1`。coins spec 因为只要求 `result <> 0`，所以 `2` 也被接受。

是否算完成原任务：只完成了布尔语义的弱版本，没有完成“直接使用原 spec”。如果验证的 C 程序确实只会返回 `0` 或 `1`，可以通过额外证明把它桥接回原 spec；但 `problem_109_spec_z` 自身仍比原 spec 弱。

# 追加对照：114, 116, 120, 121, 122

## 114

位置：

- 原 spec：`spec/114.v:23`
- 自定义 spec：`IntArrayClaude/coins_114.v:43`

原 spec：

```coq
Definition problem_114_spec (nums : list Z) (min_sum : Z) : Prop :=
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    list_sum sub_array = min_sum)
  /\
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    min_sum <= list_sum sub_array).
```

coins 自定义：

```coq
Definition problem_114_spec_z (nums : list Z) (result : Z) : Prop :=
  result = min_subarray_prefix (Zlength nums) nums.
```

结论：在 `problem_114_pre_z nums`，也就是 `nums <> []` 的前提下，语义上应当等价；但 coins 没有直接使用原 spec，而是把“最小非空连续子数组和”改写成了 Kadane 风格的计算函数。

差异点：

- 原 spec 是关系式性质：要求存在一个非空连续子数组，其和为 `min_sum`，并且所有非空连续子数组的和都不小于 `min_sum`。
- coins spec 是函数式结果：`result` 必须等于 `min_subarray_prefix (Zlength nums) nums`。
- `min_subarray_prefix` 依赖 `min_suffix_prefix`，维护“截至当前位置的最小后缀和”和“前缀内最小子数组和”。这和原 spec 描述的是同一个算法意图，但需要单独证明该函数确实满足原 spec 的存在性和最小性。
- 对空列表，coins spec 会给出 `result = 0`；原 `problem_114_pre` 排除了空列表，所以这个差异在合法输入下不暴露。

是否算完成原任务：从语义看可以认为完成，但形式上没有引用原 spec。更稳妥的写法是让 `problem_114_spec_z` 直接等于 `problem_114_spec nums result`，然后把 Kadane 函数正确性作为辅助引理使用。

## 116

位置：

- 原 spec：`spec/116.v:97`
- 自定义 spec：`IntArrayClaude/coins_116.v:84`

原 spec：

```coq
Definition problem_116_spec (input output : list nat) : Prop :=
  output = sort_array_impl input.
```

其中 `sort_array_impl` 按二进制表示中 `1` 的个数升序排序；个数相同则按数值升序排序。

coins 自定义：

```coq
Definition problem_116_spec_z (input output : list Z) : Prop :=
  output = bubble_sort_116 input.
```

`bubble_sort_116` 使用 `bit_count_116` 和 `should_swap_116` 在 `Z` 列表上做同样的相邻交换排序。

结论：在输入元素都满足非负整数范围，例如文件中的 `sort_array_116_int_range input`，并且输出保持同一组整数的前提下，语义上等价于原 spec 的 Z lifting；但 `problem_116_spec_z` 本身没有直接调用 `problem_116_spec`，也没有把非负性写进 spec。

差异点：

- 原 spec 的输入输出类型是 `list nat`，天然非负。
- coins spec 的输入输出类型是 `list Z`，而 `problem_116_pre_z input := problem_116_pre (map Z.to_nat input)`；原 pre 是 `True`，所以这个 pre 不排除负数。
- coins 里另有 `sort_array_116_int_range` 限制输入 `0 <= Znth i input 0 < INT_MAX`，但它是验证用范围条件，不是 `problem_116_spec_z` 的一部分。
- 对非负整数，`bit_count_116 z` 与原 spec 中 `count_ones (Z.to_nat z)` 一致，排序准则也一致。
- 如果允许负数，二者不再是自然的原 spec lifting：原 spec 经 `Z.to_nat` 会把负数截成 `0`，而 coins 的排序会保留负数值，并在 bit count 相同的情况下按负数本身参与 tie-break。

反例口径：

```coq
input = [-1; 0]
```

coins 会把 `-1` 和 `0` 都视作 bit count 为 `0`，再按数值排序，可能保留 `[-1; 0]` 这种 Z 输出；但原 spec 若只看 `map Z.to_nat input`，输入变成 `[0; 0]`，已经丢失了 `-1` 这个值。

是否算完成原任务：在实际验证若始终带着 `sort_array_116_int_range`，算法语义是对的；但当前 `problem_116_spec_z` 不是直接使用原 spec，且 spec 自身没有表达原 `nat` 域对应的非负约束。

## 120

位置：

- 原 spec：`spec/120.v:48`
- 自定义 spec：`IntArrayClaude/coins_120.v:31`

原 spec：

```coq
Definition problem_120_spec (arr : list Z) (k : nat) (res : list Z) : Prop :=
  length res = k /\
  Sorted Z.le res /\
  (exists rest_of_arr,
    Permutation (res ++ rest_of_arr) arr /\
    (forall x y, In x res -> In y rest_of_arr -> y <= x)).
```

coins 自定义：

```coq
Definition problem_120_spec_z (input : list Z) (k : Z) (output : list Z) : Prop :=
  (k = 0 /\ output = []) \/
  exists sorted_l,
    0 < k <= Zlength input /\
    k = Zlength output /\
    Zlength sorted_l = Zlength input /\
    sorted_int_list_by 1 sorted_l /\
    Permutation input sorted_l /\
    output = maximum_output_prefix sorted_l (Zlength input) k k.
```

结论：在 `0 <= k <= Zlength input` 的合法输入前提下，语义上应当等价；coins 是把原 spec 的 top-k 关系改写成“先整体升序排序，再取最后 k 个元素”。

差异点：

- 原 spec 用 `k : nat`；coins 用 `k : Z`。
- 原 spec 不要求给出完整排序列表，只要求存在 `rest_of_arr`，使 `res` 是升序的、`res ++ rest_of_arr` 是原数组排列，并且 `rest_of_arr` 中任意元素都不大于 `res` 中任意元素。
- coins spec 要求存在完整升序排列 `sorted_l`，并要求 `output` 精确等于 `sorted_l` 的最后 `k` 个元素。
- 对整数全序来说，这两个描述刻画的是同一个“升序排列的最大 k 个元素”。重复元素也不会破坏等价性，因为两边都用 `Permutation` 保留重数。
- `k = 0` 时，coins 单独给出 `output = []`；原 spec 由 `length res = 0` 也推出 `res = []`，并可取 `rest_of_arr = arr`。

是否算完成原任务：语义上可以认为完成，但形式上仍是自定义 spec。若要完全符合“直接使用 spec/120.v”，应改成 `problem_120_spec input (Z.to_nat k) output`，并用辅助引理证明排序后取后缀满足原 top-k 关系。

## 121

位置：

- 原 spec：`spec/121.v:21`
- 自定义 spec：`IntArrayClaude/coins_121.v:28`

原 spec：

```coq
Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.
```

原实现从下标 `0` 开始遍历整个列表，累加“下标为偶数且元素为奇数”的元素。

coins 自定义：

```coq
Definition problem_121_spec_z (lst : list Z) (output : Z) : Prop :=
  exists i,
    0 <= i /\
    2 * i <= Zlength lst + 1 /\
    Zlength lst <= 2 * i /\
    output = sum_odd_at_even_upto i lst.
```

`sum_odd_at_even_upto i lst` 只枚举下标 `0, 2, 4, ...`，并在 `Z.rem x 2 = 1` 时累加。

结论：这是原 spec 的循环形态 Z 版本，语义上基本等价；但没有直接引用 `problem_121_spec`。

差异点：

- 原 spec 的列表元素和输出是 `nat`；coins 使用 `Z`。
- 原 spec 遍历所有下标，并用 `Nat.even idx` 判断偶数位置；coins 直接枚举偶数下标 `2 * i`。
- 原 spec 用 `negb (Nat.even h)` 判断元素是奇数；coins 用 `Z.rem x 2 = 1`。对非负整数这完全一致。
- 如果输入包含负数，按原 spec 的自然 lifting 会先做 `Z.to_nat`，负数变成 `0`；coins 中负数的 `Z.rem x 2` 不会等于 `1`，因此也不会被累加。这个行为与 `map Z.to_nat` 后的求和一致。
- 退出条件 `2 * i <= Zlength lst + 1 /\ Zlength lst <= 2 * i` 表示 `i` 已经覆盖所有偶数下标，本质上是循环退出状态。

是否算完成原任务：语义上可以认为完成，属于 nat 到 Z 加循环退出形态的改写；但如果要求 `coins_121.v` 直接使用原 spec，就还需要把 `problem_121_spec_z` 改成对 `problem_121_spec (map Z.to_nat lst) (Z.to_nat output)` 的规范包装，并避免负输出被 `Z.to_nat` 截断的问题。

## 122

位置：

- 原 spec：`spec/122.v:31`
- 自定义 spec：`IntArrayClaude/coins_122.v:27`

原 spec：

```coq
Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.
```

其中：

```coq
Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).
```

coins 自定义：

```coq
Definition problem_122_spec_z (arr : list Z) (k result : Z) : Prop :=
  result = sum_two_digit_upto k arr.
```

`sum_two_digit_upto` 遍历前 `k` 个元素，并在 `-99 <= x <= 99` 时累加。

结论：在 `1 <= k <= Zlength arr` 的合法输入前提下，语义上等价；但 `coins_122.v` 不仅没有直接使用原 spec，而且当前文件开头没有 `Load "../spec/122".`，所以它和原 spec 完全没有形式连接。

差异点：

- 原 spec 的 `k` 是 `nat`；coins 的 `k` 是 `Z`。
- 原 spec 用 `firstn k arr`、`filter is_at_most_two_digits`、`fold_left Z.add` 表达。
- coins 用递归函数 `sum_two_digit_upto_nat (Z.to_nat k) arr` 表达同一件事。
- `is_at_most_two_digits n` 的条件 `-100 < n /\ n < 100` 等价于 coins 中的 `-99 <= n /\ n <= 99`，因为 `n : Z`。
- 如果 `k` 为负，coins 里的 `Z.to_nat k` 会变成 `0`；不过 `problem_122_pre_z` 要求 `1 <= k`，合法输入下不存在这个差异。

是否算完成原任务：语义上可以认为完成，但形式上没有完成“直接使用 spec/122.v”。这里至少应该先 `Load "../spec/122".`，再把 `problem_122_spec_z` 写成 `problem_122_spec arr (Z.to_nat k) result` 或证明两者等价。

## 123

位置：

- 原 spec：`spec/123.v`
- 自定义 spec：`IntArrayClaude/coins_123.v`

原 spec：

```coq
Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.
```

coins 自定义：

```coq
Definition problem_123_spec_z (n : Z) (result : list Z) : Prop :=
  exists raw_l,
    odd_collatz_prefix n 1 raw_l /\
    sorted_int_list_by 1 result /\
    Permutation raw_l result.
```

结论：语义目标基本一致，都是“Collatz 序列中的奇数，升序输出”；但 coins 没有直接使用原 spec，并且中间见证不同。

差异点：

- 原 spec 用 `collatz_aux` 生成完整 Collatz 序列 `c_seq`，再过滤所有 `Z.odd` 元素。
- coins 用归纳谓词 `odd_collatz_prefix` 只维护奇数元素列表：初始包含 `[1]`，遇到非 1 奇数时把当前数追加到末尾，偶数步骤不追加。
- 原 spec 的奇数列表来自 `filter Z.odd c_seq`，顺序是 Collatz 轨迹顺序；coins 的 `raw_l` 是 `[1]` 加上轨迹中遇到的其它奇数。因此两者一般不是同一列表，但互为排列。
- 原 spec 要求 `Sorted Z.le result`；coins 通过 `sorted_int_list_by 1 result` 表达同一排序要求。

是否算完成原任务：语义上可以认为完成，但形式上没有直接引用原 spec。应把 `problem_123_spec_z` 改成 `problem_123_spec`，并用桥接引理从 `odd_collatz_prefix` 证明原 spec。

## 126

位置：

- 原 spec：`spec/126.v`
- 自定义 spec：`IntArrayClaude/coins_126.v`

原 spec（修改前）：

```coq
Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.
```

coins 自定义：

```coq
Definition problem_126_spec_z (l : list Z) (b : bool) : Prop :=
  if b then sorted_no_triple_prefix (Zlength l) l
  else ~ sorted_no_triple_prefix (Zlength l) l.
```

其中 `sorted_no_triple_prefix` 表示非递减排序，并禁止三个连续相同元素。

结论：不等价，而且原 spec 本身不符合题目示例。

差异点：

- 题目要求“升序，且同一个数不能出现超过两次”。示例 `[1, 2, 2, 3, 3, 4]` 应返回 `True`，`[1, 2, 2, 2, 3, 4]` 应返回 `False`。
- coins 的 spec 表达的是这个题意：允许相邻两个相等元素，但禁止三个连续相等元素。
- 原 spec 使用 `Sorted Nat.lt`，这是严格递增排序，不允许任何重复元素。因此 `[1, 2, 2, 3]` 会被原 spec 判为 `False`，与题意和示例冲突。
- 原 spec 的输入是 `list nat`，coins 的输入是 `list Z`；这个 nat/Z lifting 不是主要问题，核心问题是 `Nat.lt` 过强。

是否算完成原任务：不能改成使用原 spec。这里属于 `spec/126.v` 自身语义错误，应记录并跳过，除非先修正原 spec。

后续处理：已修正 `spec/126.v`。新的原 spec 改为 `sorted_no_triple_nat l <-> b = true`，其中 `sorted_no_triple_nat` 使用下标形式表达：

- 相邻元素非递减：`nth (j - 1) l 0 <= nth j l 0`
- 不允许三个连续相同元素

`coins_126.v` 现在直接使用修正后的：

```coq
problem_126_spec (map Z.to_nat l) b
```

同时 `problem_126_pre_z` 增加了输入非负条件 `Forall (fun z => 0 <= z) l`，使 C 侧 `list Z` 到原 spec 的 `list nat` 转换是规范的。

## 155

位置：

- 原 spec：`spec/155.v`
- 自定义 spec：`IntArrayClaude/coins_155.v`

原 spec：

```coq
Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  output = even_odd_count_impl num.
```

coins 自定义：

```coq
Definition problem_155_spec_z (num : Z) (output : list Z) : Prop :=
  exists even odd,
    output = [even; odd] /\
    count_result_c num = (even, odd).
```

结论：语义上基本等价，但输出编码不同，且 coins 没有直接引用原 spec。

差异点：

- 原 spec 输出是 `nat * nat`；coins 的 C 接口输出是长度为 2 的 `list Z`，形如 `[even; odd]`。
- 原 spec 用 `Z.even` 判断数字奇偶，数字分解用 `mod`/`div`。
- coins 用 `Z.rem`/`Z.quot` 处理 C 风格整数运算；由于先取绝对值并且循环中的 `w >= 0`，这些与原 spec 的非负 `mod`/`div` 语义一致。
- 原 spec 对 `0` 的数字列表是 `[0]`，因此输出应为 `(1, 0)`；coins 的初始化也把 `0` 计为一个偶数字。

是否算完成原任务：语义上可以认为完成，但形式上没有直接使用原 spec。应把 `problem_155_spec_z` 改成对 `problem_155_spec num (even_nat, odd_nat)` 的规范列表包装。

## 163

位置：

- 原 spec：`spec/163.v`
- 自定义 spec：`IntArrayClaude/coins_163.v`

原 spec：

```coq
Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.
```

coins 自定义：

```coq
Definition problem_163_spec_z (a b : Z) (output : list Z) : Prop :=
  output = generate_list (Z.min a b) (Z.max a b).
```

其中 `generate_list` 是从固定候选 `[2; 4; 6; 8]` 中筛选落在闭区间内的元素。

结论：在正整数输入前提下语义等价，但 coins 没有直接引用原 spec。

差异点：

- 原 spec 的输入和输出都是 `nat`；coins 用 `Z`，需要通过 `Z.to_nat`/`Z.of_nat` 做规范转换。
- 原 spec 是外延式描述：成员当且仅当在区间内、小于 10、且为偶数，并要求排序和无重复。
- coins 是构造式描述：直接过滤候选列表 `[2;4;6;8]`。这个列表正好枚举所有正的偶数 digit。
- 对合法正输入，`Z.min/Z.max` 和 `Nat.min/Nat.max` 经 `Z.to_nat` 转换一致；输出也都是升序无重复。

是否算完成原任务：语义上可以认为完成，但形式上没有直接使用原 spec。应把 `problem_163_spec_z` 改成 `problem_163_spec (Z.to_nat a) (Z.to_nat b) (map Z.to_nat output)`，再证明生成列表满足原 spec。
