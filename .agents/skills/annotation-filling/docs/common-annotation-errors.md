# Common Annotation Errors

这个文件收集 annotation 阶段最常见、最值得提前规避的错误。

每个案例都保持同一结构：

1. 错误的 Assertion / Invariant
2. 它导致的错误 VC 长什么样
3. 正确的 Assertion / Invariant

## 1. 漏掉 `@pre` 桥

### 错误的 Assertion

```c
/*@ Assert
    exists parent1 rank1,
      0 <= rx && rx < n &&
      0 <= n && n < INT_MAX &&
      0 <= y && y < n &&
      safeExec(state_bridge(n, parent1, rank1), applyf(uf_union_after_find_x(y), rx), X) &&
      IntArray::full(parent, n, parent1) *
      IntArray::full(rank, n, rank1)
*/
```

### 它导致的错误 VC 长什么样

```coq
... 0 <= n /\ n < INT_MAX /\ 0 <= y /\ y < n /\
IntArray.full parent n parent1 * IntArray.full rank n rank1
|--
... 0 <= n_pre /\ n_pre < INT_MAX /\ 0 <= y_pre /\ y_pre < n_pre /\
IntArray.full parent_pre n_pre parent_out * IntArray.full rank_pre n_pre rank_out
```

左边只有当前 `n / parent / rank / x / y`，右边要的是
`n_pre / parent_pre / rank_pre / x_pre / y_pre`，中间没有桥。

### 正确的 Assertion

```c
/*@ Assert
    exists parent1 rank1,
      n == n@pre &&
      parent == parent@pre &&
      rank == rank@pre &&
      x == x@pre &&
      y == y@pre &&
      0 <= rx && rx < n &&
      0 <= n && n < INT_MAX &&
      0 <= y && y < n &&
      safeExec(state_bridge(n, parent1, rank1), applyf(uf_union_after_find_x(y), rx), X) &&
      IntArray::full(parent, n, parent1) *
      IntArray::full(rank, n, rank1)
*/
```

## 2. 读了数组元素，但没把局部变量和数组值绑定起来

### 错误的 Assertion

```c
/*@ Assert
    rx_rank == rank_out[rx] &&
    rx != ry &&
    n == n@pre &&
    parent == parent@pre &&
    rank == rank@pre &&
    x == x@pre &&
    y == y@pre &&
    0 <= rx && rx < n &&
    0 <= ry && ry < n &&
    0 <= n && n < INT_MAX &&
    safeExec(state_bridge(n, parent_out, rank_out), uf_union_after_ry_rank(rx, ry, rx_rank, ry_rank), X) &&
    IntArray::full(parent, n, parent_out) *
    IntArray::full(rank, n, rank_out)
*/
```

这里错在少了：

```c
ry_rank == rank_out[ry]
```

### 它导致的错误 VC 长什么样

```coq
safeExec(state_bridge(n, parent3, rank_out), bump_rank(ry), X)
&& IntArray.full(rank, n, rank_out)
|--
exists rank3,
  rank3 = replace_Znth(ry, ry_rank + 1, rank_out) /\
  safeExec(state_bridge(n, parent3, rank3), return(tt), X) /\
  IntArray.full(rank, n, rank3)
```

没有 `ry_rank == rank_out[ry]`，`ry_rank` 只是一个游离整数，不是
“数组当前位置读出来的值”。

### 正确的 Assertion

```c
/*@ Assert
    ry_rank == rank_out[ry] &&
    rx_rank == rank_out[rx] &&
    rx != ry &&
    n == n@pre &&
    parent == parent@pre &&
    rank == rank@pre &&
    x == x@pre &&
    y == y@pre &&
    0 <= rx && rx < n &&
    0 <= ry && ry < n &&
    0 <= n && n < INT_MAX &&
    safeExec(state_bridge(n, parent_out, rank_out), uf_union_after_ry_rank(rx, ry, rx_rank, ry_rank), X) &&
    IntArray::full(parent, n, parent_out) *
    IntArray::full(rank, n, rank_out)
*/
```

## 3. 用恒真式假装“保变量”

### 错误的 Assertion

```c
/*@ Assert
    exists parent2,
      parent2 == replace_Znth(x, r, parent1) &&
      p == p &&
      0 <= r && r < n &&
      safeExec(state_bridge(n, parent2, rank1), return(r), X) &&
      IntArray::full(parent, n, parent2) *
      IntArray::full(rank, n, rank1)
*/
```

### 它导致的错误 VC 长什么样

```coq
emp |-- &( "p") # Int |-> 0
```

`p == p` 没有提供任何新信息，只会把当前程序变量 `p` 又读进
full assertion，结果后件多出一格局部变量槽位资源。

### 正确的 Assertion

```c
/*@ Assert
    exists parent2,
      parent2 == replace_Znth(x, r, parent1) &&
      n == n@pre &&
      parent == parent@pre &&
      rank == rank@pre &&
      x == x@pre &&
      0 <= r && r < n &&
      safeExec(state_bridge(n, parent2, rank1), return(r), X) &&
      IntArray::full(parent, n, parent2) *
      IntArray::full(rank, n, rank1)
*/
```

这里关键就是删掉 `p == p`，只保留真正有信息量的关系。

## 4. Refinement 分层错误：把 functional correctness 塞进 C 侧 invariant

这个错误常见于 refinement case。它未必会立刻表现成一个
“少一句纯事实”的局部卡点，但会让 annotation 结构变重、返工成本变高。

### 错误的 Invariant

下面给出一个坏版 `kmp_rel.c` `constr` 循环不变量：

```c
/*@ Inv Assert
        exists vnext0 l0,
            safeExec(ATrue, constr_loop_from(0, str, i, vnext0, j), X) &&
            is_prefix_func(vnext0, sublist(0, i, str)) &&
            patn == patn@pre &&
            len == n && n < INT_MAX && 1 <= i &&
            CharArray::full(patn, n + 1, app(str, cons(0, nil))) *
            IntArray::full(vnext, i, vnext0) *
            IntArray::full((vnext + i * sizeof(int)), n - i, l0)
*/
```

这里多出来的坏东西是：

```c
is_prefix_func(vnext0, sublist(0, i, str))
```

### 它导致的错误 VC 长什么样

```coq
... safeExec(ATrue, constr_loop_from_after(0, str, i, vnext0, j), X)
... IntArray.full(vnext, n, l)
|--
EX vnext1 l1,
   safeExec(ATrue, constr_loop_from(0, str, i + 1, vnext1, j), X)
   && is_prefix_func(vnext1, sublist(0, i + 1, str))
   && IntArray.full(vnext, i + 1, vnext1)
   ** IntArray.full((vnext + (i + 1) * sizeof(int)), n - (i + 1), l1)
```

这会迫使 C 层 invariant 在每一步都证明 KMP 前缀函数构造的
functional correctness。对于 refinement case，这类 functional
correctness 应只出现在 `high_level_spec` 中；除 `high_level_spec`
外，C 侧 annotation 不应重复出现 monad 已经覆盖的 functional
correctness 谓词。

### 正确的 Invariant

`kmp_rel.c` 里更合理的写法是：

```c
/*@ Inv Assert
        exists vnext0 l0,
            safeExec(ATrue, constr_loop_from(0, str, i, vnext0, j), X) &&
            patn == patn@pre &&
            len == n && n < INT_MAX && 1 <= i &&
            CharArray::full(patn, n + 1, app(str, cons(0, nil))) *
            IntArray::full(vnext, i, vnext0) *
            IntArray::full((vnext + i * sizeof(int)), n - i, l0)
*/
```

这里 invariant 只维护：

- residual `safeExec(...)`
- 当前游标 / progress
- 内存 shape
- 必要的 `@pre` 桥接

而最终 functional correctness：

```c
is_prefix_func(vnext, str)
```

只出现在 `high_level_spec` 里。除 `high_level_spec` 外，C 侧
annotation 不应再次要求证明这一类最终功能语义。
