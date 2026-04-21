# StringClaude 验证进度记录

更新时间：2026-04-16

这份文档用于记录 `QCP_examples/humaneval/StringClaude` 下各题的验证进度，以及每题验证时遇到的问题、采用的建模方式和后续继续时需要注意的事项。

它和下面几份文档分工不同：

- `STRING_VERIFICATION_GUIDE.md`：记录字符串程序验证的一般方法。
- `../SKILL.md`：记录完整验证流程、命令顺序和交付要求。
- 本文档：记录每一道题当前做到哪里、踩过哪些坑、最后如何解决。

## 状态说明

- `已全链通过`：已经完成 `symexec`、`manual` 证明、`goal_check` 编译，且 `coins_XX.v` / `C_XX_proof_manual.v` 无 `Admitted.` / `Axiom`。
- `已有生成文件`：目录中已有 `C_XX_goal.v` / `C_XX_proof_auto.v` / `C_XX_proof_manual.v` / `C_XX_goal_check.v`，但本文档尚未确认完整验收。
- `待建模`：尚未建立完整 QCP 规格和验证文件，通常需要先将 C 程序改写成 QCP 可接受的格式。

## 当前总览

| 题目 | 当前状态 | 备注 |
| --- | --- | --- |
| `C_11` | 已全链通过 | 二进制字符串 XOR；使用 `CharArray` 建模字符串，功能规格采用 `list Z` 版本 `problem_11_pre_z/spec_z`，manual 已补完。 |

其它只有 `.c` 的题目暂按 `待建模` 处理。

## C_11 验证记录

### 结论

`C_11` 已完成完整验证。

已通过的验收链：

```bash
coqc coins_11.v
coqc C_11_goal.v
coqc C_11_proof_auto.v
coqc C_11_proof_manual.v
coqc C_11_goal_check.v
```

扫描结果：

```bash
grep -nE "Admitted\.|Axiom[[:space:]]" coins_11.v C_11_proof_manual.v
```

无输出。

验证完成后已清理本题相关编译产物和备份文件，包括：

- `.C_11_*.aux`
- `.coins_11.aux`
- `C_11_*.glob`
- `C_11_*.vo`
- `C_11_*.vok`
- `C_11_*.vos`
- `coins_11.glob`
- `coins_11.vo`
- `coins_11.vok`
- `coins_11.vos`
- `C_11_proof_manual_backup*.v`

### 文件变更

- `C_11.c`
  - 将原始 libc 程序改写为 QCP 可接受的形式。
  - 使用 `verification_stdlib.h`、`verification_list.h`、`char_array_def.h`。
  - 声明 `malloc_char_array`，后置条件返回 `CharArray::undef_full(__return, n)`。
  - 声明 `strlen`，用 `CharArray::full(s, n + 1, app(l, cons(0, nil)))` 表示以 `0` 结尾的字符串。
  - 函数前置条件加入 `Zlength(l1) == na`、`Zlength(l2) == nb`、`na == nb`、`problem_11_pre_z(l1, l2)`。
  - 函数后置条件返回 `out_l` 和 `n`，并要求 `problem_11_spec_z(l1, l2, out_l)`。
  - 原始 `size_t` 改为 `int`，便于 QCP 处理整数范围和数组索引。
  - 原始三目表达式 `a[i] == b[i] ? '0' : '1'` 改为显式 `if`，并使用 ASCII 数值 `48` / `49`。
  - 原始 `'\0'` 改为 `0`。
  - 循环 invariant 维护已经写出的前缀 `out_l`，以及每个位置满足 XOR 规则。
- `coins_11.v`
  - `Load "../spec/11".`
  - 新增 `list_ascii_of_string` 和 `char_list_string`，作为 `list Z` 字符数组视图与原始 Coq `string` 规格之间的连接点。
  - 新增 `problem_11_pre_z`，直接在 `list Z` 上表达输入长度相等且每个字符是 `48` 或 `49`。
  - 新增 `problem_11_spec_z`，直接在 `list Z` 上表达 XOR 输出。
  - 新增 `problem_11_spec_z_intro`，用于 return 处从循环 invariant 中维护的逐点性质推出最终规格。
- `C_11_goal.v` / `C_11_proof_auto.v` / `C_11_proof_manual.v` / `C_11_goal_check.v`
  - 已由 `symexec --gen-and-backup` 生成并补完 manual。
  - 注意本目录当前生成文件命名是 `C_11_proof_auto.v` / `C_11_proof_manual.v`，而不是部分旧文档中的 `C_11_auto.v` / `C_11_manual.v`。

### 遇到的问题

1. QCP 注解中直接使用原始 `spec/11.v` 的 Coq `string` 规格不方便。

原因：C 侧字符串用 `CharArray::full` 表示为 `list Z` 加结尾 `0`，而 `spec/11.v` 中的 `problem_11_pre/spec` 是基于 Coq `string`。QCP 注解和 VC 里直接桥接 `string` 会让目标复杂很多。

解决方式：在 `coins_11.v` 中定义 `problem_11_pre_z` 和 `problem_11_spec_z`，作为面向 C 字符数组的 `list Z` 版本规格，同时保留 `Load "../spec/11".` 和 `char_list_string` 作为后续连接原始规格的入口。

2. `char_list_string` 目前只是桥接入口，不参与主证明闭环。

当前做法：C 程序证明使用 `problem_11_pre_z/spec_z` 完成。`char_list_string` 和 `problem_11_pre_z_from_spec` 只保留了从原始 `string` 规格连接到 `list Z` 规格的方向提示，其中 `problem_11_pre_z_from_spec` 以 `Abort` 结束，不会引入公理。

后续如需严格证明 `spec/11.v` 的原始 `problem_11_spec`，需要补完整的 `string <-> list Z` 桥接引理。

3. 原始程序里的三目表达式和字符字面量不适合直接交给 QCP。

原始写法：

```c
output[i] = (a[i] == b[i]) ? '0' : '1';
output[n] = '\0';
```

解决方式：

```c
if (a[i] == b[i]) {
    output[i] = 48;
} else {
    output[i] = 49;
}
output[n] = 0;
```

这样生成的 VC 分支更清晰，循环 invariant 也可以直接写 `48` / `49`。

4. `malloc` 结果必须建模为未初始化数组。

问题：程序随后逐位写入 `output[i]`。如果 malloc 后置条件直接给 `CharArray::full`，写入时资源形状不匹配。

解决方式：

```c
Ensure __return != 0 && CharArray::undef_full(__return, n)
```

循环 invariant 中维护：

```c
CharArray::full(output, i, out_l) *
CharArray::undef_seg(output, i, n + 1)
```

5. 初始循环 invariant 需要把 `undef_full` 拆成空前缀和未初始化段。

manual 中使用：

```coq
sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (na + 1)).
rewrite (CharArray.undef_seg_empty retval 0).
rewrite (CharArray.full_empty retval 0).
```

同时因为 `n` 最终化简到 `na`，需要重写长度等式，避免 `&( "n" ) # Int |-> Zlength l2` 和 `&( "n" ) # Int |-> na` 不匹配。

6. 循环分支的手工证明要根据写入字符分别追加 `48` / `49`。

相等分支：

```coq
Exists (app out_l_2 (cons 48 nil)).
```

不相等分支：

```coq
Exists (app out_l_2 (cons 49 nil)).
```

证明逐点性质时，对 `k < i` 使用旧 invariant，对 `k = i` 使用当前分支条件和刚追加的字符。

7. `++` 会被 `string_scope` 抢走。

表现：Coq 报 `out_l_2` 类型是 `list Z`，但期望 `string`。

解决方式：在 manual 中不用 `++`，改写成显式 `app out_l_2 (cons 48 nil)` / `app out_l_2 (cons 49 nil)`。

8. `app_Znth2` 后不一定能直接 `rewrite Zlength_cons`。

表现：Coq 报找不到 `Zlength (? :: ?)` 子项。

解决方式：先用循环长度事实把索引差化成 `0`：

```coq
rewrite app_Znth2 by lia.
replace (i - Zlength out_l_2) with 0 by lia.
rewrite Znth0_cons.
```

9. return 处 `CharArray.full` 的长度需要显式对齐。

表现：目标需要 `CharArray.full output (na + 1) ...`，上下文里可能是 `CharArray.full output (Zlength out_l_2 + 1) ...`。

解决方式：

```coq
assert (Hout_len : Zlength out_l_2 = na) by lia.
rewrite Hout_len.
```

然后使用 `problem_11_spec_z_intro` 将循环维护的逐点 XOR 性质推出最终 `problem_11_spec_z`。

10. 验证完成后的清理需要包含隐藏 `.aux` 文件。

Coq 编译会生成隐藏文件，例如：

```text
.C_11_goal.aux
.C_11_proof_auto.aux
.C_11_proof_manual.aux
.C_11_goal_check.aux
.coins_11.aux
```

这些也属于编译产物，验证完成后需要删除。此规则已同步补充到 `../SKILL.md` 的清理编译产物章节。

### 关键引理和脚本片段

`problem_11_spec_z_intro` 是 return 处的核心桥接引理：

```coq
Lemma problem_11_spec_z_intro :
  forall a b output n,
    Zlength a = n ->
    Zlength b = n ->
    Zlength output = n ->
    (forall k,
      0 <= k < n ->
      ((Znth k a 0 = Znth k b 0 /\ Znth k output 0 = 48) \/
       (Znth k a 0 <> Znth k b 0 /\ Znth k output 0 = 49))) ->
    problem_11_spec_z a b output.
```

循环推进中追加一个字符的典型证明结构：

```coq
Exists (app out_l_2 (cons 48 nil)).
pre_process.
rewrite (Zlength_app_cons out_l_2 48).
entailer!.
intros k Hk.
destruct (Z_lt_ge_dec k i).
- rewrite app_Znth1 by lia.
  apply H13. lia.
- assert (k = i) by lia. subst k.
  rewrite app_Znth2 by lia.
  replace (i - Zlength out_l_2) with 0 by lia.
  rewrite Znth0_cons.
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  left; split; auto.
```

return 处典型证明结构：

```coq
Right.
Exists out_l_2 na.
pre_process.
assert (Hi : i = na) by lia.
subst i.
assert (Hout_len : Zlength out_l_2 = na) by lia.
rewrite Hout_len.
rewrite (CharArray.undef_seg_empty output (na + 1)).
entailer!.
apply problem_11_spec_z_intro with (n := na); try lia.
intros k Hk.
apply H12. lia.
```

### 剩余注意事项

- 当前完整验证的是 C 字符数组层面的 `list Z` 规格 `problem_11_pre_z/spec_z`。
- `coins_11.v` 已加载 `../spec/11`，但尚未完成从原始 Coq `string` 规格到 `list Z` 规格的全套双向桥接证明。
- `C_11_proof_auto.v` 是生成的 auto 文件，里面可能保留生成器产生的 `Admitted.`；验收扫描按当前流程检查 `coins_11.v` 和 `C_11_proof_manual.v`。
