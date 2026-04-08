# HumanEval IntClaude 验证作战手册（给大模型）

## 0. 文档目的

这份文档是大模型在本项目做验证时的单文件参考，目标是尽量不再翻其他例子。

适用范围：

- 目录：`QCP_examples/humaneval/IntClaude`
- 任务：`C_XX.c` + `coins_XX.v` + `C_XX_manual.v` 证明闭环

最终目标：

1. `coins_XX.v` 与 `C_XX_manual.v` 无 `Admitted.`
2. 手写证明文件无 `Axiom`
3. `C_XX_goal_check.v` 编译通过

---

## 1. 固定环境

工作目录：

```bash
cd /home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude
```

Coq 环境：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
COQINCLUDES="$(tr '\n' ' ' < _CoqProject)"
```

---

## 2. 实时进度（2026-04-08）

统计口径：扫描所有 `C_*_manual.v` 的 `Admitted.` 与 `Axiom`。

- 总文件数：20
- 已达 `0 Admitted / 0 Axiom`：20
- 待完成：0
- 剩余 `Admitted` 总数：0

### 2.1 已达 0 Admitted/0 Axiom

- `C_102_manual.v`
- `C_13_manual.v`
- `C_131_manual.v`
- `C_138_manual.v`
- `C_139_manual.v`
- `C_150_manual.v`
- `C_24_manual.v`
- `C_31_manual.v`
- `C_36_manual.v`
- `C_39_manual.v`
- `C_41_manual.v`
- `C_49_manual.v`
- `C_53_manual.v`
- `C_59_manual.v`
- `C_60_manual.v`
- `C_75_manual.v`
- `C_76_manual.v`
- `C_77_manual.v`
- `C_83_manual.v`
- `C_97_manual.v`

注：上述 20 题目前都已完成全链编译验收，`coins_XX.v / goal / auto / manual / goal_check` 已逐题编译通过。

### 2.2 待完成

- 无。`IntClaude` 目录下现有 20 个 `C_*.c` 已全部完成验证。

---

## 3. 每题标准流程（必须按顺序）

### Step 1: 读 4 类文件

1. `C_XX.c`：函数语义 + 注解 + 循环不变式
2. `coins_XX.v`：桥接定义/引理
3. `C_XX_goal.v`：当前待证 witness
4. `QCP_examples/humaneval/spec/XX.v`：原始规格定义

补充说明：旧文档里提到的 `Coins/spec/human/input/XX.v` 已经过期。当前 HumanEval 题目的规格文件实际位于 `QCP_examples/humaneval/spec/` 下，`coins_XX.v` 也统一通过 `Load "../spec/XX".` 引入。

### Step 2: 先判定“能证明”还是“信息不足”

如果目标缺关键信息，不要硬证，先补注解/桥接后重生成。

### Step 3: 注解与桥接最小化修改

硬规则：

1. 不改 C 程序语句逻辑（除非用户明确允许）
2. 优先复用 `spec/XX.v` 已有定义
3. 只补本题必须的局部引理，不做大而泛的引理库

### Step 4: 每次修改后强制重生成（关键门禁）

改了 `C_XX.c` 注解或 `coins_XX.v` 后，必须重跑 symexec，刷新：

- `C_XX_goal.v`
- `C_XX_auto.v`
- `C_XX_manual.v`
- `C_XX_goal_check.v`

禁止继续证明旧 goal（最常见返工原因）。

### Step 5: 按 witness 顺序补 `C_XX_manual.v`

推荐顺序：

1. `unfold ...; intros; Intros; entailer!`
2. 用已有规格引理
3. 再补最小桥接

### Step 6: 全链编译验收

注意：必须在 `IntClaude` 目录下执行，否则 `coins_XX.v` 的相对 `Load` 路径可能失败。

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
COQINCLUDES="$(tr '\n' ' ' < _CoqProject)"
coqc $COQINCLUDES coins_XX.v
coqc $COQINCLUDES C_XX_goal.v
coqc $COQINCLUDES C_XX_auto.v
coqc $COQINCLUDES C_XX_manual.v
coqc $COQINCLUDES C_XX_goal_check.v
```

补充说明：

- 当前 `IntClaude` 目录的 `symexec` 生成文件默认与 `_CoqProject` 中的 `SimpleC.EE` 逻辑路径对齐。
- 不要在编译命令里额外追加 `-R . SimpleC.EE.humaneval`；这会导致一部分题目的 generated `.v` 文件 import 路径和编译环境不一致。
- 如果某题曾被人工改成 `SimpleC.EE.humaneval` 前缀，需先恢复到 `symexec` 默认风格后再验收。
- 普通 `symexec` 在 `manual.v` 已存在时通常不会覆盖该文件；若 `goal/auto/goal_check` 已更新而 `manual.v` 仍保留旧路径前缀，编译会卡在 `manual.v` 的 import。
- 若确需让 `symexec` 连同 `manual.v` 一起重生成，可使用 `--gen-and-backup`；旧 manual 会被备份成 `C_XX_manual_backup*.v`。

### Step 7: 无残留检查

```bash
grep -nE "Admitted\\.|Axiom[[:space:]]" coins_XX.v C_XX_manual.v || true
```

### Step 8: 清理编译产物

在确认编译链通过且无 `Admitted` / `Axiom` 之后，删除本题编译产生的中间文件，例如：

- `.aux`
- 隐藏 `.aux`（例如 `.C_XX_auto.aux`、`.coins_XX.aux`）
- `.glob`
- `.vo`
- `.vok`
- `.vos`

不要删除源码和证明源文件。必须保留：

- `C_XX.c`
- `coins_XX.v`
- `C_XX_goal.v`
- `C_XX_auto.v`
- `C_XX_manual.v`
- `C_XX_goal_check.v`

---

## 4. 常见失败分流（先定位再修）

### A. `entailer!` 后安全性推不出来

现象：比如需要证明乘法不溢出，但前提不够。

处理：

1. 强化循环不变式里的边界信息
2. 明确状态变量之间的逻辑关系
3. 重跑 symexec

### B. `has |-> 1` 与 `has |-> 0` 一类状态冲突

现象：分支后堆栈状态不一致。

处理：

1. 建立统一状态抽象函数（例：`digits_state_z`）
2. odd/even 分支分别补“状态保持”引理
3. 重跑 symexec

### C. `Z.rem`/`Z.quot` 与 `mod`/`div` 对不上

处理：

1. 补局部桥接引理（前提写清：非负、分母正）
2. 在引理内做改写，不要在主证明里到处重复

### D. 改了很多证明却突然全红

高概率是 stale goal（目标文件过期）。

处理：回到 Step 4，先重生成再继续。

---

## 5. 可复用证明模板

### 5.1 通用骨架

```coq
Lemma proof_of_xxx : xxx.
Proof.
  unfold xxx.
  intros.
  Intros.
  entailer!.
  (* 纯 Coq 子目标在这里处理 *)
Qed.
```

### 5.2 `safety_wit` 常用套路

1. 先拿到范围事实：`Z.mod_pos_bound`、`Z.mod_nonneg`，若目标里 `%` 实际落成 `Z.rem`，则改用 `Z.rem_bound_pos`、`Z.rem_mod_nonneg`
2. 再用 `nia`/`lia` 收束
3. 含 `Z.pow` 时先 `pose proof` 中间结论

### 5.3 `entail_wit` 常用套路

1. 先改写状态等式（分支保持引理）
2. 再把新目标还原到已有前提
3. 最后 `exact` 或 `assumption`

### 5.4 `return_wit` 常用套路

1. 先 `assert` 终止条件（如 `n=0`）并 `subst`
2. 展开状态抽象
3. 用规格定义或桥接引理收敛

---

## 6. 已验证样例可复用经验

### 6.1 `C_131`（digits）

可复用要点：

1. 把循环状态建模成统一抽象，不要散落在多个表达式里
2. 在不变式中显式写关键蕴含关系（如 `has == 0 -> prod == 1`）
3. odd/even 分支各写保持引理
4. rem/quot 桥接要小而准

结论：`return_wit` 卡住时，优先怀疑“状态语义没入不变式”，不是 tactic 弱。

### 6.2 `C_49`（modp）

可复用要点：

1. 注解先保证溢出边界（例如把前提强化为 `p * 2 <= INT_MAX`）
2. 对 `out = 2^i % p` 先拆出 `0 <= out < p`
3. `lia` 吃不动复合项时，先建中间事实再 `nia`

### 6.3 `C_150`（prime check / x_or_y）

可复用要点：

1. 如果循环条件写成 `i * i <= n`，先检查 C 层是否会因为 `int` 乘法触发 safety obligation；必要时改成等价但更安全的 `i <= n / i`
2. 对“素数判定”这类循环，不变式不能只记“暂未发现因子”，还要记“已经发现因子时的见证存在性”
3. `return_wit` 往往需要两套桥接：
   - `i > n / i` 推出 `n < i * i`
   - `存在小因子` 推出 `~ prime n`
4. `coins_XX.v` 里补素数辅助引理通常比在 `manual.v` 里硬推更稳

### 6.4 当前统一结论

1. `IntClaude` 目录下现有 20 题已经全部验证完成
2. 编译验收统一使用 `_CoqProject` 展开的 `COQINCLUDES`
3. 不要在编译命令里额外加 `-R . SimpleC.EE.humaneval`
4. 完成后要清理：
   - `.vo/.vos/.vok/.glob/.aux`
   - 隐藏 `.aux`
   - 多余 `manual backup`

### 6.3 `C_41`、`C_53`、`C_60`、`C_97`

可复用要点：

1. 许多 `safety_wit` 只需 `entailer!`
2. `return_wit` 常见是展开 spec + nat/Z 改写
3. 常用基础引理：`Z2Nat.inj_mul`、`Z.abs_nonneg`、`Z.mul_nonneg_nonneg`

### 6.4 `C_59`（largest_prime_factor）

可复用要点：

1. `manual` 清零后，还要继续检查 `coins_XX.v` 是否残留 `Admitted.`
2. 退出条件 `i > n / i` 可以先转成 `n < i * i`，便于与素因子界组合
3. 证明 `n` 为素数可走反证：若 `~prime n`，先取小素因子，再与不变式冲突
4. 对大于等于 `i` 的素因子，直接复用 while 退出后的保留性条件

### 6.5 `C_75`（is_multiply_prime）

可复用要点：

1. 先确认问题是在注解还是在手写证明，不要因为 `manual.v` 编译失败就立刻怀疑 invariant。
2. 这题当前注解经过重新 `symexec` 后是稳定的，核心不变式可围绕 `mp_outer_inv` 建模，不需要额外改 C 语句。
3. 重生成后 `C_75_manual.v` 会被还原成骨架，旧证明需要按最新 goal 重新迁回，不能直接假设旧 proof 还能对上。
4. `return_wit` 里若已经拿到了 `prime p1 /\ prime p2 /\ prime p3 /\ a = ...` 这类目标，避免无脑 `repeat split`，否则容易把 `prime` 原子命题错误继续拆开。

---

## 7. 剩余题目建议顺序

按成本从低到高：

1. `C_76`
2. `C_39`
3. `C_31`
4. `C_150`
5. `C_77`
6. `C_36`

每完成一题都做 Step 6 和 Step 7，再进入下一题。

---

## 8. 禁止事项

1. 不在旧 `C_XX_goal.v` 上继续证明
2. 不用 `Axiom` 走捷径
3. 未确认前不改 C 程序语句
4. 不把 `coins_XX.v` 扩展成不必要的大引理仓库

---

## 9. 每题交付格式（建议固定）

1. 改动文件与原因
2. 全链编译结果
3. `Admitted/Axiom` 扫描结果
4. 若未完成：卡点类别 + 最小下一步动作
