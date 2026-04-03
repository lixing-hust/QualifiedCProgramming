# Copilot 接手指南：IntClaude Coq 证明补全

## 项目概述

这是一个使用 QCP（Qualified C Programming）对 HumanEval C 程序进行形式化验证的项目。
目标：补全 `IntClaude/` 目录下所有 `_manual.v` 文件中的 Coq 证明（替换所有 `Admitted`）。

---

## 工作目录

```
/home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/
```

---

## 环境配置

**Coq 版本**：8.20.1（opam switch `coq8201`）

**编译单个文件的命令**：
```bash
eval $(opam env --switch=coq8201 --set-switch)
cd /home/lixing/projects/QualifiedCProgramming/QCP_examples/humaneval/IntClaude
COQINCLUDES=$(cat _CoqProject | tr '\n' ' ')

# 先编译依赖（如果 .vo 文件不存在）
coqc $COQINCLUDES coins_XX.v
coqc $COQINCLUDES C_XX_goal.v
coqc $COQINCLUDES C_XX_manual.v   # 最后编译这个
```

**MCP 工具**（可选，配置在 `.mcp.json`）：
- `qcp-mcp`：运行符号执行，生成 goal/auto/manual 文件
- `rocq-mcp`：交互式 Coq 证明助手（`rocq_step`、`rocq_compile`、`rocq_auto_solve`）

---

## 当前状态

### 已完成（0 个 Admitted）
| 文件 | 说明 |
|------|------|
| `C_53_manual.v` | add 函数，`entailer!` 即可 |
| `C_41_manual.v` | car_race_collision，用了 `Z2Nat.inj_mul` |
| `C_97_manual.v` | multiply，用了 `Z.abs_nonneg`、`Z.mod_pos_bound`、`Z.mul_nonneg_nonneg` |
| `C_49_manual.v` | modp（2^n mod p），见下节 |
| `C_60_manual.v` | sum_to_n，已验证完成 |
| `C_138_manual.v` | 已验证完成 |
| `C_24_manual.v` | 已验证完成 |

### 待完成（按 Admitted 数量从少到多）
| 文件 | Admitted 数 | 备注 |
|------|-------------|------|
| `C_131_manual.v` | 4 | **当前卡点：疑似注解/目标不充分** |
| `C_59_manual.v` | 4 | |
| `C_83_manual.v` | 4 | |
| `C_102_manual.v` | 5 | |
| `C_139_manual.v` | 5 | |
| `C_13_manual.v` | 5 | |
| `C_75_manual.v` | 5 | |
| `C_76_manual.v` | 5 | |
| `C_39_manual.v` | 6 | |
| `C_31_manual.v` | 7 | |
| `C_150_manual.v` | 8 | |
| `C_77_manual.v` | 11 | |
| `C_36_manual.v` | 13 | |

---

## C_49 的特殊说明

**问题**：原 C 代码的循环中 `out * 2` 可能溢出（当 `p` 较大时）。

**已做的修改**：将 `C_49.c` 中的 QCP 注解（Require 条件）从 `p <= INT_MAX` 改为 `p * 2 <= INT_MAX`，并重新运行了 symexec，生成了新的 `C_49_goal.v`。

**边界说明**：这里修改的是注解，不是 C 程序逻辑；验证时不应修改原始 C 程序语句。

**待解决的问题**：`proof_of_modp_safety_wit_5` 的证明卡住了。

目标是证明：
```coq
Definition modp_safety_wit_5 :=
forall (p_pre n_pre out i: Z),
  [| out = 2^i % p_pre |] && [| 2 <= p_pre |] && [| p_pre * 2 <= INT_MAX |] && ...
|-- [| out * 2 <= INT_MAX |] && [| INT_MIN <= out * 2 |]
```

**已知事实**：
- `out = 2^i % p_pre`，所以 `0 <= out < p_pre`
- `p_pre * 2 <= INT_MAX`，所以 `out * 2 < p_pre * 2 <= INT_MAX`
- `INT_MAX = 2147483647`（这是 Notation，不是 Definition）

**已尝试但失败的策略**：
- `lia` / `nia` 在 `entailer!` 之后给出 "Cannot find witness"
- 原因：`lia` 无法处理含 `Z.pow` 和 `Z.modulo` 的复合项作为原子

**建议尝试的方向**：
```coq
Lemma proof_of_modp_safety_wit_5 : modp_safety_wit_5.
Proof.
  unfold modp_safety_wit_5.
  intros.
  Intros.
  entailer!.
  (* 此时 out 可能已被 entailer! 替换为 2^i % p_pre *)
  (* 尝试 1：直接使用 Z.mod_pos_bound + nlinarith *)
  pose proof (Z.mod_pos_bound (2^i) p_pre ltac:(lia)) as [Hmod_nn Hmod_lt].
  nlinarith [Z.mod_pos_bound (2^i) p_pre].
  (* 尝试 2：手动 assert 中间步骤 *)
  (* assert (H1 : 2^i % p_pre < p_pre) by (apply Z.mod_pos_bound; lia). *)
  (* assert (H2 : 0 <= 2^i % p_pre) by (apply Z.mod_nonneg; [apply Z.pow_nonneg; lia | lia]). *)
  (* split; [lia | lia]. *)
Qed.
```

---

## C_131 当前卡点（digits）

已重跑 symexec，当前 `C_131_manual.v` 仍有 4 个 `Admitted`：
- `proof_of_digits_safety_wit_12`
- `proof_of_digits_entail_wit_2_1`
- `proof_of_digits_entail_wit_2_2`
- `proof_of_digits_return_wit_1`

观察到的关键问题：
- `digits_safety_wit_12` 需要仅凭 `1 <= prod <= INT_MAX` 推出 `prod * (n % 10) <= INT_MAX`，约束不足。
- `digits_entail_wit_2_1` 的目标中出现 `has |-> 1` 推到 `has |-> 0`，与当前循环不变式未跟踪 `has` 的语义有关。
- `digits_return_wit_1` 需要证明 `problem_131_spec_z n_pre 0`，但现有不变式没有把 `has=0` 与“所有已处理位均为偶数”建立联系。

结论：
- 在不修改 C 程序逻辑的前提下，建议先增强注解（尤其是循环不变式中对 `has/prod/n` 与规格的关系）再重跑 symexec。
- 若只在当前 `goal.v` 上补 Coq proof，存在目标本身信息不足导致不可证的风险。

---

## 证明模式与常用策略

每个 `_manual.v` 文件中的 Lemma 证明都遵循以下模式：

```coq
Lemma proof_of_XXX_YYY_wit_Z : XXX_YYY_wit_Z.
Proof.
  unfold XXX_YYY_wit_Z.
  intros.
  Intros.           (* 从 separation logic 上下文提取纯命题到 Coq 上下文 *)
  entailer!.        (* 处理 separation logic 部分，剩余纯算术目标 *)
  (* 在此处补充证明 *)
Qed.
```

### witness 类型对应的证明策略

| witness 类型 | 含义 | 常用策略 |
|-------------|------|---------|
| `safety_wit` | 整数溢出/除零安全 | `entailer!`（简单）或 `entailer!; lia` |
| `entail_wit` | 循环不变式维持 | 通常需要 `subst` + 重写引理 |
| `return_wit` | 后置条件 | `entailer!; unfold spec; lia` 或 `subst; reflexivity` |

### 常用引理

```coq
(* 模运算范围 *)
Z.mod_pos_bound : forall a b, 0 < b -> 0 <= a mod b < b
Z.mod_nonneg    : forall a b, 0 <= a -> 0 < b -> 0 <= a mod b
Z.mod_1_l       : forall n, 1 < n -> 1 mod n = 1

(* 绝对值 *)
Z.abs_nonneg    : forall n, 0 <= |n|

(* 幂运算 *)
Z.pow_nonneg    : forall a n, 0 <= a -> 0 <= a ^ n
Z.pow_0_r       : forall a, a ^ 0 = 1
Z.pow_succ_r    : forall a n, 0 <= n -> a ^ (n+1) = a * a^n

(* 乘法 *)
Z.mul_nonneg_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= a * b
Z2Nat.inj_mul       : forall n m, 0 <= n -> 0 <= m -> Z.to_nat (n*m) = ...
Z.mul_mod_idemp_l   : 用于化简 (a mod n) * b mod n

(* 整除 *)
Z.div_pos   : ...
```

### 示例：已完成的证明

**最简单（entailer! 即解决）**：
```coq
(* C_41: n^2 >= 0 这类 safety_wit *)
Lemma proof_of_car_race_collision_safety_wit_1 : car_race_collision_safety_wit_1.
Proof.
  unfold car_race_collision_safety_wit_1.
  intros. Intros. entailer!.
Qed.
```

**spec 展开类（return_wit）**：
```coq
(* C_53: 直接验证规格 *)
Lemma proof_of_add_return_wit_1 : add_return_wit_1.
Proof.
  unfold add_return_wit_1. intros. Intros.
  unfold problem_53_spec. entailer!.
Qed.
```

**需要数学引理的 return_wit**：
```coq
(* C_41: Z.to_nat (n*n) = Z.to_nat n * Z.to_nat n *)
Lemma proof_of_car_race_collision_return_wit_1 : car_race_collision_return_wit_1.
Proof.
  unfold car_race_collision_return_wit_1. intros. Intros. entailer!.
  unfold problem_41_spec_z, problem_41_spec.
  rewrite Z2Nat.inj_mul by lia. lia.
Qed.
```

**循环不变式维持（entail_wit）**：
```coq
(* C_49: out*2 mod p = 2^(i+1) mod p *)
Lemma proof_of_modp_entail_wit_2 : modp_entail_wit_2.
Proof.
  unfold modp_entail_wit_2. intros. Intros. entailer!.
  subst.
  rewrite Z.pow_succ_r by lia.
  rewrite <- Z.mul_mod_idemp_l.
  ring_simplify. rewrite Z.mul_comm. reflexivity.
Qed.
```

---

## 完成标准（来自 SKILL.md）

验证完成的标准：
1. `C_XX_manual.v` 中没有 `Admitted`
2. `C_XX_goal_check.v` 能成功编译

编译 goal_check 文件：
```bash
eval $(opam env --switch=coq8201 --set-switch)
COQINCLUDES=$(cat _CoqProject | tr '\n' ' ')
coqc $COQINCLUDES coins_XX.v
coqc $COQINCLUDES C_XX_goal.v
coqc $COQINCLUDES C_XX_auto.v    # 如果 auto.v 有需要的引理
coqc $COQINCLUDES C_XX_manual.v
coqc $COQINCLUDES C_XX_goal_check.v
```

---

## 文件结构说明

每个程序 `C_XX` 对应以下文件：
- `C_XX.c` - 待验证的 C 程序（含 QCP 注释标注的规格和不变量）
- `coins_XX.v` - 加载问题规格（从 Coins 数据集）
- `C_XX_goal.v` - QCP 自动生成的待证明 Lemma 声明（**不要修改**）
- `C_XX_auto.v` - QCP 自动证明部分（**不要修改**）
- `C_XX_manual.v` - **需要补全的人工证明文件**
- `C_XX_goal_check.v` - 综合验证文件

---

## 工作流程建议

1. 从简单的程序开始（C_60 只有 2 个 Admitted）
2. 读 `C_XX.c` 了解函数功能
3. 读 `C_XX_goal.v` 了解每个 witness 的具体目标
4. 读 `coins_XX.v` 中加载的 spec 文件（在 `/home/lixing/projects/Coins/spec/human/input/XX.v`）
5. 在 `C_XX_manual.v` 中填写证明
6. 编译验证
7. 如果有无法证明的 witness，优先检查验证目标/注解是否合理；必要时可修改注解后重跑 symexec
8. 验证过程中不修改原始 C 程序逻辑（函数实现与语句保持不变）

---

## 注意事项

- `INT_MAX = 2147483647`（Notation，不是 Definition，不能 unfold）
- `INT_MIN = -2147483648`（同上）
- 验证时不可以修改原始 C 程序逻辑；若发现验证目标有问题，可以修改注解（如 Require/Ensure/Invariant）
- `lia` 有时无法处理含 `Z.pow`/`Z.modulo` 的复合项，需先用 `pose proof` 建立中间引理
- `entailer!` 之后，`[| P |]` 中的 P 才进入正常 Coq 上下文
- `Intros`（大写）是 QCP SL 框架的 tactic，不同于 Coq 标准 `intros`
- 禁止在证明中引入 `Axiom`（会被 `Print Assumptions` 检测）
