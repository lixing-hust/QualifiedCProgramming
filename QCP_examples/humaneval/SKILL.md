---
name: humaneval-c-verification-zh-compact
description: "中文精简流程：用于 humaneval/IntClaude 下 C_XX 验证，覆盖不变式重建、symexec 重生成、manual 证明补全、无 Admitted 或 Axiom、goal_check 编译通过。"
---

# HumanEval C 验证技能（中文精简版）

适用场景：验证 `QCP_examples/humaneval/IntClaude` 下的 `C_XX.c` 任务，完成从注解到 Coq 证明的全流程闭环。

## 目标

- 通过符号执行与 Coq 编译链。
- `C_XX_manual.v`（以及手写桥接文件）中无 `Admitted.`、无 `Axiom`。
- `C_XX_goal_check.v` 编译成功。

## 强约束

1. 未经用户确认，不修改 C 程序语句，只改注解和证明文件。
2. 优先复用题目规格文件已有定义，少造新谓词和大引理。
3. 每次改注解或桥接逻辑后，必须重新 symexec 生成 goal 文件。
4. 证明失败先回查信息是否不足，避免盲目堆引理。

## 七步流程

### 1) 约束确认

- 确认目标文件 `C_XX.c`。
- 确认允许改动范围：仅注解 / 注解+coins / 允许改 C 语句。
- 确认用户偏好：是否禁止复用旧不变式，是否要求最小新增引理。

### 2) 基线阅读

- 读取：`C_XX.c`、`coins_XX.v`、`Coins/spec/human/input/XX.v`、现有 `C_XX_goal.v` 和 `C_XX_manual.v`。
- 判断问题类型：
  - 不变式信息不足
  - rem/mod/div 或 nat/Z 桥接不足
  - 规格映射不一致
  - 目标文件过期（stale goal）

### 3) 重建不变式与桥接

- 在 C 注解里建立最小状态模型，保证：
  - 安全边界可证
  - 循环状态能映射到规格
  - 关键蕴含关系明确（如 `has==0 -> prod==1`）
- 在 `coins_XX.v` 只补必要桥接引理（局部、可解释、可维护）。

### 4) 强制重生成

改动后立即重新 symexec，更新：

- `C_XX_goal.v`
- `C_XX_auto.v`
- `C_XX_manual.v`
- `C_XX_goal_check.v`

禁止在旧 goal 上继续证明。

### 5) manual 逐项证明

- 按 witness 顺序补证明。
- 单个 witness 连续卡住时，按顺序回查：
  - goal 是否过期
  - 不变式是否缺信息
  - 是否缺最小桥接引理

### 6) 全链编译验收

依次编译：

1. `coins_XX.v`
2. `C_XX_goal.v`
3. `C_XX_auto.v`
4. `C_XX_manual.v`
5. `C_XX_goal_check.v`

可接受 load-path remap warning，但必须整体编译通过。

### 7) 收尾与交付

- 检查无 `Admitted.`/`Axiom`：
  - `grep -nE "Admitted\\.|Axiom[[:space:]]" coins_XX.v C_XX_manual.v || true`
- 按需清理本题临时产物（如 `.aux`），不删除生成的 goal/auto/manual/check 文件。
- 汇报：改了什么、为什么、编译结果、扫描结果、剩余风险。

## 标准命令模板

在 `QCP_examples/humaneval/IntClaude` 目录执行：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
COQINCLUDES="$(tr '\n' ' ' < _CoqProject)"
coqc $COQINCLUDES -R . SimpleC.EE.humaneval coins_XX.v
coqc $COQINCLUDES -R . SimpleC.EE.humaneval C_XX_goal.v
coqc $COQINCLUDES -R . SimpleC.EE.humaneval C_XX_auto.v
coqc $COQINCLUDES -R . SimpleC.EE.humaneval C_XX_manual.v
coqc $COQINCLUDES -R . SimpleC.EE.humaneval C_XX_goal_check.v
```

## 完成判定

同时满足以下三条才算完成：

1. `C_XX_goal_check.v` 编译通过。
2. 手写证明文件无 `Admitted.`。
3. 手写证明文件无 `Axiom`。
