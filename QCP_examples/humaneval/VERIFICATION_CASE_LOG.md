# HumanEval 程序验证日志

用途：按程序记录验证过程，便于后续复盘、迁移经验和统计成本。

记录规范：
1. 每个程序一条记录。
2. 必填：状态、问题、解决方式、验收结果。
3. token 与时间若无法自动获取，先写未记录，后补。

自动化脚本：

---

- 状态: 已通过

3. 在 coins_59.v 中补完 lpf_spec_from_exit（去除 admitted），并验证全链可编译

- QCP_examples/humaneval/IntClaude/C_131.c
- QCP_examples/humaneval/IntClaude/coins_131.v

### 遇到的问题

1. 重建循环状态抽象，使用统一状态映射思路，并将状态语义纳入不变式。
3. 在 coins_59.v 中补完 lpf_spec_from_exit（去除 admitted），并验证全链可编译
3. 在 coins_131.v 中补最小必要桥接引理，避免扩展成大而泛的引理库。
4. 每次改注解或桥接后，重新 symexec 生成最新 goal/auto/manual/check。
5. 补全 C_131_manual.v 中全部待证项并做全链编译。
- Admitted 检查: 通过（无）
- Axiom 检查: 通过（无）
- 未通过原因: 无
- 开始时间: 未记录
- 结束时间: 未记录
- 总耗时: 未记录

### 可复用经验

1. 若 return_wit 卡住，优先检查状态语义是否真正进入循环不变式。
2. 证明失败先分流：目标过期、信息不足、桥接缺失，避免盲目加 tactic。
3. 保持桥接引理最小化，稳定性明显高于历史大引理集合复用。

---

## 记录模板（复制后填写）

- 例子编号:
- 程序文件:
- 记录日期:
- 状态: 已通过 / 未通过 / 进行中

### 变更范围

- 

### 遇到的问题

1. 

### 解决方式

1. 

### 验收结果

- 编译链通过: 是/否
- Admitted 检查: 通过/未通过
- Axiom 检查: 通过/未通过
- 未通过原因:

### 成本统计

- 输入 token:
- 输出 token:
- 总 token:
- 开始时间:
- 结束时间:
- 总耗时:

### 可复用经验

1. 

---

## 记录 002

- 例子编号: C_59
- 程序文件: QCP_examples/humaneval/IntClaude/C_59.c
- 记录日期: 2026-04-07
- 状态: 已通过

### 变更范围

- QCP_examples/humaneval/IntClaude/C_59.c
- QCP_examples/humaneval/IntClaude/coins_59.v
- QCP_examples/humaneval/IntClaude/C_59_auto.v
- QCP_examples/humaneval/IntClaude/C_59_manual.v
- QCP_examples/humaneval/IntClaude/C_59_goal_check.v

### 遇到的问题

1. safety_wit_6 仅靠原条件无法直接推出 i+1 上界
2. goal_check 缺失 VC 字段导致模块字段不全

### 解决方式

1. 在 lpf_while_inv 增加 i+1<=INT_MAX 约束并补齐 manual 证明
2. 补全 auto 中缺失的 VC 字段占位，保证 goal_check 可编译
3. 在 coins_59.v 中补完 lpf_spec_from_exit（去除 admitted），并验证全链可编译

### 验收结果

- 编译链通过: 通过（coins_59->C_59_goal->C_59_auto->C_59_manual->C_59_goal_check）
- Admitted 检查: coins_59 与 C_59_manual 通过（无）
- Axiom 检查: manual 通过（无）
- 未通过原因: 无

### 成本统计

- 输入 token: 未记录
- 输出 token: 未记录
- 总 token: 未记录
- 开始时间: 未记录
- 结束时间: 2026-04-07T00:11:30+08:00
- 总耗时: 未记录

### 可复用经验

1. 先让 goal_check 可编译，再做严格去 Admitted 收敛
2. 对 "i > n / i" 这类退出条件，先转为 "n < i*i"，再配合小素因子引理收敛 primality 证明
