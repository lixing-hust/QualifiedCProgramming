# Assertion Experience

本文件只记录 `annotated/verify_<timestamp>_<name>.c` 中 `Assert` / `which implies` / bridge assertion 的经验。

不记录：

- 循环 invariant 的整体设计（见 `INV.md`）
- symbolic 执行流程（见 `SYMEXEC.md`）
- manual proof（见 `PROOF.md`）


## 1. `Assert` 用来做阶段切换，不用来补救坏 invariant

`Assert` 最适合：

- 固定循环退出后的状态
- 调用子过程前整理资源
- 在高层语义和局部表示之间做桥接

如果你发现自己要靠很多 `Assert` 才能继续，优先回去改 invariant。

## 2. `which implies` 只做必要桥接

`which implies` 应该只承担：

- 当前证明工具需要的那一步显式过渡
- 从较强的局部信息过渡到下一条语句刚好可消费的形式

不要把大量推理都塞进 `which implies`。

## 3. bridge assertion 要贴着下一条语句写

桥接断言应直接服务于下一步：

- 下一条是数组读写，就桥到对应 segment/full 形状
- 下一条是结构字段读写，就桥到对应展开层级
- 下一条是函数调用，就桥到被调函数前置条件

不要提前写很远之后才用到的 assertion。

## 4. 循环退出后通常需要一个显式退出断言

常见用途：

- 固定 `i == n`
- 固定 `j + 1 == bound`
- 把“未进入下一轮”转成后置条件所需边界

很多 `return_wit` 卡住，本质是少了一条退出后的 `Assert`。

但要注意：

- 退出断言必须贴着真正的循环退出点写
- 不要把它放到函数即将返回、局部变量准备销毁的位置去强行替换状态

典型错误现象：

- `Fail to Remove Memory Permission of i`

这通常不是“退出条件不对”，而是断言放得太晚，破坏了局部变量清理流程。

更稳的处理方法：

- 优先依赖循环 invariant 自然导出的退出状态
- 只有确实需要固定纯条件时，才补最小的 loop-exit assertion
- 如果加了退出断言反而让 `symexec` 卡在 local permission，先删掉它再重跑

## 5. 参数不变关系常常要显式桥出来

如果后面需要从当前状态回到 `@pre` 版本，通常要在注释里显式保留：

- `a == a@pre`
- `out == out@pre`
- `n == n@pre`

不要指望这些关系总能自动恢复出来。

## 6. `which implies` 不要承担“大段证明”

如果你发现 `which implies` 里需要表达很多层：

- 结构重组
- 多个纯命题联立
- 前后缀语义重建

通常说明问题不在 `which implies`，而在于：

- invariant 太弱
- 上一个 `Assert` 位置不对
- 抽象谓词展开层次不对

处理顺序应该是：

1. 先减小 `which implies` 负担
2. 回去补 invariant 或调整 bridge assert
3. 再重新 `symexec`
