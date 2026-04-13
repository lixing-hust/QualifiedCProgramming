# Annotate: 生成验证输入

Annotate 的目标是把原始题目材料转换成 Verify 可直接消费的正式输入。

## 输入材料

可以使用：
- 原始 C / C++ 代码
- 自然语言题意
- 题目约束和示例
- 必要的领域知识

## 输出产物

Annotate 的正式输出只有：
- `input/<name>.c`
- `input/<name>.v`，如果确实需要

## 你必须完成的事

- 把原始代码改成验证友好的 C
- 写完整的 `Require` / `Ensure` / 必要的 `With`
- 让规格与自然语言题意一致
- 补足边界条件、长度约束、别名约束、空指针约束、溢出前提等
- 只在确实需要时生成 `input/<name>.v`

## 你不需要完成的事

- 不补 `Assert`
- 不补 `Inv`
- 不跑 symbolic
- 不写 Coq manual proof

这些都属于 Verify。
