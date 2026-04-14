# Annotate Details

本文件只记录 annotate 阶段的细节指导。

阶段职责、输入输出边界、强制规则、完成标准，以 [skills/annotate/SKILL.md](/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/skills/annotate/SKILL.md) 为准；这里不重复这些总规则，只补充具体写法和判断细节。

## 阅读方式

本文件同时承担两件事：

- annotate 阶段的文档阅读指南
- annotate 阶段可直接复用的通用经验

使用方式：

- 开始 annotate 任务时，先从本文件开头顺序读
- 先看 workspace 约定和规格接入方式
- 再看后面的通用规格设计经验

不要把“阅读指南”和“经验”分开理解；后面的经验就是前面规则的具体化。

## Workspace 记录位置

annotate 阶段的经验记录统一放在：

- `output/annotate_<timestamp>_<name>/raw/<name>.md`
- `output/annotate_<timestamp>_<name>/input/`
- `output/annotate_<timestamp>_<name>/logs/reasoning.md`
- `output/annotate_<timestamp>_<name>/logs/issues.md`
- `output/annotate_<timestamp>_<name>/logs/metrics.md`

使用约定：
- `raw/` 保存本次 annotate 使用的原始 markdown 输入快照
- `input/` 保存本次 annotate 产出的 `input/<name>.c` 和可选 `input/<name>.v` 的 workspace 内快照
- `logs/reasoning.md` 记录规格设计前的自然语言思考过程
- `logs/issues.md` 记录 annotate 阶段的踩坑、失败尝试、边界判断和最终取舍
- `logs/metrics.md` 记录 annotate 阶段各步骤的开始时间、结束时间和耗时
- 仓库根下的 `input/<name>.c` 和可选 `input/<name>.v` 仍然是 annotate 的正式产物；workspace 里的 `input/` 是对应快照
- annotate 和 verify 现在使用不同目录；annotate 目录只负责输入准备，不再与 verify 共用同一个 workspace

## Coq 数学语义如何接进 C 规格

把 Coq 里的数学函数或题目语义接进 `input/<name>.c`，常用两种方式。

### 方式一：直接 `Extern Coq`

适用场景：
- 仓库公共库里已经有现成的 Coq 数学函数
- C 规格只需要直接引用这个函数
- 不需要额外包装成题目专用 `pre/spec`

典型写法：

```c
/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
```

使用原则：
- 优先先查仓库里是否已经有可复用的 Coq 名字
- 如果公共定义已经足够表达题意，就不要再额外创建 `input/<name>.v`
- 这种情况下，`input/<name>.v` 应留空或根本不创建

### 方式二：题目专用 `.v` 桥接

适用场景：
- 题目语义不是一个现成公共函数就能表达
- 需要把自然语言题意包装成稳定的 `pre/spec`
- 需要额外定义辅助关系、辅助谓词或题目专用逻辑名

典型写法分两部分。

`input/<name>.c` 中：

```c
/*@ Extern Coq (factorial: Z -> Z)
               (bfact_coq: Z -> Z) */
/*@ Extern Coq (problem_139_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_139_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_139 */
```

然后在规格里直接用：

```c
/*@ Require
      problem_139_pre_z(n) &&
      1 <= n && n <= 10 && emp
    Ensure
      problem_139_spec_z(n@pre, __return) && emp
*/
```

对应的 `coins_139.v` 中再做桥接：

```coq
Definition problem_139_pre_z (n : Z) : Prop := ...
Definition problem_139_spec_z (n r : Z) : Prop := ...
```

使用原则：
- `.v` 只负责桥接和补题目专用逻辑，不要把本该直接写在 C 规格里的简单内容都搬进去
- 如果只是缺一个公共数学函数名，不要为了形式统一强行新建 `.v`
- 只有当 C 规格明显需要题目专用语义层时，才创建 `input/<name>.v`

### 选择规则

- 公共数学函数已存在：优先用“直接 `Extern Coq`”
- 题目需要专用 `pre/spec` 包装：使用“题目专用 `.v` 桥接”
- 能不用 `.v` 就不用 `.v`；只有确实缺桥接层时才新建

## 通用规格设计经验

### 先定数学语义，再定前后条件

更稳的 annotate 顺序是：

1. 先写清楚函数的数学语义
2. 再决定前置条件需要限制什么
3. 再决定是否需要高层/低层两层规格
4. 最后才把这些落成 `Require` / `Ensure` / `With`

如果数学语义本身没说清楚，后面的 contract 往往会反复返工。

### 前置条件优先约束最终结果，而不是穷举中间状态

对单调累加、乘法递推、前缀构造这类题，前置条件优先约束“最终不会溢出”，通常比逐项约束中间状态更短、更稳。

例如：

- `factorial` 用 `0 <= n <= 10`
- `sum` / `sum2` 这类题优先约束最终闭式值在 `int` 范围内

如果中间状态天然单调且不超过最终状态，这种写法通常足够支撑 Verify 阶段的 safety witness。

### 有抽象语义和具体表示时，优先分两层规格

如果一个题同时存在：

- 对外更自然的抽象语义
- 对实现更自然的具体表示

就优先分成高层语义规格和低层表示规格，不要一开始把两种职责揉在一个谓词里。

这样做的好处是：

- Annotate 产出的 contract 对用户更稳定
- Verify 只需要在局部展开实现真正会用到的表示
- 高层语义不会被底层指针或局部更新污染

### 能用 shape-only 时，不要强行把值语义写满

如果题目当前阶段真正需要的是：

- 内存安全
- 结构保持
- 局部可写性

而不是精确内容等价，那么 contract 应优先考虑 shape-only 谓词，不要在 Annotate 阶段把值语义写得过满。

这能显著减少 Verify 阶段的 invariant 和 proof 负担。

### 缺 `.v` 的判断标准

判断是否需要 `input/<name>.v`，优先问：

1. 现有公共 Coq 定义能否直接表达题意？
2. 是否真的需要题目专用 `pre/spec` 包装？
3. 是否需要额外的辅助关系或中间语义层？

只有这几个问题里至少一个必须回答“是”，才创建题目专用 `.v`。

参考：
- `factorial` 这类简单整数语义，适合直接 `Extern Coq`
- `/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/C_139.c`
- `/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/IntClaude/coins_139.v`
