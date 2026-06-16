# Annotation 规则与资料入口

## 允许修改的内容

- 函数规格中的 `Require` / `Ensure`
- 证明所需的 `Assert`
- 循环中的 `Inv Assert`
- 调用相关的 `where` 子句

## 写 annotation 时的判断顺序

1. 先确认函数输入输出关系和所有权变化是否完整。
2. 再决定循环里真正需要暴露哪些“隐藏性质”：
   - 已处理前缀 / 后缀
   - 当前候选最优值
   - 尚未处理区间
   - 局部 shape / 已写前缀 / 未写后缀
3. 然后确认循环变量、数据结构形状、纯事实和边界条件是否都进入 invariant。
4. 最后确认断言是否足以支撑后续函数调用、分支或返回点。

## Array / String 先查 builtin 支持

遇见连续数组、字符数组、C 字符串或字符串字面量时，先读 `builtin-array-string-support.md`，再决定是否需要先在 `annotation_scratch_lib` 中新增 spec，并在通过 `annotation-checking` 后由主 agent 集成到 `common_case_formal_lib`。

- 普通数组资源优先使用 `IntArray` / `UIntArray` / `CharArray` / `PtrArray` 等 builtin 谓词。
- C 字符串缓冲区优先使用 `store_string(p, s)`，其中 `s : list Z` 不包含结尾 `0`。
- 字符串字面量优先使用 `store_stringLit(addr, s)` 和 `GlobalStrings(LitMap)`，其中 `s : string` 保留 Rocq 字面量。
- 不要在 `annotation_scratch_lib` / `common_case_formal_lib` 中重复定义和 builtin 等价的数组 / 字符串内存谓词；`annotation_scratch_lib` 只补充当前算法真正需要的数学性质，检查通过后才可由主 agent 回填到 `common_case_formal_lib`。

## `remove permission failed` 优先查局部资源回收

- 如果 QCP 在 `return`、函数结束或局部 scope 结束处报 `remove permission failed` / 局部变量内存回收失败，优先按 `qcp-resource-reclaim-errors.md` 排查 annotation 中漏掉的局部变量或局部数组 ownership。
- 用 `qcp-mcp` 检查失败点上一句的 symbolic state，确认当前 scope 内所有 live local store 和数组资源都还在 assertion 中。
- 对 `int a[2003]` 这类局部数组，`return` 前需要能看到完整数组资源，例如 `IntArray::undef_full(a, 2003)` 或 `IntArray::full(a, 2003, l)`；不要只留下不完整的分段资源。

## 先选性质，不先写算法

- 能用谓词描述的运行时性质，优先写成谓词，不要先在 Rocq 里重写一份算法。
- 允许的小定义，应当是“性质接口”或“局部观察”：
  - 例如 `subarray_sum`、`suffix_sum`、`prefix_sum`
  - 例如 `IntuitiveMaxSuffixSum`、`IntuitiveMaxSubArraySum`
- 不推荐的定义，是直接镜像 C 控制流的递归器 / 状态机：
  - 例如把 loop body 逐步搬成 `Fixpoint`，再让 invariant 追着这个 `Fixpoint` 跑
- refinement proof 中若 proof type 已要求 `safeExec` / monad，则保留它；但 direct-proof 风格的局部性质仍应尽量体现在 annotation 中，而不是全部留给 Rocq proof。

## Full Assertion / Refinement 常见错误

写完整 `Assert` / `Inv Assert` 时，优先检查以下四类问题：

- 是否缺少当前状态到 `@pre` 状态的桥接等式；
- 是否缺少“局部变量值 == 源数组/字段/解引用内容”的绑定；
- 是否误用了 `x == x`、`p == p`、`rx_rank == rx_rank` 这类恒真式；
- refinement case 中，是否把最终 functional correctness 谓词提前塞进了循环 invariant；这类谓词应只出现在 `high_level_spec` 中，除 `high_level_spec` 外，C 侧 annotation 不应重复证明 monad 已覆盖的功能语义。

详细案例见 `common-annotation-errors.md`。

## 先思考如何证明，再写循环不变量
- 写循环不变量之前，先用自然语言写出这个算法为什么正确；不要从 C 的每一行反推 invariant。
- 自然语言证明至少回答三件事：
  - 循环开始前，当前性质为什么成立。
  - 一次迭代后，哪些已处理部分、候选值、数据结构 shape 或边界事实被保持。
  - 哪些事实是符号执行推进所必需的，哪些可以留给后续 Rocq proof 或已有分离逻辑 lemma 推出。
- 再把证明骨架翻译成 invariant，只写支撑证明的关键性质：
  - 记录已处理 / 未处理区间、候选最优值、局部 shape、写入前缀等语义事实。
  - 保留循环变量范围、数组长度关系、指针可访问性、整数溢出边界等执行事实。
  - 不要把 loop body 逐句编码成一个镜像算法；优先写可被复用和证明的性质接口。
- 参考例子：`majorityElement.c`、`sortArray.c`。
- 有些性质可以由分离逻辑库推出；如果不影响符号执行，不必重复写进 annotation：
  - `store(&x, v)` 可推出 `v` 在 `x` 对应程序变量的类型范围内。See `SeparationLogic/SeparationLogic/StoreAux.v/valid_store_int`。
  - `IntArray::full(x, size, l)` 可推出 `0 <= size <= Int.max_unsigned / 4 + 1`。See `SeparationLogic/SeparationLogic/ArrayLibCore.v/seg_length_range`。
  - 把分离逻辑部分转化到 `store_align_n` 后，可推出部分数据的 range。See `SeparationLogic/SeparationLogic/StoreAux.v/store_align_n_valid`。

## 用 `by local` 导出局部类型事实

- 当 C 类型本身或当前局部 store 已经蕴含某个纯事实，但普通 `Assert` 的 entailment witness 没有把对应 store/range 暴露出来时，可以在值被 materialize 后紧跟一条轻量 annotation：
  ```c
  unsigned int __u = u;
  /*@ 0 <= u && u <= UINT_MAX by local */
  ```
- 这个写法适合把 `unsigned int` 参数或局部变量的范围导出到后续 VC，而不把这些实现层范围硬塞进函数 `Require` / `Ensure`。例如：
  ```c
  /*@ 0 <= u && u <= UINT_MAX by local */
  /*@ 0 <= v && v <= UINT_MAX by local */
  ```
  可以让后续 return witness 获得 `u@pre` / `v@pre` 的范围事实。
- 函数调用返回后，若局部变量由 callee 的 `store_uint` 结果写入，也可以马上导出范围：
  ```c
  gmp_umul_ppmm(&lpl, &hpl, ul, vl);
  /*@ 0 <= lpl && lpl <= UINT_MAX by local */
  /*@ 0 <= hpl && hpl <= UINT_MAX by local */
  ```
  这样后续 loop-step VC 可以使用这些 pure facts，而不必把 `w0_value` / `w1_value` 的范围加入 callee 的 `Ensure`。
- `by local` 只导出纯事实，不会替你保留非仿射空间资源。若后续 `Assert` 需要某个局部 store，仍要在 frame 中精确保留，例如 `store_uint(&ul, l[i])`；不要用额外的 `has_permission(&ul)` 叠加到已有 live local store 上，否则容易造成重复资源并触发后续 `Assign Exec fail`。

## 修复Annotation的时候不要频繁调用QCP
- 每次 QCP 失败后，先读错误位置前后的 symbolic state 和最近的 annotation；不要只改一行就立刻重跑。
- 修复前先归类错误原因，并批量检查同类位置：
  - 缺少纯事实：变量范围、下标关系、循环退出条件、整数边界。
  - 缺少 shape / ownership：数组段、结构体字段、已写前缀、未写后缀、别名关系。
  - 规格不匹配：函数 `Require` / `Ensure`、调用 `where`、返回值语义。
  - invariant 太弱或太强：弱到无法推进，或强到初始化 / 保持性不可证。
- 同一轮修复应尽量覆盖一组相关问题，再调用 QCP 验证；只有在无法判断下一步状态、或一组改动已经完成时才重新运行。
- 如果 QCP 报错只是暴露下游 VC 不可证，不要用临时 Assert 硬压过去；应回到自然语言证明，判断需要补 annotation、改规格，还是交给 VC checking。
- report 中记录本轮 QCP 失败原因、批量修复点、重新运行 QCP 的理由，以及仍可能影响后续 VC 的风险。

## 教程索引

- `tutorial/T1-representation-predicates.md`
- `tutorial/T2-pre-post-condition.md`
- `tutorial/T3-assertion-and-invariant.md`
- `tutorial/T4-symbolic-execution.md`
- `tutorial/T6-polymorphism.md`
- `tutorial/T8-function-call.md`

这些教程适合作为 annotation 语法、谓词表达方式和 symbolic execution 机制的背景资料。
