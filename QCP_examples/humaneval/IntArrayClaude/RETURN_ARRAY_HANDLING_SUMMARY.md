# IntArrayClaude 返回数组三种处理方式总结

更新时间：2026-04-15

本文总结 [QCP_examples/humaneval/IntArrayClaude/C_5.c](QCP_examples/humaneval/IntArrayClaude/C_5.c)、[QCP_examples/humaneval/IntArrayClaude/C_8.c](QCP_examples/humaneval/IntArrayClaude/C_8.c)、[QCP_examples/humaneval/IntArrayClaude/C_25.c](QCP_examples/humaneval/IntArrayClaude/C_25.c) 里三种不同的“返回数组”处理方式，并给出验证视角下的差异和选型建议。

## 1. 方式一：调用方传入输出缓冲区（预分配）

代表题目： [QCP_examples/humaneval/IntArrayClaude/C_5.c](QCP_examples/humaneval/IntArrayClaude/C_5.c)

### 核心接口形态

- 函数参数包含 `out` 和 `out_size`
- 函数本体不做内存分配
- 返回值通常直接返回 `out`（便于链式调用和统一接口）

### 规格建模重点

- 前置条件给出输出缓冲区所有权：`IntArray::undef_full(out, out_size)`
- 前置条件必须给足容量约束（如 `out_size` 与输入规模的关系）
- 后置条件把输出缓冲区升级为已定义内容：`IntArray::full(out, out_size, output_l)`

### 优点

- 不需要证明 malloc 分配流程，验证负担较轻
- 内存责任边界清晰：调用方负责分配，函数负责填充
- 适合输出长度可提前由输入确定的场景

### 难点/风险

- 很依赖前置条件的容量公式是否正确
- 若容量关系写错，容易出现越界风险或规格与实现不一致
- 循环不变式通常需要维护“已写前缀 + 未写后缀”

## 2. 方式二：函数内部申请数组并返回数组指针

代表题目： [QCP_examples/humaneval/IntArrayClaude/C_8.c](QCP_examples/humaneval/IntArrayClaude/C_8.c)

### 核心接口形态

- 函数内部调用 `malloc_int_array(size)` 分配输出数组
- 返回类型是 `int *`
- 输出长度通常是常量或可直接计算（本题为长度 2）

### 规格建模重点

- 依赖 `malloc_int_array` 的规格：返回非空 + `IntArray::undef_full(__return, size)`
- 函数内先拿到 `undef_full(out, size)`，写入后在后置条件中给出 `IntArray::full(__return, size, output_l)`
- 同时保持输入数组不变：`IntArray::full(numbers, numbers_size, lv)`

### 优点

- 接口简洁，调用方只接收结果指针
- 对固定长度输出尤其自然
- 输出所有权完整地通过返回值交给调用方

### 难点/风险

- 需要显式建模分配函数规格
- 若未来改为可变长度输出，通常还需要额外返回长度信息，否则调用方不易安全使用

## 3. 方式三：函数内部申请数组，并返回“地址+长度”结构体

代表题目： [QCP_examples/humaneval/IntArrayClaude/C_25.c](QCP_examples/humaneval/IntArrayClaude/C_25.c)

### 核心接口形态

- 返回值是结构体指针（例如 `IntArray*`）
- 结构体中含 `data` 和 `size`
- 函数内部通常需要两次分配：
  - 分配结构体本身
  - 分配结构体里的数据数组

### 规格建模重点

- 除数组谓词外，还要建模结构体字段资源：
  - `data_at(&(__return -> data), data)`
  - `data_at(&(__return -> size), output_size)`
- 输出内容与长度关系需要同时表达：
  - `output_size == Zlength(output_l)`
- 当输出长度在运行时逐步增长时，常见写法是：
  - `IntArray::seg(data, 0, output_size, output_l)`
  - `IntArray::undef_seg(data, output_size, capacity)`

### 优点

- 接口信息最完整，调用方可直接获得数组地址和长度
- 适合输出长度动态决定、且长度不易由输入直接固定推导的场景

### 难点/风险

- 验证复杂度最高：要同时处理结构体字段和数组资源
- 需要维护字段一致性（`size` 与实际写入内容长度一致）
- 内存管理责任更重，后续释放策略也更关键

## 4. 三种方式并列对比

### 接口与责任

- 方式一（C_5）：调用方分配，函数填充
- 方式二（C_8）：函数分配数组，调用方接收指针
- 方式三（C_25）：函数分配结构体和数组，调用方接收“指针+长度”

### 规格复杂度

- 方式一：中等（容量约束 + 前后缀写入不变式）
- 方式二：中等偏低（主要是 malloc 规格和固定长度输出）
- 方式三：最高（结构体字段 + 动态长度 + 分段数组资源）

### 适用场景建议

- 输出长度已知且调用方可控：优先方式一
- 输出长度固定且希望接口简洁：优先方式二
- 输出长度动态变化且需要对外暴露长度：优先方式三

## 5. 验证实践建议

1. 先确定“谁负责分配、谁负责释放”，再写前后条件。
2. 若函数不分配内存，前置条件必须明确给足输出容量。
3. 若函数内部分配，先保证分配函数规格稳定可复用，再展开业务证明。
4. 只要输出长度是动态的，优先在后置条件显式绑定 `size == Zlength(output_l)`。
5. 对增量写入场景，循环不变式优先采用 `seg + undef_seg` 的已写/未写分割。
