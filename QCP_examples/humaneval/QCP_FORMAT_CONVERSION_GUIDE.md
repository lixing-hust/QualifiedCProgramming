# Humaneval C 程序改成 QCP 支持格式的指南

本文档只描述“格式转换阶段”要做什么。

目标是把原始 C 程序改成 QCP 工具链能继续接手的形态，但不在这个阶段补完整循环不变式、不做 manual VC 证明、不生成正式 goal/proof 文件。

后续真正开始验证时，再根据 symbolic execution 的错误和 manual VC 去补 loop invariant、辅助引理和证明。

## 1. 阶段边界

格式转换阶段应该做：

- 换成 QCP 支持的头文件。
- 把原始函数接口改成 QCP 易建模的接口。
- 给外部 malloc/free/helper 函数写最小 wrapper 规格。
- 给目标函数写前后条件骨架。
- 增加必要的 `coins_XX.v` 桥接定义。
- 保持原程序主体结构尽量不变。

格式转换阶段不应该做：

- 不写复杂 loop invariant。
- 不为了让完整 `symexec` 通过而提前堆很长的 `Inv Assert`。
- 不把中间变量暴露到主函数后条件里，除非它们确实返回给调用者或没有被释放。
- 不生成或修改 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`。
- 不新增证明用引理，除非只是为了让 bridge 文件本身能定义规格。

## 2. 参考风格

优先参考：

- `QCP_examples/LLM_friendly_cases`
- `QCP_examples/humaneval/IntArrayClaude/C_25.c`
- `QCP_examples/humaneval/IntArrayClaude/C_8.c`
- `QCP_examples/humaneval/IntArrayClaude/C_9.c`

这些例子的共同风格是：

- 函数规格短。
- loop invariant 只在真正验证时补。
- 参数如果没有被修改，优先直接用参数名。
- 需要入口值时，优先用 `x@pre`，不要轻易引入 `x0` 这类 ghost snapshot。

## 3. 头文件替换

原始 humaneval C 文件常见：

```c
#include <stdio.h>
#include <stdlib.h>
```

QCP 版本通常改成：

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
```

只在确实需要字符串、链表、结构体等专用定义时引入相应的 QCP 头文件。

不要保留普通 `stdlib.h` 并直接使用裸 `malloc/free`，除非这个项目中已有对应规格。

## 4. 纯规格桥接

先看 `QCP_examples/humaneval/spec/<id>.v`，确认题目的纯语义：

- 输入对应哪些 `list Z`、`Z`、`bool`
- 输出对应什么
- 是否已有 `problem_XX_pre`
- 是否已有 `problem_XX_spec`

在 C 文件头部写：

```c
/*@ Extern Coq (problem_XX_pre: ...)
               (problem_XX_spec: ...) */
/*@ Import Coq Require Import coins_XX */
```

如果 `spec/<id>.v` 的类型不方便直接用于 C 层，可以新增 `coins_XX.v` 做桥接。

桥接文件在格式转换阶段应该只包含：

- `Load "../spec/XX".`
- 必要的 `Require Import`
- 简单定义，例如 `list_contains`、`filter_not_in`、`loop_state` 谓词

不要在格式转换阶段批量生成引理。

## 5. 数组输入的前置条件

只读输入数组的最小模板：

```c
int f(int *numbers, int numbers_size)
/*@ With input_l
    Require
        0 <= numbers_size && numbers_size < INT_MAX &&
        problem_XX_pre(input_l) &&
        IntArray::full(numbers, numbers_size, input_l)
    Ensure
        ...
*/
```

一般不要额外写：

```c
Zlength(input_l) == numbers_size
```

如果已经有 `IntArray::full(numbers, numbers_size, input_l)`，这类长度信息通常由数组谓词承载。只有后续验证阶段工具确实需要时再补。

也不要默认写 `list_int_range(input_l)`。`IntArray::full` 已经是 C `int` 数组的内存谓词，通常不需要再手动加一层元素范围。只有程序里有额外算术溢出风险时，再添加针对具体表达式的安全前提。

## 6. 返回新数组或结构体

如果原程序返回：

```c
typedef struct {
    int *data;
    int size;
} IntArray;
```

QCP 中常用两种方式：

1. 如果已有案例支持结构体值返回，可以保持值返回。
2. 如果要模仿 `C_25.c`，可以改成返回 `IntArray *`，并用 wrapper 分配结构体。

`C_25.c` 风格：

```c
IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;
```

目标函数后条件只描述真正返回给调用者的资源：

```c
Ensure
    exists data output_l output_size,
    __return != 0 &&
    0 <= output_size && output_size <= numbers_size &&
    problem_XX_spec(input_l, output_l) &&
    data_at(&(__return -> data), data) *
    data_at(&(__return -> size), output_size) *
    IntArray::full(numbers, numbers_size, input_l) *
    IntArray::seg(data, 0, output_size, output_l) *
    IntArray::undef_seg(data, output_size, numbers_size)
```

注意：

- 不要把内部临时数组写进主后条件。
- 如果输出数组只写了前缀，后条件应保留 `undef_seg` 描述未写后缀。

## 7. malloc/free wrapper

如果原程序有临时数组：

```c
int *has1 = malloc(...);
int *has2 = malloc(...);
...
free(has1);
free(has2);
```

格式转换时不要直接使用裸 `malloc/free`。建议写 wrapper：

```c
int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

void free_int_array(int *array, int init_size, int size)
/*@ Require
        exists l,
        array != 0 &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure emp
*/;
```

然后保留原程序的释放行为：

```c
free_int_array(has1, has1_size, numbers_size);
free_int_array(has2, has2_size, numbers_size);
```

这样主函数后条件不需要出现 `has1/has2`。

如果不 free，separation logic 中 malloc 出来的堆资源不能凭空消失，后条件就必须把这些临时资源以 existential 形式暴露出来。为了保持规格清爽，优先恢复或保留 free。

## 8. helper 函数规格

原始程序中已有 helper，例如：

```c
static int contains(const int *a, int n, int x)
```

QCP 格式中可以改成：

```c
int contains(int *a, int n, int x)
/*@ With l
    Require
        0 <= n && n < INT_MAX &&
        IntArray::seg(a, 0, n, l)
    Ensure
        ((__return != 0) && list_contains(x, l) ||
         (__return == 0) && list_not_contains(x, l)) &&
        IntArray::seg(a, 0, n, l)
*/
```

如果参数在函数内没有被赋值，直接用参数名即可。不要为了“保存入口值”额外写：

```c
With l (a0: Z) (n0: Z) (x0: Z)
Require a == a0 && n == n0 && x == x0 ...
```

这种 ghost snapshot 会显著降低可读性。只有参数会被修改，且后条件必须引用入口值时，才用 `@pre`：

```c
IntArray::full(a@pre, n@pre, l)
```

## 9. loop invariant 的处理原则

格式转换阶段不要主动补复杂循环不变式。

可以暂时保留原始循环：

```c
for (i = 0; i < numbers_size; i++) {
    ...
}
```

不要为了让完整 symbolic execution 一次通过而写几十行：

```c
/*@ Inv Assert
    exists ...
    ...
*/
```

这些应该留到“验证阶段”处理。验证阶段会根据：

- symbolic execution 卡在哪一行
- 需要维护哪些数组段
- 哪些 manual witness 语义可证

再逐步补 invariant。

例外：

- 如果只是为了说明格式样例，可以写一个很短的占位 invariant。
- 但正式转换任务不应默认添加。

## 10. 保持程序结构

不要为了验证方便随意拆 helper。

例如原程序是两段循环：

```c
for (...) { build has1/has2 }
for (...) { write output }
```

格式转换阶段应该保留这两段循环。不要新增 `write_unique` 这类 helper，只为了让验证状态更干净。

只有在用户明确允许重构，或 QCP 前端确实不支持某种 C 结构时，才做结构调整，并且要说明原因。

循环变量声明要使用现有样例里的保守写法，先在循环外声明，再在 `for` 中赋值：

```c
int i;
for (i = 0; i < numbers_size; i++) {
    ...
}
```

避免保留 C99 风格的循环内声明：

```c
for (int i = 0; i < numbers_size; i++) {
    ...
}
```

这类写法在普通 C 编译器里没问题，但可能不适配 QCP 前端或现有 annotation 风格。格式转换阶段遇到 `for (int i = ...)` 时，应顺手把 `int i;` 提到循环前。

## 11. 注释风格

优先短注释：

```c
/*@ With input_l
    Require
        0 <= numbers_size && numbers_size < INT_MAX &&
        problem_XX_pre(input_l) &&
        IntArray::full(numbers, numbers_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        0 <= output_size && output_size <= numbers_size &&
        problem_XX_spec(input_l, output_l) &&
        ...
*/
```

避免：

- 大量 `x0`、`size0` ghost 变量。
- 重复写可由数组谓词推出的 `Zlength`。
- 在主后条件暴露中间变量。
- 在格式转换阶段写完整 loop state。

## 12. 验收标准

格式转换阶段的验收标准：

- C 文件使用 QCP 头文件和 wrapper。
- 主函数有清晰的 `Require/Ensure` 骨架。
- 临时 malloc 资源要么被 free wrapper 消费，要么明确保留在后条件中。
- `coins_XX.v` 能通过 `coqc`。
- 不生成或修改正式 `*_goal.v`、`*_proof_auto.v`、`*_proof_manual.v`、`*_goal_check.v`。
- 不引入 `Axiom`、不留下 `Admitted`。

可以运行轻量检查：

```bash
eval "$(opam env --switch=coq8201 --set-switch)"
cd QCP_examples/humaneval/IntArrayClaude
COQINCLUDES="$(tr '\n' ' ' < ../IntClaude/_CoqProject)"
coqc $COQINCLUDES coins_XX.v
```

注意：

- 不要在仓库根目录直接执行 `coqc QCP_examples/humaneval/IntArrayClaude/coins_XX.v`。很多 bridge 文件使用 `Load "../spec/XX".`，`Load` 的相对路径会按当前工作目录解析，从仓库根目录运行会找不到 `../spec/XX.v`。
- `IntArrayClaude` 目录本身没有 `_CoqProject`。直接在该目录执行 `coqc coins_XX.v` 又会缺少 `AUXLib`、`SimpleC.SL` 等逻辑路径映射，报类似 `Cannot find a physical path bound to logical path ListLib with prefix AUXLib`。
- 因此验证 `coins_XX.v` 时，推荐在 `IntArrayClaude` 目录下复用 `../IntClaude/_CoqProject` 生成 `COQINCLUDES`。
- `coqc` 成功后可能生成 `coins_XX.vo`、`coins_XX.glob`、`coins_XX.vos`、`coins_XX.vok`。这些是本地构建产物，格式转换提交里不要保留。

如果尝试运行 `symexec`，它可能因为缺少 loop invariant 而停在循环处；这不代表格式转换失败。完整 `symexec` 通过应属于后续验证阶段目标。

## 13. C_26 的经验总结

`C_26.c` 的格式转换过程中得到的经验：

- 一开始不应该提前写完整 loop invariant。
- 不应该为了验证方便新增 `write_unique` helper；应尽量保持原始两段循环。
- `has1/has2` 是中间数组，不应该出现在主后条件中；应通过 `free_int_array` 消费。
- `list_int_range` 对 `IntArray::full` 输入通常是冗余的。
- `numbers0/numbers_size0/a0/n0/x0` 这类 ghost snapshot 可读性差；参数不修改时直接用参数名。
- `Zlength(input_l) == numbers_size` 通常可以不写，数组谓词已经承载长度关系。
- 真正的循环语义如 `remove_duplicates_first_loop`、`remove_duplicates_second_loop` 应放在验证阶段的 invariant 中，而不是格式转换阶段默认生成。
