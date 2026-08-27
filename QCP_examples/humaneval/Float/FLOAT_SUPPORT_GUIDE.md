# QCP V2.0.4 浮点验证支持调研与使用指南

调研日期：2026-07-18  
对应版本：`QCP-v2.0.4`（commit `91d4050`）

本文只记录当前仓库中已经能从源码或实际 `symexec` 行为确认的能力。需要特别区分：

- “能解析 C 并生成 VC”不等于“已有足够自动化把 VC 无公理地证明完”；
- `QCP_examples/humaneval/Float/` 目前的 20 个 `C_*.c` 都是原始候选程序，没有 annotation、goal、manual proof 或 goal-check，不能视为已验证样例；
- 官方 `QCP_examples/QCP_demos_tutorial/float.c` 是前端与 VC 形状示例。当前随仓库提交的 `float_proof_auto.v` 中 55 个 proof stub 都是 `Admitted`，因此它不是无 `Admitted` 的端到端证明样例。

## 1. 总结

当前 QCP 已经打通以下基础能力：

1. C `float` 和 `double` 标量的解析、局部变量、参数、返回值与符号执行；
2. IEEE-754 binary32/binary64 精确语义，而不是把机器浮点直接当成数学实数；
3. 十进制/科学计数法字面量、取负、`+ - * /`、复合赋值和六种比较；
4. 整数到 `float`/`double` 的转换；
5. 可选的有限值安全 VC：检查运算结果不是 NaN/Infinity，并在除法处检查除数非零；
6. Rocq 侧的浮点位模式、有限性、NaN、Infinity、比较、实数转换和标量内存模型；
7. Rocq 后端已经定义浮点数组模块，但 C 侧共享 header/strategy 尚未配齐。

当前最适合验证的是：只使用单一精度、基本算术和比较，规格也直接描述 IEEE-754 运算结果的标量程序。

当前不宜直接承诺完成的是：依赖 `sqrt/pow/fabs/floor/ceil/round/strtod`、混合 `float`/`double`、复杂浮点数组、数值迭代收敛性或实数误差界的程序。这些程序还需要额外库规格、数组策略或较重的 Flocq 证明。

## 2. 浮点语义模型

核心实现位于：

- `SeparationLogic/SeparationLogic/FloatLib.v`
- `SeparationLogic/SeparationLogic/CommonAssertion.v`
- `SeparationLogic/SeparationLogic/ArrayLib.v`
- `SeparationLogic/flocq/`

QCP 使用 Flocq 的 IEEE-754 模型：

| C 类型 | Rocq 类型 | 格式 |
|---|---|---|
| `float` | `fp32` | IEEE-754 binary32，24 位有效精度，8 位指数 |
| `double` | `fp64` | IEEE-754 binary64，53 位有效精度，11 位指数 |

当前基本运算固定使用 `mode_NE`，即 round-to-nearest, ties-to-even。QCP 没有在 C 层建模动态 rounding mode 或 `fenv`。

浮点运算会生成下面的精确模型，而不是普通 `R` 运算：

| C 表达式 | annotation/Rocq 表达式 |
|---|---|
| `1.0f` | `fp32(1.0)`，输出到 Rocq 后为 `fp32_of_real 1.0` |
| `1.0` | `fp64(1.0)`，输出到 Rocq 后为 `fp64_of_real 1.0` |
| `x + y` | `fp32_add(x,y)` / `fp64_add(x,y)` |
| `x - y` | `fp32_sub(x,y)` / `fp64_sub(x,y)` |
| `x * y` | `fp32_mul(x,y)` / `fp64_mul(x,y)` |
| `x / y` | `fp32_div(x,y)` / `fp64_div(x,y)` |
| `-x` | `fp32_neg(x)` / `fp64_neg(x)` |
| C 整数 `z` 转浮点 | `Z_to_fp32(z)` / `Z_to_fp64(z)` |

这意味着通常不能把：

```c
return (x + y) * z;
```

直接规格化为数学实数上的 `(x + y) * z`。对 `float`，精确后置条件应是：

```text
__return == fp32_mul(fp32_add(x, y), z)
```

中间的加法和最终乘法分别发生一次舍入；`x * y + z` 当前也被建模为先乘后加，不是 fused multiply-add。

## 3. 已确认支持的 C 语法与操作

以下能力由官方 35 个函数的 float tutorial 和本次实际 `symexec` 探测确认。

### 3.1 标量与字面量

支持：

- `float`、`double` 参数、局部变量和返回值；
- `0.0f`、`-0.0f`、`1.0f`、`.5f`、`1e-3f`、`1.5e+2f`、大写 `F`；
- 对应的无后缀 `double` 字面量；
- 正零和负零的不同位模式；
- 浮点恒等返回和局部赋值。

未支持：

- `long double`；实际解析报错；
- 十六进制浮点字面量，如 `0x1.8p+1f`；实际解析报错。

### 3.2 算术

支持：

- 一元负号；
- `+`、`-`、`*`、`/`；
- 括号和多步混合表达式；
- `+=`、`-=`、`*=`、`/=`；
- 整数字面量或 `int` 到 `float`/`double` 的转换。

注意：

- 除法若开启有限值 VC，会要求除数按 IEEE 比较不等于 `+0/-0`，并要求结果有限；
- 无后缀小数是 `double`。例如 `float x; x * 0.5` 会引入 `float -> double` 提升，而当前该转换不支持。纯 `float` 程序必须使用 `0.5f`；
- 把 `0.5` 改成 `0.5f` 可能改变计算精度和可观察结果，适配原程序时应先判断是否属于语义修改。

### 3.3 比较和分支

支持：

- `==`、`!=`、`<`、`<=`、`>`、`>=`；
- 比较结果用于 `if` 分支；
- Rocq 侧对应 `fp32_eq/ne/lt/le/gt/ge` 和 `fp64_eq/ne/lt/le/gt/ge`。

比较是 IEEE 比较，不是普通实数全序。NaN 会使有序比较不可比较；例如 `x < y` 为假并不总能推出 `x >= y`，除非已知输入不是 NaN。分支规格通常应要求 `fp32_isFinite`/`fp64_isFinite`，或显式覆盖 NaN 分支。

### 3.4 类型转换

| 转换 | 当前状态 |
|---|---|
| `int -> float` | 支持，使用 `Z_to_fp32` |
| `int -> double` | 支持，使用 `Z_to_fp64` |
| `float -> double` | 不支持，实际报 `Unsupported cast from type float to floating-point type` |
| `double -> float` | 不支持，实际报 `Unsupported cast from type double to floating-point type` |
| `float/double -> int` | 前端可走到符号执行，但当后置条件真正使用转换结果时产生类型错误；目前不能作为可靠能力使用 |

因此应避免混合精度表达式以及依赖 `(int)x`、`round(x)` 后再转整数的程序。

## 4. finite-value VC 模式

新版增加两个互斥选项：

```text
--float-finite-vc
--no-float-finite-vc
```

本次实测确认：不写选项时，输出与 `--no-float-finite-vc` 完全一致。也就是说，当前默认不生成浮点有限值安全 VC。

### 4.1 `--no-float-finite-vc`

运算按完整 IEEE-754 语义执行，可以产生 NaN 或 Infinity。验证者只需证明函数规格；不会自动要求每一步结果有限。

适用于：

- 规格本身覆盖 NaN/Infinity；
- 有意验证完整 IEEE 行为；
- 初期只想确认前端和基本函数规格。

### 4.2 `--float-finite-vc`

会额外生成：

- 每个整数转浮点结果有限；
- 每个取负、加、减、乘、除结果有限；
- 除法的除数不为 IEEE 零；
- 比较操作数有限。

例如：

```c
x += y;
x /= y;
```

至少会要求：

```text
fp32_isFinite(fp32_add(x, y))
fp32_ne(y, fp32(0.0))
fp32_isFinite(fp32_div(fp32_add(x, y), y))
```

开启选项不会自动证明这些事实。输入范围、每个中间结果的有限性和非零除数必须由 precondition、loop invariant 或前序断言提供。

HumanEval 浮点 case 建议显式选择模式并记录在验证文档中。若题意只讨论普通有限数，优先使用 `--float-finite-vc`；若题意允许 IEEE 特殊值，则使用 `--no-float-finite-vc` 并在规格中覆盖 NaN/Infinity。

## 5. annotation 中可以使用的定义

`FloatLib.v` 当前提供：

```text
fp32, fp64
fp32_add/sub/mul/div/neg
fp64_add/sub/mul/div/neg
fp32_isFinite, fp64_isFinite
fp32_isNaN, fp64_isNaN
fp32_isInf, fp64_isInf
fp32_eq/ne/lt/le/gt/ge
fp64_eq/ne/lt/le/gt/ge
fp32_of_bits, fp64_of_bits
bits_of_fp32, bits_of_fp64
fp32_of_real, fp64_of_real
Z_to_fp32, Z_to_fp64
fp32_to_R, fp64_to_R
fp32_to_R_total, fp64_to_R_total
fp32_zero, fp32_neg_zero
fp64_zero, fp64_neg_zero
fp32_pos_infinity, fp32_neg_infinity
fp64_pos_infinity, fp64_neg_infinity
FLT_MAX, FLT_MIN, DBL_MAX, DBL_MIN
```

`FLT_MIN`/`DBL_MIN` 是最小正规正数，不是最小负数。

一个适合当前能力的函数规格示例：

```c
float mul_add(float x, float y, float z)
/*@ Require emp &&
            fp32_isFinite(x) && fp32_isFinite(y) && fp32_isFinite(z) &&
            fp32_isFinite(fp32_mul(x, y)) &&
            fp32_isFinite(fp32_add(fp32_mul(x, y), z))
    Ensure __return == fp32_add(fp32_mul(x, y), z) && emp
  */
{
    return x * y + z;
}
```

不要写成 `__return == x * y + z` 并把 annotation 运算误认为数学实数运算；应优先显式使用 `fp32_*`/`fp64_*`。

## 6. 内存与数组支持

### 6.1 已进入 Rocq 内存模型

已经存在：

- `store_float`、`store_double`；
- `store_finite_float`、`store_finite_double`；
- 对应的未初始化 store；
- 4 字节 `float` 和 8 字节 `double` 的位模式存储；
- `FloatArray`、`DoubleArray`、`FiniteFloatArray`、`FiniteDoubleArray` 模块。

这些数组模块由通用 `ArrayLib` 实例化，理论上具有与 `IntArray` 同类的 `full`、`seg`、`missing_i`、`undef_full`、`undef_seg` 等谓词和引理。

### 6.2 当前工程缺口

仓库没有像 `int_array_def.h`/`int_array.strategies` 那样可直接 include 的共享：

```text
float_array_def.h
float_array.strategies
double_array.strategies
```

本次最小探测中：

- 未声明 `FloatArray::full` 时，annotation 前端直接报告 undeclared identifier；
- 手工声明 `FloatArray::full` 后，读取 `a[0]` 仍因缺少把 `full` 拆成单元所有权的 strategy 而失败；
- 直接手工声明 `store_float` 也没有现成前端策略把它用于 memory read。

在 `C_0.c` 的实际验证尝试中进一步确认，缺口位于 strategy 语言本身：

- `symexec` 对 `numbers[i]` 生成的读取前提是浮点 `data_at`/`store`，值类型为 `fp32`；
- strategy 语法没有可用于 `store(..., float, ...)` 的浮点 C 类型 token；
- 使用通用 `data_at(..., ?ty, ?v)` 时，strategy 类型推断仍把元素值固定为 `Z`，与 `fp32` 无法统一；
- 因而即使 Rocq 侧 `FloatArray.full_split_to_missing_i` 已存在，当前二进制也无法用一条可证明的 strategy 把 `FloatArray::full` 拆成浮点数组读取所需的单元资源。

这意味着当前缺的不只是一个可复制的 `.strategies` 文件，还需要 QCP strategy parser/type checker 增加 float/double `data_at` 支持。绕过方式（例如把读取包装成未经证明的外部 getter）不属于直接验证，不能作为完成方案。

因此当前应把浮点数组描述为“Rocq 后端模型已存在，但 HumanEval 可复用的 C header/strategy 尚未产品化”，不能简单照抄 `IntArray` 工作流就声称已经可用。

若要验证 `humaneval/Float` 中的数组题，建议先在共享目录补齐并验证通用的：

1. float/double array predicate 声明；
2. `full <-> missing_i`、`seg` 拆分/合并策略；
3. initialized/undefined segment 写入策略；
4. finite array 与普通 array 的转换或保持规则；
5. malloc/free wrapper 对 4/8 字节元素大小的规格。

这些应是通用库设施，不能做成携带某一道 HumanEval 题目结论的 wrapper。

## 7. 数学实数规格如何连接

多数 `humaneval/spec/*.v` 使用 `R`，而 C 层现在使用 `fp32`/`fp64`。两者不能直接相等。

可用桥接：

```text
fp32_to_R : fp32 -> option R
fp64_to_R : fp64 -> option R
fp32_to_R_total : fp32 -> R
fp64_to_R_total : fp64 -> R
```

建议：

- 对只接受有限值的规格，先要求 `fp32_isFinite x`/`fp64_isFinite x`，再使用 `fp*_to_R` 或 `fp*_to_R_total`；
- 精确机器语义规格应直接用 `fp32_add` 等；
- 若原始规格要求实数等式，需要证明每次舍入与该等式的关系，很多程序的实数等式实际上对机器浮点并不成立；
- 若题意允许近似，应把误差界明确写进原始 spec，而不是在 C bridge 中私自放宽等式；
- 不要把 `fp32_to_R_total` 用在 NaN/Infinity 上后假装获得了合理实数语义。

当前 `FloatLib.v` 只提供少量基础引理，尚没有面向 HumanEval 的现成加减乘除误差界、累计误差或 `Rabs` bridge 自动化。Flocq 本身有丰富定理，但将具体 C VC 连接到这些定理仍需要手工证明。

## 8. `math.h` 与外部函数

当前 `FloatLib.v` 没有直接暴露以下 C 函数的 QCP 规格：

```text
fabs/fabsf
floor/floorf
ceil/ceilf
round/roundf
sqrt/sqrtf
pow/powf
strtod
isnan/isfinite
```

实际调用一个只有普通 C 声明、没有 QCP function spec 的 `sqrt`，`symexec` 会报告找不到 function spec。

QCP 支持给外部函数声明 function spec 后验证调用者，因此可以为通用数学库函数建立 wrapper。但要注意：

- wrapper 规格必须准确描述对应精度、舍入、domain error、NaN/Infinity 和返回值；
- 只写一个过强后置条件会把真正的数学困难隐藏为未验证假设；
- 如果只验证 caller 相对于外部库合同，应明确记录该信任边界；
- `pow(x, 0.5)` 不应未经证明直接替换成实数 `sqrt x`；
- `abs` 是整数函数。仓库中若对 `float` 调用 `abs`，会引入浮点到整数转换，既可能是原 C bug，也不属于当前可靠支持路径。

## 9. 当前明确不支持或证据不足的部分

| 能力 | 结论 |
|---|---|
| `float`/`double` 基本标量运算 | 已支持 VC 生成 |
| IEEE NaN/Infinity/正负零建模 | Rocq 模型已支持 |
| 动态 rounding mode、`fenv` | 未支持 |
| `long double` | 未支持 |
| float/double 混合精度 | 未支持 |
| 十六进制浮点字面量 | 未支持 |
| 可靠的 float/double 到整数转换 | 当前不可用 |
| FMA | 未建模为 fused operation |
| `math.h` 常用函数 | 无现成 QCP 规格 |
| 浮点数组后端模型 | 已存在 |
| 可直接复用的浮点数组 header/strategy | 缺失 |
| 实数误差界自动化 | 未形成可直接使用的高层库 |
| 无 `Admitted` 的官方端到端 float demo | 当前没有 |

## 10. `humaneval/Float` 现有 20 题的初步分级

这里只评估“需要哪些浮点基础设施”，不代表规格已经与 C 行为一致。

### A. 接近当前标量能力，但源码仍需审查/适配

- `C_45.c`：核心只是乘法，但 `0.5` 是 `double`，原程序包含 float-to-double 提升和返回时 double-to-float 收窄；当前不支持。改成 `0.5f` 可能改变舍入语义，需先确认是否允许。
- `C_157.c`：标量乘法和比较本身可建模，但源码错误地对浮点表达式调用整数 `abs`，且对应 spec 使用 `Z`；不能直接开始证明。
- `C_92.c`：基本加法/比较可建模，但依赖 `round`，且 spec 使用 `Q`，需要库规格和表示桥接。

### B. 基本浮点运算可表达，但先缺浮点数组公共设施

- `C_21.c`：min/max、归一化、除法、输出数组；
- `C_30.c`：正数过滤和输出数组；
- `C_35.c`：最大值循环；
- `C_57.c`：单调性比较循环；
- `C_62.c`：整数索引乘浮点系数和输出数组；
- `C_81.c`：浮点比较数组，再叠加字符串常量/指针数组；
- `C_0.c`、`C_4.c`：除数组外还错误使用整数 `abs`。

### C. 还依赖尚无规格的数学/库函数

- `C_2.c`：`floorf`；
- `C_20.c`：`fabsf`、malloc、浮点输出数组；
- `C_32.c`：`pow`、`fabs`、函数调用、Newton 迭代及终止/收敛证明；
- `C_37.c`：`qsort`、比较器、malloc/free、浮点数组；
- `C_47.c`：`qsort`、比较器和浮点数组；
- `C_71.c`：`pow(..., 0.5)`，还涉及平方根与舍入规格；
- `C_99.c`：`strtod` 和 `round`；
- `C_133.c`：`ceil` 和 float-to-int；
- `C_151.c`：`round`、float-to-int、整数奇偶与乘法。

这批题的推荐起点不是直接逐题堆 wrapper，而是先建设两类共享设施：

1. float/double array header + strategies；
2. 经证明或明确作为可信外部合同的 `fabs/floor/ceil/round/sqrt` 规格库。

## 11. 推荐的验证命令

浮点模式必须显式固定。例如从仓库根目录生成 HumanEval Float case：

```bash
opam exec --switch=coq8201 -- linux-binary/symexec \
  --goal-file=QCP_examples/humaneval/Float/C_XX_goal.v \
  --proof-auto-file=QCP_examples/humaneval/Float/C_XX_proof_auto.v \
  --proof-manual-file=QCP_examples/humaneval/Float/C_XX_proof_manual.v \
  --coq-logic-path=SimpleC.EE \
  -slp QCP_examples/humaneval/Float SimpleC.EE \
  --input-file=QCP_examples/humaneval/Float/C_XX.c \
  --float-finite-vc \
  --gen-and-backup \
  --no-exec-info
```

若规格明确覆盖 NaN/Infinity，把选项替换为：

```text
--no-float-finite-vc
```

每次重生成都必须保持相同选项，否则 witness 数量和编号会改变。根 `_CoqProject` 已包含：

```text
-R SeparationLogic/flocq/src Flocq
```

编译 float 相关 Rocq 文件时不能漏掉该 load path。

## 12. 实际验证时的检查清单

开始一个 float case 前检查：

- [ ] 只使用 `float` 或只使用 `double`，没有隐式混合精度；
- [ ] `float` 常量都使用 `f/F` 后缀；
- [ ] 没有 `long double` 或十六进制浮点字面量；
- [ ] 没有依赖当前不可靠的 float-to-int 转换；
- [ ] 每个 `math.h` 调用都有通用、可信、精度正确的函数规格；
- [ ] 已决定并记录 finite-value VC 模式；
- [ ] finite 模式下，每一步运算的有限性和除数非零都能从 pre/invariant 推出；
- [ ] 分支是否需要排除 NaN；
- [ ] 规格要求的是 IEEE 精确结果、实数等式还是误差界；
- [ ] `fp32/fp64` 到原始 `R/Q/Z` spec 的桥接真实成立；
- [ ] 数组 case 已具备 float array predicate 声明和 verified strategies；
- [ ] 不把未经证明的数学库行为藏进题目专用 wrapper；
- [ ] 最终 manual/case library 无 `Admitted`、无额外 `Axiom`。

## 13. 本次调研的实测证据

对官方 `float.c`：

- 默认模式成功符号执行全部 35 个函数，生成 588 行 goal、55 个基础 witness；
- `--no-float-finite-vc` 与默认输出 SHA-256 完全相同；
- `--float-finite-vc` 成功符号执行，goal 增至 1060 行、112 个 witness；
- 无前提的 `+= -= *= /=` 探测在 finite 模式下生成 4 组待证 safety witness，其中除法拆出非零与有限性目标；
- int-to-float/int-to-double 和浮点复合赋值成功；
- float-to-double、double-to-float、long double、hex float literal 失败；
- float-to-int 在后置条件使用结果时触发 `fp32` 与 `Z` 类型错误；
- float array 的 Rocq 模块存在，但没有共享 C 声明/strategy 时无法完成 memory read symbolic execution；
- 无 function spec 的 `sqrt` 调用失败；带 function spec 的外部浮点函数声明可以被 caller 使用。

临时探测文件仅放在 `/tmp/qcp-float-research-20260718`，未加入仓库。

## 14. 主要参考文件

- `Version_Log/V2-0-4.md`
- `README.md`
- `QCP_examples/QCP_demos_tutorial/float.c`
- `SeparationLogic/examples/QCP_demos_tutorial/float_goal.v`
- `SeparationLogic/examples/QCP_demos_tutorial/float_proof_auto.v`
- `SeparationLogic/SeparationLogic/FloatLib.v`
- `SeparationLogic/SeparationLogic/CommonAssertion.v`
- `SeparationLogic/SeparationLogic/ArrayLib.v`
- `SeparationLogic/flocq/`
