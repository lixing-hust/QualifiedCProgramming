# C++ -> C 转换主要修改统计与分类

##  主要修改分类

### A. vector<int>/vector<float>/vector<double> -> 指针+长度

典型改法:

- C++: `vector<int> f(vector<int> a)`
- C: `IntArray f(const int* a, int a_size)` 或 `void/标量返回 + const T* + size`

要点:

- 输入容器统一拆为 `data + size`
- 输出容器用结构体封装，如:
  - `typedef struct { int* data; int size; } IntArray;`
  - `typedef struct { float* data; int size; } FloatArray;`
- 空数组使用 `size=0, data=NULL`

### B. vector<string> -> char** + size 或字符串数组结构体

典型改法:

- C++: `vector<string> f(vector<string> s)`
- C: `StrArray f(char** s, int s_size)` 或 `const char**`

要点:

- 由 C++ 字符串对象改为 C 字符串指针数组
- 返回字符串列表时使用 `StrArray/StringArray`

### C. string -> const char* 输入，char*/const char* 输出

典型改法:

- C++: `string f(string s)`
- C: `char* f(const char* s)` 或 `const char* f(const char* s)`

要点:

- 读入参数统一改为 `const char*`
- 输出若为动态构造字符串，使用 `malloc` 分配并 `\0` 终止
- 仅常量结果时返回字面量 `"YES"/"NO"` 或 `""`

### D. STL 算法替换

主要替换:

- `sort(...)` -> `qsort(...)` + 比较器
- `find(...)` -> 手写循环 / `strstr` / `strchr`
- `substr/length/push_back` -> `memcpy/strlen/手工扩容`

### E. map/list/boost::any/class/new 等高级特性替换

1) map 替换:

- 小字母计数场景改为数组计数
- 键值对输出改为结构体数组(如 `CharIntMap`)

2) list<boost::any>/boost::any 替换:

- 改为 tagged union 思路
- 典型是 `PyValue {type, i, d, s}` 来模拟异构值

3) class/new 替换:

- 面向对象接口改为普通 C 函数
- 动态分配使用 `malloc/realloc/free`

### F. 布尔与语法细节修正

- `true/false` 与 C 布尔兼容处理 (`stdbool.h` 或 `1/0`)
- `and/or/not` -> `&&/||/!`
- C++ 风格强转与调用改为 C 兼容写法

