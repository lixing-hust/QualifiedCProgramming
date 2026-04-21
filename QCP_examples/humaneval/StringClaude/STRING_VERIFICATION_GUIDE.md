# StringClaude Verification Guide

This document records the string-verification knowledge that should be used when working on
`QCP_examples/humaneval/StringClaude`.

Important note: `QCP_examples/humaneval/String/C_11.c` is treated only as a historical attempt. It is useful for seeing possible generated goals, but it should not be used as the main source of truth. The main references for this guide are QCP's original examples and libraries:

- `QCP_examples/chars.c`
- `QCP_examples/kmp_rel.c`
- `QCP_examples/char_array_def.h`
- `QCP_examples/char_array.strategies`
- `SeparationLogic/examples/char_array_strategy_proof.v`
- `SeparationLogic/examples/chars_goal.v`
- `SeparationLogic/examples/chars_proof_manual.v`
- `SeparationLogic/examples/kmp_rel_lib.v`

## 1. Core Memory Model

QCP models C strings as character arrays, not as Coq `string` directly.

The key predicate is:

```c
CharArray::full(p, n, l)
```

It means:

- `p` points to a character array segment of length `n`.
- The mathematical contents of that segment are the list `l : list Z`.
- Each character is represented by its numeric code as a `Z`.

For ordinary null-terminated C strings, the standard shape is:

```c
CharArray::full(s, n + 1, app(chars, cons(0, nil)))
```

Here:

- `chars` is the string payload without the terminating zero.
- `0` is the C `'\0'` terminator.
- `n` is the logical string length.
- The allocated memory length is `n + 1`.

This convention appears directly in `QCP_examples/kmp_rel.c` in the specifications for `strlen`, `constr`, and `match`.

## 2. Basic Headers

StringClaude C files should generally use QCP headers rather than raw libc headers:

```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
```

If the function also uses integer arrays, include:

```c
#include "int_array_def.h"
```

Avoid relying on raw `stdio.h`, `stdlib.h`, `string.h`, `stdbool.h`, or C library behavior directly in verified code. In QCP style, commonly used functions such as `strlen` and `malloc_char_array` should be specified as external functions.

## 3. External Function Specs

### 3.1 `strlen`

The original QCP style is:

```c
int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;
```

This specification says:

- The input is a valid null-terminated string.
- The return value is exactly the payload length `n`.
- The input string memory is preserved.

Use `where` when calling it:

```c
int len = strlen(s) /*@ where l = str_l, n = n */;
```

This is important because the tool often needs help instantiating the logical string payload and length.

### 3.2 `malloc_char_array`

For string-producing functions, use a QCP-style allocation wrapper:

```c
char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure exists l, CharArray::full(__return, n, l)
*/
;
```

This follows the pattern in `kmp_rel.c` for `malloc_int_array`. It models the returned memory as a character array of length `n` with arbitrary initial contents.

If the function will write the entire output string from scratch, a more precise alternative is possible:

```c
Ensure __return != 0 && CharArray::undef_full(__return, n)
```

However, the original QCP examples mostly use `full` with an existential list for allocated arrays. Pick one style and keep the invariant consistent with it.

## 4. Character Codes

Inside `CharArray`, characters are represented as `Z`, not Coq `ascii`.

Common codes:

- `0` means `'\0'`
- `32` means space
- `40` means `'('`
- `41` means `')'`
- `48` means `'0'`
- `49` means `'1'`

When writing specs for `StringClaude`, prefer using these numeric codes in C annotations and `coins_XX.v` helper predicates, unless a clean bridge from Coq `ascii/string` has already been built.

## 5. Strategy Support

`QCP_examples/char_array.strategies` provides the main automatic rules.

### 5.1 Reading `s[i]`

From:

```c
CharArray::full(s, n, l)
```

with `0 <= i < n`, the strategy can expose:

```c
data_at(s + i * sizeof(I8), I8, Znth(i, l, 0)) *
CharArray::missing_i(s, i, 0, n, l)
```

The proof behind this is in `char_array_strategy1_correctness`, using:

```coq
CharArray.full_split_to_missing_i
```

### 5.2 Preserving a Read-Only String

After a read, the strategy can merge the same value back:

```c
CharArray::missing_i(s, i, 0, n, l) *
data_at(s + i * sizeof(I8), I8, l[i])
```

back into:

```c
CharArray::full(s, n, l)
```

This corresponds to `char_array_strategy2_correctness`.

### 5.3 Updating One Character

If `s[i]` is overwritten with `v`, the array becomes:

```c
CharArray::full(s, n, replace_Znth(i, v, l))
```

This is the `missing_i_merge_to_full` pattern used by `char_array_strategy3_correctness`.

### 5.4 Appending at the End

There is a special strategy rule for appending one character at the current end:

```c
CharArray::full(p, n, l) *
data_at(p + n * sizeof(I8), I8, v)
```

can become:

```c
CharArray::full(p, n + 1, app(l, cons(v, nil)))
```

This is rule `id : 10` in `char_array.strategies`, proved by `char_array_strategy10_correctness`.

This rule is very useful for output-building loops:

- Maintain `CharArray::full(out, i, out_l)` for the already-written prefix.
- Write `out[i] = c`.
- The strategy turns it into `CharArray::full(out, i + 1, app(out_l, cons(c, nil)))`.

### 5.5 Writing Into Uninitialized Output

For initializing an output buffer, use the pattern from `QCP_examples/chars.c`:

```c
/*@ Inv
    0 <= i && i <= n@pre &&
    CharArray::full(a@pre, i, repeat_Z(m@pre, i)) *
    CharArray::undef_seg(a@pre, i, n@pre)
*/
```

This describes:

- Prefix `[0, i)` has been written.
- Suffix `[i, n)` is still uninitialized.

The generated VC for `chars_initialize` confirms this is the intended pattern.

## 6. Null-Terminated Output Strings

For functions returning a newly allocated C string, the postcondition should usually be:

```c
CharArray::full(__return, out_n + 1, app(out_l, cons(0, nil)))
```

The invariant should usually build the non-null prefix first:

```c
CharArray::full(out, i, out_l) *
CharArray::undef_seg(out, i, out_n + 1)
```

or, if allocation is modeled as arbitrary initialized `full`, keep an existential tail/list that allows safe writes.

At the end:

```c
out[out_n] = 0;
```

should establish:

```c
CharArray::full(out, out_n + 1, app(out_l, cons(0, nil)))
```

This final terminator write is not optional. Without it, the result is just a character array, not a valid C string.

## 7. Mapping `spec/*.v` Strings to `CharArray`

Many HumanEval string specs use Coq `string` and `ascii`, for example:

```coq
problem_11_spec (a b output : string) : Prop
```

But QCP's memory-level predicate uses:

```coq
list Z
```

So there is a representation gap:

- Coq spec: `string` / `ascii`
- QCP memory: `list Z` of character codes

There are two practical approaches.

### Approach A: Build a Bridge

Define helper functions in `coins_XX.v`:

```coq
ascii_to_Z : ascii -> Z
Z_to_ascii : Z -> ascii
string_to_Zlist : string -> list Z
Zlist_to_string : list Z -> string
```

Then relate:

```coq
problem_XX_spec input_string output_string
```

to:

```coq
CharArray::full(input_ptr, n + 1, app(input_l, cons(0, nil)))
```

This is more faithful to the existing `spec/*.v`, but it can add proof overhead.

### Approach B: Use a `list Z` Version of the Spec

For first-pass verification, define a local `list Z` version of the spec in `coins_XX.v`, and prove or record later that it corresponds to the original `string` spec.

This is often easier for `StringClaude`, because the program itself reads and writes numeric character codes.

Example for binary string XOR:

```coq
forall k,
  0 <= k < n ->
  ((Znth k a 0 = Znth k b 0 /\ Znth k out 0 = 48) \/
   (Znth k a 0 <> Znth k b 0 /\ Znth k out 0 = 49)).
```

This matches the C code directly.

## 8. Common String Function Templates

### 8.1 Read-Only String, Return Int

Examples:

- Length
- Count characters
- Check property

Recommended precondition:

```c
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      result_property(__return, l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

The invariant usually keeps:

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

and tracks prefix semantics separately.

### 8.2 Read-Only String, Return New String

Examples:

- `string_xor`
- `make_palindrome`
- replace/filter/fix spacing

Recommended precondition:

```c
/*@ With in_l n
    Require
      0 <= n && n < INT_MAX &&
      input_char_range(in_l) &&
      CharArray::full(s, n + 1, app(in_l, cons(0, nil)))
*/
```

Recommended postcondition:

```c
/*@ Ensure exists out_l out_n,
      output_spec(in_l, out_l) &&
      __return != 0 &&
      CharArray::full(s, n + 1, app(in_l, cons(0, nil))) *
      CharArray::full(__return, out_n + 1, app(out_l, cons(0, nil)))
*/
```

Be explicit about:

- output length
- terminating zero
- input memory preservation
- allocation success, if the program assumes it

### 8.3 Build Output Buffer Character by Character

Recommended invariant:

```c
/*@ Inv Assert
    exists out_l,
      0 <= i && i <= out_n &&
      prefix_spec(input_l, i, out_l) &&
      CharArray::full(input, in_n + 1, app(input_l, cons(0, nil))) *
      CharArray::full(out, i, out_l) *
      CharArray::undef_seg(out, i, out_n + 1)
*/
```

After writing the terminator, the return proof should expose:

```c
CharArray::full(out, out_n + 1, app(out_l, cons(0, nil)))
```

### 8.4 Initialize a Char Buffer

Use `chars.c` as the canonical model:

```c
CharArray::full(a, i, repeat_Z(m, i)) *
CharArray::undef_seg(a, i, n)
```

This is good for:

- memset-like character filling
- creating a repeated-character string
- preparing a buffer before later writes

## 9. Safety Conditions

String programs need both memory safety and C integer safety.

Always check:

- `0 <= n`
- `n < INT_MAX`
- `n + 1 <= INT_MAX` when allocating or indexing the terminator
- `i + 1 <= INT_MAX` inside loops
- output length formulas such as `2 * n + 1`, `n + add + 1`, or `cap * 2`
- character values are in valid char range if the program depends on it

For ASCII-oriented HumanEval problems, it is often useful to add:

```c
forall k, 0 <= k && k < n -> 0 <= Znth(k, l, 0) && Znth(k, l, 0) <= 127
```

For binary strings:

```c
forall k, 0 <= k && k < n ->
  Znth(k, l, 0) == 48 || Znth(k, l, 0) == 49
```

For parentheses strings:

```c
forall k, 0 <= k && k < n ->
  Znth(k, l, 0) == 40 || Znth(k, l, 0) == 41 || Znth(k, l, 0) == 32
```

These constraints should be part of the precondition, not discovered late in `manual.v`.

## 10. Malloc, Realloc, and Return Shapes

QCP examples support allocation through specified external functions.

Use this style:

```c
char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure exists l, __return != 0 && CharArray::full(__return, n, l)
*/
;
```

Avoid raw `malloc` in verified StringClaude programs. Wrap it with a specified helper.

Be cautious with `realloc`. The original QCP examples do not give a simple reusable `realloc` verification pattern for strings. For HumanEval string tasks, prefer rewriting the program to allocate the final output size once when feasible.

Also be cautious with returning structs such as:

```c
typedef struct {
  int *data;
  int size;
} IntArray;
```

The better-supported QCP patterns are:

- return `char *`
- return `int *`
- use an output buffer argument
- use a pointer to a struct with explicit field predicates

Returning a struct by value is not the usual QCP style.

## 11. Lessons From QCP Original Examples

### `chars.c`

Use it as the minimal template for writing a character array:

- precondition: `CharArray::undef_full(a, n)`
- invariant: written prefix `CharArray::full(a, i, repeat_Z(m, i))`
- invariant: unwritten suffix `CharArray::undef_seg(a, i, n)`
- postcondition: `CharArray::full(a, n, repeat_Z(m, n))`

This is the cleanest reference for output-buffer construction.

### `kmp_rel.c`

Use it as the main template for null-terminated strings:

- string input: `CharArray::full(s, n + 1, app(l, cons(0, nil)))`
- `strlen` preserves the input string and returns `n`
- function calls often need `where`
- returned arrays/allocated helper arrays should have external allocation specs

### `char_array.strategies`

Use it to understand which memory transformations are automatic:

- read from full array
- merge read cell back
- update a cell with `replace_Znth`
- append one character at the current end
- split uninitialized suffix for writing

## 12. Recommended Workflow for StringClaude

1. Replace raw libc style with QCP style headers and external specs.
2. Decide the internal representation of the string spec:
   - bridge to Coq `string`, or
   - use a `list Z` spec in `coins_XX.v`
3. Write preconditions with:
   - string memory `CharArray::full(..., app(l, cons(0,nil)))`
   - length bounds
   - character-range constraints
   - output-size safety bounds
4. Write invariants with:
   - loop index bounds
   - prefix semantic relation
   - input string memory preserved
   - output prefix and remaining buffer ownership
5. Run `symexec`.
6. In `manual.v`, expect proof obligations about:
   - prefix list update
   - `app`, `Znth`, `replace_Znth`
   - output terminator
   - length arithmetic
   - character-code case splits

## 13. First Things To Check In Each StringClaude File

- Does it return `char *`, `int`, or a struct?
- Does it use raw `malloc`, `realloc`, `memcpy`, or `strlen`?
- Can output length be known before allocation?
- Is the result null-terminated?
- Does the spec use Coq `string`, while the memory model uses `list Z`?
- Are all input characters constrained to the intended alphabet?
- Are all length expressions within `INT_MAX`?

If any answer is unclear, fix the specification or C shape first before attempting proof.

