## Semantic summary

Target function `string_reverse_copy` takes an explicit length `n`, a source C string `src`, and an output buffer `dst`. It copies the first `n` non-zero characters of `src` into `dst` in reverse order and then writes a terminating `0` at `dst[n]`.

## Contract decisions

- Keep the original interface. The explicit `n` already makes the target substring precise and avoids a scan-based contract.
- Model `src` as `CharArray::full(src, n + 1, app(l, cons(0, nil)))` with `l` the length-`n` payload.
- Add `0 <= n && n < INT_MAX` so the loop index and the access to `dst[n]` stay in `int` range.
- Add `(forall (k: Z), (0 <= k && k < n) => l[k] != 0)` so `src` is a valid C string whose first terminator is exactly at position `n`.
- Use separating conjunction between `src` and `dst` full arrays so the function matches the intended read-only source / write-only destination pattern and excludes aliasing that would change semantics.
- Express the postcondition as `CharArray::full(dst, n + 1, app(rev(l), cons(0, nil)))`. The repository already uses `rev` directly, so no custom bridge predicate is needed.

## Memory and bounds

- Reads: `src[n - 1 - i]` for `0 <= i < n`, which stays within `[0, n - 1]`.
- Writes: `dst[i]` for `0 <= i < n`, plus `dst[n] = 0`.
- No integer overflow is introduced by the loop under `0 <= n < INT_MAX`.

## Coq dependency judgment

No `input/string_reverse_copy.v` is needed. Existing list notation and `rev` are sufficient to state the result directly in the C contract.
