#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../char_array_def.h"

void string_reverse_copy(int n, char *src, char *dst)
/*@ With l d
    Require
      0 <= n && n < INT_MAX &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n + 1, d)
    Ensure
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n + 1, app(rev(l), cons(0, nil)))
*/
{
    int i;

    /*@ Inv
          0 <= i && i <= n &&
          src == src@pre &&
          dst == dst@pre &&
          n == n@pre &&
          exists l1 d1,
            Zlength(l1) == i &&
            Zlength(d1) == n + 1 - i &&
            (forall (k: Z), (0 <= k && k < i) => Znth(k, l1, 0) == Znth(n - 1 - k, l, 0)) &&
            CharArray::full(src, n + 1, app(l, cons(0, nil))) *
            CharArray::full(dst, n + 1, app(l1, d1))
    */
    for (i = 0; i < n; ++i) {
        dst[i] = src[n - 1 - i];
    }
    dst[n] = 0;
}
