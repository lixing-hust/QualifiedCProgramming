#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_scale(int n, int *a, int k, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (-2147483648 <= la[i] * k && la[i] * k <= 2147483647)) &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == la[i] * k) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n@pre &&
          a == a@pre &&
          out == out@pre &&
          n == n@pre &&
          k == k@pre &&
          n@pre == Zlength(la) &&
          n@pre == Zlength(lo) &&
          Zlength(l1) == i &&
          Zlength(l2) == n@pre - i &&
          (forall (t: Z), (0 <= t && t < i) => l1[t] == la[t] * k@pre) &&
          (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
          IntArray::full(a, n@pre, la) *
          IntArray::full(out, n@pre, app(l1, l2))
    */
    for (i = 0; i < n; ++i) {
        out[i] = a[i] * k;
    }
}
