#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_copy_positive(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      IntArray::full(a, n, la) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((la[i] > 0 => lr[i] == la[i]) &&
           (la[i] <= 0 => lr[i] == 0))) &&
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
          n@pre == Zlength(la) &&
          n@pre == Zlength(lo) &&
          Zlength(l1) == i &&
          Zlength(l2) == n@pre - i &&
          (forall (t: Z),
            (0 <= t && t < i) =>
            ((la[t] > 0 => l1[t] == la[t]) &&
             (la[t] <= 0 => l1[t] == 0))) &&
          (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
          IntArray::full(a, n@pre, la) *
          IntArray::full(out, n@pre, app(l1, l2))
    */
    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            out[i] = a[i];
        } else {
            out[i] = 0;
        }
    }
}
