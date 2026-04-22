#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_replace_negative_zero(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        Zlength(l0) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((l[i] < 0 => l0[i] == 0) &&
           (l[i] >= 0 => l0[i] == l[i]))) &&
        IntArray::full(a, n, l0)
*/
{
    int i;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n@pre &&
          a == a@pre &&
          n == n@pre &&
          n@pre == Zlength(l) &&
          Zlength(l1) == i &&
          Zlength(l2) == n@pre - i &&
          (forall (t: Z),
            (0 <= t && t < i) =>
            ((l[t] < 0 => l1[t] == 0) &&
             (l[t] >= 0 => l1[t] == l[t]))) &&
          (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == l[i + t]) &&
          IntArray::full(a, n@pre, app(l1, l2))
    */
    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            a[i] = 0;
        }
    }
}
