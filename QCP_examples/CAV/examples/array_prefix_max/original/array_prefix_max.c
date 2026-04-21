#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (max_list_nonempty : list Z -> Z) */
/*@ Import Coq Require Import array_max */

void array_prefix_max(int n, int *a, int *out)
/*@ With la, lo
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
          lr[i] == max_list_nonempty(sublist(0, i + 1, la))) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;
    int cur;

    if (n == 0) {
        return;
    }

    cur = a[0];
    out[0] = cur;
    for (i = 1; i < n; ++i) {
        if (a[i] > cur) {
            cur = a[i];
        }
        out[i] = cur;
    }
}
