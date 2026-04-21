#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (max_list_nonempty : list Z -> Z) */
/*@ Import Coq Require Import array_max */

void array_prefix_max(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n &&
      n + 1 <= INT_MAX &&
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
    /*@ Inv exists l1,
          1 <= i && i <= n@pre &&
          a == a@pre &&
          n == n@pre &&
          n + 1 <= INT_MAX &&
          out == out@pre &&
          n@pre == Zlength(la) &&
          n@pre == Zlength(lo) &&
          Zlength(l1) == i &&
          cur == max_list_nonempty(sublist(0, i, la)) &&
          (forall (k: Z),
            (0 <= k && k < i) =>
            l1[k] == max_list_nonempty(sublist(0, k + 1, la))) &&
          IntArray::full(a, n@pre, la) *
          IntArray::full(out, n@pre, app(l1, sublist(i, n@pre, lo)))
    */
    for (i = 1; i < n; ++i) {
        if (a[i] > cur) {
            cur = a[i];
        }
        /*@ Assert exists l1,
              1 <= i && i < n@pre &&
              a == a@pre &&
              n == n@pre &&
              n + 1 <= INT_MAX &&
              out == out@pre &&
              n@pre == Zlength(la) &&
              n@pre == Zlength(lo) &&
              Zlength(l1) == i &&
              cur == max_list_nonempty(sublist(0, i + 1, la)) &&
              (forall (k: Z),
                (0 <= k && k < i) =>
                l1[k] == max_list_nonempty(sublist(0, k + 1, la))) &&
              IntArray::full(a, n@pre, la) *
              IntArray::full(out, n@pre, app(l1, sublist(i, n@pre, lo)))
        */
        out[i] = cur;
    }
}
