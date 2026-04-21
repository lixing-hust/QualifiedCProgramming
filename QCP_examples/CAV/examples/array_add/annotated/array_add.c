#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_add(int n, int *a, int *b, int *out)
/*@ With la lb lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lb) == n &&
      Zlength(lo) == n &&
      (forall (i: Z),
        (0 <= i && i < n) =>
        (-2147483648 <= la[i] + lb[i] && la[i] + lb[i] <= 2147483647)) &&
      IntArray::full(a, n, la) *
      IntArray::full(b, n, lb) *
      IntArray::full(out, n, lo)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == la[i] + lb[i]) &&
        IntArray::full(a, n, la) *
        IntArray::full(b, n, lb) *
        IntArray::full(out, n, lr)
*/
{
    int i;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n@pre &&
          a == a@pre &&
          b == b@pre &&
          out == out@pre &&
          n@pre == Zlength(la) &&
          n@pre == Zlength(lb) &&
          n@pre == Zlength(lo) &&
          Zlength(l1) == i &&
          Zlength(l2) == n@pre - i &&
          (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k] + lb[k]) &&
          (forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == lo[i + k]) &&
          IntArray::full(a, n@pre, la) *
          IntArray::full(b, n@pre, lb) *
          IntArray::full(out, n@pre, app(l1, l2))
    */
    for (i = 0; i < n; ++i) {
        /*@ exists l1 l2,
              0 <= i && i < n@pre &&
              a == a@pre &&
              b == b@pre &&
              out == out@pre &&
              n@pre == Zlength(la) &&
              n@pre == Zlength(lb) &&
              n@pre == Zlength(lo) &&
              Zlength(l1) == i &&
              Zlength(l2) == n@pre - i &&
              (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k] + lb[k]) &&
              (forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == lo[i + k]) &&
              IntArray::full(a, n@pre, la) *
              IntArray::full(b, n@pre, lb) *
              IntArray::full(out, n@pre, app(l1, l2))
            which implies
              IntArray::missing_i(a, i, 0, n@pre, la) *
              data_at(a + (i * sizeof(int)), int, la[i]) *
              IntArray::missing_i(b, i, 0, n@pre, lb) *
              data_at(b + (i * sizeof(int)), int, lb[i]) *
              IntArray::missing_i(out, i, 0, n@pre, app(l1, l2)) *
              data_at(out + (i * sizeof(int)), int, lo[i])
        */
        out[i] = a[i] + b[i];
        /*@ exists l1 l2,
              0 <= i && i < n@pre &&
              a == a@pre &&
              b == b@pre &&
              out == out@pre &&
              n@pre == Zlength(la) &&
              n@pre == Zlength(lb) &&
              n@pre == Zlength(lo) &&
              Zlength(l1) == i &&
              Zlength(l2) == n@pre - i &&
              (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k] + lb[k]) &&
              (forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == lo[i + k]) &&
              IntArray::missing_i(a, i, 0, n@pre, la) *
              data_at(a + (i * sizeof(int)), int, la[i]) *
              IntArray::missing_i(b, i, 0, n@pre, lb) *
              data_at(b + (i * sizeof(int)), int, lb[i]) *
              IntArray::missing_i(out, i, 0, n@pre, app(l1, l2)) *
              data_at(out + (i * sizeof(int)), int, la[i] + lb[i])
            which implies
              exists l1',
                Zlength(l1') == i + 1 &&
                (forall (k: Z), (0 <= k && k < i + 1) => l1'[k] == la[k] + lb[k]) &&
              IntArray::full(a, n@pre, la) *
              IntArray::full(b, n@pre, lb) *
              IntArray::full(out, n@pre, app(l1', sublist(i + 1, n@pre, lo)))
        */
    }
}
