#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_sign(int n, int *a, int *out)
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
          ((la[i] > 0 => lr[i] == 1) &&
           (la[i] < 0 => lr[i] == -1) &&
           (la[i] == 0 => lr[i] == 0))) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lr)
*/
{
    int i;
    int v;
    int s;

    /*@ Inv exists l1 l2,
          0 <= i && i <= n@pre &&
          a == a@pre &&
          out == out@pre &&
          n == n@pre &&
          n@pre == Zlength(la) &&
          n@pre == Zlength(lo) &&
          Zlength(l1) == i &&
          Zlength(l2) == n@pre - i &&
          (forall (t: Z), (0 <= t && t < i && la[t] > 0) => l1[t] == 1) &&
          (forall (t: Z), (0 <= t && t < i && la[t] < 0) => l1[t] == -1) &&
          (forall (t: Z), (0 <= t && t < i && la[t] == 0) => l1[t] == 0) &&
          (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
          IntArray::full(a, n@pre, la) *
          IntArray::full(out, n@pre, app(l1, l2))
    */
    for (i = 0; i < n; ++i) {
        v = a[i];
        if (v > 0) {
            s = 1;
        } else if (v < 0) {
            s = -1;
        } else {
            s = 0;
        }

        /*@ Assert exists l1 l2,
              0 <= i && i < n@pre &&
              a == a@pre &&
              out == out@pre &&
              (la[i] > 0 => s == 1) &&
              (la[i] < 0 => s == -1) &&
              (la[i] == 0 => s == 0) &&
              n@pre == Zlength(la) &&
              n@pre == Zlength(lo) &&
              Zlength(l1) == i &&
              Zlength(l2) == n@pre - i &&
              (forall (t: Z), (0 <= t && t < i && la[t] > 0) => l1[t] == 1) &&
              (forall (t: Z), (0 <= t && t < i && la[t] < 0) => l1[t] == -1) &&
              (forall (t: Z), (0 <= t && t < i && la[t] == 0) => l1[t] == 0) &&
              (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
              IntArray::full(a@pre, n@pre, la) *
              IntArray::full(out@pre, n@pre, app(l1, l2))
        */
        /*@ exists l1 l2,
              0 <= i && i < n@pre &&
              a == a@pre &&
              out == out@pre &&
              (la[i] > 0 => s == 1) &&
              (la[i] < 0 => s == -1) &&
              (la[i] == 0 => s == 0) &&
              n@pre == Zlength(la) &&
              n@pre == Zlength(lo) &&
              Zlength(l1) == i &&
              Zlength(l2) == n@pre - i &&
              (forall (t: Z), (0 <= t && t < i && la[t] > 0) => l1[t] == 1) &&
              (forall (t: Z), (0 <= t && t < i && la[t] < 0) => l1[t] == -1) &&
              (forall (t: Z), (0 <= t && t < i && la[t] == 0) => l1[t] == 0) &&
              (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
              IntArray::full(a@pre, n@pre, la) *
              IntArray::full(out@pre, n@pre, app(l1, l2))
            which implies
              (la[i] > 0 => s == 1) &&
              (la[i] < 0 => s == -1) &&
              (la[i] == 0 => s == 0) &&
              IntArray::missing_i(out@pre, i, 0, n@pre, app(l1, l2)) *
              data_at(out@pre + (i * sizeof(int)), int, lo[i])
        */
        out[i] = s;
        /*@ exists l1 l2,
              0 <= i && i < n@pre &&
              a == a@pre &&
              out == out@pre &&
              (la[i] > 0 => s == 1) &&
              (la[i] < 0 => s == -1) &&
              (la[i] == 0 => s == 0) &&
              n@pre == Zlength(la) &&
              n@pre == Zlength(lo) &&
              Zlength(l1) == i &&
              Zlength(l2) == n@pre - i &&
              (forall (t: Z), (0 <= t && t < i && la[t] > 0) => l1[t] == 1) &&
              (forall (t: Z), (0 <= t && t < i && la[t] < 0) => l1[t] == -1) &&
              (forall (t: Z), (0 <= t && t < i && la[t] == 0) => l1[t] == 0) &&
              (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
              IntArray::full(a@pre, n@pre, la) *
              IntArray::missing_i(out@pre, i, 0, n@pre, app(l1, l2)) *
              data_at(out@pre + (i * sizeof(int)), int, s)
            which implies
              exists l1',
                Zlength(l1') == i + 1 &&
                (forall (t: Z), (0 <= t && t < i + 1 && la[t] > 0) => l1'[t] == 1) &&
                (forall (t: Z), (0 <= t && t < i + 1 && la[t] < 0) => l1'[t] == -1) &&
                (forall (t: Z), (0 <= t && t < i + 1 && la[t] == 0) => l1'[t] == 0) &&
                IntArray::full(a@pre, n@pre, la) *
                IntArray::full(out@pre, n@pre, app(l1', sublist(i + 1, n@pre, lo)))
        */
    }
}
