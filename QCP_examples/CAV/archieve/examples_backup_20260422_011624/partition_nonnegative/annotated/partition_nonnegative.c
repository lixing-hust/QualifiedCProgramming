#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop) */

int partition_nonnegative(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= 2000 &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        0 <= __return && __return <= n &&
        Permutation(l, l0) &&
        (forall (i: Z), (0 <= i && i < __return) => l0[i] < 0) &&
        (forall (i: Z), (__return <= i && i < n) => l0[i] >= 0) &&
        IntArray::full(a, n, l0)
*/
{
    int i = 0;
    int j = n - 1;
    int tmp;

    /*@ Inv
          exists l_cur,
            0 <= i && i <= n@pre &&
            -1 <= j && j < n@pre &&
            i <= j + 1 &&
            n == n@pre && a == a@pre &&
            Permutation(l, l_cur) &&
            (forall (p: Z),
              (0 <= p && p < i) => l_cur[p] < 0) &&
            (forall (q: Z),
              (j < q && q < n@pre) => l_cur[q] >= 0) &&
            IntArray::full(a, n@pre, l_cur)
    */
    while (i <= j) {
        if (a[i] < 0) {
            i++;
        } else {
            tmp = a[i];
            a[i] = a[j];
            a[j] = tmp;
            j--;
        }
    }

    return i;
}
