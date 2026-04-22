#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void rotate_left_by_one(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        Zlength(l0) == n &&
        l0[n - 1] == l[0] &&
        (forall (i: Z), (0 <= i && i + 1 < n) => l0[i] == l[i + 1]) &&
        IntArray::full(a, n, l0)
*/
{
    int i;
    int first = a[0];

    for (i = 0; i + 1 < n; ++i) {
        a[i] = a[i + 1];
    }
    a[n - 1] = first;
}
