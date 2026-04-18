#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

void array_increment(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i < n) => l[i] < 2147483647) &&
      IntArray::full(a, n, l)
    Ensure
      exists l0,
        Zlength(l0) == n &&
        (forall (i: Z), (0 <= i && i < n) => l0[i] == l[i] + 1) &&
        IntArray::full(a, n, l0)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        a[i] = a[i] + 1;
    }
}
