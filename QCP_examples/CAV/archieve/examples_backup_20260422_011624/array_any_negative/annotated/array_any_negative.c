#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_any_negative(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (exists i, 0 <= i && i < n && l[i] < 0)) ||
       (__return == 0 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] >= 0))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    /*@ Inv
          0 <= i && i <= n &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z), (0 <= j && j < i) => l[j] >= 0) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            return 1;
        }
    }

    /*@ Assert
          i == n &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z), (0 <= j && j < n) => l[j] >= 0) &&
          IntArray::full(a, n, l)
    */
    return 0;
}
