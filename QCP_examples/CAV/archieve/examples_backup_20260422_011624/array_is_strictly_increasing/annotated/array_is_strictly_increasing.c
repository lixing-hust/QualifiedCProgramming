#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_is_strictly_increasing(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (forall (i: Z), (1 <= i && i < n) => l[i - 1] < l[i])) ||
       (__return == 0 &&
        (exists i, 1 <= i && i < n && l[i - 1] >= l[i]))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    /*@ Inv
          1 <= i && i <= n + 1 &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z), (1 <= j && j < i) => l[j - 1] < l[j]) &&
          IntArray::full(a, n, l)
    */
    for (i = 1; i < n; ++i) {
        if (a[i - 1] >= a[i]) {
            /*@ Assert
                  1 <= i && i < n &&
                  a == a@pre &&
                  n == n@pre &&
                  l[i - 1] >= l[i] &&
                  IntArray::full(a, n, l)
            */
            return 0;
        }
    }

    /*@ Assert
          1 <= i && i <= n + 1 &&
          i >= n &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z), (1 <= j && j < n) => l[j - 1] < l[j]) &&
          IntArray::full(a, n, l)
    */
    return 1;
}
