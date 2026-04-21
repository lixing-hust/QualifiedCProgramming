#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int is_sorted_nondecreasing(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1])) ||
       (__return == 0 &&
        (exists i, 0 <= i && i + 1 < n && l[i] > l[i + 1]))) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    /*@ Inv
          0 <= i && i <= n &&
          n <= INT_MAX &&
          i + 1 <= INT_MAX &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z), (0 <= j && j + 1 < i) => l[j] <= l[j + 1]) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i + 1 < n; ++i) {
        if (a[i] > a[i + 1]) {
            /*@ Assert
                  0 <= i && i + 1 < n &&
                  a == a@pre &&
                  n == n@pre &&
                  l[i] > l[i + 1] &&
                  IntArray::full(a, n, l)
            */
            return 0;
        }
    }

    /*@ Assert
          0 <= i && i <= n &&
          n <= INT_MAX &&
          i + 1 >= n &&
          i + 1 <= INT_MAX &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z), (0 <= j && j + 1 < n) => l[j] <= l[j + 1]) &&
          IntArray::full(a, n, l)
    */
    return 1;
}
