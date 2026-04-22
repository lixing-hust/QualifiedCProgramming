#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_any_equal_sum(int n, int *a, int x, int y)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      INT_MIN <= x + y && x + y <= INT_MAX &&
      IntArray::full(a, n, l)
    Ensure
      ((__return == 1 &&
        (exists i, 0 <= i && i < n && l[i] == x + y)) ||
       (__return == 0 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != x + y))) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int target = x + y;

    /*@ Inv
          0 <= i && i <= n &&
          a == a@pre &&
          n == n@pre &&
          x == x@pre &&
          y == y@pre &&
          target == x + y &&
          INT_MIN <= target && target <= INT_MAX &&
          (forall (j: Z), (0 <= j && j < i) => l[j] != target) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] == target) {
            return 1;
        }
    }

    /*@ Assert
          i == n &&
          a == a@pre &&
          n == n@pre &&
          x == x@pre &&
          y == y@pre &&
          target == x + y &&
          INT_MIN <= target && target <= INT_MAX &&
          (forall (j: Z), (0 <= j && j < n) => l[j] != target) &&
          IntArray::full(a, n, l)
    */
    return 0;
}
