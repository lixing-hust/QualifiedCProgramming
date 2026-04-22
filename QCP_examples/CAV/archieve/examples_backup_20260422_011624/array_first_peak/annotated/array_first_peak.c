#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_first_peak(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((
        __return == -1 &&
        (forall (i: Z),
          (0 < i && i < n - 1) =>
            (l[i] < l[i - 1] || l[i] < l[i + 1]))
      ) || (
        0 < __return &&
        __return < n - 1 &&
        l[__return] >= l[__return - 1] &&
        l[__return] >= l[__return + 1] &&
        (forall (i: Z),
          (0 < i && i < __return) =>
            (l[i] < l[i - 1] || l[i] < l[i + 1]))
      )) &&
      IntArray::full(a, n, l)
*/
{
    int i = 1;

    /*@ Inv
          1 <= i && i <= n + 1 &&
          i + 1 <= INT_MAX &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z),
            (0 < j && j < i) =>
              (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
          IntArray::full(a, n, l)
    */
    while (i + 1 < n) {
        if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
            return i;
        }
        i++;
    }

    /*@ Assert
          i + 1 >= n &&
          1 <= i && i <= n + 1 &&
          i + 1 <= INT_MAX &&
          a == a@pre &&
          n == n@pre &&
          (forall (j: Z),
            (0 < j && j < n - 1) =>
              (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
          IntArray::full(a, n, l)
    */
    return -1;
}
