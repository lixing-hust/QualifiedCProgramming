#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_last_positive(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((
        __return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] <= 0)
      ) || (
        0 <= __return &&
        __return < n &&
        l[__return] > 0 &&
        (forall (i: Z), (__return < i && i < n) => l[i] <= 0)
      )) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int ans = -1;

    /*@ Inv
          0 <= i && i <= n &&
          a == a@pre &&
          n == n@pre &&
          -1 <= ans &&
          ans < i &&
          (ans == -1 => (forall (j: Z), (0 <= j && j < i) => l[j] <= 0)) &&
          (0 <= ans => l[ans] > 0) &&
          (forall (j: Z), (ans < j && j < i) => l[j] <= 0) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            ans = i;
        }
    }

    /*@ Assert
          i == n &&
          a == a@pre &&
          n == n@pre &&
          -1 <= ans &&
          ans < n &&
          (ans == -1 => (forall (j: Z), (0 <= j && j < n) => l[j] <= 0)) &&
          (0 <= ans => l[ans] > 0) &&
          (forall (j: Z), (ans < j && j < n) => l[j] <= 0) &&
          IntArray::full(a, n, l)
    */
    return ans;
}
