#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

int array_find_last_equal(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      ((
        __return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => l[i] != k)
      ) || (
        0 <= __return &&
        __return < n &&
        l[__return] == k &&
        (forall (i: Z), (__return < i && i < n) => l[i] != k)
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
          k == k@pre &&
          -1 <= ans &&
          ans < i &&
          (ans == -1 => (forall (j: Z), (0 <= j && j < i) => l[j] != k)) &&
          (0 <= ans => l[ans] == k) &&
          (forall (j: Z), (ans < j && j < i) => l[j] != k) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            ans = i;
        }
    }

    /*@ Assert
          i == n &&
          a == a@pre &&
          n == n@pre &&
          k == k@pre &&
          -1 <= ans &&
          ans < n &&
          (ans == -1 => (forall (j: Z), (0 <= j && j < n) => l[j] != k)) &&
          (0 <= ans => l[ans] == k) &&
          (forall (j: Z), (ans < j && j < n) => l[j] != k) &&
          IntArray::full(a, n, l)
    */
    return ans;
}
