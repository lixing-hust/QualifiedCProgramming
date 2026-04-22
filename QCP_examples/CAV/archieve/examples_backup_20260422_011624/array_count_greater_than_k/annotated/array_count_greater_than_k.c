#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_greater_than_k_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import array_count_greater_than_k */

int array_count_greater_than_k(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_greater_than_k_spec(l, k) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cnt = 0;

    /*@ Inv
          0 <= i && i <= n &&
          a == a@pre &&
          n == n@pre &&
          k == k@pre &&
          cnt == array_count_greater_than_k_spec(sublist(0, i, l), k) &&
          IntArray::full(a, n, l)
    */
    for (i = 0; i < n; ++i) {
        if (a[i] > k) {
            cnt++;
        }
    }

    /*@ Assert
          i == n &&
          a == a@pre &&
          n == n@pre &&
          k == k@pre &&
          cnt == array_count_greater_than_k_spec(l, k) &&
          IntArray::full(a, n, l)
    */
    return cnt;
}
