#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (find_first_equal_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import find_first_equal */

int find_first_equal(int n, int *a, int k)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == find_first_equal_spec(l, k) &&
      IntArray::full(a, n, l)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            return i;
        }
    }

    return -1;
}
