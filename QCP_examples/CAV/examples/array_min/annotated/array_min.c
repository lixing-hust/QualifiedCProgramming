#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (min_list_nonempty : list Z -> Z) */
/*@ Import Coq Require Import array_min */

int array_min(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == min_list_nonempty(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int ret = a[0];

    /*@ Inv
          1 <= i && i <= n && n == n@pre && a == a@pre &&
          ret == min_list_nonempty(sublist(0, i, l))
    */
    for (i = 1; i < n; ++i) {
        if (a[i] < ret) {
            ret = a[i];
        }
    }

    return ret;
}
