#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (second_largest_list : list Z -> Z) */
/*@ Import Coq Require Import array_second_largest */

int array_second_largest(int n, int *a)
/*@ With l
    Require
      2 <= n &&
      Zlength(l) == n &&
      (forall (i: Z),
        (forall (j: Z),
          (0 <= i && i < n && 0 <= j && j < n && i != j) => l[i] != l[j])) &&
      IntArray::full(a, n, l)
    Ensure
      __return == second_largest_list(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int max1 = a[0];
    int max2 = a[1];

    if (max2 > max1) {
        int t = max1;
        max1 = max2;
        max2 = t;
    }

    for (i = 2; i < n; ++i) {
        if (a[i] > max1) {
            max2 = max1;
            max1 = a[i];
        } else if (a[i] > max2) {
            max2 = a[i];
        }
    }

    return max2;
}
