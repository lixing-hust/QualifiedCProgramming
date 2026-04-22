#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_count_distinct_sorted_spec : list Z -> Z) */
/*@ Import Coq Require Import array_count_distinct_sorted */

int array_count_distinct_sorted(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_distinct_sorted_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    if (n == 0) {
        return 0;
    }
    int count = 1;
    int i = 1;
    /*@ Inv
          1 <= i && i <= n &&
          1 <= count && count <= i &&
          a == a@pre &&
          n == n@pre &&
          count == array_count_distinct_sorted_spec(sublist(0, i, l)) &&
          IntArray::full(a, n, l)
    */
    while (i < n) {
        if (a[i] != a[i - 1]) {
            count++;
        }
        i++;
    }
    return count;
}
