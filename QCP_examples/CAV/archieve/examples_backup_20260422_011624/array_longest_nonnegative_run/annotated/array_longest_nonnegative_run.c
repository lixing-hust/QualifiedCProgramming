#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (array_longest_nonnegative_run_spec : list Z -> Z) */
/*@ Extern Coq (array_longest_nonnegative_run_acc : Z -> Z -> list Z -> Z) */
/*@ Import Coq Require Import array_longest_nonnegative_run */

int array_longest_nonnegative_run(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_longest_nonnegative_run_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int best = 0;
    int current = 0;
    int i = 0;
    /*@ Inv
          0 <= i && i <= n@pre &&
          0 <= current && current <= i &&
          0 <= best && best <= i &&
          n == n@pre &&
          a == a@pre &&
          n@pre == Zlength(l) &&
          array_longest_nonnegative_run_acc(current, best, sublist(i, n@pre, l)) ==
            array_longest_nonnegative_run_spec(l) &&
          IntArray::full(a, n@pre, l)
    */
    while (i < n) {
        if (a[i] >= 0) {
            current++;
            if (current > best) {
                best = current;
            }
        } else {
            current = 0;
        }
        i++;
    }
    return best;
}
