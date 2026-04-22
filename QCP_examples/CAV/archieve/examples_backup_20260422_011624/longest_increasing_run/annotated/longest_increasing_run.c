#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (longest_increasing_run_spec : list Z -> Z) */
/*@ Extern Coq (longest_increasing_run_acc : Z -> Z -> Z -> list Z -> Z) */
/*@ Import Coq Require Import longest_increasing_run */

int longest_increasing_run(int n, int *a)
/*@ With l
    Require
      0 <= n && n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == longest_increasing_run_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int cur;
    int best;

    if (n == 0) {
        return 0;
    }

    cur = 1;
    best = 1;
    /*@ Inv
          1 <= i && i <= n &&
          n == n@pre &&
          a == a@pre &&
          n@pre == Zlength(l) &&
          1 <= cur && cur <= i &&
          1 <= best && best <= i &&
          longest_increasing_run_acc(cur, best, Znth(i - 1, l, 0), sublist(i, n, l)) ==
            longest_increasing_run_spec(l) &&
          IntArray::full(a, n, l)
    */
    for (i = 1; i < n; ++i) {
        if (a[i - 1] < a[i]) {
            cur++;
        } else {
            cur = 1;
        }
        if (best < cur) {
            best = cur;
        }
    }

    return best;
}
