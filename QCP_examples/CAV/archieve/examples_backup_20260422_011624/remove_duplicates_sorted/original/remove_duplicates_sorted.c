#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (remove_duplicates_sorted_spec : list Z -> list Z) */
/*@ Import Coq Require Import remove_duplicates_sorted */

int remove_duplicates_sorted(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i + 1 < n) => l[i] <= l[i + 1]) &&
      IntArray::full(a, n, l)
    Ensure
      exists lr t,
        __return == Zlength(remove_duplicates_sorted_spec(l)) &&
        0 <= __return && __return <= n &&
        Zlength(lr) == n &&
        lr == app(remove_duplicates_sorted_spec(l), t) &&
        IntArray::full(a, n, lr)
*/
{
    int i;
    int j;

    if (n == 0) {
        return 0;
    }

    j = 1;
    for (i = 1; i < n; ++i) {
        if (a[i] != a[j - 1]) {
            a[j] = a[i];
            j++;
        }
    }

    return j;
}
