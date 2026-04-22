#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (majority_candidate_spec : list Z -> Z) */
/*@ Extern Coq (majority_candidate_acc : Z -> Z -> list Z -> Z) */
/*@ Import Coq Require Import majority_candidate */

int majority_candidate(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i;
    int candidate = a[0];
    int count = 1;

    /*@ Inv
          1 <= i && i <= n@pre &&
          0 <= count && count <= i &&
          a == a@pre &&
          n == n@pre &&
          n@pre == Zlength(l) &&
          majority_candidate_acc(candidate, count, sublist(i, n@pre, l)) ==
            majority_candidate_spec(l) &&
          IntArray::full(a, n@pre, l)
    */
    for (i = 1; i < n; ++i) {
        if (count == 0) {
            candidate = a[i];
            count = 1;
        } else if (a[i] == candidate) {
            count++;
        } else {
            count--;
        }
    }

    return candidate;
}
