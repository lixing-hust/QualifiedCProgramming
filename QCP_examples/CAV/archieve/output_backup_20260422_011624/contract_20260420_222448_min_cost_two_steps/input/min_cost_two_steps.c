#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"

/*@ Extern Coq (min_cost_two_steps_z: list Z -> Z) */
/*@ Import Coq Require Import min_cost_two_steps */

int min_cost_two_steps(int n, int *cost)
/*@ With l
    Require
      1 <= n && n <= 10000 &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i < n) => 0 <= l[i]) &&
      sum(l) <= 2147483647 &&
      IntArray::full(cost, n, l)
    Ensure
      __return == min_cost_two_steps_z(l) &&
      IntArray::full(cost, n, l)
*/
{
    int i;
    int prev2;
    int prev1;
    int cur;

    if (n == 1) {
        return cost[0];
    }

    prev2 = cost[0];
    prev1 = cost[0] + cost[1];

    for (i = 2; i < n; ++i) {
        if (prev1 < prev2) {
            cur = prev1 + cost[i];
        } else {
            cur = prev2 + cost[i];
        }
        prev2 = prev1;
        prev1 = cur;
    }

    return prev1;
}
