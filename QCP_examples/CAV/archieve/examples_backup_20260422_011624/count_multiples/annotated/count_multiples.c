#include "../../verification_stdlib.h"

/*@ Extern Coq (count_multiples_spec : Z -> Z -> Z) */
/*@ Import Coq Require Import count_multiples */

int count_multiples(int n, int k)
/*@ Require
      1 <= n && n < INT_MAX &&
      1 <= k && emp
    Ensure
      __return == count_multiples_spec(n@pre, k@pre) && emp
*/
{
    int i;
    int cnt = 0;

    /*@ Inv
          1 <= i && i <= n + 1 &&
          n == n@pre &&
          k == k@pre &&
          1 <= n && n < INT_MAX &&
          1 <= k &&
          0 <= cnt && cnt <= i - 1 &&
          cnt == count_multiples_spec(i - 1, k) &&
          emp
    */
    for (i = 1; i <= n; ++i) {
        if (i % k == 0) {
            cnt++;
        }
    }

    /*@ Assert
          i == n + 1 &&
          n == n@pre &&
          k == k@pre &&
          cnt == count_multiples_spec(n, k) &&
          emp
    */
    return cnt;
}
