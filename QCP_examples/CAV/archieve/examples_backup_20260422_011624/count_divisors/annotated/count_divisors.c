#include "../../verification_stdlib.h"

/*@ Extern Coq (count_divisors_spec : Z -> Z) */
/*@ Extern Coq (count_divisors_prefix : Z -> Z -> Z) */
/*@ Import Coq Require Import count_divisors */
/*@ Import Coq Require Import count_divisors_verify_aux */

int count_divisors(int n)
/*@ Require
      1 <= n && n < INT_MAX && emp
    Ensure
      __return == count_divisors_spec(n@pre) && emp
*/
{
    int d;
    int cnt = 0;

    /*@ Inv
          1 <= d && d <= n + 1 &&
          n == n@pre &&
          cnt == count_divisors_prefix(n, d - 1) &&
          emp
    */
    for (d = 1; d <= n; ++d) {
        if (n % d == 0) {
            cnt++;
        }
    }

    /*@ Assert
          d == n + 1 &&
          n == n@pre &&
          cnt == count_divisors_spec(n) &&
          emp
    */
    return cnt;
}
