#include "../../verification_stdlib.h"

/*@ Extern Coq (digit_sum_z : Z -> Z) */
/*@ Import Coq Require Import digit_sum */

int digit_sum(int n)
/*@ Require
      0 <= n && n <= INT_MAX && emp
    Ensure
      __return == digit_sum_z(n@pre) && emp
*/
{
    int sum = 0;

    /*@ Inv
          0 <= n && n <= INT_MAX &&
          0 <= sum &&
          sum + n <= n@pre &&
          sum + digit_sum_z(n) == digit_sum_z(n@pre) &&
          emp
    */
    while (n > 0) {
        sum += n % 10;
        n = n / 10;
    }

    /*@ Assert
          n == 0 &&
          sum == digit_sum_z(n@pre) &&
          emp
    */
    return sum;
}
