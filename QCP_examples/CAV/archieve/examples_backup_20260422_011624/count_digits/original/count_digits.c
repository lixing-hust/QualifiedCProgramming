#include "../../verification_stdlib.h"

/*@ Extern Coq (count_digits_z : Z -> Z) */
/*@ Import Coq Require Import count_digits */

int count_digits(int n)
/*@ Require
      0 <= n && n <= INT_MAX && emp
    Ensure
      __return == count_digits_z(n@pre) && emp
*/
{
    int cnt = 0;

    if (n == 0) {
        return 1;
    }

    while (n > 0) {
        cnt++;
        n = n / 10;
    }

    return cnt;
}
