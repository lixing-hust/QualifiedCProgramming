#include "../../verification_stdlib.h"

int is_prime_simple(int n)
/*@ Require
      0 <= n && emp
    Ensure
      ((__return == 1 &&
        2 <= n@pre &&
        (forall (d: Z), (2 <= d && d < n@pre) => n@pre % d != 0)) ||
       (__return == 0 &&
        (n@pre < 2 ||
         (exists d, 2 <= d && d < n@pre && n@pre % d == 0)))) &&
      emp
*/
{
    int d;

    if (n < 2) {
        return 0;
    }

    for (d = 2; d < n; ++d) {
        if (n % d == 0) {
            return 0;
        }
    }

    return 1;
}
