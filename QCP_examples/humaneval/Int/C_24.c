#include "../verification_stdlib.h"

int largest_divisor(int n)
/*@ Require
        2 <= n && n <= INT_MAX && emp
    Ensure
        n % __return == 0 &&
        __return < n &&
        (forall i, 0 < i && i < n && n % i == 0 => i <= __return) && emp
*/
{
    int i;
    /*@ Inv
        2 <= i && emp
    */
    for (i=2; i*i<=n; i++) {
        if (n%i==0) return n/i;
    }
    return 1;
}