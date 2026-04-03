
#include "../verification_stdlib.h"

/*@ Extern Coq (fizz_buzz_coq: Z -> Z) */

int fizz_buzz(int n)
/*@ Require
        0 <= n && n <= INT_MAX && emp
    Ensure
        __return == fizz_buzz_coq(n) && emp
*/
{
    int count = 0;
    int i;
    /*@ Inv
        0 <= i && i <= n@pre && emp
    */
    for (i = 0; i < n; i++) {
        if (i % 11 == 0 || i % 13 == 0) {
            int q = i;
            /*@ Inv
                0 <= q && q <= i && emp
            */
            while (q > 0) {
                if (q % 10 == 7) count += 1;
                q = q / 10;
            }
        }
    } 
    return count;
}
