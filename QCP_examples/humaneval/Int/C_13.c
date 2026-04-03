#include "../verification_stdlib.h"
/*@ Extern Coq (Zgcd: Z -> Z -> Z) */

int greatest_common_divisor(int a, int b) 
/*@ Require
        INT_MIN < a && a <= INT_MAX && 
        INT_MIN < b && b <= INT_MAX && 
        (a != 0 || b != 0) && emp
    Ensure
        __return == Zgcd(a,b) && emp
*/
{
    int m;
    /*@ Inv
        Zgcd(a, b) == Zgcd(a@pre, b@pre) && a >= 0 && b > 0
    */
    while (1) {
        if (a < b) {
            m = a;
            a = b;
            b = m;
        }
        a = a % b;
        if (a == 0) return b;
    }
}
