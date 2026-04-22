#include "../../verification_stdlib.h"

/*@ Extern Coq (reverse_digits_z : Z -> Z) */
/*@ Extern Coq (reverse_digits_acc_z : Z -> Z -> Z) */
/*@ Import Coq Require Import reverse_digits */
/*@ Import Coq Require Import reverse_digits_verify_aux */

int reverse_digits(int n)
/*@ Require
      0 <= n && n <= INT_MAX &&
      reverse_digits_z(n) <= INT_MAX &&
      emp
    Ensure
      __return == reverse_digits_z(n@pre) && emp
*/
{
    int ans = 0;

    /*@ Inv
          0 <= n && n <= INT_MAX &&
          0 <= ans &&
          ans <= reverse_digits_z(n@pre) &&
          reverse_digits_z(n@pre) <= INT_MAX &&
          reverse_digits_acc_z(n, ans) == reverse_digits_z(n@pre) &&
          emp
    */
    while (n > 0) {
        ans = ans * 10 + n % 10;
        n = n / 10;
    }

    /*@ Assert
          n == 0 &&
          ans == reverse_digits_z(n@pre) &&
          reverse_digits_z(n@pre) <= INT_MAX &&
          emp
    */
    return ans;
}
