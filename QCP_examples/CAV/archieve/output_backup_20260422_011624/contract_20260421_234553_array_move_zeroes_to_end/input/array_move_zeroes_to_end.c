/*@ Extern Coq (move_zeroes_to_end_spec: list Z -> list Z) */
/*@ Import Coq Require Import array_move_zeroes_to_end */

void array_move_zeroes_to_end(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      IntArray::full(a, n, move_zeroes_to_end_spec(l))
*/
{
    int write = 0;
    int i = 0;
    while (i < n) {
        if (a[i] != 0) {
            a[write] = a[i];
            write++;
        }
        i++;
    }
    while (write < n) {
        a[write] = 0;
        write++;
    }
}
