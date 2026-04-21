/*@ Extern Coq (array_equal_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import array_equal */

int array_equal(int n, int *a, int *b)
/*@ With la, lb
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lb) == n &&
      IntArray::full(a, n, la) &&
      IntArray::full(b, n, lb)
    Ensure
      __return == array_equal_spec(la, lb) &&
      IntArray::full(a, n, la) &&
      IntArray::full(b, n, lb)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] != b[i]) {
            return 0;
        }
    }

    return 1;
}
